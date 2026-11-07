module

public import Chapter02OAState
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Exact dimension/initialization controls for the concrete OA procedure. -/
noncomputable section
open scoped BigOperators
namespace Chapter02
namespace OAEdgeExamples

def singletonModel : ModelData 0 0 1 0 where
  g := fun _ _ => -1
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

theorem singleton_objective (p : Point 0 0) : singletonModel.objective p = 0 := by
  simp [singletonModel,ModelData.objective,LinearForm]

theorem singleton_feasible (p : Point 0 0) :
    p ∈ singletonModel.feasibleOn Set.univ := by
  refine ⟨⟨⟨Set.mem_univ _,?_⟩,?_⟩,0,?_,?_⟩
  · intro j
    norm_num [singletonModel]
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · exact Subsingleton.elim _ _

theorem singleton_compact : IsCompact
    (singletonModel.linearRegion ∩ IntegerCylinder (n := 0) singletonModel.lo singletonModel.hi) :=
  Set.toFinite _ |>.isCompact

theorem singleton_convex : ∀ j, ConvexOn ℝ Set.univ (singletonModel.g j) := by
  intro j
  exact convexOn_const (-1) convex_univ

theorem singleton_diff : ∀ j, Differentiable ℝ (singletonModel.g j) := by
  intro j
  exact differentiable_const _

theorem singleton_CQ : OAFiberSlater singletonModel := by
  intro y _ _
  refine ⟨0,⟨?_,Subsingleton.elim _ _⟩,?_⟩
  · intro i
    exact Fin.elim0 i
  · intro j
    norm_num [singletonModel]

def singletonBatch : OABatch 0 0 := ⟨0,0,none⟩

theorem singleton_batch_valid : oaBatchValid singletonModel singletonBatch := by
  refine ⟨?_,Subsingleton.elim _ _,?_,?_⟩
  · intro i
    exact Fin.elim0 i
  · exact ⟨⟨fun i => Fin.elim0 i,Subsingleton.elim _ _⟩,by intro j; norm_num [singletonModel,singletonBatch]⟩
  · intro p _
    simp [singleton_objective]

theorem singleton_master_min (H : List (OABatch 0 0)) :
    IsMinimizer (oaMaster singletonModel H) singletonModel.objective 0 := by
  refine ⟨oa_master_contains_feasible singletonModel H singleton_convex singleton_diff
    (singleton_feasible 0),?_⟩
  intro p _
  simp [singleton_objective]

theorem singleton_optional_early_return :
    OAStop singletonModel 0 (oaInit none) (.solution 0) :=
  .feasible (singleton_master_min []) (by intro u h; cases h) (singleton_feasible 0)

theorem singleton_continue_without_early_return :
    OAContinue singletonModel 0 (oaInit none)
      (oaAppend singletonModel (oaInit none) singletonBatch) :=
  .step (singleton_master_min []) (by intro u h; cases h)
    singleton_batch_valid (Subsingleton.elim _ _)

theorem singleton_gap_after_one :
    OAStop singletonModel 0 (oaAppend singletonModel (oaInit none) singletonBatch)
      (.solution 0) := by
  refine OAStop.gap (q := (0 : Point 0 0))
    (singleton_master_min [singletonBatch]) ?_ ?_
  · rfl
  · simp [singleton_objective]

def fractionalBoxModel : ModelData 0 1 0 0 where
  g := Fin.elim0
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := 0
  c2 := 0
  lo := fun _ => 1/2
  hi := fun _ => 1/2

theorem fractional_integer_impossible (z : ℤ) : ¬ ((1/2 : ℝ) ≤ z ∧ (z : ℝ) ≤ 1/2) := by
  rintro ⟨hlo,hhi⟩
  have hlo' := Int.ceil_le.mpr hlo
  have hhi' := Int.le_floor.mpr hhi
  norm_num at hlo' hhi'
  omega

theorem fractional_base_empty :
    fractionalBoxModel.linearRegion ∩ IntegerCylinder (n := 0)
      fractionalBoxModel.lo fractionalBoxModel.hi = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨_,y,hy,_⟩
  exact fractional_integer_impossible (y 0) (hy 0)

theorem fractional_immediate_infeasible :
    OAStop fractionalBoxModel 0 (oaInit none) .infeasible := by
  apply OAStop.empty
  simpa only [oaInit,oa_master_nil] using fractional_base_empty

/-- Mixed compactness does not give an attained continuous initialization. -/
def badRelaxationModel : ModelData 1 1 0 2 where
  g := Fin.elim0
  A := fun _ _ => 0
  B := fun i _ => if i = 0 then 1 else -1
  rhs := fun i => if i = 0 then 1/2 else -1/2
  c1 := fun _ => 1
  c2 := 0
  lo := 0
  hi := fun _ => 1

theorem badRelaxation_linear_iff (p : Point 1 1) :
    p ∈ badRelaxationModel.linearRegion ↔ p.2 0 = 1/2 := by
  constructor
  · intro hp
    have h0 := hp 0
    have h1 := hp 1
    norm_num [LinearForm,badRelaxationModel,Fin.sum_univ_one] at h0 h1
    linarith
  · intro hp i
    fin_cases i <;> norm_num [LinearForm,badRelaxationModel,Fin.sum_univ_one,hp]

theorem badRelaxation_base_empty :
    badRelaxationModel.linearRegion ∩ IntegerCylinder (n := 1)
      badRelaxationModel.lo badRelaxationModel.hi = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hp,y,_,hy⟩
  have heq := (badRelaxation_linear_iff p).mp hp
  rw [hy] at heq
  exact fractional_integer_impossible (y 0) ⟨heq.ge,heq.le⟩

theorem badRelaxation_compact : IsCompact
    (badRelaxationModel.linearRegion ∩ IntegerCylinder (n := 1)
      badRelaxationModel.lo badRelaxationModel.hi) := by
  rw [badRelaxation_base_empty]
  exact isCompact_empty

theorem badRelaxation_feasible_line (x : ℝ) :
    ((fun _ => x),(fun _ => 1/2)) ∈ badRelaxationModel.relaxationOn Set.univ := by
  refine ⟨⟨Set.mem_univ _,fun j => Fin.elim0 j⟩,
    (badRelaxation_linear_iff _).mpr rfl,?_⟩
  intro i
  norm_num [badRelaxationModel]

theorem badRelaxation_objective (p : Point 1 1) :
    badRelaxationModel.objective p = p.1 0 := by
  simp [ModelData.objective,LinearForm,badRelaxationModel,Fin.sum_univ_one]

theorem badRelaxation_no_minimum :
    ¬ ∃ p, IsMinimizer (badRelaxationModel.relaxationOn Set.univ)
      badRelaxationModel.objective p := by
  rintro ⟨p,hp⟩
  have h := hp.2 _ (badRelaxation_feasible_line (p.1 0 - 1))
  simp only [badRelaxation_objective] at h
  linarith

theorem badRelaxation_mixed_return :
    OAStop badRelaxationModel 0 (oaInit none) .infeasible := by
  apply OAStop.empty
  simpa only [oaInit,oa_master_nil] using badRelaxation_base_empty

/-- With an available integer fiber, positive continuous dimension and no
affine rows, the required mixed-base compactness cannot hold. -/
theorem no_affine_nonempty_x_not_compact {n m l : ℕ} [Nonempty (Fin n)]
    (d : ModelData n m l 0) (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi) :
    ¬ IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) := by
  intro hc
  let i : Fin n := Classical.choice inferInstance
  have hcont : Continuous (fun p : Point n m => p.1 i) := by fun_prop
  obtain ⟨upper,hu⟩ := (hc.image hcont).bddAbove
  have hp : ((fun _ => upper + 1),oaIntCast y) ∈
      d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi :=
    ⟨fun row => Fin.elim0 row,y,hy,rfl⟩
  have hh := hu ⟨_,hp,rfl⟩
  change upper + 1 ≤ upper at hh
  linarith

theorem zero_rows_CQ {n m r : ℕ} (d : ModelData n m 0 r) : OAFiberSlater d := by
  intro y _ hne
  obtain ⟨p,hp⟩ := hne
  exact ⟨p,hp.1,fun j => Fin.elim0 j⟩

def zeroRowsModel : ModelData 0 0 0 0 where
  g := Fin.elim0
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

theorem zeroRows_feasible (p : Point 0 0) : p ∈ zeroRowsModel.feasibleOn Set.univ := by
  exact ⟨⟨⟨Set.mem_univ _,fun j => Fin.elim0 j⟩,fun i => Fin.elim0 i⟩,
    0,fun i => Fin.elim0 i,Subsingleton.elim _ _⟩

theorem zeroRows_master (H : List (OABatch 0 0)) :
    IsMinimizer (oaMaster zeroRowsModel H) zeroRowsModel.objective 0 := by
  refine ⟨?_,?_⟩
  · rw [oa_zero_rows_master_eq_feasible]
    exact zeroRows_feasible 0
  · intro q _
    simp [ModelData.objective,LinearForm,zeroRowsModel]

theorem zeroRows_batch_valid : oaBatchValid zeroRowsModel singletonBatch := by
  refine ⟨fun i => Fin.elim0 i,Subsingleton.elim _ _,?_,?_⟩
  · exact ⟨⟨fun i => Fin.elim0 i,Subsingleton.elim _ _⟩,fun j => Fin.elim0 j⟩
  · intro q _
    simp [ModelData.objective,LinearForm,zeroRowsModel]

theorem zeroRows_actual_returns :
    IsCompact (zeroRowsModel.linearRegion ∩ IntegerCylinder (n := 0)
      zeroRowsModel.lo zeroRowsModel.hi) ∧ OAFiberSlater zeroRowsModel ∧
    OAStop zeroRowsModel 0 (oaInit none) (.solution 0) ∧
    OAContinue zeroRowsModel 0 (oaInit none) (oaAppend zeroRowsModel (oaInit none) singletonBatch) ∧
    OAStop zeroRowsModel 0 (oaAppend zeroRowsModel (oaInit none) singletonBatch) (.solution 0) := by
  refine ⟨Set.toFinite _ |>.isCompact,zero_rows_CQ _,?_,?_,?_⟩
  · exact .feasible (zeroRows_master []) (by intro u h; cases h) (zeroRows_feasible 0)
  · exact .step (zeroRows_master []) (by intro u h; cases h)
      zeroRows_batch_valid (Subsingleton.elim _ _)
  · refine OAStop.gap (q := (0 : Point 0 0)) (zeroRows_master [singletonBatch]) rfl ?_
    simp [ModelData.objective,LinearForm,zeroRowsModel]

end OAEdgeExamples
end Chapter02

#print axioms Chapter02.OAEdgeExamples.singleton_feasible
#print axioms Chapter02.OAEdgeExamples.singleton_compact
#print axioms Chapter02.OAEdgeExamples.singleton_convex
#print axioms Chapter02.OAEdgeExamples.singleton_diff
#print axioms Chapter02.OAEdgeExamples.singleton_CQ
#print axioms Chapter02.OAEdgeExamples.singleton_batch_valid
#print axioms Chapter02.OAEdgeExamples.singleton_master_min
#print axioms Chapter02.OAEdgeExamples.singleton_optional_early_return
#print axioms Chapter02.OAEdgeExamples.singleton_continue_without_early_return
#print axioms Chapter02.OAEdgeExamples.singleton_gap_after_one
#print axioms Chapter02.OAEdgeExamples.fractional_integer_impossible
#print axioms Chapter02.OAEdgeExamples.fractional_base_empty
#print axioms Chapter02.OAEdgeExamples.fractional_immediate_infeasible
#print axioms Chapter02.OAEdgeExamples.badRelaxation_linear_iff
#print axioms Chapter02.OAEdgeExamples.badRelaxation_base_empty
#print axioms Chapter02.OAEdgeExamples.badRelaxation_compact
#print axioms Chapter02.OAEdgeExamples.badRelaxation_feasible_line
#print axioms Chapter02.OAEdgeExamples.badRelaxation_no_minimum
#print axioms Chapter02.OAEdgeExamples.badRelaxation_mixed_return
#print axioms Chapter02.OAEdgeExamples.no_affine_nonempty_x_not_compact
#print axioms Chapter02.OAEdgeExamples.zero_rows_CQ
#print axioms Chapter02.OAEdgeExamples.zeroRows_actual_returns
