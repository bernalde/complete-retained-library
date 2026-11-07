module

public import Chapter02KKTCuts
public import Chapter02ModelExamples

@[expose] public section

/-! Full-model W4 from the CH02-S005 independent source-first critique.
The original model has x ∈ [-2,2], integer y ∈ {0,1}, and two
jointly convex smooth rows. Restoration at y=0 has value 1. Selecting
one tied maximum, or selecting rows active at the original level zero,
does not exclude this infeasible integer assignment. No solver behavior
or multiplier-existence theorem is asserted here. -/
noncomputable section
open Chapter02 Chapter02Examples
open scoped BigOperators
namespace Chapter02KKTSelectionExamples

def pt (x y : ℝ) : Point 1 1 := (fun _ => x, fun _ => y)

def coordY : Point 1 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.snd ℝ (RealVector 1) (RealVector 1))

def selectionModel : ModelData 1 1 2 2 where
  g := fun j p => if j = 0 then (p.1 0)^2 + p.1 0 + 1 - 2 * p.2 0
    else (p.1 0)^2 - p.1 0 + 1 - 2 * p.2 0
  A := fun row _ => if row = 0 then 1 else -1
  B := fun _ _ => 0
  rhs := fun _ => 2
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

def rowDerivative (j : Fin 2) : Point 1 1 →L[ℝ] ℝ :=
  if j = 0 then coordX - (2 : ℝ) • coordY else -coordX - (2 : ℝ) • coordY

def lambda (_ : Fin 2) : ℝ := 1/2
def mu (_ : Fin 2) : ℝ := 0

theorem selection_rows_convex : ∀ j, ConvexOn ℝ Set.univ (selectionModel.g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t hs ht hst
  have hx : 0 ≤ s*t*(p.1 0-q.1 0)^2 :=
    mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
  fin_cases j <;> simp [selectionModel, smul_eq_mul] <;>
    nlinarith [sq_nonneg (p.1 0-q.1 0)]

theorem selection_rows_smooth : ∀ j, ContDiff ℝ 1 (selectionModel.g j) := by
  intro j
  have hx : ContDiff ℝ 1 (fun p : Point 1 1 => p.1 0) :=
    (contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst
  have hy : ContDiff ℝ 1 (fun p : Point 1 1 => p.2 0) :=
    (contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd
  fin_cases j
  · exact (((hx.pow 2).add hx).add contDiff_const).sub (contDiff_const.mul hy)
  · exact (((hx.pow 2).sub hx).add contDiff_const).sub (contDiff_const.mul hy)

theorem selection_base_compact :
    IsCompact (selectionModel.linearRegion ∩
      IntegerCylinder (n := 1) selectionModel.lo selectionModel.hi) := by
  have hL : IsClosed selectionModel.linearRegion := by
    have heq : selectionModel.linearRegion =
        ⋂ row, {p | LinearForm (selectionModel.A row) (selectionModel.B row) p ≤
          selectionModel.rhs row} := by
      ext p
      simp [ModelData.linearRegion]
    rw [heq]
    exact isClosed_iInter fun row =>
      isClosed_le (linearForm_continuous _ _) continuous_const
  have hY : IsClosed (IntegerCylinder (n := 1) selectionModel.lo selectionModel.hi) := by
    have hfin := (integerBox_finite selectionModel.lo selectionModel.hi).image
      (fun y : IntVector 1 => fun i => (y i : ℝ))
    have heq : IntegerCylinder (n := 1) selectionModel.lo selectionModel.hi =
        Prod.snd ⁻¹' ((fun y : IntVector 1 => fun i => (y i : ℝ)) ''
          IntegerBox selectionModel.lo selectionModel.hi) := by
      ext p
      simp [IntegerCylinder, eq_comm]
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  apply (isCompact_Icc : IsCompact (Set.Icc (pt (-2) 0) (pt 2 1))).of_isClosed_subset
    (hL.inter hY)
  rintro p ⟨hL, y, hy, hp⟩
  have hxlo := hL (1 : Fin 2)
  have hxhi := hL (0 : Fin 2)
  norm_num [selectionModel, LinearForm, Fin.sum_univ_one] at hxlo hxhi
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i
    fin_cases i
    change -2 ≤ p.1 0
    linarith
  · intro i
    rw [hp]
    exact (hy i).1
  · intro i
    fin_cases i
    exact hxhi
  · intro i
    rw [hp]
    exact (hy i).2

theorem selection_derivatives : ∀ j,
    HasFDerivAt (selectionModel.g j) (rowDerivative j) (pt 0 0) := by
  intro j
  have hsq := (hasDerivAt_pow 2 (0 : ℝ)).comp_hasFDerivAt (pt 0 0) coordX.hasFDerivAt
  fin_cases j
  · have h := ((hsq.add coordX.hasFDerivAt).add_const 1).sub
      (coordY.hasFDerivAt.const_mul 2)
    convert h using 1
    all_goals
      (try ext w) <;> norm_num [selectionModel, rowDerivative, coordX, coordY, pt, Function.comp_def, Pi.add_apply, Pi.sub_apply]
  · have h := ((hsq.sub coordX.hasFDerivAt).add_const 1).sub
      (coordY.hasFDerivAt.const_mul 2)
    convert h using 1
    all_goals
      (try ext w) <;> norm_num [selectionModel, rowDerivative, coordX, coordY, pt, Function.comp_def, Pi.add_apply, Pi.sub_apply]

theorem zero_linear_feasible : pt 0 0 ∈ selectionModel.linearRegion := by
  intro row
  fin_cases row <;> norm_num [selectionModel, pt, LinearForm, Fin.sum_univ_one]

theorem good_integer_feasible : pt 0 1 ∈ selectionModel.feasibleOn Set.univ := by
  rw [source_feasible_iff]
  refine ⟨Set.mem_univ _, ?_, ?_, fun _ => (1 : ℤ), ?_, by simp [pt]⟩
  · intro j
    fin_cases j <;> norm_num [selectionModel, pt]
  · intro row
    fin_cases row <;> norm_num [selectionModel, pt, LinearForm, Fin.sum_univ_one]
  · intro i
    norm_num [selectionModel]

theorem selection_restoration_kkt :
    RestorationKKT selectionModel (pt 0 0) 1 rowDerivative lambda mu := by
  refine ⟨zero_linear_feasible, ?_, selection_derivatives, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [selectionModel, pt]
  · intro j
    norm_num [lambda]
  · intro row
    norm_num [mu]
  · intro j
    fin_cases j <;> norm_num [selectionModel, pt, lambda]
  · intro row
    simp [mu]
  · intro dx
    norm_num [lambda, mu, rowDerivative, Fin.sum_univ_two, coordX, coordY]
  · norm_num [lambda, Fin.sum_univ_two]

theorem restoration_optimum :
    IsMinimizer (RestorationPairs (selectionModel.fixedLinearFiber (pt 0 0).2)
      selectionModel.g) Prod.snd (pt 0 0, 1) :=
  restoration_minimal_of_kkt selection_restoration_kkt selection_rows_convex

theorem literal_restoration_optimum :
    IsMinimizer (selectionModel.restorationModel.fixedNonlinearFiber (pt 0 0).2)
      selectionModel.restorationModel.objective (epiInsert (pt 0 0) 1) := by
  apply (restorationModel_pairMinimizer_iff selectionModel (pt 0 0).2 _).mpr
  simpa only [epiProject_insert, epiHeight_insert] using restoration_optimum

theorem bad_integer_fiber_infeasible :
    ¬ (selectionModel.fixedNonlinearFiber (pt 0 0).2).Nonempty :=
  (restoration_positive_iff_fiber_infeasible selection_restoration_kkt
    selection_rows_convex).mp (by norm_num)

theorem both_rows_exclude_fiber :
    ¬ ∃ q, q ∈ selectionModel.fixedLinearFiber (pt 0 0).2 ∧
      SelectedOARows selectionModel rowDerivative (pt 0 0) Set.univ q :=
  restoration_oa_fiber_excluded selection_restoration_kkt (by norm_num)
    Set.univ (fun _ _ => Set.mem_univ _)

theorem every_row_tied_maximum :
    (∀ j, selectionModel.g j (pt 0 0) = 1) ∧
      (∀ j, selectionModel.g j (pt 0 0) = eshMaximum selectionModel.g (pt 0 0)) := by
  have heq : ∀ j, selectionModel.g j (pt 0 0) = 1 := by
    intro j
    fin_cases j <;> norm_num [selectionModel, pt]
  refine ⟨heq, ?_⟩
  have htight := (restorationPairs_minimizer_iff _ _ _).mp restoration_optimum
  intro j
  exact (heq j).trans htight.2

theorem single_maximum_retains_point :
    pt (-1) 0 ∈ selectionModel.fixedLinearFiber (pt 0 0).2 ∧
      SelectedOARows selectionModel rowDerivative (pt 0 0) {0} (pt (-1) 0) := by
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · intro row
    fin_cases row <;> norm_num [selectionModel, pt, LinearForm, Fin.sum_univ_one]
  · intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    norm_num [tangentRow, selectionModel, rowDerivative, coordX, coordY, pt]

theorem active_at_zero_empty : {j | selectionModel.g j (pt 0 0) = 0} = ∅ := by
  ext j
  rw [Set.mem_setOf_eq, every_row_tied_maximum.1 j]
  norm_num

theorem zero_active_retains_point :
    pt 0 0 ∈ selectionModel.fixedLinearFiber (pt 0 0).2 ∧
      SelectedOARows selectionModel rowDerivative (pt 0 0)
        {j | selectionModel.g j (pt 0 0) = 0} (pt 0 0) := by
  refine ⟨⟨zero_linear_feasible, rfl⟩, ?_⟩
  rw [active_at_zero_empty]
  exact fun _ h => (Set.notMem_empty _ h).elim

def selectedMaster (J : Set (Fin 2)) : Set (Point 1 1) :=
  selectionModel.masterOn (sourceTangentFamily (pt 0 0) rowDerivative J) Set.univ

theorem source_master_membership_of_zero_fiber {q : Point 1 1} {J : Set (Fin 2)}
    (hq : q ∈ selectionModel.fixedLinearFiber (pt 0 0).2)
    (hrows : SelectedOARows selectionModel rowDerivative (pt 0 0) J q) :
    q ∈ selectedMaster J := by
  refine ⟨⟨⟨Set.mem_univ _, ?_⟩, hq.1⟩, fun _ => (0 : ℤ), ?_, ?_⟩
  · exact (sourceTangentFamily_cutRegion_iff selectionModel (pt 0 0) rowDerivative J q).mpr hrows
  · intro i
    norm_num [selectionModel]
  · simpa [pt] using hq.2

theorem single_maximum_retains_source_master : pt (-1) 0 ∈ selectedMaster {0} :=
  source_master_membership_of_zero_fiber single_maximum_retains_point.1
    single_maximum_retains_point.2

theorem zero_active_retains_source_master :
    pt 0 0 ∈ selectedMaster {j | selectionModel.g j (pt 0 0) = 0} :=
  source_master_membership_of_zero_fiber zero_active_retains_point.1
    zero_active_retains_point.2

theorem both_rows_exclude_source_master :
    ¬ ∃ q ∈ selectedMaster Set.univ, q.2 = (pt 0 0).2 := by
  rintro ⟨q, hq, hqy⟩
  apply both_rows_exclude_fiber
  exact ⟨q, ⟨hq.1.2, hqy⟩,
    (sourceTangentFamily_cutRegion_iff selectionModel (pt 0 0) rowDerivative
      Set.univ q).mp hq.1.1.2⟩

theorem selection_objective_zero (q : Point 1 1) : selectionModel.objective q = 0 := by
  simp [selectionModel, ModelData.objective, LinearForm]

theorem selected_master_minimizer_of_membership {q : Point 1 1} {J : Set (Fin 2)}
    (hq : q ∈ selectedMaster J) : IsMinimizer (selectedMaster J) selectionModel.objective q := by
  refine ⟨hq, ?_⟩
  intro z _
  simp only [selection_objective_zero, le_refl]

/-- The full smooth convex compact-base model realizes the restoration premises;
the optimum and infeasibility are consequences of its actual KKT data. -/
theorem selection_restoration_full_model :
    (∀ j, ConvexOn ℝ Set.univ (selectionModel.g j)) ∧
    (∀ j, ContDiff ℝ 1 (selectionModel.g j)) ∧
    IsCompact (selectionModel.linearRegion ∩
      IntegerCylinder (n := 1) selectionModel.lo selectionModel.hi) ∧
    RestorationKKT selectionModel (pt 0 0) 1 rowDerivative lambda mu ∧
    IsMinimizer (selectionModel.restorationModel.fixedNonlinearFiber (pt 0 0).2)
      selectionModel.restorationModel.objective (epiInsert (pt 0 0) 1) ∧
    selectionModel.restorationModel.objective (epiInsert (pt 0 0) 1) = 1 ∧
    ¬ (selectionModel.fixedNonlinearFiber (pt 0 0).2).Nonempty ∧
    pt 0 1 ∈ selectionModel.feasibleOn Set.univ := by
  exact ⟨selection_rows_convex, selection_rows_smooth, selection_base_compact,
    selection_restoration_kkt, literal_restoration_optimum, by simp,
    bad_integer_fiber_infeasible, good_integer_feasible⟩

/-- One chosen tied maximum retains an optimizer of the literal source master
on an infeasible integer fiber. Selecting both rows excludes that entire fiber. -/
theorem single_tied_maximum_counterexample :
    (∀ j, selectionModel.g j (pt 0 0) = eshMaximum selectionModel.g (pt 0 0)) ∧
    (∀ j, 0 < lambda j) ∧
    ¬ (selectionModel.fixedNonlinearFiber (pt 0 0).2).Nonempty ∧
    IsMinimizer (selectedMaster {0}) selectionModel.objective (pt (-1) 0) ∧
    ¬ ∃ q ∈ selectedMaster Set.univ, q.2 = (pt 0 0).2 := by
  exact ⟨every_row_tied_maximum.2, by intro j; norm_num [lambda],
    bad_integer_fiber_infeasible,
    selected_master_minimizer_of_membership single_maximum_retains_source_master,
    both_rows_exclude_source_master⟩

/-- Original zero activity differs from activity at the positive restoration
level: it selects no rows and retains an optimizer on the bad integer fiber. -/
theorem active_at_zero_counterexample :
    {j | selectionModel.g j (pt 0 0) = 0} = ∅ ∧
    (∀ j, selectionModel.g j (pt 0 0) = 1) ∧
    ¬ (selectionModel.fixedNonlinearFiber (pt 0 0).2).Nonempty ∧
    IsMinimizer (selectedMaster {j | selectionModel.g j (pt 0 0) = 0})
      selectionModel.objective (pt 0 0) ∧
    ¬ ∃ q ∈ selectedMaster Set.univ, q.2 = (pt 0 0).2 := by
  exact ⟨active_at_zero_empty, every_row_tied_maximum.1, bad_integer_fiber_infeasible,
    selected_master_minimizer_of_membership zero_active_retains_source_master,
    both_rows_exclude_source_master⟩

end Chapter02KKTSelectionExamples

#print axioms Chapter02KKTSelectionExamples.selection_restoration_full_model
#print axioms Chapter02KKTSelectionExamples.single_tied_maximum_counterexample
#print axioms Chapter02KKTSelectionExamples.active_at_zero_counterexample
