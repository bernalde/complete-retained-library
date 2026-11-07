module

public import Chapter02OAHistory
public import Chapter02ModelExamples

@[expose] public section

/-! Exact control for deleting an affine coupling row from the OA master.
The true source master retains the row and excludes the restored fiber.
Deleting only that row admits an exact optimum on the same infeasible fiber. -/

noncomputable section
open Chapter02 Chapter02Examples
open scoped BigOperators
namespace Chapter02OAPolicyExamples

def pt (x y : ℝ) : Point 1 1 := (fun _ => x, fun _ => y)

def coupledModel : ModelData 1 1 1 3 where
  g := fun _ p => -p.1 0
  A := fun i _ => if i = 1 then -1 else 1
  B := fun i _ => if i = 2 then -2 else 0
  rhs := fun i => if i = 2 then -1 else 2
  c1 := fun _ => 0
  c2 := fun _ => 1
  lo := fun _ => 0
  hi := fun _ => 1

/-- Only the affine coupling x-2y≤-1 is deleted; all other data are retained. -/
def deletedCouplingModel : ModelData 1 1 1 2 where
  g := coupledModel.g
  A := fun i _ => if i = 1 then -1 else 1
  B := fun _ _ => 0
  rhs := fun _ => 2
  c1 := coupledModel.c1
  c2 := coupledModel.c2
  lo := coupledModel.lo
  hi := coupledModel.hi

def restorationBatch : OABatch 1 1 := ⟨fun _ => 0,pt (-1) 0,some 1⟩

theorem batch_integer_cast : oaIntCast restorationBatch.integer = (fun _ => (0 : ℝ)) := by
  funext i
  change ((0 : ℤ) : ℝ) = 0
  norm_num

theorem coupled_linear_iff (p : Point 1 1) : p ∈ coupledModel.linearRegion ↔
    p.1 0 ≤ 2 ∧ -p.1 0 ≤ 2 ∧ p.1 0 - 2 * p.2 0 ≤ -1 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    norm_num [coupledModel, LinearForm, Fin.sum_univ_one, Fin.ext_iff] at h0 h1 h2
    exact ⟨by linarith,by linarith,by linarith⟩
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i <;> norm_num [coupledModel, LinearForm, Fin.sum_univ_one, Fin.ext_iff] <;> linarith

theorem deleted_linear_iff (p : Point 1 1) : p ∈ deletedCouplingModel.linearRegion ↔
    p.1 0 ≤ 2 ∧ -p.1 0 ≤ 2 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    norm_num [deletedCouplingModel, LinearForm, Fin.sum_univ_one] at h0 h1
    exact ⟨h0,h1⟩
  · rintro ⟨h0,h1⟩ i
    fin_cases i <;> norm_num [deletedCouplingModel, LinearForm, Fin.sum_univ_one] <;> assumption

@[simp] theorem coupled_objective (p : Point 1 1) : coupledModel.objective p = p.2 0 := by
  simp [ModelData.objective,coupledModel,LinearForm,Fin.sum_univ_one]

@[simp] theorem deleted_objective (p : Point 1 1) : deletedCouplingModel.objective p = p.2 0 := by
  simp [ModelData.objective,deletedCouplingModel,coupledModel,LinearForm,Fin.sum_univ_one]

theorem coupled_rows_convex : ∀ j, ConvexOn ℝ Set.univ (coupledModel.g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ a b _ _ _
  change -(a * p.1 0+b*q.1 0) ≤ a*(-p.1 0)+b*(-q.1 0)
  linarith

theorem coupled_row_hasFDerivAt (j : Fin 1) (p : Point 1 1) :
    HasFDerivAt (coupledModel.g j) (-coordX) p := coordX.hasFDerivAt.neg

theorem coupled_rows_differentiable : ∀ j, Differentiable ℝ (coupledModel.g j) :=
  fun j p => (coupled_row_hasFDerivAt j p).differentiableAt

theorem coupled_row_fderiv (j : Fin 1) (p : Point 1 1) :
    fderiv ℝ (coupledModel.g j) p = -coordX := (coupled_row_hasFDerivAt j p).fderiv

theorem coupled_base_compact :
    IsCompact (coupledModel.linearRegion ∩
      IntegerCylinder (n := 1) coupledModel.lo coupledModel.hi) := by
  have hL : IsClosed coupledModel.linearRegion := by
    have heq : coupledModel.linearRegion = ⋂ row,
        {p | LinearForm (coupledModel.A row) (coupledModel.B row) p ≤ coupledModel.rhs row} := by
      ext p
      simp [ModelData.linearRegion]
    rw [heq]
    exact isClosed_iInter fun row =>
      isClosed_le (linearForm_continuous _ _) continuous_const
  have hY : IsClosed (IntegerCylinder (n := 1) coupledModel.lo coupledModel.hi) := by
    have hfin := (integerBox_finite coupledModel.lo coupledModel.hi).image
      (fun y : IntVector 1 => oaIntCast y)
    have heq : IntegerCylinder (n := 1) coupledModel.lo coupledModel.hi =
        Prod.snd ⁻¹' ((fun y : IntVector 1 => oaIntCast y) ''
          IntegerBox coupledModel.lo coupledModel.hi) := by
      ext p
      constructor
      · rintro ⟨y,hy,hpy⟩
        exact ⟨y,hy,hpy.symm⟩
      · rintro ⟨y,hy,hyp⟩
        exact ⟨y,hy,hyp.symm⟩
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  apply (isCompact_Icc : IsCompact (Set.Icc (pt (-2) 0) (pt 2 1))).of_isClosed_subset
    (hL.inter hY)
  rintro p ⟨hL,y,hy,hpy⟩
  obtain ⟨hhi,hlo,_⟩ := (coupled_linear_iff p).mp hL
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i
    fin_cases i
    change -2 ≤ p.1 0
    linarith
  · intro i
    rw [hpy]
    exact (hy i).1
  · intro i
    fin_cases i
    exact hhi
  · intro i
    rw [hpy]
    exact (hy i).2

theorem restoration_anchor_linear : pt (-1) 0 ∈ coupledModel.fixedLinearFiber (fun _ => 0) := by
  refine ⟨(coupled_linear_iff _).mpr ?_,rfl⟩
  norm_num [pt]

theorem zero_fiber_infeasible :
    ¬ (coupledModel.fixedNonlinearFiber (fun _ => 0)).Nonempty := by
  rintro ⟨p,⟨hL,hpy⟩,hN⟩
  have hc := ((coupled_linear_iff p).mp hL).2.2
  have hn := hN 0
  have hy := congrFun hpy 0
  change -p.1 0 ≤ 0 at hn
  change p.2 0 = 0 at hy
  linarith

theorem restoration_minimum :
    IsMinimizer (RestorationPairs (coupledModel.fixedLinearFiber (fun _ => 0)) coupledModel.g)
      Prod.snd (pt (-1) 0,1) := by
  refine ⟨⟨restoration_anchor_linear,?_⟩,?_⟩
  · intro j
    norm_num [coupledModel,pt]
  · rintro ⟨p,rho⟩ ⟨⟨hL,hpy⟩,hg⟩
    have hc := ((coupled_linear_iff p).mp hL).2.2
    have hn := hg 0
    have hy := congrFun hpy 0
    change -p.1 0 ≤ rho at hn
    change p.2 0 = 0 at hy
    change 1 ≤ rho
    linarith

theorem restoration_batch_valid : oaBatchValid coupledModel restorationBatch := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    norm_num [restorationBatch,coupledModel]
  · rw [batch_integer_cast]
    rfl
  · simpa only [batch_integer_cast] using zero_fiber_infeasible
  · rw [show restorationBatch.anchor = pt (-1) 0 from rfl]
    simpa only [batch_integer_cast] using restoration_minimum

theorem restored_fiber_excluded :
    ¬ ∃ q ∈ oaMaster coupledModel [restorationBatch], q.2 = (fun _ => 0) := by
  rintro ⟨q,hq,hy⟩
  obtain ⟨hL,_,hrows⟩ := (oa_master_mem_iff coupledModel [restorationBatch] q).mp hq
  exact oaBatch_restoration_excludes coupledModel restorationBatch restoration_batch_valid rfl
    coupled_rows_convex coupled_rows_differentiable hL
    (by simpa only [batch_integer_cast] using hy)
    (hrows restorationBatch (by simp))

theorem restoration_batch_cut_iff (q : Point 1 1) :
    oaBatchCuts coupledModel restorationBatch q ↔ 0 ≤ q.1 0 := by
  unfold oaBatchCuts SelectedOARows oaBatchDerivative
  simp only [coupled_row_fderiv]
  simp [oaBatchRows,restorationBatch,coupledModel,pt,tangentRow,coordX]

theorem deleted_batch_cut_iff (q : Point 1 1) :
    oaBatchCuts deletedCouplingModel restorationBatch q ↔ 0 ≤ q.1 0 := by
  change oaBatchCuts coupledModel restorationBatch q ↔ _
  exact restoration_batch_cut_iff q

theorem deleted_master_readmits : pt 0 0 ∈ oaMaster deletedCouplingModel [restorationBatch] := by
  apply (oa_master_mem_iff deletedCouplingModel [restorationBatch] _).mpr
  refine ⟨(deleted_linear_iff _).mpr (by norm_num [pt]),?_,?_⟩
  · refine ⟨fun _ => 0,?_,by simp [pt]⟩
    intro i
    norm_num [deletedCouplingModel,coupledModel]
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact (deleted_batch_cut_iff _).mpr (by norm_num [pt])

theorem deleted_master_minimum :
    IsMinimizer (oaMaster deletedCouplingModel [restorationBatch])
      deletedCouplingModel.objective (pt 0 0) := by
  refine ⟨deleted_master_readmits,?_⟩
  intro q hq
  obtain ⟨_,⟨y,hy,hqy⟩,_⟩ := (oa_master_mem_iff deletedCouplingModel [restorationBatch] q).mp hq
  have hy0 := (hy 0).1
  simp only [deletedCouplingModel,coupledModel] at hy0
  simpa [pt,hqy] using hy0

theorem restoration_kkt_exists :
    ∃ lambda mu, RestorationKKT coupledModel (pt (-1) 0) 1
      (fun _ => -coordX) lambda mu :=
  exists_restorationKKT coupledModel (pt (-1) 0) 1 (fun _ => -coordX)
    coupled_rows_convex (fun j => coupled_row_hasFDerivAt j _) restoration_minimum

theorem coupling_multiplier_forced {lambda : Fin 1 → ℝ} {mu : Fin 3 → ℝ}
    (h : RestorationKKT coupledModel (pt (-1) 0) 1 (fun _ => -coordX) lambda mu) :
    mu 2 = 1 := by
  have hn := h.normalization
  norm_num [Fin.sum_univ_one] at hn
  have hc0 := h.linear_complementarity 0
  have hc1 := h.linear_complementarity 1
  norm_num [linearResidual,coupledModel,pt,LinearForm,Fin.sum_univ_one,Fin.ext_iff] at hc0 hc1
  have hmu0 : mu 0 = 0 := by linarith
  have hmu1 : mu 1 = 0 := by linarith
  have hs := h.stationarity (fun _ => 1)
  norm_num [Fin.sum_univ_three,Fin.sum_univ_one,LinearForm,coordX,coupledModel,Fin.ext_iff] at hs
  linarith

theorem actual_restoration_has_nonzero_coupling_multiplier :
    ∃ lambda mu, RestorationKKT coupledModel (pt (-1) 0) 1
      (fun _ => -coordX) lambda mu ∧ mu 2 = 1 := by
  obtain ⟨lambda,mu,hkkt⟩ := restoration_kkt_exists
  exact ⟨lambda,mu,hkkt,coupling_multiplier_forced hkkt⟩

theorem original_feasible_point : pt 0 1 ∈ coupledModel.feasibleOn Set.univ := by
  refine ⟨⟨⟨Set.mem_univ _,?_⟩,(coupled_linear_iff _).mpr ?_⟩,?_,?_,?_⟩
  · intro j
    norm_num [coupledModel,pt]
  · norm_num [pt]
  · exact fun _ => 1
  · intro i
    norm_num [coupledModel]
  · funext i
    norm_num [pt]

theorem source_feasible_integer_one {p : Point 1 1}
    (hp : p ∈ coupledModel.feasibleOn Set.univ) : p.2 0 = 1 := by
  obtain ⟨⟨⟨_,hN⟩,hL⟩,y,hy,hpy⟩ := hp
  have hc := ((coupled_linear_iff p).mp hL).2.2
  have hn := hN 0
  change -p.1 0 ≤ 0 at hn
  have hyhi := (hy 0).2
  change (y 0 : ℝ) ≤ 1 at hyhi
  have hycoord := congrFun hpy 0
  have hpos : (0 : ℝ) < (y 0 : ℝ) := by linarith
  have hypos : (0 : ℤ) < y 0 := by exact_mod_cast hpos
  have hybound : y 0 ≤ (1 : ℤ) := by exact_mod_cast hyhi
  have hyeq : y 0 = 1 := by omega
  simpa [hyeq] using hycoord

theorem original_minimum :
    IsMinimizer (coupledModel.feasibleOn Set.univ) coupledModel.objective (pt 0 1) := by
  refine ⟨original_feasible_point,?_⟩
  intro p hp
  simp [pt,source_feasible_integer_one hp]

theorem coupled_fiber_slater : OAFiberSlater coupledModel := by
  intro y hy hne
  obtain ⟨p,hp⟩ := hne
  have hporiginal : p ∈ coupledModel.feasibleOn Set.univ :=
    ⟨⟨⟨Set.mem_univ _,hp.2⟩,hp.1.1⟩,y,hy,hp.1.2⟩
  have hyone : oaIntCast y = (fun _ => 1) := by
    funext i
    fin_cases i
    have hpy := congrFun hp.1.2 0
    have hpone := source_feasible_integer_one hporiginal
    exact hpy.symm.trans hpone
  refine ⟨pt (1/2) 1,⟨(coupled_linear_iff _).mpr ?_,?_⟩,?_⟩
  · norm_num [pt]
  · rw [hyone]
    rfl
  · intro j
    norm_num [coupledModel,pt]

theorem deleted_coupling_policy_counterexample :
    oaBatchValid coupledModel restorationBatch ∧
    (¬ ∃ q ∈ oaMaster coupledModel [restorationBatch], q.2 = (fun _ => 0)) ∧
    IsMinimizer (oaMaster deletedCouplingModel [restorationBatch])
      deletedCouplingModel.objective (pt 0 0) ∧
    IsMinimizer (coupledModel.feasibleOn Set.univ) coupledModel.objective (pt 0 1) ∧
    deletedCouplingModel.objective (pt 0 0) < coupledModel.objective (pt 0 1) := by
  exact ⟨restoration_batch_valid,restored_fiber_excluded,deleted_master_minimum,
    original_minimum,by norm_num [pt]⟩

#print axioms batch_integer_cast
#print axioms coupled_linear_iff
#print axioms deleted_linear_iff
#print axioms coupled_objective
#print axioms deleted_objective
#print axioms coupled_rows_convex
#print axioms coupled_row_hasFDerivAt
#print axioms coupled_rows_differentiable
#print axioms coupled_row_fderiv
#print axioms coupled_base_compact
#print axioms restoration_anchor_linear
#print axioms zero_fiber_infeasible
#print axioms restoration_minimum
#print axioms restoration_batch_valid
#print axioms restored_fiber_excluded
#print axioms restoration_batch_cut_iff
#print axioms deleted_batch_cut_iff
#print axioms deleted_master_readmits
#print axioms deleted_master_minimum
#print axioms restoration_kkt_exists
#print axioms coupling_multiplier_forced
#print axioms actual_restoration_has_nonzero_coupling_multiplier
#print axioms original_feasible_point
#print axioms source_feasible_integer_one
#print axioms original_minimum
#print axioms coupled_fiber_slater
#print axioms deleted_coupling_policy_counterexample

end Chapter02OAPolicyExamples
