module

public import Chapter02Restoration

@[expose] public section

/-! Source-row sufficient KKT conditions for anchored GBD and OA cuts.
No KKT predicate assumes optimality, a valid cut, fiber exclusion or multiplier
existence. The fixed-y equality is not dualized in the partial Lagrangian. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

def linearResidual {n m l r : ℕ} (d : ModelData n m l r) (row : Fin r)
    (p : Point n m) : ℝ := LinearForm (d.A row) (d.B row) p - d.rhs row

def tangentRow {n m l r : ℕ} (d : ModelData n m l r)
    (D : Fin l → Point n m →L[ℝ] ℝ) (p : Point n m) (j : Fin l)
    (q : Point n m) : ℝ := d.g j p + D j (q-p)

def linearFormCLM {n m : ℕ} (a : RealVector n) (b : RealVector m) :
    Point n m →L[ℝ] ℝ where
  toFun := LinearForm a b
  map_add' := by
    intro p q
    simpa only [one_smul, one_mul] using linearForm_affine a b p q 1 1
  map_smul' := by
    intro c p
    simpa [LinearForm] using linearForm_affine a b p 0 c 0
  cont := linearForm_continuous a b

@[simp] theorem linearFormCLM_apply {n m : ℕ} (a : RealVector n) (b : RealVector m)
    (p : Point n m) : linearFormCLM a b p = LinearForm a b p := rfl

theorem linearResidual_hasFDerivAt {n m l r : ℕ} (d : ModelData n m l r)
    (row : Fin r) (p : Point n m) :
    HasFDerivAt (linearResidual d row) (linearFormCLM (d.A row) (d.B row)) p := by
  exact (linearFormCLM (d.A row) (d.B row)).hasFDerivAt.sub_const _

theorem objective_hasFDerivAt {n m l r : ℕ} (d : ModelData n m l r) (p : Point n m) :
    HasFDerivAt d.objective (linearFormCLM d.c1 d.c2) p :=
  (linearFormCLM d.c1 d.c2).hasFDerivAt

structure FixedNLPKKT {n m l r : ℕ} (d : ModelData n m l r) (p : Point n m)
    (D : Fin l → Point n m →L[ℝ] ℝ) (lambda : Fin l → ℝ) (mu : Fin r → ℝ) : Prop where
  linear_feasible : p ∈ d.linearRegion
  nonlinear_feasible : ∀ j, d.g j p ≤ 0
  derivatives : ∀ j, HasFDerivAt (d.g j) (D j) p
  lambda_nonneg : ∀ j, 0 ≤ lambda j
  mu_nonneg : ∀ row, 0 ≤ mu row
  nonlinear_complementarity : ∀ j, lambda j * d.g j p = 0
  linear_complementarity : ∀ row, mu row * linearResidual d row p = 0
  stationarity : ∀ dx : RealVector n,
    d.objective (dx,0) + ∑ j, lambda j * D j (dx,0) +
      ∑ row, mu row * LinearForm (d.A row) (d.B row) (dx,0) = 0

structure RestorationKKT {n m l r : ℕ} (d : ModelData n m l r) (p : Point n m)
    (rho : ℝ) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) : Prop where
  linear_feasible : p ∈ d.linearRegion
  slack_feasible : ∀ j, d.g j p ≤ rho
  derivatives : ∀ j, HasFDerivAt (d.g j) (D j) p
  lambda_nonneg : ∀ j, 0 ≤ lambda j
  mu_nonneg : ∀ row, 0 ≤ mu row
  nonlinear_complementarity : ∀ j, lambda j * (d.g j p - rho) = 0
  linear_complementarity : ∀ row, mu row * linearResidual d row p = 0
  stationarity : ∀ dx : RealVector n,
    (∑ j, lambda j * D j (dx,0)) +
      ∑ row, mu row * LinearForm (d.A row) (d.B row) (dx,0) = 0
  slack_stationarity : 1 - ∑ j, lambda j = 0

def anchoredOptimalityCut {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m) : ℝ :=
  d.objective (p.1,y) + ∑ j, lambda j * D j (0,y-p.2) +
    ∑ row, mu row * LinearForm (d.A row) (d.B row) (0,y-p.2)

def anchoredFeasibilityCut {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m) : ℝ :=
  (∑ j, lambda j * (d.g j p + D j (0,y-p.2))) +
    ∑ row, mu row * LinearForm (d.A row) (d.B row) (0,y-p.2)

def printedOptimalityCut {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m) : ℝ :=
  d.objective (p.1,y) + ∑ j, lambda j * D j (0,y-p.2) +
    ∑ row, mu row * LinearForm (d.A row) (d.B row) (0,y)

def printedFeasibilityCut {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m) : ℝ :=
  (∑ j, lambda j * (d.g j p + D j (0,y-p.2))) +
    ∑ row, mu row * LinearForm (d.A row) (d.B row) (0,y)

theorem linearForm_split {n m : ℕ} (a : RealVector n) (b : RealVector m)
    (p q : Point n m) : LinearForm a b q =
      LinearForm a b p + LinearForm a b (q.1-p.1,0) + LinearForm a b (0,q.2-p.2) := by
  have heq : q = p + (q.1-p.1,0) + (0,q.2-p.2) := by ext <;> simp
  have h := congrArg (linearFormCLM a b) heq
  simpa only [map_add, linearFormCLM_apply] using h

theorem tangentRow_split {n m l r : ℕ} (d : ModelData n m l r)
    (D : Fin l → Point n m →L[ℝ] ℝ) (p : Point n m) (j : Fin l) (q : Point n m) :
    tangentRow d D p j q = d.g j p + D j (q.1-p.1,0) + D j (0,q.2-p.2) := by
  have heq : q-p = (q.1-p.1,0) + (0,q.2-p.2) := by ext <;> simp
  simp only [tangentRow, heq, map_add]
  ring

theorem linearResidual_split {n m l r : ℕ} (d : ModelData n m l r)
    (row : Fin r) (p q : Point n m) : linearResidual d row q =
      linearResidual d row p + LinearForm (d.A row) (d.B row) (q.1-p.1,0) +
        LinearForm (d.A row) (d.B row) (0,q.2-p.2) := by
  unfold linearResidual
  rw [linearForm_split (d.A row) (d.B row) p q]
  ring

theorem objective_split {n m l r : ℕ} (d : ModelData n m l r) (p q : Point n m) :
    d.objective q = d.objective (p.1,q.2) + d.objective (q.1-p.1,0) := by
  have heq : q = (p.1,q.2) + (q.1-p.1,0) := by ext <;> simp
  have h := congrArg (linearFormCLM d.c1 d.c2) heq
  simpa only [map_add, linearFormCLM_apply, ModelData.objective] using h

theorem optimality_surrogate_identity {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) (q : Point n m) :
    d.objective q + (∑ j, lambda j * tangentRow d D p j q) +
        ∑ row, mu row * linearResidual d row q = anchoredOptimalityCut d p D lambda mu q.2 := by
  simp_rw [tangentRow_split, linearResidual_split d _ p q, mul_add, Finset.sum_add_distrib]
  have hnl : ∑ j, lambda j * d.g j p = 0 := Finset.sum_eq_zero fun j _ => h.nonlinear_complementarity j
  have hlin : ∑ row, mu row * linearResidual d row p = 0 :=
    Finset.sum_eq_zero fun row _ => h.linear_complementarity row
  rw [hnl, hlin, objective_split d p q]
  have hs := h.stationarity (q.1-p.1)
  unfold anchoredOptimalityCut
  linarith

theorem restoration_surrogate_identity {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : RestorationKKT d p rho D lambda mu) (q : Point n m) :
    (∑ j, lambda j * tangentRow d D p j q) + ∑ row, mu row * linearResidual d row q =
      anchoredFeasibilityCut d p D lambda mu q.2 := by
  simp_rw [tangentRow_split, linearResidual_split d _ p q, mul_add, Finset.sum_add_distrib]
  have hlin : ∑ row, mu row * linearResidual d row p = 0 :=
    Finset.sum_eq_zero fun row _ => h.linear_complementarity row
  rw [hlin]
  have hs := h.stationarity (q.1-p.1)
  simp only [anchoredFeasibilityCut, mul_add, Finset.sum_add_distrib]
  linarith


def SelectedOARows {n m l r : ℕ} (d : ModelData n m l r)
    (D : Fin l → Point n m →L[ℝ] ℝ) (p : Point n m) (J : Set (Fin l))
    (q : Point n m) : Prop := ∀ j ∈ J, tangentRow d D p j q ≤ 0

def sourceTangentFamily {n m l : ℕ} (p : Point n m)
    (D : Fin l → Point n m →L[ℝ] ℝ) (J : Set (Fin l)) : TangentFamily n m l 1 where
  origin := fun _ => p
  selected := fun _ => J
  derivative := fun _ => D

theorem sourceTangentFamily_cutRegion_iff {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ) (J : Set (Fin l)) (q : Point n m) :
    q ∈ (sourceTangentFamily p D J).cutRegion d ↔ SelectedOARows d D p J q := by
  simp [sourceTangentFamily, TangentFamily.cutRegion, SelectedOARows, tangentRow]

theorem weighted_tangents_nonpos {n m l r : ℕ} {d : ModelData n m l r}
    {D : Fin l → Point n m →L[ℝ] ℝ} {p q : Point n m} {J : Set (Fin l)}
    {lambda : Fin l → ℝ} (hlambda : ∀ j, 0 ≤ lambda j)
    (hsupport : ∀ j, 0 < lambda j → j ∈ J) (hrows : SelectedOARows d D p J q) :
    (∑ j, lambda j * tangentRow d D p j q) ≤ 0 := by
  apply Finset.sum_nonpos
  intro j _
  by_cases hj : 0 < lambda j
  · exact mul_nonpos_of_nonneg_of_nonpos (hlambda j) (hrows j (hsupport j hj))
  · have heq : lambda j = 0 := le_antisymm (le_of_not_gt hj) (hlambda j)
    simp only [heq, zero_mul, le_refl]

theorem weighted_linearResiduals_nonpos {n m l r : ℕ} {d : ModelData n m l r}
    {mu : Fin r → ℝ} (hmu : ∀ row, 0 ≤ mu row) {q : Point n m}
    (hq : q ∈ d.linearRegion) : (∑ row, mu row * linearResidual d row q) ≤ 0 := by
  apply Finset.sum_nonpos
  intro row _
  exact mul_nonpos_of_nonneg_of_nonpos (hmu row) (sub_nonpos.mpr (hq row))

theorem optimality_cut_of_selected_oa_rows {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) (J : Set (Fin l))
    (hsupport : ∀ j, 0 < lambda j → j ∈ J) {q : Point n m}
    (hqL : q ∈ d.linearRegion) (hrows : SelectedOARows d D p J q) :
    anchoredOptimalityCut d p D lambda mu q.2 ≤ d.objective q := by
  rw [← optimality_surrogate_identity h q]
  have hn := weighted_tangents_nonpos h.lambda_nonneg hsupport hrows
  have hl := weighted_linearResiduals_nonpos h.mu_nonneg hqL
  linarith

theorem restoration_cut_of_selected_oa_rows {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (J : Set (Fin l)) (hsupport : ∀ j, 0 < lambda j → j ∈ J) {q : Point n m}
    (hqL : q ∈ d.linearRegion) (hrows : SelectedOARows d D p J q) :
    anchoredFeasibilityCut d p D lambda mu q.2 ≤ 0 := by
  rw [← restoration_surrogate_identity h q]
  exact add_nonpos (weighted_tangents_nonpos h.lambda_nonneg hsupport hrows)
    (weighted_linearResiduals_nonpos h.mu_nonneg hqL)

theorem true_feasible_satisfies_selected_rows {n m l r : ℕ} {d : ModelData n m l r}
    {D : Fin l → Point n m →L[ℝ] ℝ} {p : Point n m}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hderiv : ∀ j, HasFDerivAt (d.g j) (D j) p)
    (J : Set (Fin l)) {q : Point n m} (hqN : q ∈ d.nonlinearRegion) :
    SelectedOARows d D p J q := by
  intro j _
  exact tangent_cut_valid (hconv j) (hderiv j) (hqN j)

theorem optimality_cut_valid {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {q : Point n m} (hqL : q ∈ d.linearRegion) (hqN : q ∈ d.nonlinearRegion) :
    anchoredOptimalityCut d p D lambda mu q.2 ≤ d.objective q :=
  optimality_cut_of_selected_oa_rows h Set.univ (fun _ _ => Set.mem_univ _) hqL
    (true_feasible_satisfies_selected_rows hconv h.derivatives Set.univ hqN)

theorem restoration_cut_valid {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {q : Point n m} (hqL : q ∈ d.linearRegion) (hqN : q ∈ d.nonlinearRegion) :
    anchoredFeasibilityCut d p D lambda mu q.2 ≤ 0 :=
  restoration_cut_of_selected_oa_rows h Set.univ (fun _ _ => Set.mem_univ _) hqL
    (true_feasible_satisfies_selected_rows hconv h.derivatives Set.univ hqN)

@[simp] theorem optimality_cut_at_anchor {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) :
    anchoredOptimalityCut d p D lambda mu p.2 = d.objective p := by
  simp [anchoredOptimalityCut, LinearForm]
  have hz : ∀ j, D j ((0 : RealVector n), (0 : RealVector m)) = 0 := fun j => (D j).map_zero
  simp [hz]

theorem RestorationKKT.normalization {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu) :
    ∑ j, lambda j = 1 := by linarith [h.slack_stationarity]

theorem restoration_cut_at_anchor {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu) :
    anchoredFeasibilityCut d p D lambda mu p.2 = rho := by
  simp only [anchoredFeasibilityCut, sub_self, Prod.mk_zero_zero, map_zero, add_zero]
  have hlin : ∑ row, mu row * LinearForm (d.A row) (d.B row) (0,0) = 0 := by
    simp [LinearForm]
  simp only [Prod.mk_zero_zero] at hlin
  rw [hlin, add_zero]
  calc
    ∑ j, lambda j * d.g j p =
        ∑ j, (lambda j * (d.g j p - rho) + lambda j * rho) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ j, lambda j * (d.g j p - rho)) + (∑ j, lambda j) * rho := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = rho := by
      rw [Finset.sum_eq_zero (fun j _ => h.nonlinear_complementarity j), h.normalization]
      ring

theorem fixedNLP_optimal_of_kkt {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) :
    IsMinimizer (d.fixedNonlinearFiber p.2) d.objective p := by
  refine ⟨⟨⟨h.linear_feasible,rfl⟩,h.nonlinear_feasible⟩, ?_⟩
  intro q hq
  have hh := optimality_cut_valid h hconv hq.1.1 hq.2
  simpa only [hq.1.2, optimality_cut_at_anchor] using hh

theorem optimality_oa_excludes_strict_improvement {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) (J : Set (Fin l))
    (hsupport : ∀ j, 0 < lambda j → j ∈ J) :
    ¬ ∃ q, q ∈ d.fixedLinearFiber p.2 ∧ SelectedOARows d D p J q ∧ d.objective q < d.objective p := by
  rintro ⟨q,hq,hrows,himprove⟩
  have hh := optimality_cut_of_selected_oa_rows h J hsupport hq.1 hrows
  rw [hq.2, optimality_cut_at_anchor] at hh
  exact (not_lt_of_ge hh) himprove

theorem restoration_oa_fiber_excluded {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hpos : 0 < rho) (J : Set (Fin l)) (hsupport : ∀ j, 0 < lambda j → j ∈ J) :
    ¬ ∃ q, q ∈ d.fixedLinearFiber p.2 ∧ SelectedOARows d D p J q := by
  rintro ⟨q,hq,hrows⟩
  have hh := restoration_cut_of_selected_oa_rows h J hsupport hq.1 hrows
  rw [hq.2, restoration_cut_at_anchor h] at hh
  exact (not_lt_of_ge hh) hpos



theorem restoration_minimal_of_kkt {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) :
    IsMinimizer (RestorationPairs (d.fixedLinearFiber p.2) d.g) Prod.snd (p,rho) := by
  refine ⟨⟨⟨h.linear_feasible,rfl⟩,h.slack_feasible⟩, ?_⟩
  rintro ⟨q,s⟩ ⟨⟨hqL,hqy⟩,hqs⟩
  have hn : (∑ j, lambda j * tangentRow d D p j q) ≤ s := by
    calc
      (∑ j, lambda j * tangentRow d D p j q) ≤ ∑ j, lambda j * s := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          ((tangent_underestimator (hconv j) (h.derivatives j)).trans (hqs j)) (h.lambda_nonneg j)
      _ = (∑ j, lambda j) * s := (Finset.sum_mul _ _ _).symm
      _ = s := by rw [h.normalization, one_mul]
  have hl := weighted_linearResiduals_nonpos h.mu_nonneg hqL
  have hi := restoration_surrogate_identity h q
  rw [hqy, restoration_cut_at_anchor h] at hi
  change rho ≤ s
  linarith

theorem restoration_positive_iff_fiber_infeasible {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) :
    0 < rho ↔ ¬ (d.fixedNonlinearFiber p.2).Nonempty := by
  constructor
  · intro hpos
    rintro ⟨q,hq⟩
    have hh := restoration_cut_valid h hconv hq.1.1 hq.2
    rw [hq.1.2, restoration_cut_at_anchor h] at hh
    exact (not_lt_of_ge hh) hpos
  · intro hnone
    apply lt_of_not_ge
    intro hrho
    apply hnone
    exact ⟨p,⟨⟨h.linear_feasible,rfl⟩,fun j => (h.slack_feasible j).trans hrho⟩⟩

theorem restoration_oa_fiber_excluded_of_infeasible {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hinfeas : ¬ (d.fixedNonlinearFiber p.2).Nonempty)
    (J : Set (Fin l)) (hsupport : ∀ j, 0 < lambda j → j ∈ J) :
    ¬ ∃ q, q ∈ d.fixedLinearFiber p.2 ∧ SelectedOARows d D p J q :=
  restoration_oa_fiber_excluded h ((restoration_positive_iff_fiber_infeasible h hconv).mpr hinfeas)
    J hsupport

theorem optimality_positive_multiplier_active {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) (j : Fin l) (hj : 0 < lambda j) : d.g j p = 0 :=
  (mul_eq_zero.mp (h.nonlinear_complementarity j)).resolve_left (ne_of_gt hj)

theorem restoration_positive_multiplier_active {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (j : Fin l) (hj : 0 < lambda j) : d.g j p = rho := by
  exact sub_eq_zero.mp ((mul_eq_zero.mp (h.nonlinear_complementarity j)).resolve_left (ne_of_gt hj))

theorem optimality_cut_of_active_oa_rows {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) {q : Point n m} (hqL : q ∈ d.linearRegion)
    (hrows : SelectedOARows d D p {j | d.g j p = 0} q) :
    anchoredOptimalityCut d p D lambda mu q.2 ≤ d.objective q :=
  optimality_cut_of_selected_oa_rows h _ (optimality_positive_multiplier_active h) hqL hrows

theorem optimality_cut_of_all_oa_rows {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) {q : Point n m} (hqL : q ∈ d.linearRegion)
    (hrows : SelectedOARows d D p Set.univ q) :
    anchoredOptimalityCut d p D lambda mu q.2 ≤ d.objective q :=
  optimality_cut_of_selected_oa_rows h _ (fun _ _ => Set.mem_univ _) hqL hrows

theorem restoration_oa_fiber_excluded_all {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hpos : 0 < rho) :
    ¬ ∃ q, q ∈ d.fixedLinearFiber p.2 ∧ SelectedOARows d D p Set.univ q :=
  restoration_oa_fiber_excluded h hpos _ (fun _ _ => Set.mem_univ _)

theorem restoration_oa_fiber_excluded_active {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hpos : 0 < rho) :
    ¬ ∃ q, q ∈ d.fixedLinearFiber p.2 ∧ SelectedOARows d D p {j | d.g j p = rho} q :=
  restoration_oa_fiber_excluded h hpos _ (restoration_positive_multiplier_active h)

theorem restoration_oa_fiber_excluded_violated {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hpos : 0 < rho) :
    ¬ ∃ q, q ∈ d.fixedLinearFiber p.2 ∧ SelectedOARows d D p {j | 0 < d.g j p} q := by
  apply restoration_oa_fiber_excluded h hpos
  intro j hj
  simpa only [Set.mem_setOf_eq, restoration_positive_multiplier_active h j hj] using hpos

theorem restorationKKT_impossible_empty_rows {n m r : ℕ} (d : ModelData n m 0 r)
    (p : Point n m) (rho : ℝ) (D : Fin 0 → Point n m →L[ℝ] ℝ)
    (lambda : Fin 0 → ℝ) (mu : Fin r → ℝ) : ¬ RestorationKKT d p rho D lambda mu := by
  intro h
  have hh := h.normalization
  simp at hh

theorem weighted_linear_y_split {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (mu : Fin r → ℝ) (y : RealVector m) :
    (∑ row, mu row * LinearForm (d.A row) (d.B row) (0,y)) =
      (∑ row, mu row * LinearForm (d.A row) (d.B row) (0,y-p.2)) +
      ∑ row, mu row * LinearForm (d.A row) (d.B row) (0,p.2) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  have heq : ((0,y) : Point n m) = (0,y-p.2) + (0,p.2) := by ext <;> simp
  have hh := congrArg (linearFormCLM (d.A row) (d.B row)) heq
  simp only [map_add, linearFormCLM_apply] at hh
  rw [hh, mul_add]

theorem printedOptimalityCut_eq_anchored_add_offset {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m) :
    printedOptimalityCut d p D lambda mu y = anchoredOptimalityCut d p D lambda mu y +
      ∑ row, mu row * LinearForm (d.A row) (d.B row) (0,p.2) := by
  unfold printedOptimalityCut anchoredOptimalityCut
  rw [weighted_linear_y_split d p mu y]
  ring

theorem printedFeasibilityCut_eq_anchored_add_offset {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m) :
    printedFeasibilityCut d p D lambda mu y = anchoredFeasibilityCut d p D lambda mu y +
      ∑ row, mu row * LinearForm (d.A row) (d.B row) (0,p.2) := by
  unfold printedFeasibilityCut anchoredFeasibilityCut
  rw [weighted_linear_y_split d p mu y]
  ring



def partialLagrangian {n m l r : ℕ} (d : ModelData n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (q : Point n m) : ℝ :=
  d.objective q + ∑ j, lambda j * d.g j q + ∑ row, mu row * linearResidual d row q

def partialLagrangianDerivative {n m l r : ℕ} (d : ModelData n m l r)
    (D : Fin l → Point n m →L[ℝ] ℝ) (lambda : Fin l → ℝ) (mu : Fin r → ℝ) :
    Point n m →L[ℝ] ℝ :=
  linearFormCLM d.c1 d.c2 + ∑ j, lambda j • D j +
    ∑ row, mu row • linearFormCLM (d.A row) (d.B row)

theorem partialLagrangian_hasFDerivAt {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hd : ∀ j, HasFDerivAt (d.g j) (D j) p) :
    HasFDerivAt (partialLagrangian d lambda mu) (partialLagrangianDerivative d D lambda mu) p := by
  have hn : HasFDerivAt (fun q => ∑ j, lambda j * d.g j q) (∑ j, lambda j • D j) p :=
    HasFDerivAt.fun_sum (fun j _ => (hd j).const_mul (lambda j))
  have hl : HasFDerivAt (fun q => ∑ row, mu row * linearResidual d row q)
      (∑ row, mu row • linearFormCLM (d.A row) (d.B row)) p :=
    HasFDerivAt.fun_sum (fun row _ => (linearResidual_hasFDerivAt d row p).const_mul (mu row))
  exact ((objective_hasFDerivAt d p).add hn).add hl

theorem partialLagrangianDerivative_apply {n m l r : ℕ} (d : ModelData n m l r)
    (D : Fin l → Point n m →L[ℝ] ℝ) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (v : Point n m) : partialLagrangianDerivative d D lambda mu v =
      d.objective v + ∑ j, lambda j * D j v +
        ∑ row, mu row * LinearForm (d.A row) (d.B row) v := by
  simp [partialLagrangianDerivative, ModelData.objective]

theorem partialLagrangian_tangent_identity {n m l r : ℕ} (d : ModelData n m l r)
    (p q : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) :
    partialLagrangian d lambda mu p + partialLagrangianDerivative d D lambda mu (q-p) =
      d.objective q + (∑ j, lambda j * tangentRow d D p j q) +
        ∑ row, mu row * linearResidual d row q := by
  have ho : d.objective (q-p) = d.objective q - d.objective p :=
    (linearFormCLM d.c1 d.c2).map_sub q p
  have hL (row : Fin r) : LinearForm (d.A row) (d.B row) (q-p) =
      linearResidual d row q - linearResidual d row p := by
    have hh := (linearFormCLM (d.A row) (d.B row)).map_sub q p
    simp only [linearFormCLM_apply] at hh
    rw [hh]
    unfold linearResidual
    ring
  simp only [partialLagrangian, partialLagrangianDerivative_apply, tangentRow, ho,
    hL, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem partialLagrangian_tangent_eq_anchored {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) (q : Point n m) :
    partialLagrangian d lambda mu p + partialLagrangianDerivative d D lambda mu (q-p) =
      anchoredOptimalityCut d p D lambda mu q.2 := by
  rw [partialLagrangian_tangent_identity, optimality_surrogate_identity h]

/-- The source restoration KKT equations assemble into the actual larger
ModelData fixed-NLP equations, with slack a continuous coordinate. -/
theorem RestorationKKT.to_fixedNLPKKT {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu) :
    FixedNLPKKT d.restorationModel (epiInsert p rho) (fun j => epigraphDerivative (D j)) lambda mu := by
  refine ⟨?_, ?_, ?_, h.lambda_nonneg, h.mu_nonneg, ?_, ?_, ?_⟩
  · simpa only [restorationModel_linearRegion_iff, epiProject_insert] using h.linear_feasible
  · intro j
    simpa only [ModelData.restorationModel, epiProject_insert, epiHeight_insert, sub_nonpos]
      using h.slack_feasible j
  · intro j
    apply restorationModel_row_hasFDerivAt
    simpa only [epiProject_insert] using h.derivatives j
  · intro j
    simpa only [ModelData.restorationModel, epiProject_insert, epiHeight_insert]
      using h.nonlinear_complementarity j
  · intro row
    simpa only [linearResidual, ModelData.restorationModel, linearForm_prepend_zero, epiProject_insert]
      using h.linear_complementarity row
  · intro dx
    rw [restorationModel_objective]
    simp only [epigraphDerivative_apply, ModelData.restorationModel,
      linearForm_prepend_zero, epiProject, epiHeight]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, h.normalization, one_mul]
    have hs := h.stationarity (Fin.tail dx)
    linarith

/-- Conversely, evaluating the lifted continuous stationarity equation in the
old x directions and the new unit-slack direction derives both source equations.
Original derivatives are supplied explicitly, not inferred by a junk derivative. -/
theorem restorationKKT_of_lifted_fixedNLPKKT {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (hd : ∀ j, HasFDerivAt (d.g j) (D j) p)
    (h : FixedNLPKKT d.restorationModel (epiInsert p rho)
      (fun j => epigraphDerivative (D j)) lambda mu) : RestorationKKT d p rho D lambda mu := by
  refine ⟨?_, ?_, hd, h.lambda_nonneg, h.mu_nonneg, ?_, ?_, ?_, ?_⟩
  · simpa only [restorationModel_linearRegion_iff, epiProject_insert] using h.linear_feasible
  · intro j
    simpa only [ModelData.restorationModel, epiProject_insert, epiHeight_insert, sub_nonpos]
      using h.nonlinear_feasible j
  · intro j
    simpa only [ModelData.restorationModel, epiProject_insert, epiHeight_insert]
      using h.nonlinear_complementarity j
  · intro row
    simpa only [linearResidual, ModelData.restorationModel, linearForm_prepend_zero, epiProject_insert]
      using h.linear_complementarity row
  · intro dx
    have hs := h.stationarity (Fin.cons 0 dx)
    rw [restorationModel_objective] at hs
    simpa only [epigraphDerivative_apply, ModelData.restorationModel,
      linearForm_prepend_zero, epiProject, epiHeight, Fin.tail_cons, Fin.cons_zero,
      sub_zero, zero_add] using hs
  · have hs := h.stationarity (Fin.cons 1 (0 : RealVector n))
    rw [restorationModel_objective] at hs
    simp only [epigraphDerivative_apply, ModelData.restorationModel, linearForm_prepend_zero,
      epiProject, epiHeight, Fin.tail_cons, Fin.cons_zero] at hs
    have hz : ∀ j, D j ((0 : RealVector n), (0 : RealVector m)) = 0 := fun j => (D j).map_zero
    simpa [LinearForm, sub_eq_add_neg, hz] using hs



theorem restorationModel_minimal_of_kkt {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {rho : ℝ} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} (h : RestorationKKT d p rho D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) :
    IsMinimizer (d.restorationModel.fixedNonlinearFiber p.2)
      d.restorationModel.objective (epiInsert p rho) := by
  apply (restorationModel_pairMinimizer_iff d p.2 _).mpr
  simpa only [epiProject_insert, epiHeight_insert] using restoration_minimal_of_kkt h hconv

/-- A common-history entry carries literal data and sufficient KKT/support
conditions. Validity and optimality are derived, never fields of the entry. -/
structure OptimalityCutEntry {n m l r : ℕ} (d : ModelData n m l r) where
  point : Point n m
  derivative : Fin l → Point n m →L[ℝ] ℝ
  lambda : Fin l → ℝ
  mu : Fin r → ℝ
  rows : Set (Fin l)
  kkt : FixedNLPKKT d point derivative lambda mu
  support : ∀ j, 0 < lambda j → j ∈ rows

structure RestorationCutEntry {n m l r : ℕ} (d : ModelData n m l r) where
  point : Point n m
  slack : ℝ
  derivative : Fin l → Point n m →L[ℝ] ℝ
  lambda : Fin l → ℝ
  mu : Fin r → ℝ
  rows : Set (Fin l)
  kkt : RestorationKKT d point slack derivative lambda mu
  support : ∀ j, 0 < lambda j → j ∈ rows

def ModelData.integerValues {n m l r : ℕ} (d : ModelData n m l r) : Set (RealVector m) :=
  {y | ∃ z ∈ IntegerBox d.lo d.hi, y = fun i => (z i : ℝ)}

/-- Epigraph form of the common-history OA master. The objective inequality
introduces alpha without changing its attainable minimum value. -/
def commonOAMaster {n m l r kf kr : ℕ} (d : ModelData n m l r)
    (O : Fin kf → OptimalityCutEntry d) (F : Fin kr → RestorationCutEntry d) :
    Set (Point n m × ℝ) :=
  {z | z.1 ∈ d.linearRegion ∧ z.1.2 ∈ d.integerValues ∧
    (∀ i, SelectedOARows d (O i).derivative (O i).point (O i).rows z.1) ∧
    (∀ i, SelectedOARows d (F i).derivative (F i).point (F i).rows z.1) ∧
    d.objective z.1 ≤ z.2}

def commonGBDMaster {n m l r kf kr : ℕ} (d : ModelData n m l r)
    (O : Fin kf → OptimalityCutEntry d) (F : Fin kr → RestorationCutEntry d) :
    Set (RealVector m × ℝ) :=
  {z | z.1 ∈ d.integerValues ∧
    (∀ i, anchoredOptimalityCut d (O i).point (O i).derivative (O i).lambda (O i).mu z.1 ≤ z.2) ∧
    (∀ i, anchoredFeasibilityCut d (F i).point (F i).derivative (F i).lambda (F i).mu z.1 ≤ 0)}

/-- Non-strict surrogate containment uses exactly the same origins,
multiplier certificates and supported nonlinear rows in both masters. -/
theorem common_master_projection_containment {n m l r kf kr : ℕ} (d : ModelData n m l r)
    (O : Fin kf → OptimalityCutEntry d) (F : Fin kr → RestorationCutEntry d) :
    (fun z : Point n m × ℝ => (z.1.2,z.2)) '' commonOAMaster d O F ⊆ commonGBDMaster d O F := by
  rintro _ ⟨⟨q,alpha⟩,⟨hqL,hqY,hO,hF,halpha⟩,rfl⟩
  refine ⟨hqY,fun i => ?_,fun i => ?_⟩
  · exact (optimality_cut_of_selected_oa_rows (O i).kkt (O i).rows (O i).support hqL (hO i)).trans halpha
  · exact restoration_cut_of_selected_oa_rows (F i).kkt (F i).rows (F i).support hqL (hF i)

/-- Both minima are attained hypotheses. No totalized real infimum or
unbounded/empty master is silently treated as a finite optimum. -/
theorem common_master_minimum_order {n m l r kf kr : ℕ} (d : ModelData n m l r)
    (O : Fin kf → OptimalityCutEntry d) (F : Fin kr → RestorationCutEntry d)
    {oa : Point n m × ℝ} {gbd : RealVector m × ℝ}
    (hoa : IsMinimizer (commonOAMaster d O F) Prod.snd oa)
    (hgbd : IsMinimizer (commonGBDMaster d O F) Prod.snd gbd) : gbd.2 ≤ oa.2 :=
  hgbd.2 (oa.1.2,oa.2) (common_master_projection_containment d O F ⟨oa,hoa.1,rfl⟩)

theorem source_feasible_objective_in_commonGBDMaster {n m l r kf kr : ℕ}
    (d : ModelData n m l r) (O : Fin kf → OptimalityCutEntry d) (F : Fin kr → RestorationCutEntry d)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) {q : Point n m}
    (hq : q ∈ d.feasibleOn Set.univ) (alpha : ℝ) (halpha : d.objective q ≤ alpha) :
    (q.2,alpha) ∈ commonGBDMaster d O F := by
  rcases hq with ⟨⟨⟨_,hqN⟩,hqL⟩,hqY⟩
  apply common_master_projection_containment d O F
  refine ⟨(q,alpha),⟨hqL,hqY,fun i => ?_,fun i => ?_,halpha⟩,rfl⟩
  · exact true_feasible_satisfies_selected_rows hconv (O i).kkt.derivatives (O i).rows hqN
  · exact true_feasible_satisfies_selected_rows hconv (F i).kkt.derivatives (F i).rows hqN

theorem commonGBDMaster_minimum_lowerBound {n m l r kf kr : ℕ}
    (d : ModelData n m l r) (O : Fin kf → OptimalityCutEntry d) (F : Fin kr → RestorationCutEntry d)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) {gbd : RealVector m × ℝ}
    (hgbd : IsMinimizer (commonGBDMaster d O F) Prod.snd gbd) :
    IsLowerBound (d.feasibleOn Set.univ) d.objective gbd.2 := by
  intro q hq
  exact hgbd.2 (q.2,d.objective q)
    (source_feasible_objective_in_commonGBDMaster d O F hconv hq _ le_rfl)

/-- Without slack normalization, zero nonnegative weights produce a vacuous
feasibility cut and cannot eliminate any nonempty linear fiber. They are not
presented as a RestorationKKT certificate. -/
theorem zero_weights_do_not_exclude_linear_fiber {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ) (hp : p ∈ d.linearRegion) :
    (∀ y, anchoredFeasibilityCut d p D (fun _ => 0) (fun _ => 0) y = 0) ∧
      ∃ q ∈ d.fixedLinearFiber p.2,
        SelectedOARows d D p ∅ q ∧ anchoredFeasibilityCut d p D (fun _ => 0) (fun _ => 0) q.2 ≤ 0 := by
  have hz (y : RealVector m) : anchoredFeasibilityCut d p D (fun _ => 0) (fun _ => 0) y = 0 := by
    simp [anchoredFeasibilityCut]
  refine ⟨hz,p,⟨hp,rfl⟩,?_,by simp only [hz,le_refl]⟩
  intro j hj
  exact False.elim hj


end Chapter02

#print axioms Chapter02.linearFormCLM_apply
#print axioms Chapter02.linearResidual_hasFDerivAt
#print axioms Chapter02.objective_hasFDerivAt
#print axioms Chapter02.linearForm_split
#print axioms Chapter02.tangentRow_split
#print axioms Chapter02.linearResidual_split
#print axioms Chapter02.objective_split
#print axioms Chapter02.optimality_surrogate_identity
#print axioms Chapter02.restoration_surrogate_identity
#print axioms Chapter02.sourceTangentFamily_cutRegion_iff
#print axioms Chapter02.weighted_tangents_nonpos
#print axioms Chapter02.weighted_linearResiduals_nonpos
#print axioms Chapter02.optimality_cut_of_selected_oa_rows
#print axioms Chapter02.restoration_cut_of_selected_oa_rows
#print axioms Chapter02.true_feasible_satisfies_selected_rows
#print axioms Chapter02.optimality_cut_valid
#print axioms Chapter02.restoration_cut_valid
#print axioms Chapter02.optimality_cut_at_anchor
#print axioms Chapter02.RestorationKKT.normalization
#print axioms Chapter02.restoration_cut_at_anchor
#print axioms Chapter02.fixedNLP_optimal_of_kkt
#print axioms Chapter02.optimality_oa_excludes_strict_improvement
#print axioms Chapter02.restoration_oa_fiber_excluded
#print axioms Chapter02.restoration_minimal_of_kkt
#print axioms Chapter02.restoration_positive_iff_fiber_infeasible
#print axioms Chapter02.restoration_oa_fiber_excluded_of_infeasible
#print axioms Chapter02.optimality_positive_multiplier_active
#print axioms Chapter02.restoration_positive_multiplier_active
#print axioms Chapter02.optimality_cut_of_active_oa_rows
#print axioms Chapter02.optimality_cut_of_all_oa_rows
#print axioms Chapter02.restoration_oa_fiber_excluded_all
#print axioms Chapter02.restoration_oa_fiber_excluded_active
#print axioms Chapter02.restoration_oa_fiber_excluded_violated
#print axioms Chapter02.restorationKKT_impossible_empty_rows
#print axioms Chapter02.weighted_linear_y_split
#print axioms Chapter02.printedOptimalityCut_eq_anchored_add_offset
#print axioms Chapter02.printedFeasibilityCut_eq_anchored_add_offset
#print axioms Chapter02.partialLagrangian_hasFDerivAt
#print axioms Chapter02.partialLagrangianDerivative_apply
#print axioms Chapter02.partialLagrangian_tangent_identity
#print axioms Chapter02.partialLagrangian_tangent_eq_anchored
#print axioms Chapter02.RestorationKKT.to_fixedNLPKKT
#print axioms Chapter02.restorationKKT_of_lifted_fixedNLPKKT
#print axioms Chapter02.restorationModel_minimal_of_kkt
#print axioms Chapter02.common_master_projection_containment
#print axioms Chapter02.common_master_minimum_order
#print axioms Chapter02.source_feasible_objective_in_commonGBDMaster
#print axioms Chapter02.commonGBDMaster_minimum_lowerBound
#print axioms Chapter02.zero_weights_do_not_exclude_linear_fiber
