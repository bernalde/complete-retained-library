module

public import Chapter02KKTCuts

@[expose] public section

/-! Actual finite inner values for the accepted all-row Lagrangian.
The common continuous domain is all of RealVector n, including n = 0.
No real infimum is exposed without nonempty/bounded image evidence. Joint
convexity and raw KKT data derive the support; they do not assume its validity.
This is not a general retained-domain dual or a complete GBD procedure. -/

noncomputable section
open scoped BigOperators
namespace Chapter02

/-- The actual image of the objective plus every dualized nonlinear and affine
residual, retaining each affine right-hand side. -/
def gbdInnerRange {n m l r : ℕ} (d : ModelData n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m) : Set ℝ :=
  Set.range (fun x : RealVector n => partialLagrangian d lambda mu (x,y))

theorem gbdInnerRange_nonempty {n m l r : ℕ} (d : ModelData n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m) :
    (gbdInnerRange d lambda mu y).Nonempty :=
  ⟨partialLagrangian d lambda mu (0,y), 0, rfl⟩

/-- A finite real inner infimum with both domain obligations explicit. -/
def gbdFiniteInnerValue {n m l r : ℕ} (d : ModelData n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m)
    (_hne : (gbdInnerRange d lambda mu y).Nonempty)
    (_hb : BddBelow (gbdInnerRange d lambda mu y)) : ℝ :=
  sInf (gbdInnerRange d lambda mu y)

theorem gbdFiniteInnerValue_isGLB {n m l r : ℕ} (d : ModelData n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (y : RealVector m)
    (hne : (gbdInnerRange d lambda mu y).Nonempty)
    (hb : BddBelow (gbdInnerRange d lambda mu y)) :
    IsGLB (gbdInnerRange d lambda mu y) (gbdFiniteInnerValue d lambda mu y hne hb) :=
  isGLB_csInf hne hb

/-- Joint convexity is derived from the literal rows and their nonnegative
weights; affine constants are retained in the calculation. -/
theorem gbd_partialLagrangian_convex {n m l r : ℕ} (d : ModelData n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hlambda : ∀ j, 0 ≤ lambda j) :
    ConvexOn ℝ Set.univ (partialLagrangian d lambda mu) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  have hn : (∑ j, lambda j * d.g j (a • p + b • q)) ≤
      a * (∑ j, lambda j * d.g j p) + b * (∑ j, lambda j * d.g j q) := by
    calc
      _ ≤ ∑ j, (a * (lambda j * d.g j p) + b * (lambda j * d.g j q)) := by
        apply Finset.sum_le_sum
        intro j _
        have hj := mul_le_mul_of_nonneg_left
          ((hconv j).2 (Set.mem_univ p) (Set.mem_univ q) ha hb hab) (hlambda j)
        simp only [smul_eq_mul] at hj
        calc
          _ ≤ lambda j * (a * d.g j p + b * d.g j q) := hj
          _ = _ := by ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hr (i : Fin r) : linearResidual d i (a • p + b • q) =
      a * linearResidual d i p + b * linearResidual d i q := by
    unfold linearResidual
    rw [linearForm_affine]
    have hc : (a + b) * d.rhs i = d.rhs i := by rw [hab, one_mul]
    nlinarith [hc]
  have hl : (∑ i, mu i * linearResidual d i (a • p + b • q)) =
      a * (∑ i, mu i * linearResidual d i p) +
        b * (∑ i, mu i * linearResidual d i q) := by
    calc
      _ = ∑ i, (a * (mu i * linearResidual d i p) +
          b * (mu i * linearResidual d i q)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hr]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have ho : d.objective (a • p + b • q) = a * d.objective p + b * d.objective q :=
    linearForm_affine d.c1 d.c2 p q a b
  change d.objective (a • p + b • q) + (∑ j, lambda j * d.g j (a • p + b • q)) +
      (∑ i, mu i * linearResidual d i (a • p + b • q)) ≤
    a * (d.objective p + (∑ j, lambda j * d.g j p) +
      (∑ i, mu i * linearResidual d i p)) +
    b * (d.objective q + (∑ j, lambda j * d.g j q) +
      (∑ i, mu i * linearResidual d i q))
  rw [ho, hl]
  nlinarith [hn]

/-- Full derivative support and stationarity give the repaired anchored row
below L at every continuous point, not merely at a feasible evaluation. -/
theorem gbd_anchored_le_partialLagrangian {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) (q : Point n m) :
    anchoredOptimalityCut d p D lambda mu q.2 ≤ partialLagrangian d lambda mu q := by
  rw [← partialLagrangian_tangent_eq_anchored h q]
  exact tangent_underestimator
    (gbd_partialLagrangian_convex d lambda mu hconv h.lambda_nonneg)
    (partialLagrangian_hasFDerivAt d p D lambda mu h.derivatives)

theorem gbdInnerRange_bddBelow {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) (y : RealVector m) :
    BddBelow (gbdInnerRange d lambda mu y) := by
  refine ⟨anchoredOptimalityCut d p D lambda mu y, ?_⟩
  rintro v ⟨x, rfl⟩
  exact gbd_anchored_le_partialLagrangian h hconv (x,y)

theorem gbd_anchored_le_inner_isGLB {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} {y : RealVector m} {v : ℝ}
    (h : FixedNLPKKT d p D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hv : IsGLB (gbdInnerRange d lambda mu y) v) :
    anchoredOptimalityCut d p D lambda mu y ≤ v := by
  apply hv.2
  rintro w ⟨x, rfl⟩
  exact gbd_anchored_le_partialLagrangian h hconv (x,y)

/-- Weak duality itself requires only row signs and feasibility, with no
convexity, derivative, CQ or optimal-multiplier requirement. -/
theorem gbd_partialLagrangian_le_objective {n m l r : ℕ} {d : ModelData n m l r}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} {q : Point n m}
    (hlambda : ∀ j, 0 ≤ lambda j) (hmu : ∀ i, 0 ≤ mu i)
    (hlinear : q ∈ d.linearRegion) (hnonlinear : ∀ j, d.g j q ≤ 0) :
    partialLagrangian d lambda mu q ≤ d.objective q := by
  have hn : (∑ j, lambda j * d.g j q) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hlambda j) (hnonlinear j)
  have hl := weighted_linearResiduals_nonpos hmu hlinear
  unfold partialLagrangian
  linarith

theorem gbd_inner_isGLB_weakDuality {n m l r : ℕ} {d : ModelData n m l r}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} {y : RealVector m} {v : ℝ}
    (hlambda : ∀ j, 0 ≤ lambda j) (hmu : ∀ i, 0 ≤ mu i)
    (hv : IsGLB (gbdInnerRange d lambda mu y) v) {x : RealVector n}
    (hlinear : (x,y) ∈ d.linearRegion) (hnonlinear : ∀ j, d.g j (x,y) ≤ 0) :
    v ≤ d.objective (x,y) :=
  (hv.1 ⟨x,rfl⟩).trans (gbd_partialLagrangian_le_objective hlambda hmu hlinear hnonlinear)

theorem gbd_partialLagrangian_at_anchor {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu) :
    partialLagrangian d lambda mu p = d.objective p := by
  simp [partialLagrangian, h.nonlinear_complementarity, h.linear_complementarity]

theorem gbd_inner_isGLB_anchor {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ} {v : ℝ}
    (h : FixedNLPKKT d p D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hv : IsGLB (gbdInnerRange d lambda mu p.2) v) : v = d.objective p := by
  apply le_antisymm
  · have hvp := hv.1 (show partialLagrangian d lambda mu p ∈
        gbdInnerRange d lambda mu p.2 from ⟨p.1, rfl⟩)
    simpa only [gbd_partialLagrangian_at_anchor h] using hvp
  · have hb := gbd_anchored_le_inner_isGLB h hconv hv
    have hz : ∀ j, D j ((0 : RealVector n), (0 : RealVector m)) = 0 := fun j => (D j).map_zero
    simpa [anchoredOptimalityCut, LinearForm, hz] using hb

/-- The actual image has a finite greatest lower bound, derived from KKT
support, and that value bounds every feasible objective at this parameter. -/
theorem gbd_inner_exists_of_kkt {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) (y : RealVector m) :
    ∃ v : ℝ, IsGLB (gbdInnerRange d lambda mu y) v ∧
      anchoredOptimalityCut d p D lambda mu y ≤ v ∧
      ∀ x : RealVector n, (x,y) ∈ d.linearRegion →
        (∀ j, d.g j (x,y) ≤ 0) → v ≤ d.objective (x,y) := by
  have hne := gbdInnerRange_nonempty d lambda mu y
  have hb := gbdInnerRange_bddBelow h hconv y
  have hv := gbdFiniteInnerValue_isGLB d lambda mu y hne hb
  exact ⟨_, hv, gbd_anchored_le_inner_isGLB h hconv hv,
    fun _ hL hN => gbd_inner_isGLB_weakDuality h.lambda_nonneg h.mu_nonneg hv hL hN⟩

/-- Raw KKT sufficiency at the fixed fiber follows from the derived inner
value; a primal minimum is not an additional premise here. -/
theorem gbd_kkt_fixedFiber_minimizer {n m l r : ℕ} {d : ModelData n m l r}
    {p : Point n m} {D : Fin l → Point n m →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (h : FixedNLPKKT d p D lambda mu)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) :
    IsMinimizer (d.fixedNonlinearFiber p.2) d.objective p := by
  obtain ⟨v,hv,_,hweak⟩ := gbd_inner_exists_of_kkt h hconv p.2
  have heq := gbd_inner_isGLB_anchor h hconv hv
  refine ⟨(mem_fixedNonlinearFiber d p.2 p).mpr
    ⟨h.linear_feasible,rfl,h.nonlinear_feasible⟩, ?_⟩
  intro q hq
  obtain ⟨hL,hy,hN⟩ := (mem_fixedNonlinearFiber d p.2 q).mp hq
  have hqp : q = (q.1,p.2) := Prod.ext rfl hy
  rw [hqp] at hL hN ⊢
  rw [← heq]
  exact hweak q.1 hL hN

end Chapter02

#print axioms Chapter02.gbdInnerRange_nonempty
#print axioms Chapter02.gbdFiniteInnerValue_isGLB
#print axioms Chapter02.gbd_partialLagrangian_convex
#print axioms Chapter02.gbd_anchored_le_partialLagrangian
#print axioms Chapter02.gbdInnerRange_bddBelow
#print axioms Chapter02.gbd_anchored_le_inner_isGLB
#print axioms Chapter02.gbd_partialLagrangian_le_objective
#print axioms Chapter02.gbd_inner_isGLB_weakDuality
#print axioms Chapter02.gbd_partialLagrangian_at_anchor
#print axioms Chapter02.gbd_inner_isGLB_anchor
#print axioms Chapter02.gbd_inner_exists_of_kkt
#print axioms Chapter02.gbd_kkt_fixedFiber_minimizer
