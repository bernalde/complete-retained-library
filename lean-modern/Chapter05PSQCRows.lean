module

public import Chapter05PSQCAnalytic

@[expose] public section

/-! Qualified structured quadratic PSC rows. The domain normal is retained in
the remainder identity; validity is asserted only at original feasible points.
The sufficient scale is the already established clipped safeScale of actual L. -/
noncomputable section
open Set
open scoped BigOperators
open Chapter02
namespace Chapter05.PSQC
variable {p q m l s nw nv : ℕ}

theorem retained_normal_identity (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    d.r v - pscRow d e w v y = remainder d e v -
      (∑ j, e.lambda j * d.nonlinear j w v y) - e.normalV (v-e.v) := by
  have hs := hk.stationarity_v (v-e.v)
  simp only [remainder, lagrangian_fderiv d e hk, lagrangian, pscRow,
    PSCData.objective, PSCData.nonlinear, PSCData.coupling,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at *
  linarith

theorem remainder_le_row_gap (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) : remainder d e v ≤ d.r v - pscRow d e w v y := by
  have hi := retained_normal_identity d e hk w v y
  have hn := hk.normalV_nonpos hf.1.2.1
  have hs : (∑ j, e.lambda j * d.nonlinear j w v y) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos
      (hk.lambda_nonneg j) (hf.2 j)
  linarith

theorem quadratic_le_remainder (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    {α : ℝ} (hα : α ≤ Quadratic.safeScale (lagrangian d e) e.v d.V)
    (v : RealVector q) (hv : v ∈ d.V) :
    (α/2) * Quadratic.curvature (lagrangian d e) e.v v ≤ remainder d e v := by
  have hb := Quadratic.cut_le_of_safeScale (lagrangian_convex d e hk hr ht)
    (lagrangian_contDiff d e hC2 ht2) e.v d.V hα v hv
  dsimp [Quadratic.cut, Quadratic.tangent, remainder] at *
  linarith

theorem row_le_psqcRow (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    {α : ℝ} (hα0 : 0 ≤ α)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    pscRow d e w v y ≤ psqcRow d e α w v y := by
  have hc := Quadratic.curvature_nonneg (lagrangian_convex d e hk hr ht)
    (lagrangian_contDiff d e hC2 ht2) e.v v
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hα0 (by norm_num)) hc)

theorem row_bounds (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α ≤ Quadratic.safeScale (lagrangian d e) e.v d.V)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) :
    pscRow d e w v y ≤ psqcRow d e α w v y ∧ psqcRow d e α w v y ≤ d.r v := by
  refine ⟨row_le_psqcRow d e hk hr ht hC2 ht2 hα0 w v y, ?_⟩
  have hq := quadratic_le_remainder d e hk hr ht hC2 ht2 hα v hf.1.2.1
  have hg := remainder_le_row_gap d e hk w v y hf
  dsimp [psqcRow]
  linarith

theorem fullCut_le (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α ≤ Quadratic.safeScale (lagrangian d e) e.v d.V)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) : fullCut d e α w v y ≤ d.objective w v y := by
  have hb := (row_bounds d e hk hr ht hC2 ht2 hα0 hα w v y hf).2
  dsimp [fullCut, PSCData.objective]
  linarith

theorem row_at_anchor (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e) (α : ℝ) :
    psqcRow d e α e.w e.v e.y = d.r e.v := by
  simp [psqcRow, pscRow, hk.nonlinear_complementarity]

theorem fullCut_at_anchor (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e) (α : ℝ) :
    fullCut d e α e.w e.v e.y = d.objective e.w e.v e.y := by
  rw [fullCut, row_at_anchor d e hk]
  dsimp [PSCData.objective]
  ring

end Chapter05.PSQC
