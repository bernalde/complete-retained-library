module

public import Chapter02
public import Chapter05
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Actual derivatives for the source-used convex C² quadratic rows.
The finite-dimensional source coordinates are the joint (x,y) coordinates;
retained integrality/domain restrictions belong to the consumer's base set.
This module does not supply a ratio scale or assert a maximal scale. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Chapter05.Quadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tangent (f : E → ℝ) (a x : E) : ℝ := f a + fderiv ℝ f a (x-a)
def curvature (f : E → ℝ) (a x : E) : ℝ :=
  fderiv ℝ (fderiv ℝ f) a (x-a) (x-a)
def cut (f : E → ℝ) (a : E) (α : ℝ) (x : E) : ℝ :=
  tangent f a x + (α/2)*curvature f a x

/-- Actual directional second derivative nonnegativity, from convexity.
No matrix or polynomial witness replaces the derivative of `fderiv`. -/
theorem hessian_nonneg {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a h : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) a h h := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a (a+h)
  have hline (t : ℝ) : HasDerivAt line h t := by
    simpa [line] using (AffineMap.hasDerivAt_lineMap (a := a) (b := a+h) (x := t))
  have hdf : Differentiable ℝ f := hC2.differentiable (by norm_num)
  have hdDf : Differentiable ℝ (fderiv ℝ f) :=
    (hC2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdline (t : ℝ) : HasDerivAt (f ∘ line) (fderiv ℝ f (line t) h) t :=
    (hdf (line t)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hderiv : deriv (f ∘ line) = fun t => fderiv ℝ f (line t) h := by
    funext t
    exact (hdline t).deriv
  have hcline : ConvexOn ℝ univ (f ∘ line) := by
    simpa using hconv.comp_affineMap line
  have hmono : Monotone (fun t => fderiv ℝ f (line t) h) := by
    rw [← hderiv]
    exact fun s t hst => hcline.monotoneOn_deriv
      (fun u _ => (hdline u).differentiableAt) (mem_univ s) (mem_univ t) hst
  have hd : HasDerivAt (fun t => fderiv ℝ f (line t) h)
      (fderiv ℝ (fderiv ℝ f) a h h) 0 := by
    have hc := (hdDf (line 0)).hasFDerivAt.comp_hasDerivAt 0 (hline 0)
    simpa [line] using hc.clm_apply (hasDerivAt_const (0 : ℝ) h)
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact smul_nonneg (inv_nonneg.mpr (le_of_lt ht))
    (sub_nonneg.mpr (hmono (by simpa using le_of_lt ht)))

theorem curvature_nonneg {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a x : E) : 0 ≤ curvature f a x :=
  hessian_nonneg hconv hC2 a (x-a)

theorem tangent_le {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a x : E) : tangent f a x ≤ f x :=
  Chapter02.tangent_underestimator hconv
    ((hC2.differentiable (by norm_num)) a).hasFDerivAt

theorem tangent_le_cut {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) {α : ℝ} (hα : 0 ≤ α) (x : E) :
    tangent f a x ≤ cut f a α x :=
  Chapter05.stronger_than_tangent _ _ _ (curvature_nonneg hconv hC2 a x) hα

theorem cut_le_second {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) {α : ℝ} (hα : α ≤ 1) (x : E) :
    cut f a α x ≤ cut f a 1 x := by
  unfold cut
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith)
    (curvature_nonneg hconv hC2 a x))

@[simp] theorem curvature_at_anchor (f : E → ℝ) (a : E) : curvature f a a = 0 := by
  simp [curvature]
@[simp] theorem tangent_at_anchor (f : E → ℝ) (a : E) : tangent f a a = f a := by
  simp [tangent]
@[simp] theorem cut_at_anchor (f : E → ℝ) (a : E) (α : ℝ) : cut f a α a = f a := by
  simp [cut]
@[simp] theorem cut_zero (f : E → ℝ) (a x : E) : cut f a 0 x = tangent f a x := by
  simp [cut]
theorem cut_one (f : E → ℝ) (a x : E) :
    cut f a 1 x = tangent f a x + curvature f a x / 2 := by
  unfold cut
  ring

theorem cut_eq_tangent_of_curvature_zero (f : E → ℝ) (a : E) (α : ℝ) (x : E)
    (hx : curvature f a x = 0) : cut f a α x = tangent f a x := by
  simp [cut, hx]

theorem taylor_order {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a x : E) :
    tangent f a x ≤ tangent f a x + curvature f a x / 2 := by
  simpa [cut_one] using tangent_le_cut hconv hC2 a (α := 1) (by norm_num) x

/-- Convexity of the actual quadratic row. The bilinear expansion uses only
its derived nonnegative diagonal, without separately postulating symmetry. -/
theorem cut_convex {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) {α : ℝ} (hα : 0 ≤ α) :
    ConvexOn ℝ univ (cut f a α) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy s t hs ht hst
  have hsub : s • x + t • y - a = s • (x-a) + t • (y-a) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
  let H := fderiv ℝ (fderiv ℝ f) a
  have hq : 0 ≤ H (x-y) (x-y) := hessian_nonneg hconv hC2 a (x-y)
  have hexp : s * cut f a α x + t * cut f a α y -
      cut f a α (s • x + t • y) = (α/2) * (s*t) * H (x-y) (x-y) := by
    have hxy : x-y = (x-a) - (y-a) := by abel
    unfold cut tangent curvature
    rw [hsub, hxy]
    simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    dsimp [H]
    rw [show t = 1-s by linarith]
    ring
  have hnonneg : 0 ≤ (α/2) * (s*t) * H (x-y) (x-y) :=
    mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hs ht)) hq
  rw [← hexp] at hnonneg
  simpa only [smul_eq_mul] using sub_nonneg.mp hnonneg

end Chapter05.Quadratic
