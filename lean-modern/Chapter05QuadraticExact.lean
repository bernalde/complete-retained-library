module

public import Chapter05QuadraticMaster
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Exact quadratics on a real normed space. The bilinear form need not be
symmetric or positive semidefinite. The bounded scale lemma concerns the existing
clipped scale on the identical retained set, including its empty-domain branch. -/
noncomputable section
open Set
open scoped BigOperators
namespace Chapter05.Quadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Admissibility is maximal only among coefficients in the clipped interval. -/
theorem bounded_admissible_le_safeScale {f : E → ℝ} {a : E} {B : Set E} {c : ℝ}
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hvalid : ∀ x ∈ B, cut f a c x ≤ f x) : c ≤ safeScale f a B := by
  by_cases h : (positiveCurvatureDomain f a B).Nonempty
  · rw [safeScale_of_nonempty h]
    refine le_min hc1 ?_
    have hl : c / 2 ≤ sInf (ratioSet f a B) := by
      apply le_csInf (ratioSet_nonempty h)
      rintro r ⟨x,hx,rfl⟩
      apply (le_div_iff₀ hx.2).mpr
      have hv := hvalid x hx.1
      unfold cut at hv
      linarith
    linarith
  · rw [safeScale_of_empty h]
    exact hc1

theorem safeScale_le_one (f : E → ℝ) (a : E) (B : Set E) :
    safeScale f a B ≤ 1 := by
  by_cases h : (positiveCurvatureDomain f a B).Nonempty
  · rw [safeScale_of_nonempty h]
    exact min_le_left _ _
  · rw [safeScale_of_empty h]

theorem unit_underestimation_safeScale_eq_one {f : E → ℝ} {a : E} {B : Set E}
    (hvalid : ∀ x ∈ B, cut f a 1 x ≤ f x) : safeScale f a B = 1 :=
  le_antisymm (safeScale_le_one f a B)
    (bounded_admissible_le_safeScale (by norm_num) le_rfl hvalid)

/-- Concrete constant + continuous linear + continuous bilinear representation. -/
structure QuadraticFormData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  constant : ℝ
  linear : E →L[ℝ] ℝ
  bilinear : E →L[ℝ] E →L[ℝ] ℝ

namespace QuadraticFormData

def eval (q : QuadraticFormData E) (x : E) : ℝ :=
  q.constant + q.linear x + q.bilinear x x

theorem contDiff (q : QuadraticFormData E) : ContDiff ℝ 2 q.eval :=
  (contDiff_const.add q.linear.contDiff).add
    (q.bilinear.contDiff.clm_apply contDiff_id)

theorem hasFDerivAt (q : QuadraticFormData E) (a : E) :
    HasFDerivAt q.eval (q.linear + (q.bilinear a + q.bilinear.flip a)) a := by
  unfold eval
  simpa using
    ((hasFDerivAt_const q.constant a).fun_add q.linear.hasFDerivAt).fun_add
      (q.bilinear.hasFDerivAt.clm_apply (hasFDerivAt_id a))

theorem fderiv_eq (q : QuadraticFormData E) (a : E) :
    fderiv ℝ q.eval a = q.linear + (q.bilinear a + q.bilinear.flip a) :=
  (q.hasFDerivAt a).fderiv

theorem hessian_eq (q : QuadraticFormData E) (a : E) :
    fderiv ℝ (fderiv ℝ q.eval) a = q.bilinear + q.bilinear.flip := by
  have heq : fderiv ℝ q.eval =
      fun x => q.linear + (q.bilinear x + q.bilinear.flip x) :=
    funext q.fderiv_eq
  rw [heq]
  exact ((hasFDerivAt_const q.linear a).add
    (q.bilinear.hasFDerivAt.add q.bilinear.flip.hasFDerivAt)).fderiv.trans
      (by simp)

theorem curvature_eq (q : QuadraticFormData E) (a x : E) :
    curvature q.eval a x = 2 * q.bilinear (x-a) (x-a) := by
  rw [curvature, q.hessian_eq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply]
  ring

theorem cut_one_eq (q : QuadraticFormData E) (a x : E) :
    cut q.eval a 1 x = q.eval x := by
  rw [cut, tangent, q.fderiv_eq, q.curvature_eq]
  simp only [eval, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.flip_apply]
  ring

theorem safeScale_eq_one (q : QuadraticFormData E) (a : E) (B : Set E) :
    safeScale q.eval a B = 1 :=
  unit_underestimation_safeScale_eq_one (fun x _ => (q.cut_one_eq a x).le)

theorem convex_of_bilinear_nonneg (q : QuadraticFormData E)
    (hB : ∀ x, 0 ≤ q.bilinear x x) : ConvexOn ℝ univ q.eval := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy s t hs ht hst
  have hdiag := hB (x-y)
  have heq : s * q.eval x + t * q.eval y - q.eval (s • x + t • y) =
      (s*t) * q.bilinear (x-y) (x-y) := by
    simp only [eval, map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show t = 1-s by linarith]
    ring
  have hn := mul_nonneg (mul_nonneg hs ht) hdiag
  rw [← heq] at hn
  simpa only [smul_eq_mul] using sub_nonneg.mp hn

/-- For convex quadratics this is also the accepted sufficient-scale interface.
The algebraic identity and clipped-scale equality themselves need no convexity. -/
theorem convex_safeScale_bounds (q : QuadraticFormData E)
    (hconv : ConvexOn ℝ univ q.eval) (a : E) (B : Set E) :
    (0 ≤ safeScale q.eval a B ∧ safeScale q.eval a B ≤ 1) ∧
      safeScale q.eval a B = 1 :=
  ⟨safeScale_bounds hconv q.contDiff a B, q.safeScale_eq_one a B⟩

end QuadraticFormData

/-- Every finite real matrix gives an explicit continuous bilinear form.
No symmetry requirement is needed: the diagonal uses its symmetric part. -/
def coordinateBilinear {n : ℕ} (A : Fin n → Fin n → ℝ) :
    Chapter02.RealVector n →L[ℝ] Chapter02.RealVector n →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j •
    ((ContinuousLinearMap.proj i : Chapter02.RealVector n →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj j : Chapter02.RealVector n →L[ℝ] ℝ))

theorem coordinateBilinear_apply {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Chapter02.RealVector n) :
    coordinateBilinear A x y = ∑ i, ∑ j, A i j * x i * y j := by
  simp [coordinateBilinear, ContinuousLinearMap.sum_apply, mul_assoc]

def coordinateQuadratic {n : ℕ} (c : ℝ) (l : Fin n → ℝ)
    (A : Fin n → Fin n → ℝ) : QuadraticFormData (Chapter02.RealVector n) where
  constant := c
  linear := ∑ i, l i • (ContinuousLinearMap.proj i)
  bilinear := coordinateBilinear A

theorem coordinateQuadratic_eval {n : ℕ} (c : ℝ) (l : Fin n → ℝ)
    (A : Fin n → Fin n → ℝ) (x : Chapter02.RealVector n) :
    (coordinateQuadratic c l A).eval x =
      c + (∑ i, l i * x i) + ∑ i, ∑ j, A i j * x i * x j := by
  simp [coordinateQuadratic, QuadraticFormData.eval, coordinateBilinear_apply,
    ContinuousLinearMap.sum_apply]

end Chapter05.Quadratic
