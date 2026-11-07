module

public import Chapter04BallRows
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp

@[expose] public section

/-! Canonical Euclidean normals for the source tangent rows. The original
product/Pi norm is unchanged. Differentiability makes the transported gradient
the actual derivative; convexity supplies support. A feasible witness excludes
a zero normal at a strictly violated row. Active zero-normal rows remain valid.
The S007 history uses strictly violated rows in Algorithm2.b; the broader g ≥ 0
row selection in the source's equations is not formalized by that history. -/

noncomputable section
namespace Chapter04.CenterCut
open Chapter02

/-- The source gradient in the concrete concatenated Euclidean coordinates. -/
def euclideanGradient {n m : ℕ} (g : Point n m → ℝ) (p : Point n m) :
    EuclideanPoint n m :=
  gradient (g ∘ (coordinates n m).symm) (coordinates n m p)

/-- The Euclidean normal represents the actual derivative on every displacement. -/
theorem inner_euclideanGradient {n m : ℕ} {g : Point n m → ℝ} {p : Point n m}
    (hd : DifferentiableAt ℝ g p) (v : Point n m) :
    inner ℝ (euclideanGradient g p) (coordinates n m v) = fderiv ℝ g p v := by
  have hg : HasFDerivAt g (fderiv ℝ g p)
      ((coordinates n m).symm (coordinates n m p)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hd.hasFDerivAt
  have hc := hg.comp (coordinates n m p)
    (coordinates n m).symm.toContinuousLinearMap.hasFDerivAt
  rw [euclideanGradient, gradient, hc.fderiv, InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Every nonlinear-feasible point satisfies its canonical tangent row. -/
theorem euclideanGradient_tangent_valid {n m : ℕ} {g : Point n m → ℝ}
    {p q : Point n m} (hconv : ConvexOn ℝ Set.univ g)
    (hd : DifferentiableAt ℝ g p) (hq : g q ≤ 0) :
    g p + inner ℝ (euclideanGradient g p)
      (coordinates n m q - coordinates n m p) ≤ 0 := by
  rw [← map_sub, inner_euclideanGradient hd]
  exact tangent_cut_valid hconv hd.hasFDerivAt hq

/-- A violated row has a nonzero normal when the same row has a feasible witness. -/
theorem euclideanGradient_ne_zero_of_violation {n m : ℕ} {g : Point n m → ℝ}
    {p w : Point n m} (hconv : ConvexOn ℝ Set.univ g)
    (hd : DifferentiableAt ℝ g p) (hp : 0 < g p) (hw : g w ≤ 0) :
    euclideanGradient g p ≠ 0 := by
  intro hzero
  have h := euclideanGradient_tangent_valid hconv hd hw
  simp only [hzero, inner_zero_left, add_zero] at h
  exact (not_le_of_gt hp) h

end Chapter04.CenterCut
