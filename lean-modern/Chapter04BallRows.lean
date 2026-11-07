module

public import Chapter04Euclidean
public import Chapter04

@[expose] public section

/-! Exact affine-row/closed-ball correspondence. The converse uses every
ambient direction and includes the zero normal and zero radius. No gradient
transport or retained tangent history is asserted by this module. -/

noncomputable section
namespace Chapter04.CenterCut

theorem normalized_halfspace_of_ball {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a x p : E) (v r : ℝ) (hr : 0 ≤ r)
    (hball : ∀ z, ‖z - x‖ ≤ r → v + inner ℝ a (z - p) ≤ 0) :
    v + inner ℝ a (x - p) + r * ‖a‖ ≤ 0 := by
  by_cases ha : a = 0
  · have hx := hball x (by simpa using hr)
    simpa [ha] using hx
  · have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hratio : 0 ≤ r / ‖a‖ := div_nonneg hr (norm_nonneg a)
    have hdist : ‖x + (r / ‖a‖) • a - x‖ ≤ r := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio,
        div_mul_cancel₀ _ hnorm]
    have hz := hball (x + (r / ‖a‖) • a) hdist
    have heq : x + (r / ‖a‖) • a - p = (x - p) + (r / ‖a‖) • a := by abel
    rw [heq, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at hz
    have hid : r / ‖a‖ * ‖a‖ ^ 2 = r * ‖a‖ := by
      field_simp
    linarith

theorem normalized_halfspace_ball_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a x p : E) (v r : ℝ) (hr : 0 ≤ r) :
    (v + inner ℝ a (x - p) + r * ‖a‖ ≤ 0) ↔
      ∀ z, ‖z - x‖ ≤ r → v + inner ℝ a (z - p) ≤ 0 := by
  constructor
  · intro hcut z hz
    exact Chapter04.normalized_halfspace_ball_valid a x p z v r hcut hz
  · exact normalized_halfspace_of_ball a x p v r hr

/-- The source dot-product row is equivalent to containment of the entire
concatenated Euclidean ball, including integer-coordinate directions. -/
theorem source_normalized_halfspace_ball_iff {n m : ℕ}
    (a x p : Chapter02.Point n m) (v r : ℝ) (hr : 0 ≤ r) :
    (v + Chapter02.LinearForm a.1 a.2 (x - p) + r * ‖coordinates n m a‖ ≤ 0) ↔
      ∀ z : Chapter02.Point n m,
        ‖coordinates n m z - coordinates n m x‖ ≤ r →
          v + Chapter02.LinearForm a.1 a.2 (z - p) ≤ 0 := by
  have h := normalized_halfspace_ball_iff (coordinates n m a) (coordinates n m x)
    (coordinates n m p) v r hr
  simp only [← map_sub, inner_coordinates] at h
  constructor
  · intro hcut z hz
    simpa only [← map_sub, inner_coordinates] using h.mp hcut (coordinates n m z) hz
  · intro hball
    apply h.mpr
    intro z hz
    have hz' := hball ((coordinates n m).symm z)
    simpa only [map_sub, ContinuousLinearEquiv.apply_symm_apply, ← inner_coordinates]
      using hz' (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz)

end Chapter04.CenterCut
