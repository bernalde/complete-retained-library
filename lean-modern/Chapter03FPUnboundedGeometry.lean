module

public import Chapter03FPModel
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-! Generic retained-normal geometry. No master or integer bounds occur here. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Chapter03.FPUnbounded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫_ℝ" => @inner ℝ E _ x y

def normalizedTarget (q : E) : E := ‖q‖⁻¹ • q

theorem norm_normalizedTarget {q : E} (hq : 0 < ‖q‖) :
    ‖normalizedTarget q‖ = 1 := by
  simp [normalizedTarget, norm_smul, abs_of_pos (inv_pos.mpr hq), ne_of_gt hq]

theorem retained_normal_inner_bound {p q r : E} {R : ℝ}
    (hp : ‖p‖ ≤ R) (hcut : 0 ≤ ⟪p - q, r - p⟫_ℝ) :
    ⟪q, r⟫_ℝ ≤ R * ‖q‖ + R * ‖r‖ := by
  have hex : ⟪p - q, r - p⟫_ℝ =
      ⟪p, r⟫_ℝ - ⟪p, p⟫_ℝ - ⟪q, r⟫_ℝ + ⟪q, p⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hpr := (real_inner_le_norm p r).trans
    (mul_le_mul_of_nonneg_right hp (norm_nonneg r))
  have hqp := (real_inner_le_norm q p).trans
    (mul_le_mul_of_nonneg_left hp (norm_nonneg q))
  rw [hex, real_inner_self_eq_norm_sq] at hcut
  nlinarith [sq_nonneg ‖p‖]

omit [InnerProductSpace ℝ E] in
theorem far_target_norm_pos {R : ℝ} (hR : 1 ≤ R) {q : E}
    (hq : 4 * R ≤ ‖q‖) : 0 < ‖q‖ := by linarith

theorem far_normalized_inner_le_half {p q r : E} {R : ℝ}
    (hR : 1 ≤ R) (hp : ‖p‖ ≤ R)
    (hq : 4 * R ≤ ‖q‖) (hr : 4 * R ≤ ‖r‖)
    (hcut : 0 ≤ ⟪p - q, r - p⟫_ℝ) :
    ⟪normalizedTarget q, normalizedTarget r⟫_ℝ ≤ 1 / 2 := by
  have hqpos := far_target_norm_pos hR hq
  have hrpos := far_target_norm_pos hR hr
  have hb := retained_normal_inner_bound hp hcut
  have hprod : 0 < ‖q‖ * ‖r‖ := mul_pos hqpos hrpos
  have hqr : R * ‖q‖ ≤ ‖r‖ * ‖q‖ / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hr (norm_nonneg q)]
  have hrq : R * ‖r‖ ≤ ‖q‖ * ‖r‖ / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hq (norm_nonneg r)]
  have hn : ⟪q, r⟫_ℝ ≤ (‖q‖ * ‖r‖) / 2 := by nlinarith
  have hid : ⟪normalizedTarget q, normalizedTarget r⟫_ℝ =
      ⟪q, r⟫_ℝ / (‖q‖ * ‖r‖) := by
    simp only [normalizedTarget, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    ring
  rw [hid]
  exact (div_le_iff₀ hprod).mpr (by nlinarith)

theorem far_targets_separated {p q r : E} {R : ℝ}
    (hR : 1 ≤ R) (hp : ‖p‖ ≤ R)
    (hq : 4 * R ≤ ‖q‖) (hr : 4 * R ≤ ‖r‖)
    (hcut : 0 ≤ ⟪p - q, r - p⟫_ℝ) :
    1 ≤ dist (normalizedTarget q) (normalizedTarget r) := by
  have hb := far_normalized_inner_le_half hR hp hq hr hcut
  have hqn := norm_normalizedTarget (far_target_norm_pos hR hq)
  have hrn := norm_normalizedTarget (far_target_norm_pos hR hr)
  have he := norm_sub_sq_real (normalizedTarget q) (normalizedTarget r)
  rw [hqn, hrn] at he
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (normalizedTarget q - normalizedTarget r)]

theorem retained_normal_excludes_failed {p q r : E}
    (hne : p ≠ q) (hcut : 0 ≤ ⟪p - q, r - p⟫_ℝ) : r ≠ q := by
  intro he
  subst r
  have hn := Chapter03.projection_cut_excludes hne
  linarith

end Chapter03.FPUnbounded
