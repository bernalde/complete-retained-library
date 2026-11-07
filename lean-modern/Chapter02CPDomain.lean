module

public import Chapter02
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Data.Fintype.Order

@[expose] public section

/-! Domain-relative smooth cuts. The specified derivative is an actual within-set
derivative witness, not a canonical derivative or an assumed support field.
These results hold in any real normed space; no unique-differentiability or
finite-dimensional hypothesis is used. Boundedness refers only to a specified
continuous operator-valued field on a compact set. -/

noncomputable section
namespace Chapter02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convexity and an actual derivative within the declared domain imply
two-point tangent support inside that domain, including its relative boundary. -/
theorem cp_tangent_underestimator_within
    {g : E → ℝ} {D : E →L[ℝ] ℝ} {K : Set E} {z x : E}
    (hconv : ConvexOn ℝ K g) (hz : z ∈ K) (hx : x ∈ K)
    (hderiv : HasFDerivWithinAt g D K z) :
    g z + D (x - z) ≤ g x := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap z x
  have hc : ConvexOn ℝ (line ⁻¹' K) (g ∘ line) := hconv.comp_affineMap line
  have hd : HasDerivWithinAt (g ∘ line) (D (x - z)) (line ⁻¹' K) 0 :=
    hderiv.comp_hasDerivWithinAt_of_eq 0 AffineMap.hasDerivWithinAt_lineMap
      (Set.mapsTo_preimage _ _) (by simp [line])
  have h0 : (0 : ℝ) ∈ line ⁻¹' K := by simpa [line] using hz
  have h1 : (1 : ℝ) ∈ line ⁻¹' K := by simpa [line] using hx
  have hs := hc.le_slope_of_hasDerivWithinAt h0 h1 (by norm_num) hd
  simp only [line, slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hs
  linarith

/-- A feasible point in the declared domain satisfies the derived tangent cut. -/
theorem cp_tangent_cut_valid_within
    {g : E → ℝ} {D : E →L[ℝ] ℝ} {K : Set E} {z x : E}
    (hconv : ConvexOn ℝ K g) (hz : z ∈ K) (hx : x ∈ K)
    (hderiv : HasFDerivWithinAt g D K z) (hfeas : g x ≤ 0) :
    g z + D (x - z) ≤ 0 :=
  (cp_tangent_underestimator_within hconv hz hx hderiv).trans hfeas

/-- Actual within-domain derivative witnesses imply continuity on that domain.
No continuity of the specified derivative field is inferred. -/
theorem cp_continuousOn_of_derivative_within
    {g : E → ℝ} {D : E → E →L[ℝ] ℝ} {K : Set E}
    (hderiv : ∀ z ∈ K, HasFDerivWithinAt g (D z) K z) :
    ContinuousOn g K :=
  fun z hz => (hderiv z hz).continuousWithinAt

/-- The norm of one specified continuous field has a nonnegative finite bound
on a compact domain. Empty domains require no extremum witness. -/
theorem cp_continuous_field_bounded
    {D : E → E →L[ℝ] ℝ} {K : Set E}
    (hK : IsCompact K) (hD : ContinuousOn D K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ‖D z‖ ≤ M := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hD
  exact ⟨max 0 C, le_max_left _ _, fun z hz => (hC z hz).trans (le_max_right _ _)⟩

/-- A finite family of specified continuous derivative fields has one finite
norm bound on a compact domain. The index type and domain may both be empty. -/
theorem cp_finite_continuous_fields_bounded
    {J : Type*} [Finite J] {D : J → E → E →L[ℝ] ℝ} {K : Set E}
    (hK : IsCompact K) (hD : ∀ j, ContinuousOn (D j) K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j z, z ∈ K → ‖D j z‖ ≤ M := by
  choose C hC hbound using fun j => cp_continuous_field_bounded hK (hD j)
  obtain ⟨M, hM⟩ := Finite.exists_le C
  exact ⟨max 0 M, le_max_left _ _, fun j z hz =>
    (hbound j z hz).trans ((hM j).trans (le_max_right _ _))⟩

end Chapter02

#print axioms Chapter02.cp_tangent_underestimator_within
#print axioms Chapter02.cp_tangent_cut_valid_within
#print axioms Chapter02.cp_continuousOn_of_derivative_within
#print axioms Chapter02.cp_continuous_field_bounded
#print axioms Chapter02.cp_finite_continuous_fields_bounded
