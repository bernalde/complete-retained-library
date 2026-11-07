module

public import Chapter05QuadraticAnalytic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-! A sufficient clipped scale for actual convex C² quadratic rows.
Only strictly positive curvature enters the ratio. Empty ratio domains use the
explicit scale 1 convention; no mathematical minimum of an empty set is used.
The cap 1 is sufficient, not a maximal scale or the source's unrestricted alpha.
The source specialization uses the joint continuous/discrete-relaxed dimension.
-/
noncomputable section
open Set
namespace Chapter05.Quadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def positiveCurvatureDomain (f : E → ℝ) (a : E) (B : Set E) : Set E :=
  {x ∈ B | 0 < curvature f a x}

def ratioSet (f : E → ℝ) (a : E) (B : Set E) : Set ℝ :=
  (fun x => (f x - tangent f a x) / curvature f a x) ''
    positiveCurvatureDomain f a B

def safeScale (f : E → ℝ) (a : E) (B : Set E) : ℝ := by
  classical
  exact if (positiveCurvatureDomain f a B).Nonempty then
    min 1 (2 * sInf (ratioSet f a B)) else 1

theorem ratioSet_nonempty {f : E → ℝ} {a : E} {B : Set E}
    (h : (positiveCurvatureDomain f a B).Nonempty) :
    (ratioSet f a B).Nonempty := by
  rcases h with ⟨x,hx⟩
  exact ⟨_,⟨x,hx,rfl⟩⟩

theorem ratioSet_nonneg {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) (B : Set E) :
    ∀ r ∈ ratioSet f a B, 0 ≤ r := by
  rintro r ⟨x,hx,rfl⟩
  exact div_nonneg (sub_nonneg.mpr (tangent_le hconv hC2 a x)) hx.2.le

theorem ratioSet_bddBelow {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) (B : Set E) :
    BddBelow (ratioSet f a B) :=
  ⟨0,ratioSet_nonneg hconv hC2 a B⟩

theorem ratioSet_csInf_nonneg {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) (B : Set E)
    (h : (positiveCurvatureDomain f a B).Nonempty) :
    0 ≤ sInf (ratioSet f a B) :=
  le_csInf (ratioSet_nonempty h) (ratioSet_nonneg hconv hC2 a B)

theorem safeScale_of_nonempty {f : E → ℝ} {a : E} {B : Set E}
    (h : (positiveCurvatureDomain f a B).Nonempty) :
    safeScale f a B = min 1 (2 * sInf (ratioSet f a B)) := by
  simp only [safeScale,if_pos h]

theorem safeScale_of_empty {f : E → ℝ} {a : E} {B : Set E}
    (h : ¬ (positiveCurvatureDomain f a B).Nonempty) :
    safeScale f a B = 1 := by
  simp only [safeScale,if_neg h]

theorem safeScale_bounds {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) (B : Set E) :
    0 ≤ safeScale f a B ∧ safeScale f a B ≤ 1 := by
  by_cases h : (positiveCurvatureDomain f a B).Nonempty
  · rw [safeScale_of_nonempty h]
    exact ⟨le_min (by norm_num)
      (mul_nonneg (by norm_num) (ratioSet_csInf_nonneg hconv hC2 a B h)),
      min_le_left _ _⟩
  · rw [safeScale_of_empty h]
    norm_num

theorem curvature_zero_of_empty {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) (B : Set E)
    (h : ¬ (positiveCurvatureDomain f a B).Nonempty) {x : E} (hx : x ∈ B) :
    curvature f a x = 0 := by
  apply le_antisymm _ (curvature_nonneg hconv hC2 a x)
  exact le_of_not_gt (fun hp => h ⟨x,hx,hp⟩)

theorem cut_le_of_safeScale {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) (B : Set E) {α : ℝ}
    (hα : α ≤ safeScale f a B) (x : E) (hx : x ∈ B) :
    cut f a α x ≤ f x := by
  by_cases h : (positiveCurvatureDomain f a B).Nonempty
  · apply Chapter05.underestimator_of_ratio_bound
      (f x) (tangent f a x) (curvature f a x) α
      (curvature_nonneg hconv hC2 a x)
    · intro _
      exact tangent_le hconv hC2 a x
    · intro hp
      have hi : sInf (ratioSet f a B) ≤
          (f x - tangent f a x) / curvature f a x :=
        csInf_le (ratioSet_bddBelow hconv hC2 a B) ⟨x,⟨hx,hp⟩,rfl⟩
      have hs : α ≤ 2 * sInf (ratioSet f a B) := by
        rw [safeScale_of_nonempty h] at hα
        exact hα.trans (min_le_right _ _)
      linarith
  · rw [cut_eq_tangent_of_curvature_zero f a α x
      (curvature_zero_of_empty hconv hC2 a B h hx)]
    exact tangent_le hconv hC2 a x

theorem cut_bounds_of_safeScale {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : E) (B : Set E) {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ safeScale f a B) (x : E) (hx : x ∈ B) :
    tangent f a x ≤ cut f a α x ∧ cut f a α x ≤ f x ∧
      cut f a α x ≤ cut f a 1 x :=
  ⟨tangent_le_cut hconv hC2 a hα0 x,
   cut_le_of_safeScale hconv hC2 a B hα x hx,
   cut_le_second hconv hC2 a (hα.trans (safeScale_bounds hconv hC2 a B).2) x⟩

/-- Source-facing headline. `n+p` is the full joint (x,y) dimension.
The arbitrary retained B carries original domain, affine and integer restrictions;
the anchor need not belong to B. All derivatives are actual derivatives of f. -/
theorem source_joint_safeScale {n p : ℕ}
    {f : Chapter02.RealVector (n+p) → ℝ} (hconv : ConvexOn ℝ univ f)
    (hC2 : ContDiff ℝ 2 f) (a : Chapter02.RealVector (n+p))
    (B : Set (Chapter02.RealVector (n+p))) :
    (0 ≤ safeScale f a B ∧ safeScale f a B ≤ 1) ∧
      ∀ α : ℝ, 0 ≤ α → α ≤ safeScale f a B →
        ∀ x ∈ B, tangent f a x ≤ cut f a α x ∧ cut f a α x ≤ f x ∧
          cut f a α x ≤ cut f a 1 x :=
  ⟨safeScale_bounds hconv hC2 a B,
    fun _ hα0 hα x hx => cut_bounds_of_safeScale hconv hC2 a B hα0 hα x hx⟩

end Chapter05.Quadratic
