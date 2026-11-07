module

public import Chapter02ESH
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

/-! Bounded ambient convex-subgradient preparation for the contextual Eronen2014
source, Definition2.1 and the one-way part of Lemmas2.3/2.4. This is not Clarke
calculus, a universal normal-existence theorem, the reverse maximum formula, OA
normal-selection permission, or a nonsmooth algorithm/convergence result.

The norm on a functional is its actual operator norm. In Chapter02.Point the
finite Pi/product norms are sup/max norms; no numerical Euclidean constant is
identified. The compact set need not have interior, be convex, or be nonempty.
Finite dimensionality is used to derive actual ambient local Lipschitzness of
the finite-valued globally convex function, not imposed on the compact set. -/

noncomputable section
open scoped BigOperators Topology
open Set Metric
namespace Chapter02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine ambient supporting functionals: the test point ranges over all E,
not just a selected domain, affine region, or integer cylinder. -/
def ambientConvexSubdiff (f : E → ℝ) (x : E) : Set (E →L[ℝ] ℝ) :=
  {D | ∀ y : E, f x + D (y - x) ≤ f y}

/-- The norm estimate holds for every normal at every point of a smaller
ambient ball. This is an internal analytic step, not separate target credit. -/
private lemma ambient_subgradient_bound_of_lipschitz_ball
    {f : E → ℝ} {c : E} {r : ℝ} {L : NNReal} (hr : 0 < r)
    (hLip : LipschitzOnWith L f (ball c r))
    {x : E} (hx : x ∈ ball c (r / 2))
    {D : E →L[ℝ] ℝ} (hD : D ∈ ambientConvexSubdiff f x) : ‖D‖ ≤ (L : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_of_ball (half_pos hr) L.coe_nonneg
  intro v hv
  have hsmall : ball x (r / 2) ⊆ ball c r :=
    ball_subset_ball' (by have := mem_ball.mp hx; linarith)
  have hx' : x ∈ ball c r :=
    (ball_subset_ball (by linarith : r / 2 ≤ r)) hx
  have hp : x + v ∈ ball c r := hsmall (by
    simpa [mem_ball, dist_eq_norm] using hv)
  have hm : x - v ∈ ball c r := hsmall (by
    simpa [mem_ball, dist_eq_norm] using hv)
  have hplus := hD (x + v)
  have hminus := hD (x - v)
  rw [show x + v - x = v by abel] at hplus
  rw [show x - v - x = -v by abel, map_neg] at hminus
  have hlp : |f (x + v) - f x| ≤ (L : ℝ) * ‖v‖ := by
    simpa [dist_eq_norm] using hLip.dist_le_mul (x + v) hp x hx'
  have hlm : |f (x - v) - f x| ≤ (L : ℝ) * ‖v‖ := by
    simpa [dist_eq_norm] using hLip.dist_le_mul (x - v) hm x hx'
  have hup : D v ≤ (L : ℝ) * ‖v‖ := by
    have := le_abs_self (f (x + v) - f x)
    linarith
  have hdown : -(D v) ≤ (L : ℝ) * ‖v‖ := by
    have := le_abs_self (f (x - v) - f x)
    linarith
  simpa only [Real.norm_eq_abs] using abs_le.mpr ⟨by linarith, hup⟩

/-- One finite bound covers all actual ambient convex subgradients at all points
of any compact K. No continuous choice of normals or bound oracle is assumed. -/
theorem ambient_convex_subgradients_bounded
    [FiniteDimensional ℝ E] {f : E → ℝ} {K : Set E}
    (hf : ConvexOn ℝ Set.univ f) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K,
      ∀ D ∈ ambientConvexSubdiff f x, ‖D‖ ≤ M := by
  classical
  have hlocal : ∀ c : E, ∃ L : NNReal, ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ ball c r, ∀ D ∈ ambientConvexSubdiff f x, ‖D‖ ≤ (L : ℝ) := by
    intro c
    obtain ⟨L, U, hU, hLip⟩ := hf.locallyLipschitz c
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨L, r / 2, half_pos hr, ?_⟩
    intro x hx D hD
    exact ambient_subgradient_bound_of_lipschitz_ball hr (hLip.mono hball) hx hD
  choose L r hr hlocal using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : E => ball c (r c))
    (fun _ => isOpen_ball) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_ball_self (hr x)⟩)
  refine ⟨(t.sup L : NNReal), NNReal.coe_nonneg _, ?_⟩
  intro x hx D hD
  obtain ⟨c, hc⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hct, hxc⟩ := mem_iUnion.mp hc
  apply (hlocal c x hxc D hD).trans
  exact_mod_cast (Finset.le_sup (f := L) hct)

/-- Reusable finite-maximum convexity, without any normal/existence premises.
This helper receives no separate target credit. -/
lemma eshMaximum_convexOn_univ {J : Type*} [Fintype J] [Nonempty J]
    {g : J → E → ℝ} (hg : ∀ j, ConvexOn ℝ Set.univ (g j)) :
    ConvexOn ℝ Set.univ (eshMaximum g) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply (eshMaximum_le_iff g _ _).mpr
  intro j
  calc
    g j (a • x + b • y) ≤ a • g j x + b • g j y := (hg j).2 hx hy ha hb hab
    _ ≤ a • eshMaximum g x + b • eshMaximum g y := by
      simp only [smul_eq_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left ((eshMaximum_le_iff g x _).mp le_rfl j) ha)
        (mul_le_mul_of_nonneg_left ((eshMaximum_le_iff g y _).mp le_rfl j) hb)

/-- Constructive active-normal inclusion for the same full finite maximum at
the origin and test point. Zero-weight rows need no normal witness. The reverse
calculus formula and arbitrary-point subgradient existence are not asserted. -/
theorem active_convex_subgradient_sum {J : Type*} [Fintype J] [Nonempty J]
    {g : J → E → ℝ} {z : E}
    (hg : ∀ j, ConvexOn ℝ Set.univ (g j))
    (w : J → ℝ) (D : J → E →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (hactive : ∀ j, w j ≠ 0 → g j z = eshMaximum g z)
    (hsub : ∀ j, w j ≠ 0 → D j ∈ ambientConvexSubdiff (g j) z) :
    ConvexOn ℝ Set.univ (eshMaximum g) ∧
      (∑ j, w j • D j) ∈ ambientConvexSubdiff (eshMaximum g) z := by
  refine ⟨eshMaximum_convexOn_univ hg, ?_⟩
  intro y
  have hrow : ∀ j, w j * (eshMaximum g z + D j (y - z)) ≤ w j * eshMaximum g y := by
    intro j
    by_cases hzero : w j = 0
    · simp [hzero]
    · have h := hsub j hzero y
      rw [hactive j hzero] at h
      exact mul_le_mul_of_nonneg_left
        (h.trans ((eshMaximum_le_iff g y _).mp le_rfl j)) (hw j)
  have hsumle := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hrow j)
  simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using hsumle

end Chapter02

#print axioms Chapter02.ambient_convex_subgradients_bounded
#print axioms Chapter02.active_convex_subgradient_sum
