module

public import Chapter03FPUnboundedGeometry
public import Chapter03FPUnboundedLattice
public import Chapter02ECPAnalysis
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Uniform finite chronological-prefix bounds derived from retained normals.
The bounds are proof witnesses and are never inserted into a master. -/
noncomputable section
open Chapter02
open scoped RealInnerProductSpace
namespace Chapter03.FPUnbounded

def FarPackingBound (m P : ℕ) : Prop :=
  ∀ (R : ℝ), 1 ≤ R → ∀ k : ℕ,
    ∀ p q : Fin k → EuclideanSpace ℝ (Fin m),
    (∀ i, ‖p i‖ ≤ R) → (∀ i, 4 * R ≤ ‖q i‖) →
    (∀ i j, i < j → 0 ≤ @inner ℝ _ _ (p i - q i) (q j - p i)) → k ≤ P

theorem far_packing_bound_exists (m : ℕ) : ∃ P : ℕ, FarPackingBound m P := by
  obtain ⟨P, hP⟩ := Chapter02.cp_compact_separated_prefix_bound
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (by norm_num : (0 : ℝ) < 1)
  refine ⟨P, ?_⟩
  intro R hR k p q hp hq hc
  apply hP k (fun i => normalizedTarget (q i))
  · intro i
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_normalizedTarget (far_target_norm_pos hR (hq i))).le
  · intro i j hij
    exact far_targets_separated hR (hp i) (hq i) (hq j) (hc i j hij)

theorem far_subset_card_bound {m P k : ℕ} (hP : FarPackingBound m P)
    {R : ℝ} (hR : 1 ≤ R) (T : Finset (Fin k))
    (p q : Fin k → EuclideanSpace ℝ (Fin m))
    (hp : ∀ i ∈ T, ‖p i‖ ≤ R) (hq : ∀ i ∈ T, 4 * R ≤ ‖q i‖)
    (hc : ∀ i ∈ T, ∀ j ∈ T, i < j →
      0 ≤ @inner ℝ _ _ (p i - q i) (q j - p i)) : T.card ≤ P := by
  classical
  let e := T.orderEmbOfFin rfl
  have he : ∀ i, e i ∈ T := fun i => T.orderEmbOfFin_mem rfl i
  exact hP R hR T.card (fun i => p (e i)) (fun i => q (e i))
    (fun i => hp (e i) (he i)) (fun i => hq (e i) (he i))
    (fun i j hij => hc (e i) (he i) (e j) (he j) (e.strictMono hij))

theorem failed_targets_injective {m k : ℕ}
    (p : Fin k → EuclideanSpace ℝ (Fin m)) (q : Fin k → IntVector m)
    (hne : ∀ i, p i ≠ FP.intY (q i))
    (hc : ∀ i j, i < j →
      0 ≤ @inner ℝ _ _ (p i - FP.intY (q i)) (FP.intY (q j) - p i)) :
    Function.Injective q := by
  intro i j he
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact retained_normal_excludes_failed (hne i) (hc i j hlt) (congrArg FP.intY he.symm)
  · exact retained_normal_excludes_failed (hne j) (hc j i hgt) (congrArg FP.intY he)

theorem failed_prefix_card_bound {m P k : ℕ} (hP : FarPackingBound m P)
    {R : ℝ} (hR : 1 ≤ R)
    (p : Fin k → EuclideanSpace ℝ (Fin m)) (q : Fin k → IntVector m)
    (hp : ∀ i, ‖p i‖ ≤ R) (hne : ∀ i, p i ≠ FP.intY (q i))
    (hc : ∀ i j, i < j →
      0 ≤ @inner ℝ _ _ (p i - FP.intY (q i)) (FP.intY (q j) - p i)) :
    k ≤ (proofLatticeBox m (4 * R)).card + P := by
  classical
  let far : Finset (Fin k) := Finset.univ.filter (fun i => 4 * R ≤ ‖FP.intY (q i)‖)
  let near : Finset (Fin k) := Finset.univ.filter (fun i => ¬4 * R ≤ ‖FP.intY (q i)‖)
  have hfar : far.card ≤ P := by
    apply far_subset_card_bound hP hR far p (fun i => FP.intY (q i))
    · intro i _; exact hp i
    · intro i hi; exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij; exact hc i j hij
  have hnear : near.card ≤ (proofLatticeBox m (4 * R)).card := by
    apply integer_subset_card_bound near q
    · intro i hi
      exact (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
    · exact (failed_targets_injective p q hne hc).injOn
  have hsum : far.card + near.card = k := by
    simpa [far, near] using Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun i : Fin k => 4 * R ≤ ‖FP.intY (q i)‖)
  omega

theorem failed_subset_card_bound {m P k : ℕ} (hP : FarPackingBound m P)
    {R : ℝ} (hR : 1 ≤ R) (T : Finset (Fin k))
    (p : Fin k → EuclideanSpace ℝ (Fin m)) (q : Fin k → IntVector m)
    (hp : ∀ i ∈ T, ‖p i‖ ≤ R) (hne : ∀ i ∈ T, p i ≠ FP.intY (q i))
    (hc : ∀ i ∈ T, ∀ j ∈ T, i < j →
      0 ≤ @inner ℝ _ _ (p i - FP.intY (q i)) (FP.intY (q j) - p i)) :
    T.card ≤ (proofLatticeBox m (4 * R)).card + P := by
  classical
  let e := T.orderEmbOfFin rfl
  have he : ∀ i, e i ∈ T := fun i => T.orderEmbOfFin_mem rfl i
  exact failed_prefix_card_bound hP hR (fun i => p (e i)) (fun i => q (e i))
    (fun i => hp (e i) (he i)) (fun i => hne (e i) (he i))
    (fun i j hij => hc (e i) (he i) (e j) (he j) (e.strictMono hij))

theorem zero_dimensional_no_failed_prefix {k : ℕ}
    (p : Fin k → EuclideanSpace ℝ (Fin 0)) (q : Fin k → IntVector 0)
    (hne : ∀ i, p i ≠ FP.intY (q i)) : k = 0 := by
  by_contra hk
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  exact hne ⟨0, hkpos⟩ (Subsingleton.elim _ _)

theorem zero_dimensional_no_far_prefix {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (q : Fin k → EuclideanSpace ℝ (Fin 0)) (hq : ∀ i, 4 * R ≤ ‖q i‖) : k = 0 := by
  by_contra hk
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have he : q ⟨0, hkpos⟩ = 0 := Subsingleton.elim _ _
  have hh := hq ⟨0, hkpos⟩
  rw [he, norm_zero] at hh
  linarith

end Chapter03.FPUnbounded
