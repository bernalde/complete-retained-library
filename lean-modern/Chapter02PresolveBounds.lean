module

public import Chapter02
public import Mathlib.Tactic

@[expose] public section

/-! Coordinate certificates over a stated relaxation and closed-incumbent
cutoffs. No endpoint is defined by a totalized infimum or a solver status.
The extrema describe the tightest coordinate enclosure of R, not of F ⊆ R. -/
noncomputable section
namespace Chapter02

def coordinateEnclosure {E : Type*} {n : ℕ} (q : Fin n → E → ℝ)
    (L U : Fin n → ℝ) : Set E :=
  {x | ∀ i, L i ≤ q i x ∧ q i x ≤ U i}

theorem coordinateEnclosure_zero {E : Type*} (q : Fin 0 → E → ℝ)
    (L U : Fin 0 → ℝ) : coordinateEnclosure q L U = Set.univ := by
  ext x
  simp [coordinateEnclosure]

theorem coordinateEnclosure_of_relaxation {E : Type*} {n : ℕ}
    {F R : Set E} (q : Fin n → E → ℝ) (L U : Fin n → ℝ)
    (hFR : F ⊆ R) (hL : ∀ i, IsLowerBound R (q i) (L i))
    (hU : ∀ i, IsLowerBound R (fun x => -q i x) (-U i)) :
    F ⊆ coordinateEnclosure q L U := by
  intro x hx i
  exact ⟨lowerBound_of_relaxation hFR (hL i) x hx,
    neg_le_neg_iff.mp (lowerBound_of_relaxation hFR (hU i) x hx)⟩

theorem coordinateEnclosure_preserves_intersection {E : Type*} {n : ℕ}
    {F R : Set E} (B : Set E) (q : Fin n → E → ℝ) (L U : Fin n → ℝ)
    (hFR : F ⊆ R) (hL : ∀ i, IsLowerBound R (q i) (L i))
    (hU : ∀ i, IsLowerBound R (fun x => -q i x) (-U i)) :
    F ∩ (B ∩ coordinateEnclosure q L U) = F ∩ B := by
  ext x
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, coordinateEnclosure_of_relaxation q L U hFR hL hU h.1⟩

theorem coordinateEnclosure_ordered {E : Type*} {n : ℕ} {R : Set E}
    (q : Fin n → E → ℝ) (L U : Fin n → ℝ) (hne : R.Nonempty)
    (hR : R ⊆ coordinateEnclosure q L U) : ∀ i, L i ≤ U i := by
  obtain ⟨x, hx⟩ := hne
  exact fun i => (hR hx i).1.trans (hR hx i).2

/-- Coordinate minimizers and maximizers are actual points in compact nonempty R.
Different coordinates may require different points. The conclusion is enclosure,
not equality between R (or its coordinate images) and a box. -/
theorem compact_coordinate_extrema {E : Type*} [TopologicalSpace E] {n : ℕ}
    {R : Set E} (q : Fin n → E → ℝ) (hR : IsCompact R) (hne : R.Nonempty)
    (hq : ∀ i, ContinuousOn (q i) R) :
    ∃ lower upper : Fin n → E,
      (∀ i, IsMinimizer R (q i) (lower i)) ∧
      (∀ i, IsMinimizer R (fun x => -q i x) (upper i)) := by
  have hl : ∀ i, ∃ x, IsMinimizer R (q i) x :=
    fun i => compact_feasible_attainment hR hne (hq i)
  have hu : ∀ i, ∃ x, IsMinimizer R (fun x => -q i x) x :=
    fun i => compact_feasible_attainment hR hne (hq i).neg
  choose lower hl using hl
  choose upper hu using hu
  exact ⟨lower, upper, hl, hu⟩

theorem attained_coordinate_enclosure_tightest {E : Type*} {n : ℕ}
    {R : Set E} (q : Fin n → E → ℝ) (lower upper : Fin n → E)
    (hl : ∀ i, IsMinimizer R (q i) (lower i))
    (hu : ∀ i, IsMinimizer R (fun x => -q i x) (upper i)) :
    R ⊆ coordinateEnclosure q (fun i => q i (lower i)) (fun i => q i (upper i)) ∧
    ∀ L U, R ⊆ coordinateEnclosure q L U →
      (∀ i, L i ≤ q i (lower i) ∧ q i (upper i) ≤ U i) ∧
      coordinateEnclosure q (fun i => q i (lower i)) (fun i => q i (upper i)) ⊆
        coordinateEnclosure q L U := by
  refine ⟨coordinateEnclosure_of_relaxation q _ _ (Set.Subset.refl R)
    (fun i => (hl i).2) (fun i => (hu i).2), ?_⟩
  intro L U hbox
  have hb : ∀ i, L i ≤ q i (lower i) ∧ q i (upper i) ≤ U i :=
    fun i => ⟨(hbox (hl i).1 i).1, (hbox (hu i).1 i).2⟩
  exact ⟨hb, fun _ hx i => ⟨(hb i).1.trans (hx i).1, (hx i).2.trans (hb i).2⟩⟩

theorem compact_tightest_coordinate_enclosure {E : Type*} [TopologicalSpace E] {n : ℕ}
    {R : Set E} (q : Fin n → E → ℝ) (hR : IsCompact R) (hne : R.Nonempty)
    (hq : ∀ i, ContinuousOn (q i) R) :
    ∃ L U : Fin n → ℝ,
      (∀ i, L i ≤ U i) ∧ R ⊆ coordinateEnclosure q L U ∧
      (∀ i, (∃ x ∈ R, q i x = L i) ∧ ∃ x ∈ R, q i x = U i) ∧
      ∀ L' U', R ⊆ coordinateEnclosure q L' U' →
        coordinateEnclosure q L U ⊆ coordinateEnclosure q L' U' := by
  obtain ⟨lower, upper, hl, hu⟩ := compact_coordinate_extrema q hR hne hq
  obtain ⟨henclose, htight⟩ := attained_coordinate_enclosure_tightest q lower upper hl hu
  exact ⟨_, _, coordinateEnclosure_ordered q _ _ hne henclose, henclose,
    fun i => ⟨⟨lower i, (hl i).1, rfl⟩, ⟨upper i, (hu i).1, rfl⟩⟩,
    fun L U h => (htight L U h).2⟩

def cutoffSet {E : Type*} (F : Set E) (f : E → ℝ) (u : ℝ) : Set E :=
  {x | x ∈ F ∧ f x ≤ u}

theorem minimizer_mem_cutoff {E : Type*} {F : Set E} {f : E → ℝ} {u : ℝ}
    (hinc : HasUpperBoundWitness F f u) {x : E} (hx : IsMinimizer F f x) :
    x ∈ cutoffSet F f u := by
  obtain ⟨z, hz, hzu⟩ := hinc
  exact ⟨hx.1, (hx.2 z hz).trans hzu⟩

/-- F' may delete points above the closed cutoff, but no point below or at it.
An actual feasible incumbent suffices, including objective ties. -/
theorem cutoff_minimizer_iff {E : Type*} {F F' : Set E} {f : E → ℝ} {u : ℝ}
    (hinc : HasUpperBoundWitness F f u) (hkeep : cutoffSet F f u ⊆ F')
    (hsub : F' ⊆ F) (x : E) : IsMinimizer F f x ↔ IsMinimizer F' f x := by
  constructor
  · intro hx
    exact ⟨hkeep (minimizer_mem_cutoff hinc hx), fun y hy => hx.2 y (hsub hy)⟩
  · intro hx
    obtain ⟨z, hz, hzu⟩ := hinc
    have hxu : f x ≤ u := (hx.2 z (hkeep ⟨hz, hzu⟩)).trans hzu
    refine ⟨hsub hx.1, ?_⟩
    intro y hy
    by_cases hyu : f y ≤ u
    · exact hx.2 y (hkeep ⟨hy, hyu⟩)
    · exact hxu.trans (le_of_not_ge hyu)

theorem cutoff_bounds_preserve_minimizers {E : Type*} {n : ℕ}
    {F R : Set E} {f : E → ℝ} {u : ℝ} (q : Fin n → E → ℝ) (L U : Fin n → ℝ)
    (hinc : HasUpperBoundWitness F f u) (hR : cutoffSet F f u ⊆ R)
    (hL : ∀ i, IsLowerBound R (q i) (L i))
    (hU : ∀ i, IsLowerBound R (fun x => -q i x) (-U i)) (x : E) :
    IsMinimizer F f x ↔ IsMinimizer (F ∩ coordinateEnclosure q L U) f x := by
  apply cutoff_minimizer_iff hinc
  · intro y hy
    exact ⟨hy.1, coordinateEnclosure_of_relaxation q L U hR hL hU hy⟩
  · exact Set.inter_subset_left

theorem cutoff_nonempty_of_incumbent {E : Type*} {F : Set E} {f : E → ℝ} {u : ℝ}
    (hinc : HasUpperBoundWitness F f u) : (cutoffSet F f u).Nonempty := by
  obtain ⟨x, hx, hfu⟩ := hinc
  exact ⟨x, hx, hfu⟩

end Chapter02

#print axioms Chapter02.coordinateEnclosure_zero
#print axioms Chapter02.coordinateEnclosure_of_relaxation
#print axioms Chapter02.coordinateEnclosure_preserves_intersection
#print axioms Chapter02.coordinateEnclosure_ordered
#print axioms Chapter02.compact_coordinate_extrema
#print axioms Chapter02.attained_coordinate_enclosure_tightest
#print axioms Chapter02.compact_tightest_coordinate_enclosure
#print axioms Chapter02.minimizer_mem_cutoff
#print axioms Chapter02.cutoff_minimizer_iff
#print axioms Chapter02.cutoff_bounds_preserve_minimizers
#print axioms Chapter02.cutoff_nonempty_of_incumbent
