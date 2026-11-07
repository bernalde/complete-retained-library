module

public import Chapter02Initializer
public import Chapter02BBAffine

@[expose] public section

/-! The source initializer chooses X or X ∩ L, without integer restrictions.
Actual feasible-height and universal-bound evidence have separate consumers.
Compactness of X is explicit and says nothing about unrestricted thesis L.
This module gives no solver status, producer, or convergence certificate. -/

noncomputable section
namespace Chapter02

/-- The source's continuous initializer domain; integrality is absent. -/
def sourceInitializerDomain {n m l r : ℕ} (d : ModelData n m l r)
    (K : Set (Point n m)) (retainAffine : Bool) : Set (Point n m) :=
  if retainAffine then K ∩ d.linearRegion else K

private theorem initializer_domain_subset {n m l r : ℕ} (d : ModelData n m l r)
    (K : Set (Point n m)) (retainAffine : Bool) :
    sourceInitializerDomain d K retainAffine ⊆ K := by
  cases retainAffine <;> simp [sourceInitializerDomain]

/-- Compact X and its closed affine restriction supply an actual signed
minimum and its tight free-height minimum. Only relative row continuity is used. -/
theorem source_initializer_minimum_attained {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (K : Set (Point n m)) (retainAffine : Bool)
    (hK : IsCompact K) (hne : (sourceInitializerDomain d K retainAffine).Nonempty)
    (hg : ∀ j, ContinuousOn (d.g j) K) :
    ∃ p, IsMinimizer (sourceInitializerDomain d K retainAffine) (eshMaximum d.g) p ∧
      IsMinimizer (RestorationPairs (sourceInitializerDomain d K retainAffine) d.g)
        Prod.snd (p, eshMaximum d.g p) := by
  have hs : IsCompact (sourceInitializerDomain d K retainAffine) := by
    cases retainAffine
    · simpa [sourceInitializerDomain] using hK
    · simpa [sourceInitializerDomain] using hK.inter_right (bb_linearRegion_closed d)
  exact initializer_minimum_attained hs hne
    (fun j => (hg j).mono (initializer_domain_subset d K retainAffine))

/-- Nonpositive pair height restores original feasibility only with actual
affine membership and the bounded integer-cylinder witness. -/
theorem source_initializer_feasible {n m l r : ℕ} (d : ModelData n m l r)
    (K : Set (Point n m)) (retainAffine : Bool) {p : Point n m} {h : ℝ}
    (hp : (p,h) ∈ RestorationPairs (sourceInitializerDomain d K retainAffine) d.g)
    (hh : h ≤ 0) (hL : p ∈ d.linearRegion)
    (hY : p ∈ IntegerCylinder (n := n) d.lo d.hi) : p ∈ d.feasibleOn K := by
  have he := initializer_feasible_height hp
  apply (source_feasible_iff d K p).mpr
  exact ⟨initializer_domain_subset d K retainAffine he.1, he.2.2 hh, hL, hY⟩

/-- Empty selected domain or a strictly positive universal pair-height bound
excludes original feasible points, whose selected-domain coverage is derived. -/
theorem source_initializer_empty {n m l r : ℕ} (d : ModelData n m l r)
    (K : Set (Point n m)) (retainAffine : Bool)
    (he : sourceInitializerDomain d K retainAffine = ∅ ∨
      ∃ rho : ℝ, 0 < rho ∧
        IsLowerBound (RestorationPairs (sourceInitializerDomain d K retainAffine) d.g)
          Prod.snd rho) : d.feasibleOn K = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpK, hpg, hpL, _⟩ := (source_feasible_iff d K p).mp hp
  have hpS : p ∈ sourceInitializerDomain d K retainAffine := by
    cases retainAffine
    · exact hpK
    · exact ⟨hpK, hpL⟩
  rcases he with he | ⟨rho, hrho, hb⟩
  · rw [he] at hpS
    exact Set.notMem_empty p hpS
  · have hempty := initializer_positive_bound_empty hb hrho
    have hmem : p ∈ {x | x ∈ sourceInitializerDomain d K retainAffine ∧
        ∀ j, d.g j x ≤ 0} := ⟨hpS, hpg⟩
    rw [hempty] at hmem
    exact Set.notMem_empty p hmem

end Chapter02

#print axioms Chapter02.source_initializer_minimum_attained
#print axioms Chapter02.source_initializer_feasible
#print axioms Chapter02.source_initializer_empty
