module

public import Chapter02CPDomain
public import Chapter02Model

@[expose] public section

/-! Source-interface adapters for the domain-relative smooth cutting-plane
increment. The continuous comparison domain K is distinct from the affine and
integer restrictions retained by ModelData.feasibleOn and ModelData.masterOn.
Origins belong to K; they need not satisfy those affine or integer restrictions.
No solver or convergence claim is made. -/

noncomputable section
namespace Chapter02

/-- Form a finite family by evaluating the specified row derivative field at
each chosen origin. Selection need not include every row. -/
def cpDomainTangentFamily {n m l k : ℕ}
    (origin : Fin k → Point n m) (selected : Fin k → Set (Fin l))
    (D : Fin l → Point n m → Point n m →L[ℝ] ℝ) : TangentFamily n m l k where
  origin := origin
  selected := selected
  derivative := fun i j => D j (origin i)

/-- Actual within-domain derivatives derive containment of the full mixed
feasible set in the selected tangent master. Affine rows and the integer
cylinder are carried unchanged; support is proved rather than assumed. -/
theorem source_cp_domain_outer {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k) (K : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ K (d.g j)) (ha : ∀ i, c.origin i ∈ K)
    (hd : ∀ i j, j ∈ c.selected i →
      HasFDerivWithinAt (d.g j) (c.derivative i j) K (c.origin i)) :
    d.feasibleOn K ⊆ d.masterOn c K := by
  rintro p ⟨⟨⟨hpK, hpg⟩, hpL⟩, hpY⟩
  refine ⟨⟨⟨hpK, ?_⟩, hpL⟩, hpY⟩
  intro i j hj
  exact cp_tangent_cut_valid_within (hg j) (ha i) hpK (hd i j hj) (hpg j)

/-- On a compact continuous domain, the specified continuous derivative fields
give scalar continuity and one nonnegative finite norm bound, while every
finite selected tangent family formed from those fields preserves the full
mixed feasible set. No nonemptiness of K, rows, or origins is required. -/
theorem source_cp_compact_domain {n m l r : ℕ} (d : ModelData n m l r)
    (K : Set (Point n m)) (D : Fin l → Point n m → Point n m →L[ℝ] ℝ)
    (hK : IsCompact K) (hg : ∀ j, ConvexOn ℝ K (d.g j))
    (hd : ∀ j z, z ∈ K → HasFDerivWithinAt (d.g j) (D j z) K z)
    (hD : ∀ j, ContinuousOn (D j) K) :
    (∀ j, ContinuousOn (d.g j) K) ∧
    ∃ M : ℝ, 0 ≤ M ∧ (∀ j z, z ∈ K → ‖D j z‖ ≤ M) ∧
      ∀ (k : ℕ) (origin : Fin k → Point n m) (selected : Fin k → Set (Fin l)),
        (∀ i, origin i ∈ K) →
          d.feasibleOn K ⊆ d.masterOn (cpDomainTangentFamily origin selected D) K := by
  refine ⟨fun j => cp_continuousOn_of_derivative_within (hd j), ?_⟩
  obtain ⟨M, hM, hbound⟩ := cp_finite_continuous_fields_bounded hK hD
  refine ⟨M, hM, hbound, ?_⟩
  intro k origin selected ha
  exact source_cp_domain_outer d (cpDomainTangentFamily origin selected D) K hg ha
    (fun i j _ => hd j (origin i) (ha i))

end Chapter02

#print axioms Chapter02.source_cp_domain_outer
#print axioms Chapter02.source_cp_compact_domain
