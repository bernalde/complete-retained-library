module

public import Chapter03FPModel
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! Proof-only finite lattice sets. These are not restrictions on any master. -/
noncomputable section
open Chapter02
namespace Chapter03.FPUnbounded

def proofLatticeBox (m : ℕ) (R : ℝ) : Finset (IntVector m) :=
  (integerBox_finite (fun _ => -R) (fun _ => R)).toFinset

theorem mem_proofLatticeBox {m : ℕ} {R : ℝ} {q : IntVector m} :
    q ∈ proofLatticeBox m R ↔ ∀ j, -R ≤ (q j : ℝ) ∧ (q j : ℝ) ≤ R := by
  simp [proofLatticeBox, IntegerBox]

theorem intY_norm_mem_proofLatticeBox {m : ℕ} {R : ℝ} {q : IntVector m}
    (hq : ‖FP.intY q‖ ≤ R) : q ∈ proofLatticeBox m R := by
  apply mem_proofLatticeBox.mpr
  intro j
  have hj := (PiLp.norm_apply_le (FP.intY q) j).trans hq
  have hj' : |(q j : ℝ)| ≤ R := by simpa [FP.intY, FP.intCast] using hj
  exact abs_le.mp hj'

theorem norm_bounded_integer_set_finite (m : ℕ) (R : ℝ) :
    {q : IntVector m | ‖FP.intY q‖ ≤ R}.Finite :=
  (proofLatticeBox m R).finite_toSet.subset (fun _ hq => intY_norm_mem_proofLatticeBox hq)

theorem integer_prefix_card_bound {m k : ℕ} {R : ℝ}
    (q : Fin k → IntVector m) (hnorm : ∀ i, ‖FP.intY (q i)‖ ≤ R)
    (hinj : Function.Injective q) : k ≤ (proofLatticeBox m R).card := by
  classical
  let f : Fin k → ↥(proofLatticeBox m R) := fun i =>
    ⟨q i, intY_norm_mem_proofLatticeBox (hnorm i)⟩
  have hf : Function.Injective f := by
    intro i j he
    exact hinj (congrArg Subtype.val he)
  simpa using Fintype.card_le_of_injective f hf

theorem integer_subset_card_bound {m k : ℕ} {R : ℝ}
    (T : Finset (Fin k)) (q : Fin k → IntVector m)
    (hnorm : ∀ i ∈ T, ‖FP.intY (q i)‖ ≤ R)
    (hinj : Set.InjOn q (T : Set (Fin k))) : T.card ≤ (proofLatticeBox m R).card := by
  classical
  let f : ↥T → ↥(proofLatticeBox m R) := fun i =>
    ⟨q i, intY_norm_mem_proofLatticeBox (hnorm i i.property)⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    exact hinj i.property j.property (congrArg Subtype.val he)
  simpa using Fintype.card_le_of_injective f hf

theorem compact_projected_radius {n m : ℕ} {C : Set (Point n m)}
    (hC : IsCompact C) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p ∈ C, ‖Chapter03.yMap n m p‖ ≤ R := by
  have hy : Continuous (Chapter03.yMap n m) :=
    (Chapter03.yMap n m).continuous_of_finiteDimensional
  obtain ⟨r, _, hr⟩ := (hC.image hy).isBounded.exists_pos_norm_le
  refine ⟨max r 1, le_max_right _ _, ?_⟩
  intro p hp
  exact (hr _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)

theorem compact_integer_projection_finite {n m : ℕ} {C : Set (Point n m)}
    (hC : IsCompact C) :
    {q : IntVector m | ∃ p ∈ C, p.2 = FP.intCast q}.Finite := by
  obtain ⟨R, _, hR⟩ := compact_projected_radius hC
  apply (norm_bounded_integer_set_finite m R).subset
  rintro q ⟨p, hp, he⟩
  have h := hR p hp
  have hy : Chapter03.yMap n m p = FP.intY q := by
    change (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm p.2 = _
    rw [he]
    rfl
  simpa [hy] using h

end Chapter03.FPUnbounded
