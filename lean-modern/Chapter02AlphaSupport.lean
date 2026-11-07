module

public import Chapter02

@[expose] public section

/-! A per-anchor compact support contract for the complete alpha cut. -/
noncomputable section
namespace Chapter02

/-- The attained support margin in Westerlund–Pörn 2002, Eqs. 14–16 and 20–22,
with an exact criterion for every real scale. Arbitrary normed E and U are a
formal enlargement. The proof consumes only the q-anchored strict implication
on S, together with continuity/linearity of G q. The ambient derivative and
all-pairs hypotheses scope G as the actual derivative of g, not a freely
supplied valid normal. No common margin or scale across anchors is asserted. -/
theorem alpha_compact_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U S : Set E) (g : E → ℝ) (G : E → E →L[ℝ] ℝ) (q : E)
    (_hderiv : ∀ x ∈ U, HasFDerivAt g (G x) x)
    (hpseudo : ∀ x ∈ U, ∀ y ∈ U, g y < g x → G x (y - x) < 0)
    (hS : IsCompact S) (hne : S.Nonempty) (hSU : S ⊆ U)
    (hgS : ∀ p ∈ S, g p ≤ 0) (hqU : q ∈ U) (hgq : 0 < g q) :
    ∃ pstar ∈ S, ∃ h : ℝ, 0 < h ∧
      h = -(G q (pstar - q)) ∧
      (∀ p ∈ S, G q (p - q) ≤ -h) ∧
      G q ≠ 0 ∧
      (∀ α : ℝ, (∀ p ∈ S, g q + α * G q (p - q) ≤ 0) ↔ g q / h ≤ α) ∧
      (∀ α : ℝ, max 1 (g q / h) ≤ α →
        ∀ p ∈ S, g q + α * G q (p - q) ≤ 0) ∧
      (∀ α : ℝ, 0 < g q + α * G q (q - q)) := by
  have hcont : ContinuousOn (fun p => G q (p - q)) S :=
    ((G q).continuous.comp (continuous_id.sub continuous_const)).continuousOn
  obtain ⟨pstar, hpstar, hmax⟩ := hS.exists_isMaxOn hne hcont
  have hneg : G q (pstar - q) < 0 :=
    hpseudo q hqU pstar (hSU hpstar) ((hgS pstar hpstar).trans_lt hgq)
  let h : ℝ := -(G q (pstar - q))
  have hh : 0 < h := neg_pos.mpr hneg
  have hbound : ∀ p ∈ S, G q (p - q) ≤ -h := by
    intro p hp
    simpa only [h, neg_neg, Set.mem_setOf_eq] using hmax hp
  have hnonzero : G q ≠ 0 := by
    intro hz
    simp only [hz, ContinuousLinearMap.zero_apply] at hneg
    exact (lt_irrefl 0) hneg
  have hiff : ∀ α : ℝ,
      (∀ p ∈ S, g q + α * G q (p - q) ≤ 0) ↔ g q / h ≤ α := by
    intro α
    constructor
    · intro hcut
      apply (div_le_iff₀ hh).2
      have hp := hcut pstar hpstar
      dsimp [h] at *
      nlinarith
    · intro hα
      have hαpos : 0 < α := (div_pos hgq hh).trans_le hα
      have hprod : g q ≤ α * h := (div_le_iff₀ hh).1 hα
      intro p hp
      have hmul := mul_le_mul_of_nonneg_left (hbound p hp) hαpos.le
      nlinarith
  refine ⟨pstar, hpstar, h, hh, rfl, hbound, hnonzero, hiff, ?_, ?_⟩
  · intro α hα
    exact (hiff α).2 ((le_max_right 1 (g q / h)).trans hα)
  · intro α
    simpa only [sub_self, map_zero, mul_zero, add_zero] using hgq

#print axioms alpha_compact_support

end Chapter02
