module

public import Chapter02AlphaSupport
public import Chapter02CPDomain
public import Mathlib.Tactic

@[expose] public section

/-! A qualified mathematical safe-scale construction. Relative continuity of
the actual operator field is explicit. The bound is uniform only above each
fixed positive row threshold, never over all positive origins at once. -/
noncomputable section
namespace Chapter02

/-- The complete original row-feasible set inside the declared compact base. -/
def alphaScaleFeasible {E J : Type*} (B : Set E) (g : J → E → ℝ) : Set E :=
  {p | p ∈ B ∧ ∀ j, g j p ≤ 0}

private theorem alpha_threshold_margin
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype J] [Nonempty J]
    (B S : Set E) (g : J → E → ℝ) (G : J → E → E →L[ℝ] ℝ)
    (hB : IsCompact B) (hS : IsCompact S) (hSB : S ⊆ B)
    (hgS : ∀ j p, p ∈ S → g j p ≤ 0)
    (hg : ∀ j, ContinuousOn (g j) B) (hG : ∀ j, ContinuousOn (G j) B)
    (hpseudo : ∀ j x, x ∈ B → ∀ y, y ∈ B →
      g j y < g j x → G j x (y-x) < 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j q, q ∈ B → ε ≤ g j q →
      ∀ p ∈ S, δ ≤ -(G j q (p-q)) := by
  classical
  have hrow : ∀ j, ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ ({q | q ∈ B ∧ ε ≤ g j q} ×ˢ S),
        δ ≤ -(G j z.1 (z.2-z.1)) := by
    intro j
    have hQ : IsCompact {q | q ∈ B ∧ ε ≤ g j q} :=
      hB.of_isClosed_subset (hB.isClosed.isClosed_le continuousOn_const (hg j))
        (fun _ hq => hq.1)
    apply (hQ.prod hS).exists_forall_le'
    · have hd : ContinuousOn (fun z : E × E => G j z.1)
          ({q | q ∈ B ∧ ε ≤ g j q} ×ˢ S) :=
        (hG j).comp continuous_fst.continuousOn (fun _ hz => hz.1.1)
      exact (hd.clm_apply
        (continuous_snd.continuousOn.sub continuous_fst.continuousOn)).neg
    · intro z hz
      apply neg_pos.mpr
      exact hpseudo j z.1 hz.1.1 z.2 (hSB hz.2)
        ((hgS j z.2 hz.2).trans_lt (hε.trans_le hz.1.2))
  choose δ hδpos hδbound using hrow
  refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun j _ => hδpos j)
  · intro j q hq hεq p hp
    exact (Finset.inf'_le δ (Finset.mem_univ j)).trans
      (hδbound j (q,p) ⟨⟨hq,hεq⟩,hp⟩)

/-- One derived safe policy, a uniform unscaled norm bound and positive-threshold
scale bounds. The row underestimates the actual row value on the full original
feasible set. The cap holds for every subsequent scale in the displayed band.
The noncomputable construction is not an operational scale or margin oracle.
Arbitrary normed bases and W02's added continuous-field premise are explicit. -/
theorem alpha_uniform_threshold_scale_control
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype J] [Nonempty J]
    (B : Set E) (g : J → E → ℝ) (G : J → E → E →L[ℝ] ℝ)
    (hB : IsCompact B) (hne : (alphaScaleFeasible B g).Nonempty)
    (hderiv : ∀ j q, q ∈ B → HasFDerivAt (g j) (G j q) q)
    (hG : ∀ j, ContinuousOn (G j) B)
    (hpseudo : ∀ j x, x ∈ B → ∀ y, y ∈ B →
      g j y < g j x → G j x (y-x) < 0) :
    ∃ (a : J → E → ℝ) (M : ℝ),
      (∀ j q, 1 ≤ a j q) ∧
      (∀ j q, q ∉ B ∨ g j q ≤ 0 → a j q = 1) ∧
      1 ≤ M ∧ (∀ j q, q ∈ B → ‖G j q‖ ≤ M) ∧
      (∀ j q, q ∈ B → 0 < g j q → ∀ α : ℝ, a j q ≤ α →
        ∀ p ∈ alphaScaleFeasible B g,
          g j q + α * G j q (p-q) ≤ g j p ∧ g j p ≤ 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧
        ∀ j q, q ∈ B → ε ≤ g j q → a j q ≤ A ∧
          ∀ ρ : ℝ, 1 ≤ ρ → ∀ α : ℝ, a j q ≤ α → α ≤ ρ * a j q →
            ‖α • G j q‖ ≤ ρ * A * M) := by
  classical
  let S := alphaScaleFeasible B g
  have hSB : S ⊆ B := fun _ hp => hp.1
  have hgS : ∀ j p, p ∈ S → g j p ≤ 0 := fun j _ hp => hp.2 j
  have hg : ∀ j, ContinuousOn (g j) B :=
    fun j q hq => (hderiv j q hq).continuousAt.continuousWithinAt
  have hS : IsCompact S := by
    have hc : IsClosed {p | ∀ j, p ∈ B ∧ g j p ≤ 0} := by
      simpa only [Set.setOf_forall] using isClosed_iInter
        (fun j => hB.isClosed.isClosed_le (hg j) continuousOn_const)
    have he : S = B ∩ {p | ∀ j, p ∈ B ∧ g j p ≤ 0} := by
      ext p
      constructor
      · intro hp; exact ⟨hp.1, fun j => ⟨hp.1, hp.2 j⟩⟩
      · rintro ⟨hp, h⟩; exact ⟨hp, fun j => (h j).2⟩
    rw [he]
    exact hB.inter_right hc
  choose C hC using fun j => hB.exists_bound_of_continuousOn (hg j)
  obtain ⟨R, hR⟩ := Finite.exists_le C
  let D : ℝ := max 1 (2*R)
  have hD : 1 ≤ D := le_max_left _ _
  have hdiff : ∀ j q, q ∈ B → ∀ p ∈ S, g j q - g j p ≤ D := by
    intro j q hq p hp
    have hq' := (hC j q hq).trans (hR j)
    have hp' := (hC j p (hSB hp)).trans (hR j)
    rw [Real.norm_eq_abs] at hq' hp'
    have hqle := (le_abs_self (g j q)).trans hq'
    have hple := (neg_le_abs (g j p)).trans hp'
    have hr : 2*R ≤ D := le_max_right _ _
    linarith
  have hex : ∀ j q, ∃ h : ℝ, (q ∈ B ∧ 0 < g j q) →
      0 < h ∧ (∃ p ∈ S, h = -(G j q (p-q))) ∧
        (∀ p ∈ S, G j q (p-q) ≤ -h) := by
    intro j q
    by_cases hq : q ∈ B ∧ 0 < g j q
    · obtain ⟨p, hp, h, hh, he, hb, _⟩ :=
        alpha_compact_support B S (g j) (G j) q (hderiv j) (hpseudo j)
          hS hne hSB (hgS j) hq.1 hq.2
      exact ⟨h, fun _ => ⟨hh, ⟨p,hp,he⟩, hb⟩⟩
    · exact ⟨1, fun hn => False.elim (hq hn)⟩
  choose h hh using hex
  let a : J → E → ℝ := fun j q =>
    if q ∈ B ∧ 0 < g j q then max 1 (D / h j q) else 1
  have ha : ∀ j q, 1 ≤ a j q := by
    intro j q
    dsimp [a]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  obtain ⟨M₀, _, hM₀⟩ := cp_finite_continuous_fields_bounded hB hG
  let M : ℝ := max 1 M₀
  have hM : 1 ≤ M := le_max_left _ _
  have hnorm : ∀ j q, q ∈ B → ‖G j q‖ ≤ M :=
    fun j q hq => (hM₀ j q hq).trans (le_max_right _ _)
  refine ⟨a, M, ha, ?_, hM, hnorm, ?_, ?_⟩
  · intro j q hq
    have hn : ¬ (q ∈ B ∧ 0 < g j q) := by
      intro hp
      rcases hq with hn | hn
      · exact hn hp.1
      · exact (not_lt_of_ge hn) hp.2
    simp only [a, if_neg hn]
  · intro j q hq hgq α hα p hp
    have hpos := (hh j q ⟨hq,hgq⟩).1
    have hbound := (hh j q ⟨hq,hgq⟩).2.2 p hp
    have hquot : D / h j q ≤ α := by
      apply (le_max_right 1 (D / h j q)).trans
      have hpositive : q ∈ B ∧ 0 < g j q := ⟨hq,hgq⟩
      simpa only [a, if_pos hpositive] using hα
    have hprod := (div_le_iff₀ hpos).mp hquot
    have hαpos : 0 ≤ α := le_trans (by norm_num) ((ha j q).trans hα)
    have hmul := mul_le_mul_of_nonneg_left hbound hαpos
    have hd := hdiff j q hq p hp
    exact ⟨by nlinarith, hgS j p hp⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ :=
      alpha_threshold_margin B S g G hB hS hSB hgS hg hG hpseudo ε hε
    let A : ℝ := max 1 (D/δ)
    refine ⟨A, le_max_left _ _, ?_⟩
    intro j q hq hεq
    have hgq : 0 < g j q := hε.trans_le hεq
    obtain ⟨p, hp, he⟩ := (hh j q ⟨hq,hgq⟩).2.1
    have hδh : δ ≤ h j q := by
      rw [he]
      exact hδbound j q hq hεq p hp
    have haA : a j q ≤ A := by
      dsimp [a, A]
      rw [if_pos ⟨hq,hgq⟩]
      exact max_le_max le_rfl
        (div_le_div_of_nonneg_left (le_trans (by norm_num) hD) hδ hδh)
    refine ⟨haA, ?_⟩
    intro ρ hρ α hα hαρ
    have hρpos : 0 ≤ ρ := le_trans (by norm_num) hρ
    have hapos : 0 ≤ a j q := le_trans (by norm_num) (ha j q)
    have hαpos : 0 ≤ α := hapos.trans hα
    have hMpos : 0 ≤ M := le_trans (by norm_num) hM
    have hsmul : ‖α • G j q‖ = α * ‖G j q‖ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hαpos] using norm_smul α (G j q)
    rw [hsmul]
    calc
      α * ‖G j q‖ ≤ (ρ * a j q) * M :=
        mul_le_mul hαρ (hnorm j q hq) (norm_nonneg _) (mul_nonneg hρpos hapos)
      _ ≤ ρ * A * M := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left haA hρpos) hMpos

#print axioms alpha_uniform_threshold_scale_control

end Chapter02
