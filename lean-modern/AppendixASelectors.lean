module

public import AppendixAPaths

@[expose] public section

/-! Literal real gamma rows with an explicit vertex-bounded ambient-path guard.
Gamma selects a contained path; it is not the product of interior membership. -/
open scoped BigOperators
namespace AppendixAPaths

def selected {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : ℝ := if v ∈ S then 1 else 0

abbrev Gamma (n : ℕ) := Fin n → Fin n → NodupVertices n → Bool

def gammaMass {n : ℕ} (E : Finset (Fin n × Fin n)) (k : ℕ)
    (a b : Fin n) (g : Gamma n) : ℝ :=
  ∑ p ∈ catalogue E k a b, Chapter10.bit (g a b p)

def GammaRows {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (k : ℕ) (g : Gamma n) : Prop :=
  ∀ a b p, p ∈ catalogue E k a b →
    (∀ v ∈ interior a b p, Chapter10.bit (g a b p) ≤ selected S v) ∧
    1 - ((k : ℝ) - 1) + (∑ v ∈ interior a b p, selected S v) ≤ Chapter10.bit (g a b p)

def StaticPairRows {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (k : ℕ) (g : Gamma n) : Prop :=
  ∀ a b, a ≠ b →
    (¬ (catalogue E k a b).Nonempty → selected S a + selected S b ≤ 1) ∧
    (a ∈ S → b ∈ S → selected S a + selected S b + (gammaMass E k a b g - 1) ≤ 2) ∧
    ((catalogue E k a b).Nonempty → ¬ AppendixA.adjacent E a b →
      selected S a + selected S b - gammaMass E k a b g ≤ 1)

def SelectorRows {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (k : ℕ) (g : Gamma n) : Prop := GammaRows E S k g ∧ StaticPairRows E S k g

theorem selected_nonneg {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : 0 ≤ selected S v := by
  simp only [selected]; split <;> norm_num

theorem selected_le_one {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : selected S v ≤ 1 := by
  simp only [selected]; split <;> norm_num

theorem bit_nonneg (b : Bool) : 0 ≤ Chapter10.bit b := by cases b <;> norm_num [Chapter10.bit]

theorem gammaMass_nonneg {n : ℕ} (E : Finset (Fin n × Fin n)) (k : ℕ)
    (a b : Fin n) (g : Gamma n) : 0 ≤ gammaMass E k a b g := by
  exact Finset.sum_nonneg (fun p hp => bit_nonneg (g a b p))

theorem literal_lower_redundant {n : ℕ} {E : Finset (Fin n × Fin n)}
    (S : Finset (Fin n)) {k : ℕ} {a b : Fin n} {p : NodupVertices n}
    (hp : p ∈ catalogue E k a b) :
    1 - ((k : ℝ) - 1) + (∑ v ∈ interior a b p, selected S v) ≤ 0 := by
  have hs : (∑ v ∈ interior a b p, selected S v) ≤ ((interior a b p).card : ℝ) := by
    calc
      _ ≤ ∑ _v ∈ interior a b p, (1 : ℝ) := Finset.sum_le_sum (fun v _ => selected_le_one S v)
      _ = _ := by simp
  have hc : ((interior a b p).card : ℝ) + 2 ≤ (k : ℝ) := by
    exact_mod_cast interior_card_add_two_le hp
  linarith

theorem static_rows_selected_pair {n : ℕ} {E : Finset (Fin n × Fin n)}
    {S : Finset (Fin n)} {k : ℕ} {g : Gamma n} (h : StaticPairRows E S k g)
    {a b : Fin n} (hne : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) :
    (catalogue E k a b).Nonempty ∧ gammaMass E k a b g ≤ 1 ∧
      (¬ AppendixA.adjacent E a b → 1 ≤ gammaMass E k a b g) := by
  obtain ⟨hn,hu,hl⟩ := h a b hne
  have ha' : selected S a = 1 := by simp [selected,ha]
  have hb' : selected S b = 1 := by simp [selected,hb]
  have hp : (catalogue E k a b).Nonempty := by
    by_contra hh
    have hh' := hn hh
    rw [ha',hb'] at hh'
    linarith
  refine ⟨hp,?_,?_⟩
  · have hh := hu ha hb; rw [ha',hb'] at hh; linarith
  · intro hnab
    have hh := hl hp hnab; rw [ha',hb'] at hh; linarith

theorem static_rows_of_selected_pairs {n : ℕ} {E : Finset (Fin n × Fin n)}
    {S : Finset (Fin n)} {k : ℕ} {g : Gamma n}
    (h : ∀ a b, a ≠ b → a ∈ S → b ∈ S →
      (catalogue E k a b).Nonempty ∧ gammaMass E k a b g ≤ 1 ∧
        (¬ AppendixA.adjacent E a b → 1 ≤ gammaMass E k a b g)) :
    StaticPairRows E S k g := by
  intro a b hne
  have hq := gammaMass_nonneg E k a b g
  constructor
  · intro hn
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · exact False.elim (hn (h a b hne ha hb).1)
    all_goals simp [selected,ha,hb]
  · constructor
    · intro ha hb
      have hh := (h a b hne ha hb).2.1
      simp only [selected,if_pos ha,if_pos hb]
      linarith
    · intro hp hnab
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
      · have hh := (h a b hne ha hb).2.2 hnab
        simp only [selected,if_pos ha,if_pos hb]
        linarith
      all_goals simp only [selected,ha,hb,↓reduceIte]; linarith

theorem active_path_contained {n : ℕ} {E : Finset (Fin n × Fin n)}
    {S : Finset (Fin n)} {k : ℕ} {g : Gamma n} (hg : GammaRows E S k g)
    {a b : Fin n} {p : NodupVertices n} (hp : p ∈ catalogue E k a b)
    (ha : a ∈ S) (hb : b ∈ S) (hactive : g a b p = true) : Contains S p := by
  apply (contains_iff_interior hp S).mpr
  refine ⟨ha,hb,?_⟩
  intro v hv
  by_contra hn
  have hh := (hg a b p hp).1 v hv
  simp [Chapter10.bit,hactive,selected,hn] at hh
  norm_num at hh

theorem positive_mass_active_path {n : ℕ} {E : Finset (Fin n × Fin n)}
    {k : ℕ} {a b : Fin n} {g : Gamma n} (h : 0 < gammaMass E k a b g) :
    ∃ p ∈ catalogue E k a b, g a b p = true := by
  by_contra hn
  have hz : gammaMass E k a b g = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hh : g a b p = false := by
      cases he : g a b p
      · rfl
      · exact False.elim (hn ⟨p,hp,he⟩)
    simp [Chapter10.bit,hh]
  linarith

theorem selector_rows_connected {n : ℕ} {E : Finset (Fin n × Fin n)}
    {S : Finset (Fin n)} {k : ℕ} {g : Gamma n} (h : SelectorRows E S k g) :
    AppendixA.connected E S := by
  intro a ha b hb
  by_cases he : a = b
  · subst b; exact .refl
  by_cases hab : AppendixA.adjacent E a b
  · exact Relation.ReflTransGen.single ⟨ha,hb,hab⟩
  have hm := (static_rows_selected_pair h.2 he ha hb).2.2 hab
  obtain ⟨p,hp,hactive⟩ := positive_mass_active_path (by linarith : 0 < gammaMass E k a b g)
  exact catalogue_path_sound hp (active_path_contained h.1 hp ha hb hactive)

noncomputable def chosenGamma {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) : Gamma n := fun a b p =>
  if h : ∃ q ∈ catalogue E k a b, Contains S q then decide (p = Classical.choose h) else false

theorem chosenGamma_active {n : ℕ} {E : Finset (Fin n × Fin n)}
    {S : Finset (Fin n)} {k : ℕ} {a b : Fin n} {p : NodupVertices n}
    (hactive : chosenGamma E S k a b p = true) :
    p ∈ catalogue E k a b ∧ Contains S p := by
  classical
  unfold chosenGamma at hactive
  split at hactive
  next h =>
    have he : p = Classical.choose h := of_decide_eq_true hactive
    simpa [he] using Classical.choose_spec h
  next h => simp at hactive

theorem chosenGamma_mass_of_witness {n : ℕ} {E : Finset (Fin n × Fin n)}
    {S : Finset (Fin n)} {k : ℕ} {a b : Fin n}
    (h : ∃ p ∈ catalogue E k a b, Contains S p) :
    gammaMass E k a b (chosenGamma E S k) = 1 := by
  classical
  have hp := (Classical.choose_spec h).1
  simp only [gammaMass,chosenGamma,dif_pos h,Chapter10.bit,decide_eq_true_eq]
  simp only [Finset.sum_ite_eq',hp,if_true]

theorem chosenGamma_mass_le_one {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) (a b : Fin n) :
    gammaMass E k a b (chosenGamma E S k) ≤ 1 := by
  classical
  by_cases h : ∃ p ∈ catalogue E k a b, Contains S p
  · rw [chosenGamma_mass_of_witness h]
  · simp only [gammaMass,chosenGamma,dif_neg h,Chapter10.bit]
    norm_num

theorem chosenGamma_rows {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) : GammaRows E S k (chosenGamma E S k) := by
  intro a b p hp
  constructor
  · intro v hv
    cases he : chosenGamma E S k a b p
    · simpa [Chapter10.bit,he] using selected_nonneg S v
    · have hc := (chosenGamma_active he).2
      have hm := ((contains_iff_interior hp S).mp hc).2.2 v hv
      simp [Chapter10.bit,he,selected,hm]
  · exact (literal_lower_redundant S hp).trans (bit_nonneg _)

theorem connected_selector_rows {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) (hcard : S.card ≤ k) (h : AppendixA.connected E S) :
    SelectorRows E S k (chosenGamma E S k) := by
  refine ⟨chosenGamma_rows E S k,static_rows_of_selected_pairs ?_⟩
  intro a b hne ha hb
  have hw := bounded_path_complete E S k hcard h ha hb hne
  have hm := chosenGamma_mass_of_witness hw
  exact ⟨⟨hw.choose,(hw.choose_spec).1⟩,by rw [hm],fun _ => by rw [hm]⟩

theorem selector_exists_iff_connected {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) (hcard : S.card ≤ k) :
    (∃ g, SelectorRows E S k g) ↔ AppendixA.connected E S := by
  constructor
  · rintro ⟨g,hg⟩; exact selector_rows_connected hg
  · intro h; exact ⟨chosenGamma E S k,connected_selector_rows E S k hcard h⟩

theorem static_rows_iff_selected_pairs {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) (g : Gamma n) :
    StaticPairRows E S k g ↔
      ∀ a b, a ≠ b → a ∈ S → b ∈ S →
        (catalogue E k a b).Nonempty ∧ gammaMass E k a b g ≤ 1 ∧
          (¬ AppendixA.adjacent E a b → 1 ≤ gammaMass E k a b g) := by
  exact ⟨fun h _ _ hne ha hb => static_rows_selected_pair h hne ha hb,
    static_rows_of_selected_pairs⟩

theorem nonadjacent_selected_exactly_one {n : ℕ} {E : Finset (Fin n × Fin n)}
    {S : Finset (Fin n)} {k : ℕ} {g : Gamma n} (h : StaticPairRows E S k g)
    {a b : Fin n} (hne : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hnab : ¬ AppendixA.adjacent E a b) : gammaMass E k a b g = 1 := by
  have hh := static_rows_selected_pair h hne ha hb
  exact le_antisymm hh.2.1 (hh.2.2 hnab)

theorem two_active_mass {n : ℕ} {E : Finset (Fin n × Fin n)} {k : ℕ}
    {a b : Fin n} {g : Gamma n} {p q : NodupVertices n}
    (hp : p ∈ catalogue E k a b) (hq : q ∈ catalogue E k a b) (hne : p ≠ q)
    (hgp : g a b p = true) (hgq : g a b q = true) : 2 ≤ gammaMass E k a b g := by
  have hs : ({p,q} : Finset (NodupVertices n)) ⊆ catalogue E k a b := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun r _ _ => bit_nonneg (g a b r))
  calc
    (2 : ℝ) = ∑ r ∈ ({p,q} : Finset (NodupVertices n)), Chapter10.bit (g a b r) := by
      rw [Finset.sum_pair hne,hgp,hgq]
      norm_num [Chapter10.bit]
    _ ≤ gammaMass E k a b g := hh

def LiteralUpperRows {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (k : ℕ) (g : Gamma n) : Prop := ∀ a b, a ≠ b →
  selected S a + selected S b + (gammaMass E k a b g - 1) ≤ 2

def FullSelectorRows {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (k : ℕ) (g : Gamma n) : Prop := SelectorRows E S k g ∧ LiteralUpperRows E S k g

theorem chosenGamma_literal_upper {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) : LiteralUpperRows E S k (chosenGamma E S k) := by
  intro a b hne
  have ha := selected_le_one S a
  have hb := selected_le_one S b
  have hq := chosenGamma_mass_le_one E S k a b
  linarith

theorem chosenGamma_full_rows {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) (hcard : S.card ≤ k) (h : AppendixA.connected E S) :
    FullSelectorRows E S k (chosenGamma E S k) :=
  ⟨connected_selector_rows E S k hcard h,chosenGamma_literal_upper E S k⟩

theorem full_selector_exists_iff_connected {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) (hcard : S.card ≤ k) :
    (∃ g, FullSelectorRows E S k g) ↔ AppendixA.connected E S := by
  constructor
  · rintro ⟨g,hg⟩; exact selector_rows_connected hg.1
  · intro h; exact ⟨chosenGamma E S k,chosenGamma_full_rows E S k hcard h⟩

end AppendixAPaths
