module

public import AppendixAChimeraTwoCell

@[expose] public section

/-! Author candidate: one-row A-shore budgets only. No four-cell embedding. -/
noncomputable section
namespace AppendixAChimeraFour
open AppendixAChimera
attribute [local instance] Classical.propDecidable

def Canonical (D : Sample) : Prop :=
  ∀ e ∈ D.F, e.1.1 = false ∧ e.2.1 = true

def aShore (D : Sample) (C : Component D) : Finset Cell :=
  C.val.filter (fun x => x.1 = false)

def keptA (D : Sample) (C : Component D) : Finset Cell :=
  insert (pick D C true) (aShore D C)

theorem mem_aShore (D : Sample) (C : Component D) (x : Cell) :
    x ∈ aShore D C ↔ x ∈ C.val ∧ x.1 = false :=
  Finset.mem_filter

theorem aShore_disjoint (D : Sample) (C K : Component D) (hne : C ≠ K) :
    Disjoint (aShore D C) (aShore D K) := by
  apply Finset.disjoint_left.mpr
  intro x hx hk
  exact hne (component_eq_of_shared D C K
    ((mem_aShore D C x).mp hx).1 ((mem_aShore D K x).mp hk).1)

theorem aShore_subset_selected (D : Sample) (hcan : Canonical D)
    (C : Component D) (hm : 1 < C.val.card) :
    aShore D C ⊆ D.F.image Prod.fst := by
  intro x hx
  rcases (mem_aShore D C x).mp hx with ⟨hx, hs⟩
  rcases (component_nonsingleton_mixed D C hm).2 with ⟨y, hy, hsy⟩
  have hne : x ≠ y := by intro h; subst y; simp_all
  rcases (component_reachable D C hx hy).cases_head with h | ⟨z, hxz, _⟩
  · exact (hne h).elim
  · rcases hxz with hz | hz
    · exact Finset.mem_image.mpr ⟨(x,z), hz, rfl⟩
    · have ht := (hcan (z,x) hz).2
      simp_all

theorem aShore_card_le (D : Sample) (hcan : Canonical D) (C : Component D)
    (hm : 1 < C.val.card) : (aShore D C).card ≤ D.F.card :=
  (Finset.card_le_card (aShore_subset_selected D hcan C hm)).trans Finset.card_image_le

theorem multiA_nontrivial (D : Sample) (C : Component D)
    (h : 2 ≤ (aShore D C).card) : 1 < C.val.card := by
  have := Finset.card_le_card (Finset.filter_subset (fun x : Cell => x.1 = false) C.val)
  change (aShore D C).card ≤ C.val.card at this
  omega

theorem aShore_pair_budget (D : Sample) (hcan : Canonical D)
    (C K : Component D) (hne : C ≠ K)
    (hc : 2 ≤ (aShore D C).card) (hk : 2 ≤ (aShore D K).card) :
    (aShore D C).card + (aShore D K).card ≤ D.F.card := by
  rw [← Finset.card_union_of_disjoint (aShore_disjoint D C K hne)]
  apply (Finset.card_le_card (Finset.union_subset
    (aShore_subset_selected D hcan C (multiA_nontrivial D C hc))
    (aShore_subset_selected D hcan K (multiA_nontrivial D K hk)))).trans
  exact Finset.card_image_le

theorem multiA_unique (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (C K : Component D) (hc : 2 ≤ (aShore D C).card) (hk : 2 ≤ (aShore D K).card) :
    C = K := by
  by_contra hne
  have := aShore_pair_budget D hcan C K hne hc hk
  omega

def multiComponents (D : Sample) : Finset (Component D) :=
  Finset.univ.filter (fun C => 2 ≤ (aShore D C).card)

def multiAUnion (D : Sample) : Finset Cell :=
  (multiComponents D).biUnion (aShore D)

theorem multiAUnion_subset_selected (D : Sample) (hcan : Canonical D) :
    multiAUnion D ⊆ D.F.image Prod.fst := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨C, hC, hx⟩
  exact aShore_subset_selected D hcan C
    (multiA_nontrivial D C (Finset.mem_filter.mp hC).2) hx

theorem multiAUnion_budget (D : Sample) (hcan : Canonical D) :
    (multiAUnion D).card ≤ D.F.card :=
  (Finset.card_le_card (multiAUnion_subset_selected D hcan)).trans Finset.card_image_le

theorem multiA_sum_budget (D : Sample) (hcan : Canonical D) :
    ∑ C ∈ multiComponents D, (aShore D C).card ≤ D.F.card := by
  have hd : (↑(multiComponents D) : Set (Component D)).PairwiseDisjoint (aShore D) := by
    intro C _ K _ hne
    exact aShore_disjoint D C K hne
  rw [← Finset.card_biUnion hd]
  exact multiAUnion_budget D hcan

theorem aShore_card_le_three (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (C : Component D) : (aShore D C).card ≤ 3 := by
  by_cases h : 2 ≤ (aShore D C).card
  · exact (aShore_card_le D hcan C (multiA_nontrivial D C h)).trans hF
  · omega

theorem multiAUnion_le_two (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (hno : ∀ C : Component D, (aShore D C).card ≠ 3) : (multiAUnion D).card ≤ 2 := by
  by_cases hm : (multiComponents D).Nonempty
  · rcases hm with ⟨C, hC⟩
    have hc : 2 ≤ (aShore D C).card := (Finset.mem_filter.mp hC).2
    have hsub : multiAUnion D ⊆ aShore D C := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨K, hK, hx⟩
      have heq := multiA_unique D hcan hF K C (Finset.mem_filter.mp hK).2 hc
      simpa [heq] using hx
    have hbound := aShore_card_le_three D hcan hF C
    have hne := hno C
    have hcard := Finset.card_le_card hsub
    omega
  · have he : multiComponents D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hm
    simp [multiAUnion, he]

def multiAIndices (D : Sample) : Finset (Fin 4) := (multiAUnion D).image Prod.snd

theorem multiAIndices_le_two (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (hno : ∀ C : Component D, (aShore D C).card ≠ 3) : (multiAIndices D).card ≤ 2 :=
  Finset.card_image_le.trans (multiAUnion_le_two D hcan hF hno)

theorem keptA_card_le_four (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (C : Component D) : (keptA D C).card ≤ 4 := by
  have := Finset.card_insert_le (pick D C true) (aShore D C)
  have := aShore_card_le_three D hcan hF C
  unfold keptA
  omega

theorem keptA_card_le_two (D : Sample) (C : Component D)
    (h : (aShore D C).card ≤ 1) : (keptA D C).card ≤ 2 := by
  have := Finset.card_insert_le (pick D C true) (aShore D C)
  unfold keptA
  omega

theorem picked_B_of_multiA (D : Sample) (C : Component D)
    (h : 2 ≤ (aShore D C).card) : (pick D C true).1 = true :=
  pick_shore D C true (component_nonsingleton_mixed D C (multiA_nontrivial D C h)).2

theorem keptA_card_of_multiA (D : Sample) (C : Component D)
    (h : 2 ≤ (aShore D C).card) : (keptA D C).card = (aShore D C).card + 1 := by
  apply Finset.card_insert_of_notMem
  intro hp
  have := ((mem_aShore D C _).mp hp).2
  have := picked_B_of_multiA D C h
  simp_all

theorem keptA_over_three_iff (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (C : Component D) : 3 < (keptA D C).card ↔ (aShore D C).card = 3 := by
  constructor
  · intro h
    have := Finset.card_insert_le (pick D C true) (aShore D C)
    have := aShore_card_le_three D hcan hF C
    change 3 < (insert (pick D C true) (aShore D C)).card at h
    omega
  · intro h
    have hm : 2 ≤ (aShore D C).card := by omega
    rw [keptA_card_of_multiA D C hm, h]
    omega

theorem three_A_exhausts_selected_first (D : Sample) (hcan : Canonical D)
    (hF : D.F.card ≤ 3) (C : Component D) (hc : (aShore D C).card = 3) :
    aShore D C = D.F.image Prod.fst := by
  have hm : 2 ≤ (aShore D C).card := by omega
  apply Finset.eq_of_subset_of_card_le
    (aShore_subset_selected D hcan C (multiA_nontrivial D C hm))
  have hcard : (D.F.image Prod.fst).card ≤ D.F.card := Finset.card_image_le
  omega

theorem component_closed_selected (D : Sample) (C : Component D) {x y : Cell}
    (hx : x ∈ C.val) (hxy : Adj D.F x y) : y ∈ C.val := by
  rw [component_eq_at D C hx]
  exact Finset.mem_filter.mpr ⟨(selected_active D hxy).2, Relation.ReflTransGen.single hxy⟩

theorem three_A_all_selected_in_component (D : Sample) (hcan : Canonical D)
    (hF : D.F.card ≤ 3) (C : Component D) (hc : (aShore D C).card = 3)
    (e : Cell × Cell) (he : e ∈ D.F) : e.1 ∈ C.val ∧ e.2 ∈ C.val := by
  have hx : e.1 ∈ aShore D C := by
    rw [three_A_exhausts_selected_first D hcan hF C hc]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hxC := ((mem_aShore D C _).mp hx).1
  exact ⟨hxC, component_closed_selected D C hxC (Or.inl he)⟩

theorem three_A_other_singleton (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (C K : Component D) (hc : (aShore D C).card = 3) (hne : K ≠ C) : K.val.card = 1 := by
  have hpos : 0 < K.val.card := Finset.card_pos.mpr (component_nonempty D K)
  by_contra hn
  have hm : 1 < K.val.card := by omega
  rcases (component_nonsingleton_mixed D K hm).1 with ⟨x,hx,hs⟩
  have hxA : x ∈ aShore D K := (mem_aShore D K x).mpr ⟨hx,hs⟩
  have hi := aShore_subset_selected D hcan K hm hxA
  rw [← three_A_exhausts_selected_first D hcan hF C hc] at hi
  exact hne (component_eq_of_shared D K C hx ((mem_aShore D C x).mp hi).1)

theorem keptA_nonempty (D : Sample) (C : Component D) : (keptA D C).Nonempty :=
  ⟨pick D C true, Finset.mem_insert_self _ _⟩

theorem keptA_subset (D : Sample) (C : Component D) : keptA D C ⊆ C.val := by
  intro x hx
  rcases Finset.mem_insert.mp hx with h | h
  · subst x; exact pick_mem D C true
  · exact ((mem_aShore D C x).mp h).1

theorem keptA_retains_A (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ C.val) (hs : x.1 = false) : x ∈ keptA D C :=
  Finset.mem_insert_of_mem ((mem_aShore D C x).mpr ⟨hx,hs⟩)

theorem no_three_A_keptA_le_three (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (C : Component D) (hc : (aShore D C).card ≠ 3) : (keptA D C).card ≤ 3 := by
  have := (keptA_over_three_iff D hcan hF C).not.mpr hc
  omega

def aIndices (D : Sample) (C : Component D) : Finset (Fin 4) :=
  (aShore D C).image Prod.snd

theorem aIndices_card (D : Sample) (C : Component D) :
    (aIndices D C).card = (aShore D C).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  apply Prod.ext
  · exact ((mem_aShore D C x).mp hx).2.trans ((mem_aShore D C y).mp hy).2.symm
  · exact hxy

theorem receiver_small_of_index_outside (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ C.val) (hs : x.1 = false) (hi : x.2 ∉ multiAIndices D) :
    (keptA D C).card ≤ 2 ∧ x ∈ keptA D C := by
  have hsmall : (aShore D C).card ≤ 1 := by
    by_contra hn
    have hm : 2 ≤ (aShore D C).card := by omega
    apply hi
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, rfl⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩,
      (mem_aShore D C x).mpr ⟨hx,hs⟩⟩
  exact ⟨keptA_card_le_two D C hsmall, keptA_retains_A D C hx hs⟩

theorem exists_donor_index_outside (D E : Sample) (C : Component D)
    (hc : (aShore D C).card = 3) (hcan : Canonical E) (hF : E.F.card ≤ 3)
    (hno : ∀ K : Component E, (aShore E K).card ≠ 3) :
    ∃ x ∈ aShore D C, x.2 ∉ multiAIndices E := by
  by_contra hn
  have hsub : aIndices D C ⊆ multiAIndices E := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨x,hx,rfl⟩
    by_contra hxnot
    exact hn ⟨x,hx,hxnot⟩
  have hcard := Finset.card_le_card hsub
  rw [aIndices_card D C, hc] at hcard
  have := multiAIndices_le_two E hcan hF hno
  omega

theorem exists_small_opposite_receiver (D E : Sample) (C : Component D)
    (hc : (aShore D C).card = 3) (hcan : Canonical E) (hF : E.F.card ≤ 3)
    (hno : ∀ K : Component E, (aShore E K).card ≠ 3) (hU : E.U = Finset.univ) :
    ∃ x ∈ aShore D C, ∃ K : Component E,
      x ∈ K.val ∧ (keptA E K).card ≤ 2 ∧ x ∈ keptA E K := by
  rcases exists_donor_index_outside D E C hc hcan hF hno with ⟨x,hx,hi⟩
  have hxU : x ∈ E.U := by rw [hU]; exact Finset.mem_univ _
  let K : Component E := componentLabel E x hxU
  have hxK : x ∈ K.val := Finset.mem_filter.mpr ⟨hxU,Relation.ReflTransGen.refl⟩
  have hr := receiver_small_of_index_outside E K hxK ((mem_aShore D C x).mp hx).2 hi
  exact ⟨x,hx,K,hxK,hr⟩

end AppendixAChimeraFour

#print axioms AppendixAChimeraFour.aShore_subset_selected
#print axioms AppendixAChimeraFour.aShore_card_le
