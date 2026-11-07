module

public import AppendixAChimeraShoreBudget

@[expose] public section

/-! Author candidate: a single row retaining every A vertex and one B
representative per left component, with omitted B vertices transferred to their
matching right branches. No four-cell construction or cap-three conclusion. -/
noncomputable section
namespace AppendixAChimeraFour
open AppendixAChimera
attribute [local instance] Classical.propDecidable

def BaseOmittedB (D : Sample) (x : Cell) : Prop :=
  x.1 = true ∧ ∃ C : Component D, x ∈ C.val ∧ x ∉ keptA D C

def baseBranch (D : Sample) : Label D → Finset Phys
  | .inl C => (keptA D C).image first
  | .inr x => if BaseOmittedB D x then {second x, first x} else {second x}

theorem keptA_shore (D : Sample) (C : Component D) {x : Cell} (hx : x ∈ C.val) :
    ∃ y ∈ keptA D C, y.1 = x.1 := by
  cases hs : x.1
  · exact ⟨x, keptA_retains_A D C hx hs, hs⟩
  · exact ⟨pick D C true, Finset.mem_insert_self _ _,
      pick_shore D C true ⟨x,hx,hs⟩⟩

theorem keptA_B_unique (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ keptA D C) (hs : x.1 = true) : x = pick D C true := by
  rcases Finset.mem_insert.mp hx with heq | ha
  · exact heq
  · have := ((mem_aShore D C x).mp ha).2
    simp_all

theorem keptA_to_pick (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ keptA D C) : x = pick D C true ∨ Hardware (first x) (first (pick D C true)) := by
  by_cases heq : x = pick D C true
  · exact Or.inl heq
  right
  have hxA : x.1 = false := by
    rcases Finset.mem_insert.mp hx with h | h
    · exact (heq h).elim
    · exact ((mem_aShore D C x).mp h).2
  have hm := component_mixed_of_distinct D C (keptA_subset D C hx) (pick_mem D C true) heq
  simp [Hardware, hxA, pick_shore D C true hm.2]

theorem keptA_eq_singleton (D : Sample) (C : Component D) (x : Cell)
    (hc : C.val = {x}) : keptA D C = {x} := by
  apply Finset.Subset.antisymm
  · simpa only [hc] using keptA_subset D C
  · have hp : pick D C true = x := by
      have h := pick_mem D C true
      rw [hc] at h
      exact Finset.mem_singleton.mp h
    rw [Finset.singleton_subset_iff, ← hp]
    exact Finset.mem_insert_self _ _

theorem base_first_mem_left (D : Sample) (C : Component D) (x : Cell) :
    first x ∈ baseBranch D (.inl C) ↔ x ∈ keptA D C := by
  simp [baseBranch]

theorem base_left_mem_shape (D : Sample) (C : Component D) (p : Phys) :
    p ∈ baseBranch D (.inl C) ↔ ∃ x ∈ keptA D C, first x = p :=
  Finset.mem_image

theorem base_second_not_mem_left (D : Sample) (C : Component D) (x : Cell) :
    second x ∉ baseBranch D (.inl C) := by
  simp [baseBranch]

theorem base_second_mem_right (D : Sample) (x : Cell) :
    second x ∈ baseBranch D (.inr x) := by
  simp only [baseBranch]
  split_ifs <;> simp

theorem base_right_mem_shape (D : Sample) (x : Cell) (p : Phys) :
    p ∈ baseBranch D (.inr x) ↔ p = second x ∨ (BaseOmittedB D x ∧ p = first x) := by
  by_cases h : BaseOmittedB D x <;> simp [baseBranch, h]

theorem base_left_singleton (D : Sample) (C : Component D) (x : Cell)
    (hc : C.val = {x}) : baseBranch D (.inl C) = {first x} := by
  simp [baseBranch, keptA_eq_singleton D C x hc]

theorem base_left_singleton_of_card_one (D : Sample) (C : Component D)
    (hc : C.val.card = 1) : ∃ x ∈ C.val, baseBranch D (.inl C) = {first x} := by
  rcases Finset.card_eq_one.mp hc with ⟨x,hx⟩
  exact ⟨x, by simp [hx], base_left_singleton D C x hx⟩

theorem base_not_omitted_of_kept (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ keptA D C) : ¬ BaseOmittedB D x := by
  rintro ⟨_,K,hK,hnot⟩
  have heq := component_eq_of_shared D C K (keptA_subset D C hx) hK
  subst K
  exact hnot hx

theorem base_right_of_kept (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ keptA D C) : baseBranch D (.inr x) = {second x} := by
  simp [baseBranch, base_not_omitted_of_kept D C hx]

theorem base_right_of_A (D : Sample) (x : Cell) (hs : x.1 = false) :
    baseBranch D (.inr x) = {second x} := by
  have hn : ¬ BaseOmittedB D x := by rintro ⟨ht,_⟩; simp_all
  simp [baseBranch,hn]

theorem base_right_pair (D : Sample) (x : Cell) :
    ∃ u v, baseBranch D (.inr x) = {u,v} ∧ (u = v ∨ Hardware u v) := by
  by_cases h : BaseOmittedB D x
  · exact ⟨second x,first x,by simp [baseBranch,h],Or.inr ⟨h.1,rfl⟩⟩
  · exact ⟨second x,second x,by simp [baseBranch,h],Or.inl rfl⟩

theorem base_left_card (D : Sample) (C : Component D) :
    (baseBranch D (.inl C)).card = (keptA D C).card := by
  apply Finset.card_image_of_injOn
  intro x _ y _ h
  exact Sum.inl.inj h

theorem base_left_card_le_four (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (C : Component D) : (baseBranch D (.inl C)).card ≤ 4 := by
  rw [base_left_card]
  exact keptA_card_le_four D hcan hF C

theorem base_right_card_le_two (D : Sample) (x : Cell) :
    (baseBranch D (.inr x)).card ≤ 2 := by
  rcases base_right_pair D x with ⟨u,v,h,_⟩
  rw [h]
  exact (Finset.card_insert_le u {v}).trans (by simp)

theorem base_branch_center (D : Sample) (j : Label D) :
    ∃ c ∈ baseBranch D j, ∀ p ∈ baseBranch D j, p = c ∨ Hardware p c := by
  cases j with
  | inl C =>
    refine ⟨first (pick D C true), (base_first_mem_left D C _).mpr (Finset.mem_insert_self _ _), ?_⟩
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x,hx,rfl⟩
    exact (keptA_to_pick D C hx).imp (congrArg first) id
  | inr x =>
    refine ⟨second x, base_second_mem_right D x, ?_⟩
    intro p hp
    rcases (base_right_mem_shape D x p).mp hp with h | ⟨ho,h⟩
    · exact Or.inl h
    · subst p
      exact Or.inr ⟨ho.1,rfl⟩

theorem base_branch_nonempty (D : Sample) (j : Label D) :
    (baseBranch D j).Nonempty := by
  rcases base_branch_center D j with ⟨c,hc,_⟩
  exact ⟨c,hc⟩

theorem base_branch_connected (D : Sample) (j : Label D) :
    ∀ u ∈ baseBranch D j, ∀ v ∈ baseBranch D j,
      Relation.ReflTransGen
        (fun a b => a ∈ baseBranch D j ∧ b ∈ baseBranch D j ∧ Hardware a b) u v := by
  rcases base_branch_center D j with ⟨c,hc,hstar⟩
  intro u hu v hv
  have huc : Relation.ReflTransGen
      (fun a b => a ∈ baseBranch D j ∧ b ∈ baseBranch D j ∧ Hardware a b) u c := by
    rcases hstar u hu with heq | h
    · subst u; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hu,hc,h⟩
  have hcv : Relation.ReflTransGen
      (fun a b => a ∈ baseBranch D j ∧ b ∈ baseBranch D j ∧ Hardware a b) c v := by
    rcases hstar v hv with heq | h
    · subst v; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hc,hv,hardware_symmetric h⟩
  exact huc.trans hcv

theorem base_left_right_disjoint (D : Sample) (C : Component D) (x : Cell) :
    Disjoint (baseBranch D (.inl C)) (baseBranch D (.inr x)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rcases Finset.mem_image.mp hp with ⟨y,hy,rfl⟩
  rcases (base_right_mem_shape D x (first y)).mp hq with hbad | ⟨ho,heq⟩
  · cases hbad
  · have hyx : y = x := Sum.inl.inj heq
    subst y
    exact base_not_omitted_of_kept D C hy ho

theorem base_branch_disjoint (D : Sample) (j l : Label D) (hne : j ≠ l) :
    Disjoint (baseBranch D j) (baseBranch D l) := by
  cases j with
  | inl C =>
    cases l with
    | inl K =>
      apply Finset.disjoint_left.mpr
      intro p hp hq
      rcases Finset.mem_image.mp hp with ⟨x,hx,rfl⟩
      rcases Finset.mem_image.mp hq with ⟨y,hy,hxy⟩
      have hyx : y = x := Sum.inl.inj hxy
      subst y
      exact hne (congrArg Sum.inl (component_eq_of_shared D C K
        (keptA_subset D C hx) (keptA_subset D K hy)))
    | inr x => exact base_left_right_disjoint D C x
  | inr x =>
    cases l with
    | inl C => exact (base_left_right_disjoint D C x).symm
    | inr y =>
      apply Finset.disjoint_left.mpr
      intro p hp hq
      have hp' := (base_right_mem_shape D x p).mp hp
      have hq' := (base_right_mem_shape D y p).mp hq
      rcases hp' with rfl | ⟨_,rfl⟩ <;> rcases hq' with heq | ⟨_,heq⟩
      · exact hne (congrArg Sum.inr (Sum.inr.inj heq))
      · cases heq
      · cases heq
      · exact hne (congrArg Sum.inr (Sum.inl.inj heq))

theorem base_omitted_mixed (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ C.val) (ho : x ∉ keptA D C) : Mixed C.val := by
  apply component_mixed_of_distinct D C hx (pick_mem D C true)
  intro heq
  apply ho
  rw [heq]
  exact Finset.mem_insert_self _ _

theorem base_cross_covered (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ C.val) (hs : x.1 = true) :
    ∃ u ∈ baseBranch D (.inl C), ∃ v ∈ baseBranch D (.inr x), Hardware u v := by
  by_cases hk : x ∈ keptA D C
  · exact ⟨first x, Finset.mem_image.mpr ⟨x,hk,rfl⟩,
      second x, base_second_mem_right D x, hs, rfl⟩
  · have hm := base_omitted_mixed D C hx hk
    have ho : BaseOmittedB D x := ⟨hs,C,hx,hk⟩
    refine ⟨first (pick D C false), ?_, first x, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨pick D C false,
        keptA_retains_A D C (pick_mem D C false) (pick_shore D C false hm.1),rfl⟩
    · exact (base_right_mem_shape D x (first x)).mpr (Or.inr ⟨ho,rfl⟩)
    · simp [Hardware,pick_shore D C false hm.1,hs]

theorem base_original_hardware_covered (D : Sample) (j l : Label D) {u v : Phys}
    (hu : u ∈ originalFiber D j) (hv : v ∈ originalFiber D l) (h : Hardware u v) :
    ∃ a ∈ baseBranch D j, ∃ b ∈ baseBranch D l, Hardware a b := by
  cases j with
  | inl C =>
    rcases Finset.mem_image.mp hu with ⟨x,hx,rfl⟩
    cases l with
    | inl K =>
      rcases Finset.mem_image.mp hv with ⟨y,hy,rfl⟩
      rcases keptA_shore D C hx with ⟨a,ha,hsa⟩
      rcases keptA_shore D K hy with ⟨b,hb,hsb⟩
      refine ⟨first a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
        first b,Finset.mem_image.mpr ⟨b,hb,rfl⟩,?_⟩
      simpa only [Hardware,hsa,hsb] using h
    | inr y =>
      have hv' : v = second y := Finset.mem_singleton.mp hv
      subst v
      rcases h with ⟨hs,rfl⟩
      exact base_cross_covered D C hx hs
  | inr x =>
    have hu' : u = second x := Finset.mem_singleton.mp hu
    subst u
    cases l with
    | inl C =>
      rcases Finset.mem_image.mp hv with ⟨y,hy,rfl⟩
      rcases h with ⟨hs,rfl⟩
      rcases base_cross_covered D C hy hs with ⟨a,ha,b,hb,hab⟩
      exact ⟨b,hb,a,ha,hardware_symmetric hab⟩
    | inr y =>
      have hv' : v = second y := Finset.mem_singleton.mp hv
      subst v
      exact ⟨second x,base_second_mem_right D x,second y,base_second_mem_right D y,h⟩

theorem base_quotient_covered (D : Sample) {j l : Label D} (h : QuotientAdj D j l) :
    ∃ a ∈ baseBranch D j, ∃ b ∈ baseBranch D l, Hardware a b := by
  rcases h.2 with ⟨u,hu,v,hv,he⟩
  exact base_original_hardware_covered D j l hu hv (sampled_hardware D he)

theorem base_left_mem_component (D : Sample) (C : Component D) {x : Cell}
    (hx : first x ∈ baseBranch D (.inl C)) : x ∈ C.val :=
  keptA_subset D C ((base_first_mem_left D C x).mp hx)

theorem base_left_B_mem_iff (D : Sample) (C : Component D) (x : Cell) (hs : x.1 = true) :
    first x ∈ baseBranch D (.inl C) ↔ x = pick D C true := by
  rw [base_first_mem_left]
  constructor
  · exact fun hx => keptA_B_unique D C hx hs
  · rintro rfl
    exact Finset.mem_insert_self _ _

theorem base_first_mem_right_iff (D : Sample) (x y : Cell) :
    first y ∈ baseBranch D (.inr x) ↔ y = x ∧ BaseOmittedB D x := by
  constructor
  · intro h
    rcases (base_right_mem_shape D x (first y)).mp h with heq | ⟨ho,heq⟩
    · cases heq
    · exact ⟨Sum.inl.inj heq,ho⟩
  · rintro ⟨heq,ho⟩
    subst y
    exact (base_right_mem_shape D x (first x)).mpr (Or.inr ⟨ho,rfl⟩)

theorem base_omitted_active (D : Sample) (x : Cell) (h : BaseOmittedB D x) : x ∈ D.U := by
  rcases h.2 with ⟨C,hx,_⟩
  exact component_mem_active D C hx

theorem base_first_A_originalLabel (D : Sample) (x : Cell) (hx : x ∈ D.U)
    (hs : x.1 = false) : first x ∈ baseBranch D (originalLabel D (first x) hx) := by
  apply (base_first_mem_left D (componentLabel D x hx) x).mpr
  apply keptA_retains_A D _ _ hs
  exact Finset.mem_filter.mpr ⟨hx,Relation.ReflTransGen.refl⟩

theorem base_second_originalLabel (D : Sample) (x : Cell) (hx : Active D.U (second x)) :
    second x ∈ baseBranch D (originalLabel D (second x) hx) :=
  base_second_mem_right D x

theorem base_original_A_retained (D : Sample) (p : Phys) (hp : Active D.U p)
    (hs : Sum.elim Prod.fst Prod.fst p = false) :
    p ∈ baseBranch D (originalLabel D p hp) := by
  cases p with
  | inl x => exact base_first_A_originalLabel D x hp hs
  | inr x => exact base_second_mem_right D x

theorem base_kept_B_adjacent (D : Sample) (C : Component D) (a : Cell)
    (ha : a ∈ C.val) (hs : a.1 = false) (hb : ∃ b ∈ C.val, b.1 = true) :
    first a ∈ baseBranch D (.inl C) ∧
      first (pick D C true) ∈ baseBranch D (.inl C) ∧
      Hardware (first a) (first (pick D C true)) := by
  refine ⟨(base_first_mem_left D C a).mpr (keptA_retains_A D C ha hs),
    (base_first_mem_left D C _).mpr (Finset.mem_insert_self _ _), ?_⟩
  simp [Hardware,hs,pick_shore D C true hb]

theorem base_left_over_three_iff (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (C : Component D) : 3 < (baseBranch D (.inl C)).card ↔ (aShore D C).card = 3 := by
  rw [base_left_card]
  exact keptA_over_three_iff D hcan hF C

theorem base_branch_card_le_four (D : Sample) (hcan : Canonical D) (hF : D.F.card ≤ 3)
    (j : Label D) : (baseBranch D j).card ≤ 4 := by
  cases j with
  | inl C => exact base_left_card_le_four D hcan hF C
  | inr x => exact (base_right_card_le_two D x).trans (by omega)

end AppendixAChimeraFour
