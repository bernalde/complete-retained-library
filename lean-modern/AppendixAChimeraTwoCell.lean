module

public import AppendixAChimeraData

@[expose] public section

noncomputable section
namespace AppendixAChimera
attribute [local instance] Classical.propDecidable

theorem hardware_symmetric : Symmetric Hardware := by
  intro x y h
  cases x <;> cases y
  · exact Ne.symm h
  · exact h
  · exact h
  · exact Ne.symm h

theorem sampled_hardware (D : Sample) {u v : Phys} (h : Adj D.H u v) :
    Hardware u v := by
  rcases h with h | h
  · exact D.sampled_hardware _ h
  · exact hardware_symmetric (D.sampled_hardware _ h)

theorem selected_cross (D : Sample) {x y : Cell} (h : Adj D.F x y) : x.1 ≠ y.1 := by
  rcases h with h | h
  · exact sampled_hardware D (D.selected_sampled _ h)
  · exact Ne.symm (sampled_hardware D (D.selected_sampled _ h))

theorem selected_active (D : Sample) {x y : Cell} (h : Adj D.F x y) :
    x ∈ D.U ∧ y ∈ D.U := by
  rcases h with h | h
  · exact D.selected_active _ h
  · exact (D.selected_active _ h).symm

theorem reach_symmetric (D : Sample) : Symmetric (Relation.ReflTransGen (Adj D.F)) := by
  letI : Std.Symm (Adj D.F) := ⟨fun _ _ h => h.symm⟩
  exact Relation.ReflTransGen.stdSymm.symm

theorem component_eq_of_reach (D : Sample) {x y : Cell}
    (h : Relation.ReflTransGen (Adj D.F) x y) : component D x = component D y := by
  ext z
  simp only [component, Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨fun hz => (reach_symmetric D h).trans hz,
    fun hz => h.trans hz⟩)

theorem component_eq_at (D : Sample) (C : Component D) {x : Cell} (hx : x ∈ C.val) :
    C.val = component D x := by
  rcases C.property with ⟨r, hr, hC⟩
  rw [hC] at hx ⊢
  exact component_eq_of_reach D (Finset.mem_filter.mp hx).2

theorem component_mem_active (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ C.val) : x ∈ D.U := by
  rw [component_eq_at D C hx] at hx
  exact (Finset.mem_filter.mp hx).1

theorem component_reachable (D : Sample) (C : Component D) {x y : Cell}
    (hx : x ∈ C.val) (hy : y ∈ C.val) : Relation.ReflTransGen (Adj D.F) x y := by
  rw [component_eq_at D C hx] at hy
  exact (Finset.mem_filter.mp hy).2

theorem component_eq_of_shared (D : Sample) (C K : Component D) {x : Cell}
    (hx : x ∈ C.val) (hk : x ∈ K.val) : C = K := by
  apply Subtype.ext
  exact (component_eq_at D C hx).trans (component_eq_at D K hk).symm

def Mixed (C : Finset Cell) : Prop :=
  (∃ a ∈ C, a.1 = false) ∧ ∃ b ∈ C, b.1 = true

theorem component_mixed_of_distinct (D : Sample) (C : Component D) {x y : Cell}
    (hx : x ∈ C.val) (hy : y ∈ C.val) (hne : x ≠ y) : Mixed C.val := by
  rcases (component_reachable D C hx hy).cases_head with heq | ⟨z, hxz, _⟩
  · exact (hne heq).elim
  have hz : z ∈ C.val := by
    rw [component_eq_at D C hx]
    exact Finset.mem_filter.mpr ⟨(selected_active D hxz).2, Relation.ReflTransGen.single hxz⟩
  have hcross := selected_cross D hxz
  cases hs : x.1
  · have ht : z.1 = true := by cases ht : z.1 <;> simp_all
    exact ⟨⟨x, hx, hs⟩, ⟨z, hz, ht⟩⟩
  · have ht : z.1 = false := by cases ht : z.1 <;> simp_all
    exact ⟨⟨z, hz, ht⟩, ⟨x, hx, hs⟩⟩

theorem pick_mem (D : Sample) (C : Component D) (s : Bool) : pick D C s ∈ C.val := by
  unfold pick
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact Classical.choose_spec (component_nonempty D C)

theorem pick_shore (D : Sample) (C : Component D) (s : Bool)
    (h : ∃ x ∈ C.val, x.1 = s) : (pick D C s).1 = s := by
  simp only [pick, dif_pos h]
  exact (Classical.choose_spec h).2

theorem kept_subset (D : Sample) (C : Component D) : kept D C ⊆ C.val := by
  intro x hx
  simp only [kept, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> exact pick_mem D C _

theorem kept_shore (D : Sample) (C : Component D) {x : Cell} (hx : x ∈ C.val) :
    ∃ y ∈ kept D C, y.1 = x.1 := by
  refine ⟨pick D C x.1, ?_, pick_shore D C x.1 ⟨x, hx, rfl⟩⟩
  cases x.1 <;> simp [kept]

theorem omitted_mixed (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ C.val) (ho : x ∉ kept D C) : Mixed C.val := by
  apply component_mixed_of_distinct D C hx (pick_mem D C false)
  intro heq
  apply ho
  simp [heq, kept]

theorem branch_pair (D : Sample) (j : Label D) :
    ∃ u v, branch D j = {u, v} ∧ (u = v ∨ Hardware u v) := by
  cases j with
  | inl C =>
    refine ⟨first (pick D C false), first (pick D C true), ?_, ?_⟩
    · simp [branch, kept]
    · by_cases h : pick D C false = pick D C true
      · exact Or.inl (congrArg first h)
      · have hm := component_mixed_of_distinct D C (pick_mem D C false) (pick_mem D C true) h
        right
        simp [Hardware, pick_shore D C false hm.1, pick_shore D C true hm.2]
  | inr x =>
    by_cases h : OmittedB D x
    · exact ⟨second x, first x, by simp [branch, h], Or.inr ⟨h.1, rfl⟩⟩
    · exact ⟨second x, second x, by simp [branch, h], Or.inl rfl⟩

theorem branch_nonempty (D : Sample) (j : Label D) : (branch D j).Nonempty := by
  rcases branch_pair D j with ⟨u,v,h,_⟩
  simp [h]

theorem branch_card (D : Sample) (j : Label D) : (branch D j).card ≤ 2 := by
  rcases branch_pair D j with ⟨u,v,h,_⟩
  rw [h]
  exact (Finset.card_insert_le u {v}).trans (by simp)

theorem second_mem_branch (D : Sample) (x : Cell) : second x ∈ branch D (.inr x) := by
  simp only [branch]
  split_ifs <;> simp

theorem mem_branch_right (D : Sample) (x : Cell) (p : Phys) :
    p ∈ branch D (.inr x) ↔ p = second x ∨ (OmittedB D x ∧ p = first x) := by
  by_cases h : OmittedB D x <;> simp [branch, h]

theorem left_right_disjoint (D : Sample) (C : Component D) (x : Cell) :
    Disjoint (branch D (.inl C)) (branch D (.inr x)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rcases Finset.mem_image.mp hp with ⟨y, hy, rfl⟩
  rcases (mem_branch_right D x (first y)).mp hq with hbad | ⟨ho, heq⟩
  · cases hbad
  · have hyx : y = x := Sum.inl.inj heq
    subst y
    rcases ho.2 with ⟨K, hxK, hnot⟩
    have hCK := component_eq_of_shared D C K (kept_subset D C hy) hxK
    subst K
    exact hnot hy

theorem branch_disjoint (D : Sample) (j l : Label D) (hne : j ≠ l) :
    Disjoint (branch D j) (branch D l) := by
  cases j with
  | inl C =>
    cases l with
    | inl K =>
      apply Finset.disjoint_left.mpr
      intro p hp hq
      rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨y, hy, hxy⟩
      have hyx : y = x := Sum.inl.inj hxy
      subst y
      exact hne (congrArg Sum.inl (component_eq_of_shared D C K
        (kept_subset D C hx) (kept_subset D K hy)))
    | inr x => exact left_right_disjoint D C x
  | inr x =>
    cases l with
    | inl C => exact (left_right_disjoint D C x).symm
    | inr y =>
      apply Finset.disjoint_left.mpr
      intro p hp hq
      have hp' := (mem_branch_right D x p).mp hp
      have hq' := (mem_branch_right D y p).mp hq
      rcases hp' with rfl | ⟨_,rfl⟩ <;>
        rcases hq' with heq | ⟨_,heq⟩
      · exact hne (congrArg Sum.inr (Sum.inr.inj heq))
      · cases heq
      · cases heq
      · exact hne (congrArg Sum.inr (Sum.inl.inj heq))

theorem cross_covered (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ C.val) (hs : x.1 = true) :
    ∃ u ∈ branch D (.inl C), ∃ v ∈ branch D (.inr x), Hardware u v := by
  by_cases hk : x ∈ kept D C
  · exact ⟨first x, Finset.mem_image.mpr ⟨x,hk,rfl⟩,
      second x, second_mem_branch D x, hs, rfl⟩
  · have hm := omitted_mixed D C hx hk
    have ho : OmittedB D x := ⟨hs, C, hx, hk⟩
    refine ⟨first (pick D C false), ?_, first x, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨pick D C false, by simp [kept], rfl⟩
    · exact (mem_branch_right D x (first x)).mpr (Or.inr ⟨ho,rfl⟩)
    · simp [Hardware, pick_shore D C false hm.1, hs]

theorem original_hardware_covered (D : Sample) (j l : Label D) {u v : Phys}
    (hu : u ∈ originalFiber D j) (hv : v ∈ originalFiber D l) (h : Hardware u v) :
    ∃ a ∈ branch D j, ∃ b ∈ branch D l, Hardware a b := by
  cases j with
  | inl C =>
    rcases Finset.mem_image.mp hu with ⟨x,hx,rfl⟩
    cases l with
    | inl K =>
      rcases Finset.mem_image.mp hv with ⟨y,hy,rfl⟩
      rcases kept_shore D C hx with ⟨a,ha,hsa⟩
      rcases kept_shore D K hy with ⟨b,hb,hsb⟩
      refine ⟨first a, Finset.mem_image.mpr ⟨a,ha,rfl⟩,
        first b, Finset.mem_image.mpr ⟨b,hb,rfl⟩, ?_⟩
      simpa only [Hardware, hsa, hsb] using h
    | inr y =>
      have hv' : v = second y := Finset.mem_singleton.mp hv
      subst v
      rcases h with ⟨hs,rfl⟩
      exact cross_covered D C hx hs
  | inr x =>
    have hu' : u = second x := Finset.mem_singleton.mp hu
    subst u
    cases l with
    | inl C =>
      rcases Finset.mem_image.mp hv with ⟨y,hy,rfl⟩
      rcases h with ⟨hs,rfl⟩
      rcases cross_covered D C hy hs with ⟨a,ha,b,hb,hab⟩
      exact ⟨b,hb,a,ha,hardware_symmetric hab⟩
    | inr y =>
      have hv' : v = second y := Finset.mem_singleton.mp hv
      subst v
      exact ⟨second x,second_mem_branch D x,second y,second_mem_branch D y,h⟩

theorem quotient_covered (D : Sample) {j l : Label D} (h : QuotientAdj D j l) :
    ∃ a ∈ branch D j, ∃ b ∈ branch D l, Hardware a b := by
  rcases h.2 with ⟨u,hu,v,hv,he⟩
  exact original_hardware_covered D j l hu hv (sampled_hardware D he)

theorem component_nonsingleton_mixed (D : Sample) (C : Component D)
    (h : 1 < C.val.card) : Mixed C.val := by
  rcases Finset.one_lt_card.mp h with ⟨x,hx,y,hy,hne⟩
  exact component_mixed_of_distinct D C hx hy hne

theorem originalLabel_mem (D : Sample) (p : Phys) (hp : Active D.U p) :
    p ∈ originalFiber D (originalLabel D p hp) := by
  cases p with
  | inl x =>
    apply Finset.mem_image.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨hp, Relation.ReflTransGen.refl⟩, rfl⟩
  | inr x => simp [originalLabel, originalFiber]

theorem originalFiber_unique (D : Sample) {j l : Label D} {p : Phys}
    (hj : p ∈ originalFiber D j) (hl : p ∈ originalFiber D l) : j = l := by
  cases j with
  | inl C =>
    rcases Finset.mem_image.mp hj with ⟨x,hx,rfl⟩
    cases l with
    | inl K =>
      rcases Finset.mem_image.mp hl with ⟨y,hy,heq⟩
      have hyx : y = x := Sum.inl.inj heq
      subst y
      exact congrArg Sum.inl (component_eq_of_shared D C K hx hy)
    | inr y =>
      have hbad := Finset.mem_singleton.mp hl
      cases hbad
  | inr x =>
    have hp : p = second x := Finset.mem_singleton.mp hj
    subst p
    cases l with
    | inl K =>
      rcases Finset.mem_image.mp hl with ⟨y,_,hbad⟩
      cases hbad
    | inr y =>
      exact congrArg Sum.inr (Sum.inr.inj (Finset.mem_singleton.mp hl))

theorem originalFiber_active (D : Sample) {j : Label D} {p : Phys}
    (h : p ∈ originalFiber D j) : Active D.U p := by
  cases j with
  | inl C =>
    rcases Finset.mem_image.mp h with ⟨x,hx,rfl⟩
    exact component_mem_active D C hx
  | inr x =>
    have hp : p = second x := Finset.mem_singleton.mp h
    subst p
    trivial

theorem originalFiber_exact_preimage (D : Sample) (j : Label D) (p : Phys) :
    p ∈ originalFiber D j ↔ ∃ hp : Active D.U p, originalLabel D p hp = j := by
  constructor
  · intro h
    have hp := originalFiber_active D h
    exact ⟨hp, originalFiber_unique D (originalLabel_mem D p hp) h⟩
  · rintro ⟨hp,rfl⟩
    exact originalLabel_mem D p hp

theorem originalFiber_nonempty (D : Sample) (j : Label D) :
    (originalFiber D j).Nonempty := by
  cases j with
  | inl C =>
    rcases component_nonempty D C with ⟨x,hx⟩
    exact ⟨first x,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
  | inr x => exact ⟨second x,Finset.mem_singleton_self _⟩

theorem originalLabel_surjective (D : Sample) (j : Label D) :
    ∃ p, ∃ hp : Active D.U p, originalLabel D p hp = j := by
  rcases originalFiber_nonempty D j with ⟨p,hp⟩
  exact ⟨p,(originalFiber_exact_preimage D j p).mp hp⟩

theorem quotientAdj_irreflexive (D : Sample) (j : Label D) : ¬ QuotientAdj D j j :=
  fun h => h.1 rfl

theorem quotientAdj_symmetric (D : Sample) : Symmetric (QuotientAdj D) := by
  rintro j l ⟨hne,u,hu,v,hv,h⟩
  exact ⟨hne.symm,v,hv,u,hu,h.symm⟩

end AppendixAChimera

#print axioms AppendixAChimera.hardware_symmetric
#print axioms AppendixAChimera.sampled_hardware
#print axioms AppendixAChimera.selected_cross
#print axioms AppendixAChimera.selected_active
#print axioms AppendixAChimera.reach_symmetric
#print axioms AppendixAChimera.component_eq_of_reach
#print axioms AppendixAChimera.component_eq_at
#print axioms AppendixAChimera.component_mem_active
#print axioms AppendixAChimera.component_reachable
#print axioms AppendixAChimera.component_eq_of_shared
#print axioms AppendixAChimera.component_mixed_of_distinct
#print axioms AppendixAChimera.pick_mem
#print axioms AppendixAChimera.pick_shore
#print axioms AppendixAChimera.kept_subset
#print axioms AppendixAChimera.kept_shore
#print axioms AppendixAChimera.omitted_mixed
#print axioms AppendixAChimera.branch_pair
#print axioms AppendixAChimera.branch_nonempty
#print axioms AppendixAChimera.branch_card
#print axioms AppendixAChimera.second_mem_branch
#print axioms AppendixAChimera.mem_branch_right
#print axioms AppendixAChimera.left_right_disjoint
#print axioms AppendixAChimera.branch_disjoint
#print axioms AppendixAChimera.cross_covered
#print axioms AppendixAChimera.original_hardware_covered
#print axioms AppendixAChimera.quotient_covered
#print axioms AppendixAChimera.component_nonsingleton_mixed
#print axioms AppendixAChimera.originalLabel_mem
#print axioms AppendixAChimera.originalFiber_unique
#print axioms AppendixAChimera.originalFiber_active
#print axioms AppendixAChimera.originalFiber_exact_preimage
#print axioms AppendixAChimera.originalFiber_nonempty
#print axioms AppendixAChimera.originalLabel_surjective
#print axioms AppendixAChimera.quotientAdj_irreflexive
#print axioms AppendixAChimera.quotientAdj_symmetric
