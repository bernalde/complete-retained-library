module

public import AppendixAChimeraPlacements

@[expose] public section

/-! Opposite diagonal contraction cells. One representative of each occupied
shore stays in a donor; omitted B vertices move horizontally and omitted A
vertices vertically to their unique untouched matching receiver. -/
noncomputable section
namespace AppendixAChimeraConstruction
open AppendixAChimera AppendixAChimeraFour
attribute [local instance] Classical.propDecidable

def swapCell : Phys → Phys
  | .inl x => .inr x
  | .inr x => .inl x

@[simp] theorem swapCell_twice (p : Phys) : swapCell (swapCell p) = p := by
  cases p <;> rfl

def orient (r : Bool) (p : Phys) : Phys := if r then swapCell p else p

@[simp] theorem orient_twice (r : Bool) (p : Phys) : orient r (orient r p) = p := by
  cases r <;> simp [orient]

theorem orient_injective (r : Bool) : Function.Injective (orient r) :=
  Function.LeftInverse.injective (orient_twice r)

theorem orient_hardware (r : Bool) (p q : Phys) :
    Hardware (orient r p) (orient r q) ↔ Hardware p q := by
  cases r <;> cases p <;> cases q <;> simp [orient,swapCell,Hardware] <;> aesop

def diagLift (r : Bool) (p : Phys) : Phys4 := (r,orient r p)

theorem diagLift_injective (r : Bool) : Function.Injective (diagLift r) := by
  intro p q h
  exact orient_injective r (congrArg Prod.snd h)

theorem diagLift_row {r s : Bool} {p q : Phys}
    (h : diagLift r p = diagLift s q) : r = s := congrArg Prod.fst h

@[simp] theorem diagLift_eq_iff (r s : Bool) (p q : Phys) :
    diagLift r p = diagLift s q ↔ r = s ∧ p = q := by
  constructor
  · intro h
    have hr := diagLift_row h
    subst s
    exact ⟨rfl,diagLift_injective r h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem diagLift_hardware (r : Bool) (p q : Phys) :
    Hardware4 (diagLift r p) (diagLift r q) ↔ Hardware p q := by
  simp only [diagLift, hardware4_same_row_iff, orient_hardware]

theorem diagLift_vertical (r : Bool) (x : Cell) (hs : x.1 = false) :
    Hardware4 (diagLift r (second x)) (diagLift (!r) (first x)) := by
  cases r <;> simp [diagLift,orient,swapCell,Hardware4,OnA,hs]

theorem diagLift_cross {r s : Bool} (hrs : r ≠ s) (p q : Phys) :
    Hardware4 (diagLift r p) (diagLift s q) ↔
      ∃ x : Cell, x.1 = false ∧
        ((p = first x ∧ q = second x) ∨ (p = second x ∧ q = first x)) := by
  cases r <;> cases s <;> cases p <;> cases q <;>
    simp_all [diagLift,orient,swapCell,Hardware4,OnA,first,second] <;> aesop

def OmittedA (D : Sample) (x : Cell) : Prop :=
  x.1 = false ∧ ∃ C : Component D, x ∈ C.val ∧ x ∉ kept D C

abbrev DiagLabel (D : Bool → Sample) := (r : Bool) × Label (D r)

def diagBranch (D : Bool → Sample) (j : DiagLabel D) : Finset Phys4 :=
  match j.2 with
  | .inl C => (kept (D j.1) C).image (fun x => diagLift j.1 (first x))
  | .inr x => {diagLift j.1 (second x)} ∪
      (if OmittedB (D j.1) x then {diagLift j.1 (first x)} else ∅) ∪
      (if OmittedA (D (!j.1)) x then {diagLift (!j.1) (first x)} else ∅)

theorem diagBranch_left_mem (D : Bool → Sample) (r : Bool)
    (C : Component (D r)) (p : Phys4) :
    p ∈ diagBranch D ⟨r,.inl C⟩ ↔ ∃ x ∈ kept (D r) C, diagLift r (first x) = p := by
  exact Finset.mem_image

theorem diagBranch_right_mem (D : Bool → Sample) (r : Bool) (x : Cell) (p : Phys4) :
    p ∈ diagBranch D ⟨r,.inr x⟩ ↔
      p = diagLift r (second x) ∨
      (OmittedB (D r) x ∧ p = diagLift r (first x)) ∨
      (OmittedA (D (!r)) x ∧ p = diagLift (!r) (first x)) := by
  by_cases hb : OmittedB (D r) x <;> by_cases ha : OmittedA (D (!r)) x <;>
    simp [diagBranch,hb,ha,or_assoc]

theorem diagBranch_second_mem (D : Bool → Sample) (r : Bool) (x : Cell) :
    diagLift r (second x) ∈ diagBranch D ⟨r,.inr x⟩ :=
  (diagBranch_right_mem D r x _).mpr (Or.inl rfl)

theorem diagBranch_base_subset (D : Bool → Sample) (r : Bool) (j : Label (D r))
    {p : Phys} (hp : p ∈ branch (D r) j) : diagLift r p ∈ diagBranch D ⟨r,j⟩ := by
  cases j with
  | inl C =>
    rcases Finset.mem_image.mp hp with ⟨x,hx,rfl⟩
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  | inr x =>
    rcases (mem_branch_right (D r) x p).mp hp with rfl | ⟨ho,rfl⟩
    · exact diagBranch_second_mem D r x
    · exact (diagBranch_right_mem D r x _).mpr (Or.inr (Or.inl ⟨ho,rfl⟩))

theorem diagBranch_pair (D : Bool → Sample) (j : DiagLabel D) :
    ∃ u v, diagBranch D j = {u,v} ∧ (u = v ∨ Hardware4 u v) := by
  rcases j with ⟨r,C|x⟩
  · rcases branch_pair (D r) (.inl C) with ⟨u,v,h,hc⟩
    refine ⟨diagLift r u,diagLift r v,?_,hc.imp (congrArg (diagLift r))
      ((diagLift_hardware r u v).mpr)⟩
    have he : diagBranch D ⟨r,.inl C⟩ = (branch (D r) (.inl C)).image (diagLift r) := by
      simp [diagBranch,branch,Finset.image_image,Function.comp_def]
    rw [he,h]
    simp
  · by_cases hb : OmittedB (D r) x
    · have ha : ¬ OmittedA (D (!r)) x := by intro ha; simp_all [OmittedA,OmittedB]
      refine ⟨diagLift r (second x),diagLift r (first x),?_,Or.inr ?_⟩
      · ext z; simp [diagBranch,hb,ha]
      · exact (diagLift_hardware r _ _).mpr ⟨hb.1,rfl⟩
    · by_cases ha : OmittedA (D (!r)) x
      · exact ⟨diagLift r (second x),diagLift (!r) (first x),
          by ext z; simp [diagBranch,hb,ha],Or.inr (diagLift_vertical r x ha.1)⟩
      · exact ⟨diagLift r (second x),diagLift r (second x),
          by ext z; simp [diagBranch,hb,ha],Or.inl rfl⟩

theorem diagBranch_nonempty (D : Bool → Sample) (j : DiagLabel D) :
    (diagBranch D j).Nonempty := by
  rcases diagBranch_pair D j with ⟨u,v,h,_⟩
  simp [h]

theorem diagBranch_card (D : Bool → Sample) (j : DiagLabel D) :
    (diagBranch D j).card ≤ 2 := by
  rcases diagBranch_pair D j with ⟨u,v,h,_⟩
  rw [h]
  exact (Finset.card_insert_le u {v}).trans (by simp)

theorem diagBranch_connected (D : Bool → Sample) (j : DiagLabel D) :
    ∀ a ∈ diagBranch D j, ∀ b ∈ diagBranch D j,
      Relation.ReflTransGen
        (fun u v => u ∈ diagBranch D j ∧ v ∈ diagBranch D j ∧ Hardware4 u v) a b := by
  rcases diagBranch_pair D j with ⟨u,v,h,hc⟩
  rw [h]
  intro a ha b hb
  rcases hc with rfl | hc
  · simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self u),Finset.mem_singleton] at ha hb
    subst a; subst b
    exact Relation.ReflTransGen.refl
  · simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by simp,by simp,hc⟩
    · exact Relation.ReflTransGen.single ⟨by simp,by simp,hardware4_symmetric hc⟩
    · exact Relation.ReflTransGen.refl

theorem kept_not_omitted (D : Sample) (C : Component D) {x : Cell}
    (hx : x ∈ kept D C) : ¬ ∃ K : Component D, x ∈ K.val ∧ x ∉ kept D K := by
  rintro ⟨K,hk,ho⟩
  have he := component_eq_of_shared D C K (kept_subset D C hx) hk
  subst K
  exact ho hx

theorem diag_left_right_disjoint (D : Bool → Sample) (r s : Bool)
    (C : Component (D r)) (x : Cell) :
    Disjoint (diagBranch D ⟨r,.inl C⟩) (diagBranch D ⟨s,.inr x⟩) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rcases (diagBranch_left_mem D r C p).mp hp with ⟨y,hy,rfl⟩
  rcases (diagBranch_right_mem D s x _).mp hq with h | ⟨ho,h⟩ | ⟨ho,h⟩
  · simp only [diagLift_eq_iff,Sum.inl_ne_inr,and_false] at h
  · rcases (diagLift_eq_iff _ _ _ _).mp h with ⟨hrs,hxy⟩
    have hyx := Sum.inl.inj hxy
    subst s; subst y
    exact kept_not_omitted (D r) C hy ho.2
  · rcases (diagLift_eq_iff _ _ _ _).mp h with ⟨hrs,hxy⟩
    have hyx := Sum.inl.inj hxy
    subst r; subst y
    exact kept_not_omitted (D (!s)) C hy ho.2

theorem diag_right_unique (D : Bool → Sample) (r s : Bool) (x y : Cell) {p : Phys4}
    (hp : p ∈ diagBranch D ⟨r,.inr x⟩) (hq : p ∈ diagBranch D ⟨s,.inr y⟩) :
    (⟨r,.inr x⟩ : DiagLabel D) = ⟨s,.inr y⟩ := by
  rcases (diagBranch_right_mem D r x p).mp hp with rfl | ⟨hx,rfl⟩ | ⟨hx,rfl⟩ <;>
    rcases (diagBranch_right_mem D s y _).mp hq with h | ⟨hy,h⟩ | ⟨hy,h⟩
  · rcases (diagLift_eq_iff _ _ _ _).mp h with ⟨rfl,he⟩
    have he' := Sum.inr.inj he
    subst y
    rfl
  · simp only [diagLift_eq_iff,Sum.inr_ne_inl,and_false] at h
  · simp only [diagLift_eq_iff,Sum.inr_ne_inl,and_false] at h
  · simp only [diagLift_eq_iff,Sum.inl_ne_inr,and_false] at h
  · rcases (diagLift_eq_iff _ _ _ _).mp h with ⟨rfl,he⟩
    have he' := Sum.inl.inj he
    subst y
    rfl
  · have he := Sum.inl.inj ((diagLift_eq_iff _ _ _ _).mp h).2
    subst y
    simp_all [OmittedA,OmittedB]
  · simp only [diagLift_eq_iff,Sum.inl_ne_inr,and_false] at h
  · have he := Sum.inl.inj ((diagLift_eq_iff _ _ _ _).mp h).2
    subst y
    simp_all [OmittedA,OmittedB]
  · rcases (diagLift_eq_iff _ _ _ _).mp h with ⟨hr,he⟩
    have hrs : r = s := by cases r <;> cases s <;> simp_all
    have hxy := Sum.inl.inj he
    subst s; subst y
    rfl

theorem diagBranch_disjoint (D : Bool → Sample) (j l : DiagLabel D) (hne : j ≠ l) :
    Disjoint (diagBranch D j) (diagBranch D l) := by
  rcases j with ⟨r,C|x⟩ <;> rcases l with ⟨s,K|y⟩
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases (diagBranch_left_mem D r C p).mp hp with ⟨x,hx,rfl⟩
    rcases (diagBranch_left_mem D s K _).mp hq with ⟨y,hy,he⟩
    rcases (diagLift_eq_iff _ _ _ _).mp he with ⟨hrs,he⟩
    have hyx := Sum.inl.inj he
    subst s; subst y
    have hCK := component_eq_of_shared (D r) C K
      (kept_subset (D r) C hx) (kept_subset (D r) K hy)
    subst K
    exact hne rfl
  · exact diag_left_right_disjoint D r s C y
  · exact (diag_left_right_disjoint D s r K x).symm
  · exact Finset.disjoint_left.mpr (fun _ hp hq => hne (diag_right_unique D r s x y hp hq))

theorem diag_cross_covered (D : Bool → Sample) (r : Bool)
    (C : Component (D r)) {x : Cell} (hx : x ∈ C.val) (hs : x.1 = false) :
    ∃ a ∈ diagBranch D ⟨r,.inl C⟩,
      ∃ b ∈ diagBranch D ⟨!r,.inr x⟩, Hardware4 a b := by
  by_cases hk : x ∈ kept (D r) C
  · exact ⟨diagLift r (first x),Finset.mem_image.mpr ⟨x,hk,rfl⟩,
      diagLift (!r) (second x),diagBranch_second_mem D (!r) x,
      hardware4_symmetric (by simpa using diagLift_vertical (!r) x hs)⟩
  · have hm := omitted_mixed (D r) C hx hk
    refine ⟨diagLift r (first (pick (D r) C true)),?_,diagLift r (first x),?_,?_⟩
    · exact Finset.mem_image.mpr ⟨pick (D r) C true,by simp [kept],rfl⟩
    · apply (diagBranch_right_mem D (!r) x _).mpr
      right; right
      simpa using (show OmittedA (D r) x ∧ diagLift r (first x) = diagLift r (first x)
        from ⟨⟨hs,C,hx,hk⟩,rfl⟩)
    · apply (diagLift_hardware r _ _).mpr
      simp [Hardware,pick_shore (D r) C true hm.2,hs]

def diagOriginalFiber (D : Bool → Sample) (j : DiagLabel D) : Finset Phys4 :=
  (originalFiber (D j.1) j.2).image (diagLift j.1)

theorem diag_original_hardware_covered (D : Bool → Sample) (j l : DiagLabel D)
    {u v : Phys4} (hu : u ∈ diagOriginalFiber D j) (hv : v ∈ diagOriginalFiber D l)
    (h : Hardware4 u v) :
    ∃ a ∈ diagBranch D j, ∃ b ∈ diagBranch D l, Hardware4 a b := by
  rcases j with ⟨r,j⟩; rcases l with ⟨s,l⟩
  rcases Finset.mem_image.mp hu with ⟨p,hp,rfl⟩
  rcases Finset.mem_image.mp hv with ⟨q,hq,rfl⟩
  by_cases hrs : r = s
  · subst s
    rcases original_hardware_covered (D r) j l hp hq
      ((diagLift_hardware r p q).mp h) with ⟨a,ha,b,hb,hab⟩
    exact ⟨diagLift r a,diagBranch_base_subset D r j ha,
      diagLift r b,diagBranch_base_subset D r l hb,(diagLift_hardware r a b).mpr hab⟩
  · have hs : s = !r := by cases r <;> cases s <;> simp_all
    subst s
    rcases (diagLift_cross hrs p q).mp h with ⟨x,hx,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · cases j with
      | inl C =>
        have hxC : x ∈ C.val := by simpa [originalFiber] using hp
        cases l with
        | inl K => simp [originalFiber] at hq
        | inr y =>
          have hxy : x = y := by simpa [originalFiber] using hq
          subst y
          exact diag_cross_covered D r C hxC hx
      | inr y => simp [originalFiber] at hp
    · cases j with
      | inl C => simp [originalFiber] at hp
      | inr y =>
        have hxy : x = y := by simpa [originalFiber] using hp
        subst y
        cases l with
        | inl K =>
          have hxK : x ∈ K.val := by simpa [originalFiber] using hq
          rcases diag_cross_covered D (!r) K hxK hx with ⟨a,ha,b,hb,hab⟩
          exact ⟨b,by cases r <;> exact hb,a,ha,hardware4_symmetric hab⟩
        | inr y => simp [originalFiber] at hq

end AppendixAChimeraConstruction
