module

public import AppendixAChimeraFourPlan
public import AppendixAChimeraShoreBase

@[expose] public section

/-! Shared exact branch definitions and pointwise facts for plan-dependent surgery.
No global quotient coverage or embedding theorem is asserted here. -/
noncomputable section
namespace AppendixAChimeraFour
open AppendixAChimera
attribute [local instance] Classical.propDecidable

def retainedA (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) : Finset Cell :=
  (keptA (rowSample D r) C).filter (fun x => P.drop r ≠ some x)

def retainedLocal (D : Sample4) (P : RepairPlan D) (r : Bool) :
    Label (rowSample D r) → Finset Phys
  | .inl C => (retainedA D P r C).image first
  | .inr x => baseBranch (rowSample D r) (.inr x)

def incomingCells (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) : Finset Cell :=
  Finset.univ.filter (fun x => P.drop (!r) = some x ∧ P.transfer (!r) = true ∧
    j = .inl (rowComponent D r x))

def incomingBranch (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) : Finset Phys4 :=
  (incomingCells D P r j).image (fun x => rowLift (!r) (first x))

def finalBranch (D : Sample4) (P : RepairPlan D) (j : Label4 D) : Finset Phys4 :=
  (retainedLocal D P j.1 j.2).image (rowLift j.1) ∪ incomingBranch D P j.1 j.2

theorem mem_retainedA (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) (x : Cell) :
    x ∈ retainedA D P r C ↔ x ∈ keptA (rowSample D r) C ∧ P.drop r ≠ some x :=
  Finset.mem_filter

theorem retainedA_subset (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) : retainedA D P r C ⊆ keptA (rowSample D r) C :=
  Finset.filter_subset _ _

theorem retainedA_eq_erase (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) (x : Cell) (hd : P.drop r = some x) :
    retainedA D P r C = (keptA (rowSample D r) C).erase x := by
  ext y
  simp [retainedA,hd,ne_comm,and_comm]

theorem drop_mem_bad (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) (x : Cell) (hd : P.drop r = some x)
    (hx : x ∈ C.val) : (aShore (rowSample D r) C).card = 3 := by
  have h := (P.drop_bad r x hd).2
  rw [rowComponent_eq D r x C hx] at h
  exact h

theorem retained_pick (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) : pick (rowSample D r) C true ∈ retainedA D P r C := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_insert_self _ _,?_⟩
  intro hd
  have ha := (P.drop_bad r _ hd).1
  have hc := drop_mem_bad D P r C _ hd (pick_mem (rowSample D r) C true)
  have hb := picked_B_of_multiA (rowSample D r) C (by omega)
  simp_all

theorem retained_eq_kept_of_not_bad (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) (hc : (aShore (rowSample D r) C).card ≠ 3) :
    retainedA D P r C = keptA (rowSample D r) C := by
  apply Finset.Subset.antisymm (retainedA_subset D P r C)
  intro x hx
  exact (mem_retainedA D P r C x).mpr ⟨hx,fun hd =>
    hc (drop_mem_bad D P r C x hd (keptA_subset (rowSample D r) C hx))⟩

theorem three_A_erase_card (E : Sample) (C : Component E) (x : Cell)
    (hc : (aShore E C).card = 3) (hx : x ∈ aShore E C) :
    ((aShore E C).erase x).card = 2 := by
  rw [Finset.card_erase_of_mem hx,hc]

theorem drop_leaves_two_A (D : Sample4) (P : RepairPlan D) (r : Bool)
    (x : Cell) (hd : P.drop r = some x) :
    ((aShore (rowSample D r) (rowComponent D r x)).erase x).card = 2 ∧
      (aShore (rowSample D r) (rowComponent D r x)).erase x ⊆
        retainedA D P r (rowComponent D r x) := by
  have hxA := (mem_aShore (rowSample D r) (rowComponent D r x) x).mpr
    ⟨mem_rowComponent D r x,(P.drop_bad r x hd).1⟩
  refine ⟨three_A_erase_card _ _ x (P.drop_bad r x hd).2 hxA,?_⟩
  rw [retainedA_eq_erase D P r _ x hd]
  intro y hy
  rcases Finset.mem_erase.mp hy with ⟨hne,hy⟩
  exact Finset.mem_erase.mpr ⟨hne,Finset.mem_insert_of_mem hy⟩

theorem retained_shore (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) {x : Cell} (hx : x ∈ C.val) :
    ∃ y ∈ retainedA D P r C, y.1 = x.1 := by
  rcases keptA_shore (rowSample D r) C hx with ⟨y,hy,hys⟩
  by_cases hd : P.drop r = some y
  · have hc := drop_mem_bad D P r C y hd (keptA_subset (rowSample D r) C hy)
    have hyA := (mem_aShore (rowSample D r) C y).mpr
      ⟨keptA_subset (rowSample D r) C hy,(P.drop_bad r y hd).1⟩
    have hn : ((aShore (rowSample D r) C).erase y).Nonempty := by
      apply Finset.card_pos.mp
      rw [three_A_erase_card _ _ y hc hyA]
      omega
    rcases hn with ⟨z,hz⟩
    rcases Finset.mem_erase.mp hz with ⟨hne,hzA⟩
    refine ⟨z,?_,?_⟩
    · rw [retainedA_eq_erase D P r C y hd]
      exact Finset.mem_erase.mpr ⟨hne,Finset.mem_insert_of_mem hzA⟩
    · exact ((mem_aShore (rowSample D r) C z).mp hzA).2.trans
        (((P.drop_bad r y hd).1).symm.trans hys)
  · exact ⟨y,(mem_retainedA D P r C y).mpr ⟨hy,hd⟩,hys⟩

theorem retained_A_of_not_drop (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) {x : Cell} (hx : x ∈ C.val)
    (hs : x.1 = false) (hd : P.drop r ≠ some x) : x ∈ retainedA D P r C :=
  (mem_retainedA D P r C x).mpr ⟨keptA_retains_A (rowSample D r) C hx hs,hd⟩

theorem retained_B (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) {x : Cell} (hx : x ∈ keptA (rowSample D r) C)
    (hs : x.1 = true) : x ∈ retainedA D P r C := by
  apply (mem_retainedA D P r C x).mpr
  refine ⟨hx,?_⟩
  intro hd
  have := (P.drop_bad r x hd).1
  simp_all

theorem incoming_receiver (D : Sample4) (P : RepairPlan D) (r : Bool) (x : Cell)
    (hd : P.drop (!r) = some x) (ht : P.transfer (!r) = true) :
    (keptA (rowSample D r) (rowComponent D r x)).card ≤ 2 ∧
      x ∈ keptA (rowSample D r) (rowComponent D r x) := by
  rcases P.transfer_valid (!r) ht with ⟨y,hy,hsmall,hkept⟩
  have heq : y = x := Option.some.inj (hy.symm.trans hd)
  subst y
  cases r <;> exact And.intro hsmall hkept

theorem incoming_receiver_unchanged (D : Sample4) (P : RepairPlan D) (r : Bool) (x : Cell)
    (hd : P.drop (!r) = some x) (ht : P.transfer (!r) = true) :
    retainedA D P r (rowComponent D r x) = keptA (rowSample D r) (rowComponent D r x) := by
  apply retained_eq_kept_of_not_bad
  intro hc
  have hs := (incoming_receiver D P r x hd ht).1
  have hb := keptA_card_of_multiA (rowSample D r) (rowComponent D r x) (by omega)
  omega

theorem incoming_mate_retained (D : Sample4) (P : RepairPlan D) (r : Bool) (x : Cell)
    (hd : P.drop (!r) = some x) (ht : P.transfer (!r) = true) :
    x ∈ retainedA D P r (rowComponent D r x) := by
  rw [incoming_receiver_unchanged D P r x hd ht]
  exact (incoming_receiver D P r x hd ht).2

theorem incoming_receiver_not_dropped (D : Sample4) (P : RepairPlan D) (r : Bool) (x : Cell)
    (hd : P.drop (!r) = some x) (ht : P.transfer (!r) = true) : P.drop r ≠ some x :=
  ((mem_retainedA D P r (rowComponent D r x) x).mp
    (incoming_mate_retained D P r x hd ht)).2

theorem retainedLocal_first_mem (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) (x : Cell) :
    first x ∈ retainedLocal D P r (.inl C) ↔ x ∈ retainedA D P r C := by
  simp [retainedLocal]

theorem retainedLocal_second_mem (D : Sample4) (P : RepairPlan D) (r : Bool) (x : Cell) :
    second x ∈ retainedLocal D P r (.inr x) := base_second_mem_right _ x

theorem retainedLocal_right_mem (D : Sample4) (P : RepairPlan D) (r : Bool)
    (x : Cell) (p : Phys) : p ∈ retainedLocal D P r (.inr x) ↔
      p = second x ∨ (BaseOmittedB (rowSample D r) x ∧ p = first x) :=
  base_right_mem_shape _ x p

theorem retainedLocal_subset_base (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) : retainedLocal D P r j ⊆ baseBranch (rowSample D r) j := by
  cases j with
  | inl C =>
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x,hx,rfl⟩
    exact Finset.mem_image.mpr ⟨x,retainedA_subset D P r C hx,rfl⟩
  | inr x => exact Finset.Subset.refl _

theorem dropped_not_retainedLocal (D : Sample4) (P : RepairPlan D) (r : Bool)
    (x : Cell) (hd : P.drop r = some x) (j : Label (rowSample D r)) :
    first x ∉ retainedLocal D P r j := by
  intro hx
  cases j with
  | inl C =>
    have h := (retainedLocal_first_mem D P r C x).mp hx
    exact ((mem_retainedA D P r C x).mp h).2 hd
  | inr y =>
    rcases (base_first_mem_right_iff (rowSample D r) y x).mp hx with ⟨heq,ho⟩
    subst y
    have hs := (P.drop_bad r x hd).1
    have ht := ho.1
    simp_all

theorem mem_incomingCells (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) (x : Cell) : x ∈ incomingCells D P r j ↔
      P.drop (!r) = some x ∧ P.transfer (!r) = true ∧ j = .inl (rowComponent D r x) := by
  simp [incomingCells]

theorem mem_finalBranch (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) (u : Phys4) : u ∈ finalBranch D P ⟨r,j⟩ ↔
      (∃ p ∈ retainedLocal D P r j, rowLift r p = u) ∨
      ∃ x, P.drop (!r) = some x ∧ P.transfer (!r) = true ∧
        j = .inl (rowComponent D r x) ∧ rowLift (!r) (first x) = u := by
  simp only [finalBranch,Finset.mem_union,Finset.mem_image,incomingBranch,mem_incomingCells]
  constructor
  · rintro (h | ⟨x,⟨hd,ht,hj⟩,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x,hd,ht,hj,he⟩
  · rintro (h | ⟨x,hd,ht,hj,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x,⟨hd,ht,hj⟩,he⟩

theorem finalBranch_same_row (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) (p : Phys) :
    rowLift r p ∈ finalBranch D P ⟨r,j⟩ ↔ p ∈ retainedLocal D P r j := by
  rw [mem_finalBranch]
  constructor
  · rintro (⟨q,hq,he⟩ | ⟨x,_,_,_,he⟩)
    · exact (rowLift_injective r he) ▸ hq
    · have hr : (!r) = r := congrArg Prod.fst he
      cases r <;> cases hr
  · intro hp
    exact Or.inl ⟨p,hp,rfl⟩

theorem finalBranch_incoming_iff (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) (x : Cell) :
    rowLift (!r) (first x) ∈ finalBranch D P ⟨r,j⟩ ↔
      P.drop (!r) = some x ∧ P.transfer (!r) = true ∧ j = .inl (rowComponent D r x) := by
  rw [mem_finalBranch]
  constructor
  · rintro (⟨p,_,he⟩ | ⟨y,hd,ht,hj,he⟩)
    · have hr : r = (!r) := congrArg Prod.fst he
      cases r <;> cases hr
    · have hyx : y = x := Sum.inl.inj (rowLift_injective (!r) he)
      subst y
      exact ⟨hd,ht,hj⟩
  · rintro ⟨hd,ht,hj⟩
    exact Or.inr ⟨x,hd,ht,hj,rfl⟩

theorem final_first_A_survives (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) {x : Cell} (hx : x ∈ C.val)
    (hs : x.1 = false) (hd : P.drop r ≠ some x) :
    rowLift r (first x) ∈ finalBranch D P ⟨r,.inl C⟩ := by
  rw [finalBranch_same_row,retainedLocal_first_mem]
  exact retained_A_of_not_drop D P r C hx hs hd

theorem final_kept_B_survives (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) {x : Cell} (hx : x ∈ keptA (rowSample D r) C)
    (hs : x.1 = true) : rowLift r (first x) ∈ finalBranch D P ⟨r,.inl C⟩ := by
  rw [finalBranch_same_row,retainedLocal_first_mem]
  exact retained_B D P r C hx hs

theorem final_second_survives (D : Sample4) (P : RepairPlan D) (r : Bool) (x : Cell) :
    rowLift r (second x) ∈ finalBranch D P ⟨r,.inr x⟩ :=
  (finalBranch_same_row D P r (.inr x) (second x)).mpr (retainedLocal_second_mem D P r x)

end AppendixAChimeraFour
