module

public import AppendixAChimeraFourBranchData

@[expose] public section

/-! Structural plan-dependent branches only. Global sampled quotient coverage
is a separate obligation. No final embedding or minimum-footprint claim. -/
noncomputable section
namespace AppendixAChimeraFour
open AppendixAChimera
attribute [local instance] Classical.propDecidable

theorem retainedLocal_center (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) :
    ∃ c ∈ retainedLocal D P r j, ∀ p ∈ retainedLocal D P r j, p = c ∨ Hardware p c := by
  cases j with
  | inl C =>
    refine ⟨first (pick (rowSample D r) C true),
      (retainedLocal_first_mem D P r C _).mpr (retained_pick D P r C),?_⟩
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x,hx,rfl⟩
    exact (keptA_to_pick (rowSample D r) C (retainedA_subset D P r C hx)).imp
      (congrArg first) id
  | inr x => exact base_branch_center (rowSample D r) (.inr x)

theorem retainedLocal_nonempty (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) : (retainedLocal D P r j).Nonempty := by
  rcases retainedLocal_center D P r j with ⟨c,hc,_⟩
  exact ⟨c,hc⟩

theorem retainedLocal_card_le_three (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) : (retainedLocal D P r j).card ≤ 3 := by
  cases j with
  | inl C =>
    change ((retainedA D P r C).image first).card ≤ 3
    apply Finset.card_image_le.trans
    by_cases hc : (aShore (rowSample D r) C).card = 3
    · rcases P.bad_eq_donor D r C hc with ⟨x,hd,hC⟩
      have hxC : x ∈ C.val := by rw [hC]; exact mem_rowComponent D r x
      have hx := keptA_retains_A (rowSample D r) C hxC (P.drop_bad r x hd).1
      rw [retainedA_eq_erase D P r C x hd,Finset.card_erase_of_mem hx,
        keptA_card_of_multiA (rowSample D r) C (by omega),hc]
    · exact (Finset.card_le_card (retainedA_subset D P r C)).trans
        (no_three_A_keptA_le_three (rowSample D r) (rowSample_canonical D r)
          (rowSample_selected_card D r) C hc)
  | inr x => exact (base_right_card_le_two (rowSample D r) x).trans (by omega)

theorem incomingCells_card_le_one (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) : (incomingCells D P r j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact Option.some.inj (((mem_incomingCells D P r j x).mp hx).1.symm.trans
    ((mem_incomingCells D P r j y).mp hy).1)

theorem incomingBranch_card_le_one (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) : (incomingBranch D P r j).card ≤ 1 :=
  Finset.card_image_le.trans (incomingCells_card_le_one D P r j)

theorem incoming_nonempty_local_small (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j : Label (rowSample D r)) (hi : (incomingBranch D P r j).Nonempty) :
    (retainedLocal D P r j).card ≤ 2 := by
  rcases hi with ⟨u,hu⟩
  rcases Finset.mem_image.mp hu with ⟨x,hx,_⟩
  rcases (mem_incomingCells D P r j x).mp hx with ⟨hd,ht,hj⟩
  subst j
  change ((retainedA D P r (rowComponent D r x)).image first).card ≤ 2
  rw [incoming_receiver_unchanged D P r x hd ht]
  exact Finset.card_image_le.trans (incoming_receiver D P r x hd ht).1

theorem finalBranch_card_le_three (D : Sample4) (P : RepairPlan D) (j : Label4 D) :
    (finalBranch D P j).card ≤ 3 := by
  rcases j with ⟨r,j⟩
  by_cases hi : (incomingBranch D P r j).Nonempty
  · have hlocal := incoming_nonempty_local_small D P r j hi
    have hin := incomingBranch_card_le_one D P r j
    have hlift : ((retainedLocal D P r j).image (rowLift r)).card ≤
        (retainedLocal D P r j).card := Finset.card_image_le
    have hu := Finset.card_union_le ((retainedLocal D P r j).image (rowLift r))
      (incomingBranch D P r j)
    change (((retainedLocal D P r j).image (rowLift r)) ∪ incomingBranch D P r j).card ≤ 3
    omega
  · have he : incomingBranch D P r j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    simp only [finalBranch,he,Finset.union_empty]
    exact Finset.card_image_le.trans (retainedLocal_card_le_three D P r j)

theorem finalBranch_nonempty (D : Sample4) (P : RepairPlan D) (j : Label4 D) :
    (finalBranch D P j).Nonempty := by
  rcases j with ⟨r,j⟩
  rcases retainedLocal_nonempty D P r j with ⟨p,hp⟩
  exact ⟨rowLift r p,(finalBranch_same_row D P r j p).mpr hp⟩

theorem finalBranch_reaches_center (D : Sample4) (P : RepairPlan D) (j : Label4 D) :
    ∃ c ∈ finalBranch D P j, ∀ u ∈ finalBranch D P j,
      Relation.ReflTransGen
        (fun a b => a ∈ finalBranch D P j ∧ b ∈ finalBranch D P j ∧ Hardware4 a b) u c := by
  rcases j with ⟨r,j⟩
  rcases retainedLocal_center D P r j with ⟨c,hc,hstar⟩
  have hcF : rowLift r c ∈ finalBranch D P ⟨r,j⟩ := (finalBranch_same_row D P r j c).mpr hc
  have hlocal : ∀ p ∈ retainedLocal D P r j,
      Relation.ReflTransGen
        (fun a b => a ∈ finalBranch D P ⟨r,j⟩ ∧ b ∈ finalBranch D P ⟨r,j⟩ ∧ Hardware4 a b)
        (rowLift r p) (rowLift r c) := by
    intro p hp
    rcases hstar p hp with he | hh
    · rw [he]
    · exact Relation.ReflTransGen.single
        ⟨(finalBranch_same_row D P r j p).mpr hp,hcF,Or.inl ⟨rfl,hh⟩⟩
  refine ⟨rowLift r c,hcF,?_⟩
  intro u hu
  rcases (mem_finalBranch D P r j u).mp hu with ⟨p,hp,rfl⟩ | ⟨x,hd,ht,hj,rfl⟩
  · exact hlocal p hp
  · have hm : first x ∈ retainedLocal D P r j := by
      rw [hj,retainedLocal_first_mem]
      exact incoming_mate_retained D P r x hd ht
    have hmf : rowLift r (first x) ∈ finalBranch D P ⟨r,j⟩ :=
      (finalBranch_same_row D P r j (first x)).mpr hm
    have hedge : Hardware4 (rowLift (!r) (first x)) (rowLift r (first x)) := by
      apply Or.inr
      refine ⟨?_,rfl,(P.drop_bad (!r) x hd).1⟩
      cases r <;> simp [rowLift]
    exact (Relation.ReflTransGen.single ⟨hu,hmf,hedge⟩).trans (hlocal (first x) hm)

theorem finalBranch_connected (D : Sample4) (P : RepairPlan D) (j : Label4 D) :
    ∀ u ∈ finalBranch D P j, ∀ v ∈ finalBranch D P j,
      Relation.ReflTransGen
        (fun a b => a ∈ finalBranch D P j ∧ b ∈ finalBranch D P j ∧ Hardware4 a b) u v := by
  rcases finalBranch_reaches_center D P j with ⟨c,_,hc⟩
  letI : Std.Symm (fun a b : Phys4 =>
      a ∈ finalBranch D P j ∧ b ∈ finalBranch D P j ∧ Hardware4 a b) :=
    ⟨fun _ _ h => ⟨h.2.1,h.1,hardware4_symmetric h.2.2⟩⟩
  intro u hu v hv
  exact (hc u hu).trans (Relation.ReflTransGen.stdSymm.symm _ _ (hc v hv))

theorem finalBranch_label_unique (D : Sample4) (P : RepairPlan D)
    {j l : Label4 D} {u : Phys4} (hj : u ∈ finalBranch D P j)
    (hl : u ∈ finalBranch D P l) : j = l := by
  rcases j with ⟨r,j⟩
  rcases l with ⟨s,l⟩
  rcases (mem_finalBranch D P r j u).mp hj with ⟨p,hp,he⟩ | ⟨x,hd,_,hx,he⟩
  · rcases (mem_finalBranch D P s l u).mp hl with ⟨q,hq,hf⟩ | ⟨y,hd,_,hy,hf⟩
    · have hrs : r = s := congrArg Prod.fst (he.trans hf.symm)
      subst s
      have hpq : p = q := congrArg Prod.snd (he.trans hf.symm)
      subst q
      have hjl : j = l := by
        by_contra hne
        exact Finset.disjoint_left.mp (base_branch_disjoint (rowSample D r) j l hne)
          (retainedLocal_subset_base D P r j hp) (retainedLocal_subset_base D P r l hq)
      exact congrArg (Sigma.mk r) hjl
    · have hrs : r = (!s) := congrArg Prod.fst (he.trans hf.symm)
      have hpy : p = first y := congrArg Prod.snd (he.trans hf.symm)
      have hd' : P.drop r = some y := by rw [hrs]; exact hd
      exact (dropped_not_retainedLocal D P r y hd' j (hpy ▸ hp)).elim
  · rcases (mem_finalBranch D P s l u).mp hl with ⟨q,hq,hf⟩ | ⟨y,_,_,hy,hf⟩
    · have hrs : (!r) = s := congrArg Prod.fst (he.trans hf.symm)
      have hxq : first x = q := congrArg Prod.snd (he.trans hf.symm)
      have hd' : P.drop s = some x := by rw [← hrs]; exact hd
      exact (dropped_not_retainedLocal D P s x hd' l (hxq.symm ▸ hq)).elim
    · have hrows : (!r) = (!s) := congrArg Prod.fst (he.trans hf.symm)
      have hrs : r = s := by
        cases r <;> cases s
        · rfl
        · cases hrows
        · cases hrows
        · rfl
      subst s
      have hxy : x = y := Sum.inl.inj (congrArg Prod.snd (he.trans hf.symm))
      subst y
      exact congrArg (Sigma.mk r) (hx.trans hy.symm)

theorem finalBranch_disjoint (D : Sample4) (P : RepairPlan D) (j l : Label4 D)
    (hne : j ≠ l) : Disjoint (finalBranch D P j) (finalBranch D P l) := by
  apply Finset.disjoint_left.mpr
  intro u hj hl
  exact hne (finalBranch_label_unique D P hj hl)

end AppendixAChimeraFour
