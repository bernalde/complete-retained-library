module

public import AppendixAChimeraFourBranchData

@[expose] public section

/-! Coverage of the actual original global quotient by plan-dependent branches.
No branch cardinality, connectedness, disjointness or embedding is assumed. -/
noncomputable section
namespace AppendixAChimeraFour
open AppendixAChimera
attribute [local instance] Classical.propDecidable

theorem retained_cross_covered (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r)) {x : Cell} (hx : x ∈ C.val) (hs : x.1 = true) :
    ∃ u ∈ retainedLocal D P r (.inl C),
      ∃ v ∈ retainedLocal D P r (.inr x), Hardware u v := by
  by_cases hk : x ∈ keptA (rowSample D r) C
  · exact ⟨first x,(retainedLocal_first_mem D P r C x).mpr (retained_B D P r C hk hs),
      second x,retainedLocal_second_mem D P r x,hs,rfl⟩
  · have hm := base_omitted_mixed (rowSample D r) C hx hk
    rcases hm.1 with ⟨a,ha,haA⟩
    rcases retained_shore D P r C ha with ⟨b,hb,hbA⟩
    refine ⟨first b,(retainedLocal_first_mem D P r C b).mpr hb,first x,?_,?_⟩
    · exact (retainedLocal_right_mem D P r x (first x)).mpr
        (Or.inr ⟨⟨hs,C,hx,hk⟩,rfl⟩)
    · simp [Hardware,hbA,haA,hs]

theorem retained_original_hardware_covered (D : Sample4) (P : RepairPlan D) (r : Bool)
    (j l : Label (rowSample D r)) {u v : Phys}
    (hu : u ∈ originalFiber (rowSample D r) j)
    (hv : v ∈ originalFiber (rowSample D r) l) (h : Hardware u v) :
    ∃ a ∈ retainedLocal D P r j, ∃ b ∈ retainedLocal D P r l, Hardware a b := by
  cases j with
  | inl C =>
    rcases Finset.mem_image.mp hu with ⟨x,hx,rfl⟩
    cases l with
    | inl K =>
      rcases Finset.mem_image.mp hv with ⟨y,hy,rfl⟩
      rcases retained_shore D P r C hx with ⟨a,ha,hsa⟩
      rcases retained_shore D P r K hy with ⟨b,hb,hsb⟩
      refine ⟨first a,(retainedLocal_first_mem D P r C a).mpr ha,
        first b,(retainedLocal_first_mem D P r K b).mpr hb,?_⟩
      simpa only [Hardware,hsa,hsb] using h
    | inr y =>
      have hv' : v = second y := Finset.mem_singleton.mp hv
      subst v
      rcases h with ⟨hs,rfl⟩
      exact retained_cross_covered D P r C hx hs
  | inr x =>
    have hu' : u = second x := Finset.mem_singleton.mp hu
    subst u
    cases l with
    | inl C =>
      rcases Finset.mem_image.mp hv with ⟨y,hy,rfl⟩
      rcases h with ⟨hs,rfl⟩
      rcases retained_cross_covered D P r C hy hs with ⟨a,ha,b,hb,hab⟩
      exact ⟨b,hb,a,ha,hardware_symmetric hab⟩
    | inr y =>
      have hv' : v = second y := Finset.mem_singleton.mp hv
      subst v
      exact ⟨second x,retainedLocal_second_mem D P r x,
        second y,retainedLocal_second_mem D P r y,h⟩

theorem final_same_row_original_hardware_covered (D : Sample4) (P : RepairPlan D)
    (r : Bool) (j l : Label (rowSample D r)) {u v : Phys}
    (hu : u ∈ originalFiber (rowSample D r) j)
    (hv : v ∈ originalFiber (rowSample D r) l) (h : Hardware u v) :
    ∃ a ∈ finalBranch D P ⟨r,j⟩, ∃ b ∈ finalBranch D P ⟨r,l⟩, Hardware4 a b := by
  rcases retained_original_hardware_covered D P r j l hu hv h with ⟨a,ha,b,hb,hab⟩
  exact ⟨rowLift r a,(finalBranch_same_row D P r j a).mpr ha,
    rowLift r b,(finalBranch_same_row D P r l b).mpr hb,Or.inl ⟨rfl,hab⟩⟩

theorem final_vertical_transfer_covered (D : Sample4) (P : RepairPlan D)
    (r : Bool) (x : Cell) (hd : P.drop r = some x) (ht : P.transfer r = true) :
    ∃ a ∈ finalBranch D P ⟨r,.inl (rowComponent D r x)⟩,
      ∃ b ∈ finalBranch D P ⟨!r,.inl (rowComponent D (!r) x)⟩, Hardware4 a b := by
  have hxA := (P.drop_bad r x hd).1
  have hc := (P.drop_bad r x hd).2
  let C := rowComponent D r x
  let b := pick (rowSample D r) C true
  have hb : b.1 = true := picked_B_of_multiA (rowSample D r) C (by dsimp [C]; omega)
  have hm : rowLift r (first x) ∈
      finalBranch D P ⟨!r,.inl (rowComponent D (!r) x)⟩ := by
    have h := (finalBranch_incoming_iff D P (!r) (.inl (rowComponent D (!r) x)) x).mpr
      ⟨by simpa using hd,by simpa using ht,rfl⟩
    simpa using h
  refine ⟨rowLift r (first b),?_,rowLift r (first x),hm,?_⟩
  · exact final_kept_B_survives D P r C (Finset.mem_insert_self _ _) hb
  · apply Or.inl
    exact ⟨rfl,by simp [rowLift,Hardware,hb,hxA]⟩

theorem final_vertical_paired_covered (D : Sample4) (P : RepairPlan D)
    (r : Bool) (x : Cell) (hd : P.drop r = some x) (ht : P.transfer r = false) :
    ∃ a ∈ finalBranch D P ⟨r,.inl (rowComponent D r x)⟩,
      ∃ b ∈ finalBranch D P ⟨!r,.inl (rowComponent D (!r) x)⟩, Hardware4 a b := by
  rcases P.paired_drop r x hd ht with ⟨hd',_,y,hne,hy,hy'⟩
  have hyC := (mem_aShore (rowSample D r) (rowComponent D r x) y).mp hy
  have hyK := (mem_aShore (rowSample D (!r)) (rowComponent D (!r) x) y).mp hy'
  have hn : P.drop r ≠ some y := by
    intro h
    exact hne (Option.some.inj (h.symm.trans hd))
  have hn' : P.drop (!r) ≠ some y := by
    intro h
    exact hne (Option.some.inj (h.symm.trans hd'))
  refine ⟨rowLift r (first y),final_first_A_survives D P r _ hyC.1 hyC.2 hn,
    rowLift (!r) (first y),final_first_A_survives D P (!r) _ hyK.1 hyK.2 hn',?_⟩
  apply Or.inr
  refine ⟨?_,rfl,hyC.2⟩
  cases r <;> simp [rowLift]

theorem final_vertical_first_covered (D : Sample4) (P : RepairPlan D)
    (r : Bool) (x : Cell) (hxA : x.1 = false) :
    ∃ a ∈ finalBranch D P ⟨r,.inl (rowComponent D r x)⟩,
      ∃ b ∈ finalBranch D P ⟨!r,.inl (rowComponent D (!r) x)⟩, Hardware4 a b := by
  by_cases hd : P.drop r = some x
  · cases ht : P.transfer r
    · exact final_vertical_paired_covered D P r x hd ht
    · exact final_vertical_transfer_covered D P r x hd ht
  · by_cases hd' : P.drop (!r) = some x
    · have h : ∃ b ∈ finalBranch D P ⟨!r,.inl (rowComponent D (!r) x)⟩,
          ∃ a ∈ finalBranch D P ⟨r,.inl (rowComponent D r x)⟩, Hardware4 b a := by
        cases ht : P.transfer (!r)
        · cases r <;> exact final_vertical_paired_covered D P _ x hd' ht
        · cases r <;> exact final_vertical_transfer_covered D P _ x hd' ht
      rcases h with ⟨b,hb,a,ha,hba⟩
      exact ⟨a,ha,b,hb,hardware4_symmetric hba⟩
    · refine ⟨rowLift r (first x),
        final_first_A_survives D P r _ (mem_rowComponent D r x) hxA hd,
        rowLift (!r) (first x),
        final_first_A_survives D P (!r) _ (mem_rowComponent D (!r) x) hxA hd',?_⟩
      apply Or.inr
      refine ⟨?_,rfl,hxA⟩
      cases r <;> simp [rowLift]

theorem final_vertical_original_covered (D : Sample4) (P : RepairPlan D)
    (r : Bool) (p : Phys) (hA : OnA p) :
    ∃ a ∈ finalBranch D P (originalLabel4 D (r,p)),
      ∃ b ∈ finalBranch D P (originalLabel4 D (!r,p)), Hardware4 a b := by
  cases p with
  | inl x => exact final_vertical_first_covered D P r x hA
  | inr x =>
    refine ⟨rowLift r (second x),final_second_survives D P r x,
      rowLift (!r) (second x),final_second_survives D P (!r) x,?_⟩
    apply Or.inr
    refine ⟨?_,rfl,hA⟩
    cases r <;> simp [rowLift]

theorem final_original_hardware_covered (D : Sample4) (P : RepairPlan D)
    {j l : Label4 D} {u v : Phys4}
    (hu : u ∈ originalFiber4 D j) (hv : v ∈ originalFiber4 D l) (h : Hardware4 u v) :
    ∃ a ∈ finalBranch D P j, ∃ b ∈ finalBranch D P l, Hardware4 a b := by
  have hju := (originalFiber4_exact_preimage D j u).mp hu
  have hlv := (originalFiber4_exact_preimage D l v).mp hv
  subst j
  subst l
  rcases u with ⟨r,p⟩
  rcases v with ⟨s,q⟩
  rcases h with ⟨hrs,hh⟩ | ⟨hrs,hpq,hA⟩
  · change r = s at hrs
    subst s
    exact final_same_row_original_hardware_covered D P r _ _
      (originalLabel_mem (rowSample D r) p (rowSample_active D r p))
      (originalLabel_mem (rowSample D r) q (rowSample_active D r q)) hh
  · change r ≠ s at hrs
    change p = q at hpq
    subst q
    have he : s = !r := RepairPlan.other_row_of_ne hrs.symm
    subst s
    exact final_vertical_original_covered D P r p hA

theorem final_quotient_covered (D : Sample4) (P : RepairPlan D)
    {j l : Label4 D} (h : QuotientAdj4 D j l) :
    ∃ u ∈ finalBranch D P j, ∃ v ∈ finalBranch D P l, Hardware4 u v := by
  rcases h.2 with ⟨u,hu,v,hv,he⟩
  exact final_original_hardware_covered D P hu hv (sampled_hardware4 D he)

end AppendixAChimeraFour

-- Explicit types and bounded transitive-axiom diagnostics.
set_option pp.all true
set_option pp.deepTerms true
#check AppendixAChimeraFour.retained_cross_covered
#print axioms AppendixAChimeraFour.retained_cross_covered
#check AppendixAChimeraFour.retained_original_hardware_covered
#print axioms AppendixAChimeraFour.retained_original_hardware_covered
#check AppendixAChimeraFour.final_same_row_original_hardware_covered
#print axioms AppendixAChimeraFour.final_same_row_original_hardware_covered
#check AppendixAChimeraFour.final_vertical_transfer_covered
#print axioms AppendixAChimeraFour.final_vertical_transfer_covered
#check AppendixAChimeraFour.final_vertical_paired_covered
#print axioms AppendixAChimeraFour.final_vertical_paired_covered
#check AppendixAChimeraFour.final_vertical_first_covered
#print axioms AppendixAChimeraFour.final_vertical_first_covered
#check AppendixAChimeraFour.final_vertical_original_covered
#print axioms AppendixAChimeraFour.final_vertical_original_covered
#check AppendixAChimeraFour.final_original_hardware_covered
#print axioms AppendixAChimeraFour.final_original_hardware_covered
#check AppendixAChimeraFour.final_quotient_covered
#print axioms AppendixAChimeraFour.final_quotient_covered
