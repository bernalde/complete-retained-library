module

public import AppendixAChimeraBridge

@[expose] public section

/-! Author candidate for the exact Figure A.2 graph. Names are assigned diagram
coordinates, not original node labels. No solver-performance statement. -/
noncomputable section
open scoped BigOperators
namespace AppendixAIllustrativeMinimum
open AppendixAChimera AppendixATheory
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
inductive Left where
  | sideLeft | top | sideRight | bottom
  deriving DecidableEq, Fintype

abbrev Logical := Left ⊕ Cell

def Diamond : Left → Left → Prop
  | .sideLeft, .top | .top, .sideLeft
  | .sideLeft, .bottom | .bottom, .sideLeft
  | .top, .sideRight | .sideRight, .top
  | .top, .bottom | .bottom, .top
  | .sideRight, .bottom | .bottom, .sideRight => True
  | _, _ => False

def SourceAdj : Logical → Logical → Prop
  | .inl x, .inl y => Diamond x y
  | .inr x, .inr y => x.1 ≠ y.1
  | .inl x, .inr y => x = .top ∧ y = (true,0)
  | .inr x, .inl y => y = .top ∧ x = (true,0)

theorem diamond_symmetric : Symmetric Diamond := by
  intro x y h
  cases x <;> cases y <;> simp_all [Diamond]

theorem source_symmetric : Symmetric SourceAdj := by
  intro u v h
  cases u with
  | inl x =>
    cases v with
    | inl y => exact diamond_symmetric h
    | inr y => exact h
  | inr x =>
    cases v with
    | inl y => exact h
    | inr y => exact Ne.symm h

theorem source_irreflexive (u : Logical) : ¬ SourceAdj u u := by
  cases u with
  | inl x => cases x <;> simp [SourceAdj,Diamond]
  | inr x => simp [SourceAdj]

theorem logical_card : Fintype.card Logical = 12 := by decide

def logicalEquiv : Logical ≃ Fin 12 := Fintype.equivFinOfCardEq logical_card

def logicalEdges : Finset (Fin 12 × Fin 12) :=
  Finset.univ.filter (fun e => SourceAdj (logicalEquiv.symm e.1) (logicalEquiv.symm e.2))

theorem logical_adjacent_iff (j l : Fin 12) :
    AppendixA.adjacent logicalEdges j l ↔ SourceAdj (logicalEquiv.symm j) (logicalEquiv.symm l) := by
  simp only [AppendixA.adjacent,logicalEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => h.elim id (fun h => source_symmetric h),Or.inl⟩

theorem logical_transport (j l : Logical) :
    AppendixA.adjacent logicalEdges (logicalEquiv j) (logicalEquiv l) ↔ SourceAdj j l := by
  simpa using logical_adjacent_iff (logicalEquiv j) (logicalEquiv l)

theorem logical_loopFree : LoopFree logicalEdges := by
  intro j h
  exact source_irreflexive _ ((logical_adjacent_iff j j).mp h)

def color : Phys → Bool
  | .inl x => x.1
  | .inr x => !x.1

theorem hardware_color_ne {u v : Phys} (h : Hardware u v) : color u ≠ color v := by
  cases u with
  | inl x =>
    cases v with
    | inl y => exact h
    | inr y =>
      rcases h with ⟨hx,rfl⟩
      simp [color,hx]
  | inr x =>
    cases v with
    | inl y =>
      rcases h with ⟨hy,rfl⟩
      simp [color,hy]
    | inr y =>
      change (!x.1) ≠ (!y.1)
      simpa [Hardware] using h

theorem hardware_triangle_free (u v w : Phys) :
    ¬ (Hardware u v ∧ Hardware v w ∧ Hardware u w) := by
  rintro ⟨huv,hvw,huw⟩
  have h1 := hardware_color_ne huv
  have h2 := hardware_color_ne hvw
  have h3 := hardware_color_ne huw
  cases hcu : color u <;> cases hcv : color v <;> cases hcw : color w <;> simp_all

theorem target_triangle_free (u v w : Fin 16) :
    ¬ (AppendixA.adjacent targetEdges u v ∧ AppendixA.adjacent targetEdges v w ∧
       AppendixA.adjacent targetEdges u w) := by
  rintro ⟨huv,hvw,huw⟩
  exact hardware_triangle_free _ _ _ ⟨(target_adjacent_iff u v).mp huv,
    (target_adjacent_iff v w).mp hvw,(target_adjacent_iff u w).mp huw⟩

def branches : Logical → Finset Phys
  | .inl .sideLeft => {first (false,1)}
  | .inl .top => {first (false,0),first (true,0)}
  | .inl .sideRight => {first (false,2)}
  | .inl .bottom => {first (true,1)}
  | .inr x => {second x}

theorem branches_pair (j : Logical) :
    ∃ u v, branches j = {u,v} ∧ (u = v ∨ Hardware u v) := by
  cases j with
  | inl x =>
    cases x with
    | sideLeft => exact ⟨first (false,1),first (false,1),by simp [branches],Or.inl rfl⟩
    | top => exact ⟨first (false,0),first (true,0),rfl,Or.inr (by simp [Hardware])⟩
    | sideRight => exact ⟨first (false,2),first (false,2),by simp [branches],Or.inl rfl⟩
    | bottom => exact ⟨first (true,1),first (true,1),by simp [branches],Or.inl rfl⟩
  | inr x => exact ⟨second x,second x,by simp [branches],Or.inl rfl⟩

theorem branches_nonempty (j : Logical) : (branches j).Nonempty := by
  rcases branches_pair j with ⟨u,v,h,_⟩
  rw [h]
  exact Finset.insert_nonempty _ _

theorem branches_card (j : Logical) : (branches j).card ≤ 2 := by
  rcases branches_pair j with ⟨u,v,h,_⟩
  rw [h]
  exact (Finset.card_insert_le u {v}).trans (by simp)

theorem branches_disjoint (j l : Logical) (hne : j ≠ l) :
    Disjoint (branches j) (branches l) := by
  cases j with
  | inl x =>
    cases l with
    | inl y => cases x <;> cases y <;> simp_all [branches,Finset.disjoint_left]
    | inr y => cases x <;> simp [branches,Finset.disjoint_left]
  | inr x =>
    cases l with
    | inl y => cases y <;> simp [branches,Finset.disjoint_left]
    | inr y => simpa [branches] using hne

theorem source_edge_covered {j l : Logical} (h : SourceAdj j l) :
    ∃ u ∈ branches j, ∃ v ∈ branches l, Hardware u v := by
  cases j with
  | inl x =>
    cases l with
    | inl y => cases x <;> cases y <;> simp_all [SourceAdj,Diamond,branches,Hardware]
    | inr y =>
      rcases h with ⟨rfl,rfl⟩
      simp [branches,Hardware]
  | inr x =>
    cases l with
    | inl y =>
      rcases h with ⟨rfl,rfl⟩
      simp [branches,Hardware]
    | inr y => exact ⟨second x,by simp [branches],second y,by simp [branches],h⟩

def finiteBranches (j : Fin 12) : Finset (Fin 16) :=
  (branches (logicalEquiv.symm j)).image physEquiv

theorem finiteBranches_connected (j : Fin 12) :
    AppendixA.connected targetEdges (finiteBranches j) := by
  rcases branches_pair (logicalEquiv.symm j) with ⟨u,v,hpair,h⟩
  simp only [finiteBranches,hpair,Finset.image_insert,Finset.image_singleton]
  apply connected_pair_bridge
  exact h.imp (congrArg physEquiv) ((hardware_transport u v).mpr)

theorem finiteBranches_branchModel : BranchModel targetEdges logicalEdges 2 finiteBranches := by
  refine ⟨?_,?_,?_⟩
  · intro j
    exact ⟨(branches_nonempty _).image physEquiv,
      Finset.card_image_le.trans (branches_card _),finiteBranches_connected j⟩
  · intro j l hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_image.mp hp with ⟨u,hu,hu'⟩
    rcases Finset.mem_image.mp hq with ⟨v,hv,hv'⟩
    have he : u = v := physEquiv.injective (hu'.trans hv'.symm)
    subst v
    exact Finset.disjoint_left.mp (branches_disjoint _ _
      (fun heq => hne (logicalEquiv.symm.injective heq))) hu hv
  · intro j l h
    rcases source_edge_covered ((logical_adjacent_iff j l).mp h) with ⟨u,hu,v,hv,he⟩
    exact ⟨physEquiv u,Finset.mem_image.mpr ⟨u,hu,rfl⟩,
      physEquiv v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,(hardware_transport u v).mpr he⟩

def assignment : Alpha 16 12 := alphaOfFibers finiteBranches

theorem assignment_fiber : fiber assignment = finiteBranches := fiber_alphaOfFibers _

theorem assignment_embedding : Embedding targetEdges logicalEdges 2 assignment := by
  apply (embedding_iff_branchModel _ _ _ _).mpr
  simpa [assignment] using finiteBranches_branchModel

theorem assignment_embedding_of_two_le (k : ℕ) (hk : 2 ≤ k) :
    Embedding targetEdges logicalEdges k assignment := by
  have h := assignment_embedding
  exact ⟨⟨h.1.1,fun j => ⟨(h.1.2 j).1,(h.1.2 j).2.trans hk⟩⟩,h.2⟩

theorem left_univ : (Finset.univ : Finset Left) =
    {.sideLeft,.top,.sideRight,.bottom} := by
  ext x
  cases x <;> simp

theorem branches_sum : ∑ j : Logical, (branches j).card = 13 := by
  rw [Fintype.sum_sum_type]
  simp [left_univ,branches,Cell]

theorem finiteBranches_card (j : Logical) :
    (finiteBranches (logicalEquiv j)).card = (branches j).card := by
  simp [finiteBranches,Finset.card_image_of_injective _ physEquiv.injective]

theorem assignment_footprint : footprint assignment = 13 := by
  rw [← sum_fiber_card_eq_footprint assignment
    ((row_card_iff_exclusive assignment).mp assignment_embedding.1.1),assignment_fiber]
  rw [← logicalEquiv.sum_comp (fun j => (finiteBranches j).card)]
  simpa only [finiteBranches_card] using branches_sum

theorem singleton_edge {k : ℕ} {A : Alpha 16 12}
    (h : Embedding targetEdges logicalEdges k A) {j l : Fin 12} {u v : Fin 16}
    (hj : fiber A j = {u}) (hl : fiber A l = {v})
    (he : AppendixA.adjacent logicalEdges j l) : AppendixA.adjacent targetEdges u v := by
  rcases h.2.1 j l he with ⟨a,ha,b,hb,hab⟩
  rw [hj] at ha
  rw [hl] at hb
  have h1 := Finset.mem_singleton.mp ha
  have h2 := Finset.mem_singleton.mp hb
  simpa [h1,h2] using hab

theorem footprint_lower_bound (k : ℕ) (A : Alpha 16 12)
    (h : Embedding targetEdges logicalEdges k A) : 13 ≤ footprint A := by
  by_contra hn
  have hupper : footprint A ≤ 12 := by omega
  have hsum : (∑ j : Fin 12, (fiber A j).card) ≤ 12 := by
    rw [sum_fiber_card_eq_footprint A ((row_card_iff_exclusive A).mp h.1.1)]
    exact hupper
  have hc : ∀ j, (fiber A j).card ≤ 1 := by
    intro j
    by_contra hj
    have hj' : 1 < (fiber A j).card := by omega
    have hh : (∑ _j : Fin 12, (1 : ℕ)) < ∑ j : Fin 12, (fiber A j).card :=
      Finset.sum_lt_sum (fun i _ => (h.1.2 i).1.card_pos) ⟨j,Finset.mem_univ _,hj'⟩
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hh
    omega
  have hr : RowBounds 1 A := ⟨h.1.1,fun j => ⟨(h.1.2 j).1,hc j⟩⟩
  obtain ⟨u,hu⟩ := cap_one_singletons A hr (logicalEquiv (.inl .sideLeft))
  obtain ⟨v,hv⟩ := cap_one_singletons A hr (logicalEquiv (.inl .top))
  obtain ⟨w,hw⟩ := cap_one_singletons A hr (logicalEquiv (.inl .bottom))
  apply target_triangle_free u v w
  exact ⟨singleton_edge h hu hv ((logical_transport _ _).mpr (by trivial)),
    singleton_edge h hv hw ((logical_transport _ _).mpr (by trivial)),
    singleton_edge h hu hw ((logical_transport _ _).mpr (by trivial))⟩

theorem minimum_thirteen (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : Alpha 16 12, Embedding targetEdges logicalEdges k A ∧ footprint A = 13 ∧
      ∀ k' (B : Alpha 16 12), Embedding targetEdges logicalEdges k' B → footprint A ≤ footprint B := by
  refine ⟨assignment,assignment_embedding_of_two_le k hk,assignment_footprint,?_⟩
  intro k' B hB
  rw [assignment_footprint]
  exact footprint_lower_bound k' B hB

end AppendixAIllustrativeMinimum
