module

public import AppendixAChimeraConstruction

@[expose] public section

/-! Uncompiled symbolic controls. The physical sample is the hardware induced
by a proper active domain. No concrete value of Classical.choose is assumed. -/
noncomputable section

namespace AppendixAChimeraConstruction.Controls

open AppendixAChimera AppendixAChimeraFour

attribute [local instance] Classical.propDecidable

def starIndices : Finset (Fin 4 × Fin 4) := {(0, 0), (1, 0), (2, 0)}
def starA : Finset Cell := {(false, 0), (false, 1), (false, 2)}

def available : Phys → Prop
  | .inl x => x ≠ (false, 3)
  | .inr x => x ≠ (false, 3)

def partialU : Finset Phys4 := Finset.univ.filter (fun u => available u.2)

set_option backward.isDefEq.respectTransparency false in
theorem partialU_cellPoint (p : Position) (x : Cell) :
    cellPoint p x ∈ partialU ↔ x ≠ (false, 3) := by
  rcases p with ⟨r, c⟩
  cases c <;> simp [partialU, available, cellPoint]

def sampledH : Finset (Phys4 × Phys4) :=
  Finset.univ.filter (fun e => e.1 ∈ partialU ∧ e.2 ∈ partialU ∧ Hardware4 e.1 e.2)

theorem sampledH_adj {u v : Phys4} (hu : u ∈ partialU) (hv : v ∈ partialU)
    (h : Hardware4 u v) : Adj sampledH u v :=
  Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hv, h⟩)

def selections (p q : Position) (b c : Bool) (t : Position) :
    Finset (Fin 4 × Fin 4) :=
  if (b = true ∧ t = p) ∨ (c = true ∧ t = q) then starIndices else ∅

theorem selections_subset (p q : Position) (b c : Bool) (t : Position) :
    selections p q b c t ⊆ starIndices := by
  intro e he
  unfold selections at he
  split_ifs at he with h
  · exact he
  · simp at he

theorem star_endpoints_available (e : Fin 4 × Fin 4) (he : e ∈ starIndices) :
    (false, e.1) ≠ (false, (3 : Fin 4)) ∧
      (true, e.2) ≠ (false, (3 : Fin 4)) := by
  simp only [starIndices, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> norm_num [Fin.ext_iff] <;> decide

def placement (p q : Position) (hne : p ≠ q) (b c : Bool) : PlacementSample where
  U := partialU
  H := sampledH
  donor₁ := p
  donor₂ := q
  distinct := hne
  F := selections p q b c
  supported := by
    intro t hp hq
    simp [selections, hp, hq]
  selected_card := by
    intro t
    exact (Finset.card_le_card (selections_subset p q b c t)).trans
      (by norm_num [starIndices,Finset.card_insert_eq_ite,Fin.ext_iff,Prod.ext_iff])
  sampled_hardware := by
    intro e he
    exact (Finset.mem_filter.mp he).2.2.2
  sampled_active := by
    intro e he
    exact ⟨(Finset.mem_filter.mp he).2.1, (Finset.mem_filter.mp he).2.2.1⟩
  selected_sampled := by
    intro t e he
    have ha := star_endpoints_available e (selections_subset p q b c t he)
    apply sampledH_adj
    · exact (partialU_cellPoint t _).mpr ha.1
    · exact (partialU_cellPoint t _).mpr ha.2
    · rcases t with ⟨r, d⟩
      cases d <;> simp [cellPoint, Hardware4, Hardware]

def zeroAdjacent : PlacementSample :=
  placement (false, false) (true, false) (by simp) false false

def adjacentOne : PlacementSample :=
  placement (false, false) (true, false) (by simp) true false

def adjacentBoth : PlacementSample :=
  placement (false, false) (true, false) (by simp) true true

def diagonalOne : PlacementSample :=
  placement (false, false) (true, true) (by simp) true false

def diagonalBoth : PlacementSample :=
  placement (false, false) (true, true) (by simp) true true

theorem zero_no_selected_edges (p : Position) : zeroAdjacent.F p = ∅ := by
  simp [zeroAdjacent, placement, selections]

theorem adjacent_one_selected :
    adjacentOne.F (false, false) = starIndices ∧ adjacentOne.F (true, false) = ∅ := by
  simp [adjacentOne, placement, selections]

theorem adjacent_both_selected (r : Bool) : adjacentBoth.F (r, false) = starIndices := by
  cases r <;> simp [adjacentBoth, placement, selections]

theorem diagonal_one_selected :
    diagonalOne.F (false, false) = starIndices ∧ diagonalOne.F (true, true) = ∅ := by
  simp [diagonalOne, placement, selections]

theorem diagonal_both_selected (r : Bool) : diagonalBoth.F (r, r) = starIndices := by
  cases r <;> simp [diagonalBoth, placement, selections]

theorem selected_star_has_three_edges : starIndices.card = 3 := by
  norm_num [starIndices,Finset.card_insert_eq_ite,Fin.ext_iff,Prod.ext_iff]

theorem partial_domain_is_proper (p : Position) :
    cellPoint p (false, 3) ∉ diagonalBoth.U ∧
      cellPoint p (true, 3) ∈ diagonalBoth.U := by
  change cellPoint p (false, 3) ∉ partialU ∧ cellPoint p (true, 3) ∈ partialU
  simp [partialU_cellPoint]

theorem adjacent_actual_intercell_edge :
    Adj adjacentBoth.H (cellPoint (false, false) (false, 0))
      (cellPoint (true, false) (false, 0)) := by
  apply sampledH_adj
  · norm_num [partialU_cellPoint,Fin.ext_iff] <;> decide
  · norm_num [partialU_cellPoint,Fin.ext_iff] <;> decide
  · simp [cellPoint, Hardware4, OnA]

def localStar : Finset (Cell × Cell) :=
  starIndices.image (fun e => ((false, e.1), (true, e.2)))

theorem diagLift_first_cellPoint (r : Bool) (x : Cell) :
    diagLift r (first x) = cellPoint (r, r) x := by
  cases r <;> rfl

theorem partialU_diagLift_first (r : Bool) (x : Cell) :
    diagLift r (first x) ∈ partialU ↔ x ≠ (false, 3) := by
  rw [diagLift_first_cellPoint, partialU_cellPoint]

set_option backward.isDefEq.respectTransparency false in
theorem partialU_diagLift_second (r : Bool) (x : Cell) :
    diagLift r (second x) ∈ partialU ↔ x ≠ (false, 3) := by
  cases r <;> simp [diagLift, orient, swapCell, partialU, available]

/-- Actual global sampled edges restricted to an oriented row. Inactive local
vertices are retained as isolated full-domain labels for this branch control. -/
def diagonalRows (r : Bool) : Sample where
  U := Finset.univ
  H := Finset.univ.filter (fun e =>
    Adj diagonalBoth.H (diagLift r e.1) (diagLift r e.2))
  F := localStar
  sampled_hardware := by
    intro e he
    have h := (Finset.mem_filter.mp he).2
    apply (diagLift_hardware r e.1 e.2).mp
    rcases h with h | h
    · exact diagonalBoth.sampled_hardware _ h
    · exact hardware4_symmetric (diagonalBoth.sampled_hardware _ h)
  sampled_active := by
    rintro ⟨p, q⟩ _
    constructor
    · cases p <;> simp [Active]
    · cases q <;> simp [Active]
  selected_sampled := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨f, hf, rfl⟩
    have hF : f ∈ diagonalBoth.F (r, r) := by
      rw [diagonal_both_selected]
      exact hf
    have h := diagonalBoth.selected_sampled (r, r) f hF
    exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [diagLift_first_cellPoint] using h⟩)
  selected_active := by simp

theorem diagonalRows_actual_edges (r : Bool) (p q : Phys) :
    Adj (diagonalRows r).H p q ↔
      Adj diagonalBoth.H (diagLift r p) (diagLift r q) := by
  change ((p, q) ∈ (diagonalRows r).H ∨ (q, p) ∈ (diagonalRows r).H) ↔ _
  simp only [diagonalRows, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun h => h.symm), Or.inl⟩

def starComponent (r : Bool) : Component (diagonalRows r) :=
  componentLabel (diagonalRows r) (true, 0) (by simp [diagonalRows])

theorem starA_card : starA.card = 3 := by norm_num [starA,Finset.card_insert_eq_ite,Fin.ext_iff]

theorem starA_shore {x : Cell} (hx : x ∈ starA) : x.1 = false := by
  simp only [starA, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem starA_available {x : Cell} (hx : x ∈ starA) : x ≠ (false, 3) := by
  simp only [starA, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> norm_num [Fin.ext_iff] <;> decide

theorem starA_selected {x : Cell} (hx : x ∈ starA) :
    (x, (true, 0)) ∈ localStar := by
  simp only [starA, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨(0, 0), by simp [starIndices], rfl⟩
  · exact Finset.mem_image.mpr ⟨(1, 0), by simp [starIndices], rfl⟩
  · exact Finset.mem_image.mpr ⟨(2, 0), by simp [starIndices], rfl⟩

theorem starA_in_component (r : Bool) {x : Cell} (hx : x ∈ starA) :
    x ∈ (starComponent r).val := by
  change x ∈ component (diagonalRows r) (true, 0)
  refine Finset.mem_filter.mpr ⟨by simp [diagonalRows], ?_⟩
  exact Relation.ReflTransGen.single (Or.inr (starA_selected hx))

/-- Cardinality forces an actual omitted A; the chosen representative is never
identified with a particular index. -/
theorem some_star_A_omitted (r : Bool) :
    ∃ x ∈ starA, x ∉ kept (diagonalRows r) (starComponent r) := by
  by_contra h
  have hsub : starA ⊆ kept (diagonalRows r) (starComponent r) := by
    intro x hx
    by_contra hn
    exact h ⟨x, hx, hn⟩
  have hle := Finset.card_le_card hsub
  have hcap : (kept (diagonalRows r) (starComponent r)).card ≤ 2 := by
    unfold kept
    exact (Finset.card_insert_le _ _).trans (by simp)
  rw [starA_card] at hle
  omega

theorem actual_omitted_A_vertical_transfer (r : Bool) :
    ∃ x ∈ starA,
      OmittedA (diagonalRows r) x ∧
      diagLift r (first x) ∉ diagBranch diagonalRows ⟨r, .inl (starComponent r)⟩ ∧
      diagLift r (first x) ∈ diagBranch diagonalRows ⟨!r, .inr x⟩ ∧
      diagLift (!r) (second x) ∈ diagBranch diagonalRows ⟨!r, .inr x⟩ ∧
      diagLift r (first x) ≠ diagLift (!r) (second x) ∧
      Hardware4 (diagLift r (first x)) (diagLift (!r) (second x)) ∧
      Adj diagonalBoth.H (diagLift r (first x)) (diagLift (!r) (second x)) := by
  rcases some_star_A_omitted r with ⟨x, hx, ho⟩
  have hs := starA_shore hx
  have ha : OmittedA (diagonalRows r) x :=
    ⟨hs, starComponent r, starA_in_component r hx, ho⟩
  have hw : Hardware4 (diagLift r (first x)) (diagLift (!r) (second x)) := by
    simpa using hardware4_symmetric (diagLift_vertical (!r) x hs)
  refine ⟨x, hx, ha, ?_, ?_, diagBranch_second_mem diagonalRows (!r) x, ?_, hw, ?_⟩
  · intro hm
    rcases (diagBranch_left_mem diagonalRows r (starComponent r) _).mp hm with
      ⟨y, hy, he⟩
    have heq : y = x := Sum.inl.inj (diagLift_injective r he)
    exact ho (heq ▸ hy)
  · apply (diagBranch_right_mem diagonalRows (!r) x _).mpr
    apply Or.inr
    apply Or.inr
    simpa using (show OmittedA (diagonalRows r) x ∧
      diagLift r (first x) = diagLift r (first x) from ⟨ha, rfl⟩)
  · intro he
    have hr := diagLift_row he
    cases r <;> simp at hr
  · change Adj sampledH _ _
    exact sampledH_adj ((partialU_diagLift_first r x).mpr (starA_available hx))
      ((partialU_diagLift_second (!r) x).mpr (starA_available hx)) hw

theorem adjacent_partial_embedding :
    ∃ A : AppendixATheory.Alpha 32 adjacentBoth.activeData.count,
      AppendixATheory.Embedding targetEdges4 adjacentBoth.activeData.logicalEdges 3 A :=
  exists_anyPlacement_active_embedding adjacentBoth

theorem diagonal_partial_embedding :
    ∃ A : AppendixATheory.Alpha 32 diagonalBoth.activeData.count,
      AppendixATheory.Embedding targetEdges4 diagonalBoth.activeData.logicalEdges 3 A :=
  exists_anyPlacement_active_embedding diagonalBoth

theorem zero_selected : zeroAdjacent.selected = ∅ := by
  ext e
  simp [PlacementSample.selected, zero_no_selected_edges]

theorem zero_component_singleton (x : Phys4) (hx : x ∈ zeroAdjacent.U) :
    zeroAdjacent.activeData.component x = {x} := by
  ext y
  simp only [ActiveData.component, Finset.mem_filter]
  change (y ∈ zeroAdjacent.U ∧ Relation.ReflTransGen (Adj zeroAdjacent.selected) x y) ↔
    y ∈ ({x} : Finset Phys4)
  constructor
  · rintro ⟨_, hr⟩
    rcases hr.cases_head with heq | ⟨z, hz, _⟩
    · exact Finset.mem_singleton.mpr heq.symm
    · simp [zero_selected, Adj] at hz
  · intro hy
    have heq := Finset.mem_singleton.mp hy
    subst y
    exact ⟨hx, Relation.ReflTransGen.refl⟩

def retainedPoint : Phys4 := cellPoint (false, false) (true, 0)
def deletedPoint : Phys4 := cellPoint (false, false) (false, 0)

theorem retainedPoint_active : retainedPoint ∈ zeroAdjacent.U := by
  change cellPoint (false, false) (true, 0) ∈ partialU
  simp [partialU_cellPoint]

theorem deletedPoint_active : deletedPoint ∈ zeroAdjacent.U := by
  change cellPoint (false, false) (false, 0) ∈ partialU
  norm_num [partialU_cellPoint,Fin.ext_iff] <;> decide

def retainedLabel : zeroAdjacent.activeData.Label :=
  zeroAdjacent.activeData.originalLabel retainedPoint retainedPoint_active

def deletedLabel : zeroAdjacent.activeData.Label :=
  zeroAdjacent.activeData.originalLabel deletedPoint deletedPoint_active

theorem retained_deleted_distinct : retainedLabel ≠ deletedLabel := by
  intro h
  have he := congrArg Subtype.val h
  change zeroAdjacent.activeData.component retainedPoint =
    zeroAdjacent.activeData.component deletedPoint at he
  have hm : retainedPoint ∈ zeroAdjacent.activeData.component deletedPoint := by
    rw [← he]
    exact zeroAdjacent.activeData.originalLabel_mem retainedPoint retainedPoint_active
  rw [zero_component_singleton deletedPoint deletedPoint_active] at hm
  have heq := Finset.mem_singleton.mp hm
  norm_num [retainedPoint, deletedPoint, cellPoint] at heq

theorem retained_deleted_sampled : Adj zeroAdjacent.H retainedPoint deletedPoint := by
  apply sampledH_adj retainedPoint_active deletedPoint_active
  simp [retainedPoint, deletedPoint, cellPoint, Hardware4, Hardware]

theorem retained_deleted_quotient_edge :
    zeroAdjacent.activeData.QuotientAdj retainedLabel deletedLabel := by
  refine ⟨retained_deleted_distinct, retainedPoint, ?_, deletedPoint, ?_, retained_deleted_sampled⟩
  · exact zeroAdjacent.activeData.originalLabel_mem retainedPoint retainedPoint_active
  · exact zeroAdjacent.activeData.originalLabel_mem deletedPoint deletedPoint_active

def singletonMap : Fin 1 → Fin zeroAdjacent.activeData.count :=
  fun _ => zeroAdjacent.activeData.labelEquiv retainedLabel

theorem singletonMap_injective : Function.Injective singletonMap := by
  intro a b _
  exact Subsingleton.elim a b

theorem singletonMap_not_surjective : ¬ Function.Surjective singletonMap := by
  intro h
  rcases h (zeroAdjacent.activeData.labelEquiv deletedLabel) with ⟨i, hi⟩
  exact retained_deleted_distinct (zeroAdjacent.activeData.labelEquiv.injective hi)

/-- One actual quotient vertex is retained and another actual vertex is deleted.
This invokes the final restriction endpoint, not a supplied successful model. -/
theorem proper_singleton_logical_restriction :
    Function.Injective singletonMap ∧ ¬ Function.Surjective singletonMap ∧
      zeroAdjacent.activeData.QuotientAdj retainedLabel deletedLabel ∧
      ∃ A : AppendixATheory.Alpha 32 1,
        AppendixATheory.Embedding targetEdges4 (∅ : Finset (Fin 1 × Fin 1)) 3 A := by
  refine ⟨singletonMap_injective, singletonMap_not_surjective, retained_deleted_quotient_edge, ?_⟩
  apply anyPlacement_logical_restriction zeroAdjacent ∅ singletonMap singletonMap_injective
  intro j l h
  simp [AppendixA.adjacent] at h

end AppendixAChimeraConstruction.Controls

/-! Author fragment to merge into the single supporting controls module before
its first successful build. Not a separate compiler input. -/
namespace AppendixAChimeraConstruction
open AppendixAChimera AppendixAChimeraFour
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ActiveData
variable {V : Type*} [Fintype V] {R : V → V → Prop}

theorem selected_endpoints_active (D : ActiveData V R) {x y : V} (h : Adj D.S x y) :
    x ∈ D.U ∧ y ∈ D.U := h.elim (D.selected_active _) (fun h => (D.selected_active _ h).symm)

theorem selected_reach_active (D : ActiveData V R) {x y : V} (hx : x ∈ D.U)
    (h : Relation.ReflTransGen (Adj D.S) x y) : y ∈ D.U := by
  induction h with
  | refl => exact hx
  | @tail b c hab hbc ih => exact (D.selected_endpoints_active hbc).2

theorem inactive_reach_eq (D : ActiveData V R) {x y : V} (hx : x ∉ D.U)
    (h : Relation.ReflTransGen (Adj D.S) x y) : y = x := by
  rcases h.cases_head with h | ⟨z,hxz,_⟩
  · exact h.symm
  · exact (hx (D.selected_endpoints_active hxz).1).elim

def complete (D : ActiveData V R) : ActiveData V R :=
  {D with U := Finset.univ, sampled_active := by simp, selected_active := by simp}

set_option backward.isDefEq.respectTransparency false in
theorem completion_component_active (D : ActiveData V R) {x : V} (hx : x ∈ D.U) :
    D.complete.component x = D.component x := by
  ext y
  simp only [component,complete,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => ⟨D.selected_reach_active hx h,h⟩,And.right⟩

set_option backward.isDefEq.respectTransparency false in
theorem completion_component_inactive (D : ActiveData V R) {x : V} (hx : x ∉ D.U) :
    D.complete.component x = {x} := by
  ext y
  simp only [component,complete,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  exact ⟨D.inactive_reach_eq hx,fun h => h ▸ Relation.ReflTransGen.refl⟩

theorem originalLabel_eq_iff_reach (D : ActiveData V R) (x y : V)
    (hx : x ∈ D.U) (hy : y ∈ D.U) :
    D.originalLabel x hx = D.originalLabel y hy ↔ Relation.ReflTransGen (Adj D.S) x y := by
  constructor
  · intro h
    have he := congrArg Subtype.val h
    change D.component x = D.component y at he
    have hy' : y ∈ D.component x := by rw [he]; exact D.originalLabel_mem y hy
    exact (Finset.mem_filter.mp hy').2
  · intro h
    exact Subtype.ext (D.component_eq_of_reach h)

def completionInjection (D : ActiveData V R) (C : D.Label) : D.complete.Label :=
  ⟨C.val, D.repr C,Finset.mem_univ _,(D.component_eq_at C (D.repr_mem C)).trans
    (D.completion_component_active (D.component_active C (D.repr_mem C))).symm⟩

theorem completionInjection_injective (D : ActiveData V R) :
    Function.Injective D.completionInjection := by
  intro C K h
  have he := congrArg (fun c : D.complete.Label => c.val) h
  exact Subtype.ext he

theorem completionInjection_adjacent (D : ActiveData V R) {C K : D.Label}
    (h : D.QuotientAdj C K) : D.complete.QuotientAdj (D.completionInjection C) (D.completionInjection K) :=
  ⟨fun he => h.1 (D.completionInjection_injective he),h.2⟩

end ActiveData

namespace Controls

def emptyActive : PlacementSample where
  U := ∅
  H := ∅
  donor₁ := (false,false)
  donor₂ := (true,true)
  distinct := by decide
  F := fun _ => ∅
  supported := by simp
  selected_card := by simp
  sampled_hardware := by simp
  sampled_active := by simp
  selected_sampled := by simp

theorem emptyActive_no_labels : IsEmpty emptyActive.activeData.Label := by
  constructor
  intro C
  rcases emptyActive.activeData.component_nonempty C with ⟨x,hx⟩
  have := emptyActive.activeData.component_active C hx
  simp [emptyActive,PlacementSample.activeData] at this

theorem emptyActive_embedding :
    ∃ A : AppendixATheory.Alpha 32 emptyActive.activeData.count,
      AppendixATheory.Embedding targetEdges4 emptyActive.activeData.logicalEdges 3 A :=
  exists_anyPlacement_active_embedding emptyActive

def isolatedActive : PlacementSample :=
  {emptyActive with U := {cellPoint (false,true) (false,3)}, sampled_active := by simp [emptyActive]}

theorem isolatedActive_retained :
    ∃ C : isolatedActive.activeData.Label,
      cellPoint (false,true) (false,3) ∈ C.val := by
  have hx : cellPoint (false,true) (false,3) ∈ isolatedActive.activeData.U := by
    simp [isolatedActive,PlacementSample.activeData]
  exact ⟨isolatedActive.activeData.originalLabel _ hx,isolatedActive.activeData.originalLabel_mem _ hx⟩

theorem isolatedActive_has_no_sampled_edge (u v : Phys4) :
    ¬ Adj isolatedActive.H u v := by simp [isolatedActive,emptyActive,Adj]

theorem identity_restriction (D : PlacementSample) :
    ∃ A : AppendixATheory.Alpha 32 D.activeData.count,
      AppendixATheory.Embedding targetEdges4 D.activeData.logicalEdges 3 A :=
  anyPlacement_logical_restriction D D.activeData.logicalEdges id Function.injective_id
    (fun _ _ h => h)

end Controls
end
end AppendixAChimeraConstruction
