module

public import AppendixAChimeraBridge

@[expose] public section

/-! Candidate data model for two aligned rows of two Chimera cells.
All 32 vertices are retained. The left cell in each row is contracted along
at most three selected sampled edges. This file states no branch-size theorem. -/
namespace AppendixAChimeraFour

open AppendixAChimera
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Phys4 := Bool × Phys

/-- The A shore in either of the two columns of one row. -/
def OnA : Phys → Prop
  | Sum.inl x => x.1 = false
  | Sum.inr x => x.1 = false

/-- Horizontal matching is inherited from `Hardware`; vertical matching
joins identical A vertices in the two rows, in both columns. -/
def Hardware4 (u v : Phys4) : Prop :=
  (u.1 = v.1 ∧ Hardware u.2 v.2) ∨
  (u.1 ≠ v.1 ∧ u.2 = v.2 ∧ OnA u.2)

structure Sample4 where
  H : Finset (Phys4 × Phys4)
  F : Bool → Finset (Cell × Cell)
  sampled_hardware : ∀ e ∈ H, Hardware4 e.1 e.2
  selected_canonical : ∀ r e, e ∈ F r → e.1.1 = false ∧ e.2.1 = true
  selected_card : ∀ r, (F r).card ≤ 3
  selected_sampled : ∀ r e, e ∈ F r → Adj H (r, first e.1) (r, first e.2)

theorem hardware4_symmetric : Symmetric Hardware4 := by
  rintro u v (⟨hr,h⟩ | ⟨hr,he,hA⟩)
  · exact Or.inl ⟨hr.symm, hardware_symmetric h⟩
  · exact Or.inr ⟨hr.symm, he.symm, he ▸ hA⟩

theorem hardware4_same_row_iff (r : Bool) (p q : Phys) :
    Hardware4 (r,p) (r,q) ↔ Hardware p q := by
  simp [Hardware4]

theorem hardware4_cross_row_iff {r s : Bool} (h : r ≠ s) (p q : Phys) :
    Hardware4 (r,p) (s,q) ↔ p = q ∧ OnA p := by
  simp [Hardware4,h]

theorem hardware4_irreflexive (u : Phys4) : ¬ Hardware4 u u := by
  rcases u with ⟨r,p⟩
  rw [hardware4_same_row_iff]
  cases p <;> simp [Hardware]

theorem sampled_hardware4 (D : Sample4) {u v : Phys4} (h : Adj D.H u v) :
    Hardware4 u v := by
  rcases h with h | h
  · exact D.sampled_hardware _ h
  · exact hardware4_symmetric (D.sampled_hardware _ h)

/-- The symmetric restriction of the actual sampled global graph to one row. -/
def rowEdges (D : Sample4) (r : Bool) : Finset (Phys × Phys) :=
  Finset.univ.filter (fun e => Adj D.H (r,e.1) (r,e.2))

theorem rowEdges_adj_iff (D : Sample4) (r : Bool) (p q : Phys) :
    Adj (rowEdges D r) p q ↔ Adj D.H (r,p) (r,q) := by
  change ((p,q) ∈ rowEdges D r ∨ (q,p) ∈ rowEdges D r) ↔ _
  simp only [rowEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun h => h.symm), Or.inl⟩

def rowSample (D : Sample4) (r : Bool) : Sample where
  U := Finset.univ
  H := rowEdges D r
  F := D.F r
  sampled_hardware := by
    intro e he
    have h : Adj D.H (r,e.1) (r,e.2) := (Finset.mem_filter.mp he).2
    exact (hardware4_same_row_iff r e.1 e.2).mp (sampled_hardware4 D h)
  sampled_active := by
    rintro ⟨p,q⟩ _
    constructor
    · cases p <;> simp [Active]
    · cases q <;> simp [Active]
  selected_sampled := by
    intro e he
    exact (rowEdges_adj_iff D r (first e.1) (first e.2)).mpr
      (D.selected_sampled r e he)
  selected_active := by simp

@[simp] theorem rowSample_U (D : Sample4) (r : Bool) :
    (rowSample D r).U = Finset.univ := rfl

@[simp] theorem rowSample_H (D : Sample4) (r : Bool) :
    (rowSample D r).H = rowEdges D r := rfl

@[simp] theorem rowSample_F (D : Sample4) (r : Bool) :
    (rowSample D r).F = D.F r := rfl

theorem rowSample_active (D : Sample4) (r : Bool) (p : Phys) :
    Active (rowSample D r).U p := by
  cases p <;> simp [Active]

theorem rowSample_selected_canonical (D : Sample4) (r : Bool)
    (e : Cell × Cell) (h : e ∈ (rowSample D r).F) :
    e.1.1 = false ∧ e.2.1 = true := D.selected_canonical r e h

theorem rowSample_selected_card (D : Sample4) (r : Bool) :
    (rowSample D r).F.card ≤ 3 := D.selected_card r

abbrev Label4 (D : Sample4) := (r : Bool) × Label (rowSample D r)

def rowLift (r : Bool) (p : Phys) : Phys4 := (r,p)

theorem rowLift_injective (r : Bool) : Function.Injective (rowLift r) := by
  intro p q h
  exact congrArg Prod.snd h

def originalLabel4 (D : Sample4) (u : Phys4) : Label4 D :=
  ⟨u.1, originalLabel (rowSample D u.1) u.2 (rowSample_active D u.1 u.2)⟩

def originalFiber4 (D : Sample4) (j : Label4 D) : Finset Phys4 :=
  (originalFiber (rowSample D j.1) j.2).image (rowLift j.1)

theorem originalLabel4_mem (D : Sample4) (u : Phys4) :
    u ∈ originalFiber4 D (originalLabel4 D u) := by
  exact Finset.mem_image.mpr ⟨u.2,
    originalLabel_mem (rowSample D u.1) u.2 (rowSample_active D u.1 u.2), rfl⟩

theorem originalFiber4_row (D : Sample4) {j : Label4 D} {u : Phys4}
    (h : u ∈ originalFiber4 D j) : u.1 = j.1 := by
  rcases Finset.mem_image.mp h with ⟨p,_,rfl⟩
  rfl

theorem originalFiber4_lift_mem_iff (D : Sample4) (r : Bool)
    (j : Label (rowSample D r)) (p : Phys) :
    rowLift r p ∈ originalFiber4 D ⟨r,j⟩ ↔ p ∈ originalFiber (rowSample D r) j := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨q,hq,he⟩
    exact (rowLift_injective r he) ▸ hq
  · intro h
    exact Finset.mem_image.mpr ⟨p,h,rfl⟩

theorem originalFiber4_exact_preimage (D : Sample4) (j : Label4 D) (u : Phys4) :
    u ∈ originalFiber4 D j ↔ originalLabel4 D u = j := by
  constructor
  · rcases j with ⟨r,j⟩
    intro h
    rcases Finset.mem_image.mp h with ⟨p,hp,rfl⟩
    have he : originalLabel (rowSample D r) p (rowSample_active D r p) = j :=
      originalFiber_unique (rowSample D r)
        (originalLabel_mem (rowSample D r) p (rowSample_active D r p)) hp
    exact congrArg (Sigma.mk r) he
  · intro h
    rw [← h]
    exact originalLabel4_mem D u

theorem originalFiber4_nonempty (D : Sample4) (j : Label4 D) :
    (originalFiber4 D j).Nonempty := by
  rcases originalFiber_nonempty (rowSample D j.1) j.2 with ⟨p,hp⟩
  exact ⟨rowLift j.1 p, Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩

theorem originalLabel4_surjective (D : Sample4) :
    Function.Surjective (originalLabel4 D) := by
  intro j
  rcases originalFiber4_nonempty D j with ⟨p,hp⟩
  exact ⟨p,(originalFiber4_exact_preimage D j p).mp hp⟩

theorem originalFiber4_unique (D : Sample4) {j l : Label4 D} {u : Phys4}
    (hj : u ∈ originalFiber4 D j) (hl : u ∈ originalFiber4 D l) : j = l :=
  ((originalFiber4_exact_preimage D j u).mp hj).symm.trans
    ((originalFiber4_exact_preimage D l u).mp hl)

/-- The actual quotient of the global sampled graph, including cross-row edges. -/
def QuotientAdj4 (D : Sample4) (j l : Label4 D) : Prop :=
  j ≠ l ∧ ∃ u ∈ originalFiber4 D j, ∃ v ∈ originalFiber4 D l, Adj D.H u v

theorem quotientAdj4_irreflexive (D : Sample4) (j : Label4 D) :
    ¬ QuotientAdj4 D j j := fun h => h.1 rfl

theorem quotientAdj4_symmetric (D : Sample4) : Symmetric (QuotientAdj4 D) := by
  rintro j l ⟨hne,u,hu,v,hv,h⟩
  exact ⟨hne.symm,v,hv,u,hu,h.symm⟩

theorem sampled_crossing_quotient4 (D : Sample4) {u v : Phys4}
    (h : Adj D.H u v) (hne : originalLabel4 D u ≠ originalLabel4 D v) :
    QuotientAdj4 D (originalLabel4 D u) (originalLabel4 D v) :=
  ⟨hne,u,originalLabel4_mem D u,v,originalLabel4_mem D v,h⟩

theorem quotientAdj4_same_row_iff (D : Sample4) (r : Bool)
    (j l : Label (rowSample D r)) :
    QuotientAdj4 D ⟨r,j⟩ ⟨r,l⟩ ↔ QuotientAdj (rowSample D r) j l := by
  constructor
  · rintro ⟨hne,u,hu,v,hv,h⟩
    rcases Finset.mem_image.mp hu with ⟨p,hp,rfl⟩
    rcases Finset.mem_image.mp hv with ⟨q,hq,rfl⟩
    exact ⟨fun he => hne (congrArg (Sigma.mk r) he),p,hp,q,hq,
      (rowEdges_adj_iff D r p q).mpr h⟩
  · rintro ⟨hne,p,hp,q,hq,h⟩
    refine ⟨?_,rowLift r p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      rowLift r q,Finset.mem_image.mpr ⟨q,hq,rfl⟩,?_⟩
    · intro he
      exact hne (eq_of_heq (Sigma.mk.inj_iff.mp he).2)
    · exact (rowEdges_adj_iff D r p q).mp h

/-- Nonvacuity of the data model, including retained isolated vertices. -/
def emptySample4 : Sample4 where
  H := ∅
  F := fun _ => ∅
  sampled_hardware := by simp
  selected_canonical := by simp
  selected_card := by simp
  selected_sampled := by simp

/-- Arbitrary finite equivalences: numeric vertices do not encode hand coordinates. -/
def physEquiv4 : Phys4 ≃ Fin 32 :=
  Fintype.equivFinOfCardEq (by simp [Phys4, Phys, Cell, Fintype.card_sum,
    Fintype.card_prod])

def logicalCount4 (D : Sample4) : ℕ := Fintype.card (Label4 D)

def labelEquiv4 (D : Sample4) : Label4 D ≃ Fin (logicalCount4 D) := Fintype.equivFin _

def targetEdges4 : Finset (Fin 32 × Fin 32) :=
  Finset.univ.filter (fun e => Hardware4 (physEquiv4.symm e.1) (physEquiv4.symm e.2))

def logicalEdges4 (D : Sample4) :
    Finset (Fin (logicalCount4 D) × Fin (logicalCount4 D)) :=
  Finset.univ.filter (fun e =>
    QuotientAdj4 D ((labelEquiv4 D).symm e.1) ((labelEquiv4 D).symm e.2))

theorem target_adjacent4_iff (a b : Fin 32) :
    AppendixA.adjacent targetEdges4 a b ↔
      Hardware4 (physEquiv4.symm a) (physEquiv4.symm b) := by
  simp only [AppendixA.adjacent, targetEdges4, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun h => hardware4_symmetric h), Or.inl⟩

theorem hardware4_transport (u v : Phys4) :
    AppendixA.adjacent targetEdges4 (physEquiv4 u) (physEquiv4 v) ↔ Hardware4 u v := by
  simpa using target_adjacent4_iff (physEquiv4 u) (physEquiv4 v)

theorem logical_adjacent4_iff (D : Sample4) (j l : Fin (logicalCount4 D)) :
    AppendixA.adjacent (logicalEdges4 D) j l ↔
      QuotientAdj4 D ((labelEquiv4 D).symm j) ((labelEquiv4 D).symm l) := by
  simp only [AppendixA.adjacent, logicalEdges4, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun h => quotientAdj4_symmetric D h), Or.inl⟩

theorem logical4_transport (D : Sample4) (j l : Label4 D) :
    AppendixA.adjacent (logicalEdges4 D) (labelEquiv4 D j) (labelEquiv4 D l) ↔
      QuotientAdj4 D j l := by
  simpa using logical_adjacent4_iff D (labelEquiv4 D j) (labelEquiv4 D l)

theorem logicalEdges4_loopFree (D : Sample4) :
    AppendixATheory.LoopFree (logicalEdges4 D) := by
  intro j h
  exact ((logical_adjacent4_iff D j j).mp h).1 rfl

theorem targetEdges4_loopFree : AppendixATheory.LoopFree targetEdges4 := by
  intro u h
  exact hardware4_irreflexive _ ((target_adjacent4_iff u u).mp h)

end
end AppendixAChimeraFour

-- Bounded diagnostics: every explicit declaration in this candidate module.
#print axioms AppendixAChimeraFour.Phys4
#print axioms AppendixAChimeraFour.OnA
#print axioms AppendixAChimeraFour.Hardware4
#print axioms AppendixAChimeraFour.Sample4
#print axioms AppendixAChimeraFour.hardware4_symmetric
#print axioms AppendixAChimeraFour.hardware4_same_row_iff
#print axioms AppendixAChimeraFour.hardware4_cross_row_iff
#print axioms AppendixAChimeraFour.hardware4_irreflexive
#print axioms AppendixAChimeraFour.sampled_hardware4
#print axioms AppendixAChimeraFour.rowEdges
#print axioms AppendixAChimeraFour.rowEdges_adj_iff
#print axioms AppendixAChimeraFour.rowSample
#print axioms AppendixAChimeraFour.rowSample_U
#print axioms AppendixAChimeraFour.rowSample_H
#print axioms AppendixAChimeraFour.rowSample_F
#print axioms AppendixAChimeraFour.rowSample_active
#print axioms AppendixAChimeraFour.rowSample_selected_canonical
#print axioms AppendixAChimeraFour.rowSample_selected_card
#print axioms AppendixAChimeraFour.Label4
#print axioms AppendixAChimeraFour.rowLift
#print axioms AppendixAChimeraFour.rowLift_injective
#print axioms AppendixAChimeraFour.originalLabel4
#print axioms AppendixAChimeraFour.originalFiber4
#print axioms AppendixAChimeraFour.originalLabel4_mem
#print axioms AppendixAChimeraFour.originalFiber4_row
#print axioms AppendixAChimeraFour.originalFiber4_lift_mem_iff
#print axioms AppendixAChimeraFour.originalFiber4_exact_preimage
#print axioms AppendixAChimeraFour.originalFiber4_nonempty
#print axioms AppendixAChimeraFour.originalLabel4_surjective
#print axioms AppendixAChimeraFour.originalFiber4_unique
#print axioms AppendixAChimeraFour.QuotientAdj4
#print axioms AppendixAChimeraFour.quotientAdj4_irreflexive
#print axioms AppendixAChimeraFour.quotientAdj4_symmetric
#print axioms AppendixAChimeraFour.sampled_crossing_quotient4
#print axioms AppendixAChimeraFour.quotientAdj4_same_row_iff
#print axioms AppendixAChimeraFour.emptySample4
#print axioms AppendixAChimeraFour.physEquiv4
#print axioms AppendixAChimeraFour.logicalCount4
#print axioms AppendixAChimeraFour.labelEquiv4
#print axioms AppendixAChimeraFour.targetEdges4
#print axioms AppendixAChimeraFour.logicalEdges4
#print axioms AppendixAChimeraFour.target_adjacent4_iff
#print axioms AppendixAChimeraFour.hardware4_transport
#print axioms AppendixAChimeraFour.logical_adjacent4_iff
#print axioms AppendixAChimeraFour.logical4_transport
#print axioms AppendixAChimeraFour.logicalEdges4_loopFree
#print axioms AppendixAChimeraFour.targetEdges4_loopFree
