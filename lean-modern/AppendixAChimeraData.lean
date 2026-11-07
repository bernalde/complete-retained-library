module

public import AppendixAAssignment
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Relation

@[expose] public section

/-! Explicit sampled two-cell graph and its selected-edge quotient.
The full hardware target, sampled edges, selected edges, active labels, and
constructed branch sets are distinct. No contraction-count or cap premise. -/
noncomputable section
open scoped BigOperators
namespace AppendixAChimera
attribute [local instance] Classical.propDecidable

abbrev Cell := Bool × Fin 4
abbrev Phys := Cell ⊕ Cell
abbrev first (x : Cell) : Phys := Sum.inl x
abbrev second (x : Cell) : Phys := Sum.inr x

def Hardware : Phys → Phys → Prop
  | .inl x, .inl y => x.1 ≠ y.1
  | .inr x, .inr y => x.1 ≠ y.1
  | .inl x, .inr y => x.1 = true ∧ x = y
  | .inr x, .inl y => y.1 = true ∧ y = x

def Adj {V : Type*} (E : Finset (V × V)) (x y : V) : Prop :=
  (x,y) ∈ E ∨ (y,x) ∈ E

def Active (U : Finset Cell) : Phys → Prop
  | .inl x => x ∈ U
  | .inr _ => True

structure Sample where
  U : Finset Cell
  H : Finset (Phys × Phys)
  F : Finset (Cell × Cell)
  sampled_hardware : ∀ e ∈ H, Hardware e.1 e.2
  sampled_active : ∀ e ∈ H, Active U e.1 ∧ Active U e.2
  selected_sampled : ∀ e ∈ F, Adj H (first e.1) (first e.2)
  selected_active : ∀ e ∈ F, e.1 ∈ U ∧ e.2 ∈ U

def component (D : Sample) (x : Cell) : Finset Cell :=
  D.U.filter (fun y => Relation.ReflTransGen (Adj D.F) x y)

def Component (D : Sample) :=
  {C : Finset Cell // ∃ x ∈ D.U, C = component D x}

instance (D : Sample) : Fintype (Component D) := by
  unfold Component
  infer_instance

abbrev Label (D : Sample) := Component D ⊕ Cell

def componentLabel (D : Sample) (x : Cell) (hx : x ∈ D.U) : Component D :=
  ⟨component D x, x, hx, rfl⟩

def originalLabel (D : Sample) (p : Phys) (hp : Active D.U p) : Label D :=
  match p with
  | .inl x => .inl (componentLabel D x hp)
  | .inr x => .inr x

def originalFiber (D : Sample) : Label D → Finset Phys
  | .inl C => C.val.image first
  | .inr x => {second x}

def QuotientAdj (D : Sample) (j l : Label D) : Prop :=
  j ≠ l ∧ ∃ u ∈ originalFiber D j, ∃ v ∈ originalFiber D l, Adj D.H u v

theorem component_nonempty (D : Sample) (C : Component D) : C.val.Nonempty := by
  rcases C.property with ⟨x, hx, hC⟩
  refine ⟨x, ?_⟩
  rw [hC]
  exact Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩

def pick (D : Sample) (C : Component D) (s : Bool) : Cell :=
  if h : ∃ x ∈ C.val, x.1 = s then Classical.choose h
  else Classical.choose (component_nonempty D C)

def kept (D : Sample) (C : Component D) : Finset Cell :=
  {pick D C false, pick D C true}

def OmittedB (D : Sample) (x : Cell) : Prop :=
  x.1 = true ∧ ∃ C : Component D, x ∈ C.val ∧ x ∉ kept D C

def branch (D : Sample) : Label D → Finset Phys
  | .inl C => (kept D C).image first
  | .inr x => if OmittedB D x then {second x, first x} else {second x}

def physEquiv : Phys ≃ Fin 16 :=
  Fintype.equivFinOfCardEq (by simp [Phys, Cell, Fintype.card_sum, Fintype.card_prod])

def logicalCount (D : Sample) : ℕ := Fintype.card (Label D)

def labelEquiv (D : Sample) : Label D ≃ Fin (logicalCount D) := Fintype.equivFin _

def targetEdges : Finset (Fin 16 × Fin 16) :=
  Finset.univ.filter (fun e => Hardware (physEquiv.symm e.1) (physEquiv.symm e.2))

def logicalEdges (D : Sample) : Finset (Fin (logicalCount D) × Fin (logicalCount D)) :=
  Finset.univ.filter (fun e => QuotientAdj D ((labelEquiv D).symm e.1) ((labelEquiv D).symm e.2))

def finiteBranches (D : Sample) (j : Fin (logicalCount D)) : Finset (Fin 16) :=
  (branch D ((labelEquiv D).symm j)).image physEquiv

end AppendixAChimera

#print axioms AppendixAChimera.component_nonempty
