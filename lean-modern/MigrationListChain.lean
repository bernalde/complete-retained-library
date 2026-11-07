/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
LegacyChain/legacyChain' adapt Batteries.Data.List.Basic, authored by Leonardo de Moura.
Those copied definitions are released under Apache 2.0; see LICENSES/Batteries-Apache-2.0.txt.
The compatibility proofs add no thesis claim or archive-wide license grant.
-/
module

public import Mathlib.Data.List.Chain

/-! Compatibility evidence for the retired Batteries `List.Chain'` predicate.
`LegacyChain` and `legacyChain'` copy its old inductive/empty-list semantics,
with fresh names only. Their exact definitions are pinned in PROJECT-S225.
The bridge covers every type, relation and list, including empty lists.
It adds no thesis claim or proof credit. -/
@[expose] public section

universe u v
namespace MigrationListChain
variable {α : Type u}

inductive LegacyChain (R : α → α → Prop) : α → List α → Prop where
  | nil {a : α} : LegacyChain R a []
  | cons {a b : α} {l : List α} : R a b → LegacyChain R b l → LegacyChain R a (b :: l)

def legacyChain' (R : α → α → Prop) : List α → Prop
  | [] => True
  | a :: l => LegacyChain R a l

theorem legacyChain_iff_isChain_cons (R : α → α → Prop) (a : α) (l : List α) :
    LegacyChain R a l ↔ List.IsChain R (a :: l) := by
  induction l generalizing a with
  | nil => exact ⟨fun _ => .singleton a, fun _ => .nil⟩
  | cons b l ih =>
    constructor
    · intro h
      cases h with
      | cons hab hbl => exact .cons_cons hab ((ih b).mp hbl)
    · intro h
      cases h with
      | cons_cons hab hbl => exact .cons hab ((ih b).mpr hbl)

theorem legacyChain'_iff_isChain (R : α → α → Prop) (l : List α) :
    legacyChain' R l ↔ List.IsChain R l := by
  cases l with
  | nil => exact ⟨fun _ => .nil, fun _ => trivial⟩
  | cons a l => exact legacyChain_iff_isChain_cons R a l

/-- Preserve the old implicit-endpoint `ReflTransGen.lift` interface.
The modern theorem states the same relation inclusion with explicit endpoints. -/
theorem reflTransGen_lift {β : Type v} {r : α → α → Prop} {p : β → β → Prop}
    {a b : α} (f : α → β) (h : ∀ a b, r a b → p (f a) (f b))
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p (f a) (f b) :=
  Relation.ReflTransGen.lift f h a b hab

end MigrationListChain
