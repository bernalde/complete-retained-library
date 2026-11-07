module

public import AppendixA

@[expose] public section

/-! Shared actual finite graph model. Auxiliary IP projections are separate.
No completeness, connectivity, or solver correctness premise is hidden here. -/
noncomputable section
open scoped BigOperators
namespace AppendixATheory

abbrev Alpha (n m : ℕ) := Fin n → Fin m → Bool

def fiber {n m : ℕ} (A : Alpha n m) (j : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => A i j = true)

@[simp] theorem mem_fiber {n m : ℕ} (A : Alpha n m) (i : Fin n) (j : Fin m) :
    i ∈ fiber A j ↔ A i j = true := by simp [fiber]

def RowBounds {n m : ℕ} (k : ℕ) (A : Alpha n m) : Prop :=
  (∀ i, (Finset.univ.filter (fun j => A i j = true)).card ≤ 1) ∧
  ∀ j, (fiber A j).Nonempty ∧ (fiber A j).card ≤ k

def EdgeCoverage {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) : Prop :=
  ∀ j l, AppendixA.adjacent L j l →
    ∃ a ∈ fiber A j, ∃ b ∈ fiber A l, AppendixA.adjacent E a b

def NeighborRows {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m) : Prop :=
  ∀ j, 1 < (fiber A j).card → ∀ a ∈ fiber A j,
    ∃ b ∈ fiber A j, AppendixA.adjacent E a b

def RelaxedMaster {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) : Prop :=
  RowBounds k A ∧ EdgeCoverage E L A ∧ NeighborRows E A

def Embedding {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) : Prop :=
  RowBounds k A ∧ EdgeCoverage E L A ∧
    ∀ j, AppendixA.connected E (fiber A j)

def footprint {n m : ℕ} (A : Alpha n m) : ℕ :=
  (Finset.univ.filter (fun i => ∃ j, A i j = true)).card

def LoopFree {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∀ a, ¬ AppendixA.adjacent E a a

theorem reach_last_neighbor {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) {a b : Fin n}
    (h : Relation.ReflTransGen (AppendixA.fiberStep E S) a b) (hne : a ≠ b) :
    ∃ c ∈ S, AppendixA.adjacent E b c := by
  induction h with
  | refl => exact (hne rfl).elim
  | @tail b c hab hbc ih =>
    exact ⟨b, hbc.1, AppendixA.adjacent_symmetric E hbc.2.2⟩

theorem connected_neighbors {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (hconn : AppendixA.connected E S) (hsize : 1 < S.card) :
    ∀ a ∈ S, ∃ b ∈ S, AppendixA.adjacent E a b := by
  intro a ha
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hsize a
  exact reach_last_neighbor E S (hconn b hb a ha) hba

theorem embedding_relaxedMaster {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m)
    (h : Embedding E L k A) : RelaxedMaster E L k A := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro j hj
  exact connected_neighbors E (fiber A j) (h.2.2 j) hj

end AppendixATheory

#print axioms AppendixATheory.connected_neighbors
#print axioms AppendixATheory.embedding_relaxedMaster
