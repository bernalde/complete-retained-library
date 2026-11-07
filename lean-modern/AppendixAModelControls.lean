module

public import AppendixAMaster

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AppendixATheory

theorem connected_singleton {n : ℕ} (E : Finset (Fin n × Fin n)) (a : Fin n) :
    AppendixA.connected E {a} := by
  intro x hx y hy
  simp only [Finset.mem_singleton] at hx hy
  subst x; subst y
  exact Relation.ReflTransGen.refl

theorem cap_one_embedding_iff {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) :
    Embedding E L 1 A ↔ RowBounds 1 A ∧ EdgeCoverage E L A := by
  constructor
  · intro h; exact ⟨h.1,h.2.1⟩
  · rintro ⟨hr,he⟩
    refine ⟨hr,he,?_⟩
    intro j
    obtain ⟨a,ha⟩ := cap_one_singletons A hr j
    rw [ha]
    exact connected_singleton E a

theorem cap_one_distinct_representatives {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) (h : Embedding E L 1 A) :
    ∃ f : Fin m → Fin n, Function.Injective f ∧
      (∀ j, fiber A j = {f j}) ∧
      ∀ j l, AppendixA.adjacent L j l → AppendixA.adjacent E (f j) (f l) := by
  classical
  choose f hf using cap_one_singletons A h.1
  refine ⟨f, ?_, hf, ?_⟩
  · intro j l heq
    have hx := (row_card_iff_exclusive A).mp h.1.1
    apply hx (f j) j l
    · apply (mem_fiber A _ _).mp
      simp [hf]
    · apply (mem_fiber A _ _).mp
      simp [hf,heq]
  · intro j l hjl
    obtain ⟨a,ha,b,hb,hab⟩ := h.2.1 j l hjl
    simpa [hf] using (show ∃ a ∈ ({f j} : Finset (Fin n)),
      ∃ b ∈ ({f l} : Finset (Fin n)), AppendixA.adjacent E a b from
        ⟨a,by simpa [hf] using ha,b,by simpa [hf] using hb,hab⟩)

theorem empty_logical_embedding {n : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin 0 × Fin 0)) (k : ℕ) (A : Alpha n 0) : Embedding E L k A := by
  refine ⟨⟨?_,fun j => Fin.elim0 j⟩,fun j => Fin.elim0 j,fun j => Fin.elim0 j⟩
  intro i
  simp

theorem empty_logical_footprint {n : ℕ} (A : Alpha n 0) : footprint A = 0 := by
  simp [footprint]

theorem empty_physical_positive_logical {m : ℕ} (hm : 0 < m)
    (E : Finset (Fin 0 × Fin 0)) (L : Finset (Fin m × Fin m)) (k : ℕ)
    (A : Alpha 0 m) : ¬ Embedding E L k A :=
  fun h => too_many_logical_impossible k A hm h.1

theorem zero_cap_positive_logical {n m : ℕ} (hm : 0 < m)
    (E : Finset (Fin n × Fin n)) (L : Finset (Fin m × Fin m)) (A : Alpha n m) :
    ¬ Embedding E L 0 A := fun h => positive_logical_zero_cap A hm h.1

def reversedPhysical : Finset (Fin 3 × Fin 3) := {(1,0)}
def twoLogical : Finset (Fin 2 × Fin 2) := {(0,1)}
def reversedAlpha : Alpha 3 2 := fun i j => decide (i.val = j.val)

theorem reversed_rows : RowBounds 1 reversedAlpha := by
  unfold RowBounds fiber reversedAlpha
  decide

theorem reversed_edge_coverage : EdgeCoverage reversedPhysical twoLogical reversedAlpha := by
  unfold EdgeCoverage AppendixA.adjacent fiber reversedPhysical twoLogical reversedAlpha
  decide

theorem reversed_embedding : Embedding reversedPhysical twoLogical 1 reversedAlpha :=
  (cap_one_embedding_iff _ _ _).mpr ⟨reversed_rows,reversed_edge_coverage⟩

theorem reversed_unused_vertex : (∀ j, reversedAlpha 2 j = false) ∧ footprint reversedAlpha = 2 := by
  unfold reversedAlpha footprint
  decide

theorem reversed_full_extensions :
    (∃ D, DeltaRows reversedPhysical twoLogical reversedAlpha D) ∧
    ∃ Z w, RepairedMasterRows reversedPhysical twoLogical 1 reversedAlpha Z w :=
  ⟨(delta_projection _ _ _).mpr reversed_edge_coverage,
    embedding_master_extension _ _ _ _ reversed_embedding⟩

def doubleStoredPhysical : Finset (Fin 3 × Fin 3) := {(1,0),(0,1)}

theorem duplicate_orientation_control :
    Embedding doubleStoredPhysical twoLogical 1 reversedAlpha ∧
      (∃ Z, SelectedEdgeRows doubleStoredPhysical twoLogical reversedAlpha Z) := by
  have he : EdgeCoverage doubleStoredPhysical twoLogical reversedAlpha := by
    unfold EdgeCoverage AppendixA.adjacent fiber doubleStoredPhysical twoLogical reversedAlpha
    decide
  exact ⟨(cap_one_embedding_iff _ _ _).mpr ⟨reversed_rows,he⟩,
    (selected_edge_projection _ _ _).mpr he⟩

def twoEdges : Finset (Fin 4 × Fin 4) := {(0,1),(2,3)}
def allOneFiber : Alpha 4 1 := fun _ _ => true

theorem disconnected_relaxed_master : RelaxedMaster twoEdges ∅ 4 allOneFiber := by
  unfold RelaxedMaster RowBounds EdgeCoverage NeighborRows fiber AppendixA.adjacent twoEdges allOneFiber
  decide

theorem twoEdges_reach_stays_left {b : Fin 4}
    (h : Relation.ReflTransGen (AppendixA.fiberStep twoEdges (fiber allOneFiber 0)) 0 b) :
    b = 0 ∨ b = 1 := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c hab hbc ih =>
    rcases ih with rfl | rfl <;> fin_cases c <;>
      simp_all [AppendixA.fiberStep,AppendixA.adjacent,twoEdges,fiber,allOneFiber]

theorem disconnected_no_embedding : ¬ Embedding twoEdges ∅ 4 allOneFiber := by
  intro h
  have hp := twoEdges_reach_stays_left (h.2.2 0 0 (by simp [fiber,allOneFiber])
    2 (by simp [fiber,allOneFiber]))
  rcases hp with hp | hp
  · exact (by decide : (2 : Fin 4) ≠ 0) hp
  · exact (by decide : (2 : Fin 4) ≠ 1) hp

theorem disconnected_master_extensions :
    (∃ Z w, RepairedMasterRows twoEdges ∅ 4 allOneFiber Z w) ∧
      ¬ Embedding twoEdges ∅ 4 allOneFiber :=
  ⟨(repaired_master_projection _ _ _ _).mpr disconnected_relaxed_master,
    disconnected_no_embedding⟩

theorem disconnected_graph_loopfree : LoopFree twoEdges := by
  unfold LoopFree AppendixA.adjacent twoEdges
  decide

theorem impossible_size_control (A : Alpha 2 3) : ¬ RowBounds 10 A :=
  too_many_logical_impossible _ _ (by decide)

theorem no_logical_edges_does_not_erase_fibers (A : Alpha 0 1) :
    ¬ Embedding ∅ ∅ 4 A := empty_physical_positive_logical (by decide) _ _ _ A

end AppendixATheory

#print axioms AppendixATheory.cap_one_distinct_representatives
#print axioms AppendixATheory.empty_logical_embedding
#print axioms AppendixATheory.empty_logical_footprint
#print axioms AppendixATheory.empty_physical_positive_logical
#print axioms AppendixATheory.zero_cap_positive_logical
#print axioms AppendixATheory.reversed_full_extensions
#print axioms AppendixATheory.duplicate_orientation_control
#print axioms AppendixATheory.disconnected_master_extensions
#print axioms AppendixATheory.impossible_size_control
