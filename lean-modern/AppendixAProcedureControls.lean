module

public import AppendixAMonolithic
public import AppendixAModelControls

@[expose] public section

noncomputable section
namespace AppendixATheory

theorem exactMin_singleton {n m : ℕ} (A : Alpha n m)
    (h : ({A} : Finset (Alpha n m)).Nonempty) : exactMin {A} h = A :=
  Finset.mem_singleton.mp (exactMin_spec {A} h).1

theorem singleton_rejection_control {n m : ℕ} (E : Finset (Fin n × Fin n))
    (check : Alpha n m → Bool)
    (hcheck : ∀ A, check A = true ↔ ∀ j, AppendixA.connected E (fiber A j))
    (A : Alpha n m) (hc : check A = false) :
    (cutRun E check hcheck 1 {A} []).answer = none ∧
    (cutRun E check hcheck 1 {A} []).steps = 1 ∧
    (cutRun E check hcheck 1 {A} []).history.length = 1 := by
  classical
  simp [cutRun, exactMin_singleton, hc]

theorem disconnected_checker_rejects : allFiberCheck twoEdges allOneFiber = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  have hconn := (allFiberCheck_eq_true_iff twoEdges allOneFiber).mp hc
  exact disconnected_no_embedding
    ⟨disconnected_relaxed_master.1, disconnected_relaxed_master.2.1, hconn⟩

theorem disconnected_actual_one_rejection :
    (cutRun twoEdges (allFiberCheck twoEdges) (allFiberCheck_eq_true_iff twoEdges)
      1 {allOneFiber} []).answer = none ∧
    (cutRun twoEdges (allFiberCheck twoEdges) (allFiberCheck_eq_true_iff twoEdges)
      1 {allOneFiber} []).steps = 1 ∧
    (cutRun twoEdges (allFiberCheck twoEdges) (allFiberCheck_eq_true_iff twoEdges)
      1 {allOneFiber} []).history.length = 1 :=
  singleton_rejection_control twoEdges (allFiberCheck twoEdges)
    (allFiberCheck_eq_true_iff twoEdges) allOneFiber disconnected_checker_rejects

theorem reversed_procedure_optimum : ∃ A,
    (solveEmbedding reversedPhysical twoLogical 1).answer = some A ∧ footprint A = 2 := by
  cases ha : (solveEmbedding reversedPhysical twoLogical 1).answer with
  | none =>
      have h := (solveEmbedding_none_iff reversedPhysical twoLogical 1).mp ha
      exact (h ⟨reversedAlpha,reversed_embedding⟩).elim
  | some A =>
      have h := solveEmbedding_some_optimal reversedPhysical twoLogical 1 A ha
      have hlo := (rowBounds_size_bounds 1 A h.1.1).1
      have hhi := h.2 reversedAlpha reversed_embedding
      rw [reversed_unused_vertex.2] at hhi
      exact ⟨A,rfl,by omega⟩

theorem empty_logical_procedure {n : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin 0 × Fin 0)) (k : ℕ) : ∃ A,
    (solveEmbedding E L k).answer = some A ∧ footprint A = 0 := by
  cases ha : (solveEmbedding E L k).answer with
  | none =>
      have h := (solveEmbedding_none_iff E L k).mp ha
      exact (h ⟨fun _ j => Fin.elim0 j,empty_logical_embedding E L k _⟩).elim
  | some A => exact ⟨A,rfl,empty_logical_footprint A⟩

theorem zero_cap_procedure {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (hm : 0 < m) : (solveEmbedding E L 0).answer = none := by
  apply (solveEmbedding_none_iff E L 0).mpr
  rintro ⟨A,hA⟩
  exact zero_cap_positive_logical hm E L A hA

theorem impossible_size_procedure {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (hsize : n < m) :
    (solveEmbedding E L k).answer = none := by
  apply (solveEmbedding_none_iff E L k).mpr
  rintro ⟨A,hA⟩
  exact too_many_logical_impossible k A hsize hA.1

end AppendixATheory

#print axioms AppendixATheory.disconnected_checker_rejects
#print axioms AppendixATheory.disconnected_actual_one_rejection
#print axioms AppendixATheory.reversed_procedure_optimum
#print axioms AppendixATheory.empty_logical_procedure
#print axioms AppendixATheory.zero_cap_procedure
#print axioms AppendixATheory.impossible_size_procedure
