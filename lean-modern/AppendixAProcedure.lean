module

public import AppendixACutProcedure
public import AppendixAPaths

@[expose] public section

/-! The complete finite path checker instantiated in the concrete master/cut
procedure. No commercial solver, timeout, floating-point or runtime certificate. -/
noncomputable section
namespace AppendixATheory

def allFiberCheck {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m) : Bool :=
  decide (∀ j, AppendixAPaths.connectedCheck E (fiber A j) = true)

theorem allFiberCheck_eq_true_iff {n m : ℕ} (E : Finset (Fin n × Fin n))
    (A : Alpha n m) : allFiberCheck E A = true ↔ ∀ j, AppendixA.connected E (fiber A j) := by
  simp only [allFiberCheck, decide_eq_true_eq]
  exact forall_congr' (fun j => AppendixAPaths.connectedCheck_eq_true_iff E (fiber A j))

def solveEmbedding {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) : ProcedureResult n m :=
  cutRun E (allFiberCheck E) (allFiberCheck_eq_true_iff E)
    (masterPool E L k []).card (masterPool E L k []) []

theorem solveEmbedding_correct {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) :
    AnswerCorrect E L k (solveEmbedding E L k).answer ∧
    (∀ c ∈ (solveEmbedding E L k).history, validCut E c) ∧
    (solveEmbedding E L k).steps ≤ (masterPool E L k []).card := by
  apply cutRun_correct E L k (allFiberCheck E) (allFiberCheck_eq_true_iff E)
  · exact le_refl _
  · intro A hA
    exact ((mem_masterPool E L k [] A).mp hA).1
  · intro A hA
    exact embedding_mem_masterPool E L k [] (by simp) A hA
  · simp

theorem solveEmbedding_none_iff {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) :
    (solveEmbedding E L k).answer = none ↔ ¬ ∃ A, Embedding E L k A := by
  have h := (solveEmbedding_correct E L k).1
  cases ha : (solveEmbedding E L k).answer with
  | none => simpa [ha, AnswerCorrect] using h
  | some A =>
      have hA : Embedding E L k A := (show AnswerCorrect E L k (some A) from ha ▸ h).1
      simp only [Option.some_ne_none, false_iff, not_not]
      exact ⟨A, hA⟩

theorem solveEmbedding_some_optimal {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m)
    (ha : (solveEmbedding E L k).answer = some A) :
    Embedding E L k A ∧ ∀ B, Embedding E L k B → footprint A ≤ footprint B := by
  have h := (solveEmbedding_correct E L k).1
  simpa [ha, AnswerCorrect] using h

theorem solveEmbedding_terminal {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) :
    match (solveEmbedding E L k).answer with
    | none => masterPool E L k (solveEmbedding E L k).history = ∅
    | some A => A ∈ masterPool E L k (solveEmbedding E L k).history ∧ allFiberCheck E A = true :=
  cutRun_terminal E L k (allFiberCheck E) (allFiberCheck_eq_true_iff E)
    (masterPool E L k []).card [] (le_refl _)

theorem solveEmbedding_history_preserves {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) (hA : Embedding E L k A) :
    A ∈ masterPool E L k (solveEmbedding E L k).history ∧
    ∀ c ∈ (solveEmbedding E L k).history, sourceCutRow E c A := by
  have hh := (solveEmbedding_correct E L k).2.1
  refine ⟨embedding_mem_masterPool E L k _ hh A hA, ?_⟩
  intro c hc
  exact (cutHolds_iff_sourceCutRow E c A).mp (embedding_survives_cut E L k c (hh c hc) A hA)

theorem masterPool_card_bound {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (history : List (FiberCut n m)) :
    (masterPool E L k history).card ≤ 2 ^ (n * m) := by
  have h := Finset.card_le_univ (masterPool E L k history)
  simpa [Alpha, Fintype.card_fun, ← Nat.pow_mul, Nat.mul_comm] using h

theorem solveEmbedding_rejection_bound {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) :
    (solveEmbedding E L k).steps ≤ 2 ^ (n * m) :=
  (solveEmbedding_correct E L k).2.2.trans (masterPool_card_bound E L k [])

theorem embedding_full_cap {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) :
    (∃ k, Embedding E L k A) ↔ Embedding E L n A := by
  constructor
  · rintro ⟨k, hA⟩
    refine ⟨⟨hA.1.1, ?_⟩, hA.2⟩
    intro j
    exact ⟨(hA.1.2 j).1, by simpa using Finset.card_le_univ (fiber A j)⟩
  · exact fun h => ⟨n, h⟩

theorem solveEmbedding_full_cap_none_iff {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) :
    (solveEmbedding E L n).answer = none ↔ ¬ ∃ A k, Embedding E L k A := by
  rw [solveEmbedding_none_iff]
  simp only [embedding_full_cap]

end AppendixATheory

#print axioms AppendixATheory.allFiberCheck_eq_true_iff
#print axioms AppendixATheory.solveEmbedding_correct
#print axioms AppendixATheory.solveEmbedding_none_iff
#print axioms AppendixATheory.solveEmbedding_some_optimal
#print axioms AppendixATheory.solveEmbedding_terminal
#print axioms AppendixATheory.solveEmbedding_history_preserves
#print axioms AppendixATheory.masterPool_card_bound
#print axioms AppendixATheory.solveEmbedding_rejection_bound
#print axioms AppendixATheory.embedding_full_cap
#print axioms AppendixATheory.solveEmbedding_full_cap_none_iff
