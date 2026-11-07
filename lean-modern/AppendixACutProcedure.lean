module

public import AppendixAModel

@[expose] public section

/-! Exact finite master/cut execution. The checker parameter is instantiated by
the exhaustive simple-path checker in AppendixAProcedure; it is not a research
axiom. All cuts use the retained actual restricted-edge connectivity relation. -/
noncomputable section
open scoped BigOperators
namespace AppendixATheory

structure FiberCut (n m : ℕ) where
  index : Fin m
  rejected : Finset (Fin n)

def cutHolds {n m : ℕ} (E : Finset (Fin n × Fin n)) (c : FiberCut n m)
    (A : Alpha n m) : Prop :=
  1 ≤ c.rejected.card - (c.rejected ∩ fiber A c.index).card +
    (AppendixA.boundary E c.rejected ∩ fiber A c.index).card

def validCut {n m : ℕ} (E : Finset (Fin n × Fin n)) (c : FiberCut n m) : Prop :=
  ¬ AppendixA.connected E c.rejected

theorem real_selected_sum {n m : ℕ} (S : Finset (Fin n)) (A : Alpha n m) (j : Fin m) :
    (∑ v ∈ S, Chapter10.bit (A v j)) = ((S ∩ fiber A j).card : ℝ) := by
  have h := AppendixA.selected_sum_is_intersection_card S (fiber A j)
  have hc : (∑ v ∈ S, if v ∈ fiber A j then (1 : ℝ) else 0) =
      ((S ∩ fiber A j).card : ℝ) := by exact_mod_cast h
  convert hc using 1
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Finset.sum_ite_irrel, mem_fiber]
  cases hbit : A v j <;> simp [Chapter10.bit]

def sourceCutRow {n m : ℕ} (E : Finset (Fin n × Fin n)) (c : FiberCut n m)
    (A : Alpha n m) : Prop :=
  (1 : ℝ) ≤ (∑ v ∈ c.rejected, (1 - Chapter10.bit (A v c.index))) +
    ∑ v ∈ AppendixA.boundary E c.rejected, Chapter10.bit (A v c.index)

theorem cutHolds_iff_sourceCutRow {n m : ℕ} (E : Finset (Fin n × Fin n))
    (c : FiberCut n m) (A : Alpha n m) : cutHolds E c A ↔ sourceCutRow E c A := by
  classical
  have hle := Finset.card_le_card
    (Finset.inter_subset_left : c.rejected ∩ fiber A c.index ⊆ c.rejected)
  have hcast : ((c.rejected.card - (c.rejected ∩ fiber A c.index).card +
      (AppendixA.boundary E c.rejected ∩ fiber A c.index).card : ℕ) : ℝ) =
      (c.rejected.card : ℝ) - ((c.rejected ∩ fiber A c.index).card : ℝ) +
      ((AppendixA.boundary E c.rejected ∩ fiber A c.index).card : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hle]
  unfold sourceCutRow
  simp only [Finset.sum_sub_distrib, real_selected_sum]
  simp only [Finset.sum_const, Finset.sum_eq_single_of_mem, nsmul_eq_mul, mul_one]
  rw [← hcast]
  unfold cutHolds
  exact_mod_cast Iff.rfl

def historyHolds {n m : ℕ} (E : Finset (Fin n × Fin n))
    (history : List (FiberCut n m)) (A : Alpha n m) : Prop :=
  ∀ c ∈ history, cutHolds E c A

def masterPool {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (history : List (FiberCut n m)) :
    Finset (Alpha n m) := by
  classical
  exact Finset.univ.filter (fun A => RelaxedMaster E L k A ∧ historyHolds E history A)

def retainCut {n m : ℕ} (E : Finset (Fin n × Fin n)) (c : FiberCut n m)
    (pool : Finset (Alpha n m)) : Finset (Alpha n m) := by
  classical
  exact pool.filter (cutHolds E c)

theorem mem_masterPool {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (history : List (FiberCut n m))
    (A : Alpha n m) :
    A ∈ masterPool E L k history ↔ RelaxedMaster E L k A ∧ historyHolds E history A := by
  classical
  simp [masterPool]

theorem retainCut_masterPool {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (history : List (FiberCut n m))
    (c : FiberCut n m) :
    retainCut E c (masterPool E L k history) = masterPool E L k (c :: history) := by
  classical
  ext A
  simp only [retainCut, Finset.mem_filter, mem_masterPool]
  simp only [historyHolds, List.mem_cons, forall_eq_or_imp]
  tauto

theorem embedding_survives_cut {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (c : FiberCut n m)
    (hc : validCut E c) (A : Alpha n m) (hA : Embedding E L k A) : cutHolds E c A :=
  AppendixA.boundary_cut_valid E c.rejected (fiber A c.index) hc (hA.2.2 c.index)

theorem embedding_mem_masterPool {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (history : List (FiberCut n m))
    (hh : ∀ c ∈ history, validCut E c) (A : Alpha n m) (hA : Embedding E L k A) :
    A ∈ masterPool E L k history := by
  apply (mem_masterPool E L k history A).mpr
  exact ⟨embedding_relaxedMaster E L k A hA,
    fun c hc => embedding_survives_cut E L k c (hh c hc) A hA⟩

def rejectedCut {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m)
    (hbad : ¬ ∀ j, AppendixA.connected E (fiber A j)) : FiberCut n m :=
  ⟨Classical.choose (not_forall.mp hbad),
    fiber A (Classical.choose (not_forall.mp hbad))⟩

theorem rejectedCut_valid {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m)
    (hbad : ¬ ∀ j, AppendixA.connected E (fiber A j)) : validCut E (rejectedCut E A hbad) :=
  Classical.choose_spec (not_forall.mp hbad)

theorem rejectedCut_excludes {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m)
    (hbad : ¬ ∀ j, AppendixA.connected E (fiber A j)) :
    ¬ cutHolds E (rejectedCut E A hbad) A := by
  unfold cutHolds rejectedCut
  simp only
  rw [AppendixA.boundary_cut_rejects_current]
  omega

theorem retainCut_card_lt {n m : ℕ} (E : Finset (Fin n × Fin n))
    (pool : Finset (Alpha n m)) (A : Alpha n m) (hA : A ∈ pool)
    (hbad : ¬ ∀ j, AppendixA.connected E (fiber A j)) :
    (retainCut E (rejectedCut E A hbad) pool).card < pool.card := by
  classical
  apply Finset.card_lt_card
  exact Finset.filter_ssubset.mpr ⟨A, hA, rejectedCut_excludes E A hbad⟩

def exactMin {n m : ℕ} (pool : Finset (Alpha n m)) (h : pool.Nonempty) : Alpha n m :=
  Classical.choose (Finset.exists_min_image pool footprint h)

theorem exactMin_spec {n m : ℕ} (pool : Finset (Alpha n m)) (h : pool.Nonempty) :
    exactMin pool h ∈ pool ∧ ∀ A ∈ pool, footprint (exactMin pool h) ≤ footprint A :=
  Classical.choose_spec (Finset.exists_min_image pool footprint h)

/-- One recursive execution records all cuts, including those present initially.
`steps` counts rejected master assignments, not numerical solver calls. -/
structure ProcedureResult (n m : ℕ) where
  answer : Option (Alpha n m)
  history : List (FiberCut n m)
  steps : ℕ

def cutRun {n m : ℕ} (E : Finset (Fin n × Fin n))
    (check : Alpha n m → Bool)
    (hcheck : ∀ A, check A = true ↔ ∀ j, AppendixA.connected E (fiber A j)) :
    ℕ → Finset (Alpha n m) → List (FiberCut n m) → ProcedureResult n m
  | 0, _, history => ⟨none, history, 0⟩
  | fuel + 1, pool, history => by
      classical
      exact if hp : pool.Nonempty then
        let A := exactMin pool hp
        if hc : check A = true then ⟨some A, history, 0⟩ else
          let bad : ¬ ∀ j, AppendixA.connected E (fiber A j) := fun h => hc ((hcheck A).mpr h)
          let c := rejectedCut E A bad
          let result := cutRun E check hcheck fuel (retainCut E c pool) (c :: history)
          ⟨result.answer, result.history, result.steps + 1⟩
      else ⟨none, history, 0⟩

def AnswerCorrect {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) : Option (Alpha n m) → Prop
  | none => ¬ ∃ A, Embedding E L k A
  | some A => Embedding E L k A ∧ ∀ B, Embedding E L k B → footprint A ≤ footprint B

theorem cutRun_correct {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (check : Alpha n m → Bool)
    (hcheck : ∀ A, check A = true ↔ ∀ j, AppendixA.connected E (fiber A j))
    (fuel : ℕ) (pool : Finset (Alpha n m)) (history : List (FiberCut n m))
    (hsize : pool.card ≤ fuel)
    (hmaster : ∀ A ∈ pool, RelaxedMaster E L k A)
    (hretain : ∀ A, Embedding E L k A → A ∈ pool)
    (hh : ∀ c ∈ history, validCut E c) :
    AnswerCorrect E L k (cutRun E check hcheck fuel pool history).answer ∧
    (∀ c ∈ (cutRun E check hcheck fuel pool history).history, validCut E c) ∧
    (cutRun E check hcheck fuel pool history).steps ≤ pool.card := by
  classical
  induction fuel generalizing pool history with
  | zero =>
      have hempty : pool = ∅ := Finset.card_eq_zero.mp (by omega)
      refine ⟨?_, hh, by simp [cutRun]⟩
      rintro ⟨A, hA⟩
      have := hretain A hA
      simp [hempty] at this
  | succ fuel ih =>
      by_cases hp : pool.Nonempty
      · let A := exactMin pool hp
        have hA := exactMin_spec pool hp
        by_cases hc : check A = true
        · have hemb : Embedding E L k A :=
            ⟨(hmaster A hA.1).1, (hmaster A hA.1).2.1, (hcheck A).mp hc⟩
          have hans : AnswerCorrect E L k (some A) :=
            ⟨hemb, fun B hB => hA.2 B (hretain B hB)⟩
          simpa [cutRun, hp, A, hc] using And.intro hans (And.intro hh (Nat.zero_le pool.card))
        · let bad : ¬ ∀ j, AppendixA.connected E (fiber A j) := fun h => hc ((hcheck A).mpr h)
          let c := rejectedCut E A bad
          have hv : validCut E c := rejectedCut_valid E A bad
          have hlt : (retainCut E c pool).card < pool.card := retainCut_card_lt E pool A hA.1 bad
          have hs : (retainCut E c pool).card ≤ fuel := by omega
          have hm : ∀ B ∈ retainCut E c pool, RelaxedMaster E L k B := by
            intro B hB
            exact hmaster B (Finset.mem_filter.mp hB).1
          have hr : ∀ B, Embedding E L k B → B ∈ retainCut E c pool := by
            intro B hB
            exact Finset.mem_filter.mpr ⟨hretain B hB, embedding_survives_cut E L k c hv B hB⟩
          have hh' : ∀ d ∈ c :: history, validCut E d := by
            intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hv
            · exact hh d hd
          have res := ih (retainCut E c pool) (c :: history) hs hm hr hh'
          have step : (cutRun E check hcheck fuel (retainCut E c pool) (c :: history)).steps + 1 ≤ pool.card := by
            omega
          simpa [cutRun, hp, A, hc, bad, c] using And.intro res.1 (And.intro res.2.1 step)
      · have hempty : pool = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
        have hans : AnswerCorrect E L k none := by
          rintro ⟨A, hA⟩
          have := hretain A hA
          simp [hempty] at this
        simpa [cutRun, hp] using And.intro hans (And.intro hh (Nat.zero_le pool.card))

theorem cutRun_history_pool {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (check : Alpha n m → Bool)
    (hcheck : ∀ A, check A = true ↔ ∀ j, AppendixA.connected E (fiber A j))
    (fuel : ℕ) (history : List (FiberCut n m)) :
    history.IsSuffix (cutRun E check hcheck fuel (masterPool E L k history) history).history := by
  classical
  induction fuel generalizing history with
  | zero => simp [cutRun]
  | succ fuel ih =>
      unfold cutRun
      split
      · rename_i hp
        dsimp only
        split
        · exact List.suffix_refl _
        · rename_i hc
          dsimp only
          rw [retainCut_masterPool]
          exact (List.suffix_cons _ _).trans (ih _)
      · exact List.suffix_refl _

/-- The cardinal fuel is sufficient for an actual terminal branch: a `none`
result has an empty retained master, not merely an exhausted arbitrary fuel. -/
theorem cutRun_terminal {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (check : Alpha n m → Bool)
    (hcheck : ∀ A, check A = true ↔ ∀ j, AppendixA.connected E (fiber A j))
    (fuel : ℕ) (history : List (FiberCut n m))
    (hsize : (masterPool E L k history).card ≤ fuel) :
    let result := cutRun E check hcheck fuel (masterPool E L k history) history
    match result.answer with
    | none => masterPool E L k result.history = ∅
    | some A => A ∈ masterPool E L k result.history ∧ check A = true := by
  classical
  induction fuel generalizing history with
  | zero =>
      simp only [cutRun]
      exact Finset.card_eq_zero.mp (by omega)
  | succ fuel ih =>
      by_cases hp : (masterPool E L k history).Nonempty
      · let A := exactMin (masterPool E L k history) hp
        by_cases hc : check A = true
        · simpa [cutRun, hp, A, hc] using And.intro (exactMin_spec _ hp).1 hc
        · let bad : ¬ ∀ j, AppendixA.connected E (fiber A j) := fun h => hc ((hcheck A).mpr h)
          let c := rejectedCut E A bad
          have hlt := retainCut_card_lt E (masterPool E L k history) A (exactMin_spec _ hp).1 bad
          have hs : (masterPool E L k (c :: history)).card ≤ fuel := by
            rw [retainCut_masterPool] at hlt
            dsimp only [c]
            omega
          have res := ih (c :: history) hs
          simpa [cutRun, hp, A, hc, bad, c, retainCut_masterPool] using res
      · simpa [cutRun, hp] using (Finset.not_nonempty_iff_eq_empty.mp hp)

end AppendixATheory

#print axioms AppendixATheory.cutHolds_iff_sourceCutRow
#print axioms AppendixATheory.embedding_mem_masterPool
#print axioms AppendixATheory.retainCut_card_lt
#print axioms AppendixATheory.cutRun_correct
#print axioms AppendixATheory.cutRun_history_pool
#print axioms AppendixATheory.cutRun_terminal
