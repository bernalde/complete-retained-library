module

public import Chapter03FPSearchMaster

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch
variable {n m l : ℕ}

def State.targets (s : State n m) : List (IntVector m) := s.history.map Event.target

structure Invariant (d : Data n m l) (Q : Finset (IntVector m)) (s : State n m) : Prop where
  valid : Valid d s
  nodup : s.targets.Nodup
  mem : ∀ e ∈ s.history, e.target ∈ Q

theorem initial_invariant (d : Data n m l) (Q : Finset (IntVector m))
    {p : Point n m} (hp : p ∈ d.relaxation) : Invariant d Q (initialState p) := by
  exact ⟨initial_valid d hp, by simp [State.targets, initialState], by simp [initialState]⟩

theorem master_target_fresh (d : Data n m l) {mode : Mode}
    {Q : Finset (IntVector m)} (hn : NormalLaw d mode Q)
    {s : State n m} (hs : Invariant d Q s) {p : Point n m}
    (hp : p ∈ master d mode s) {q : IntVector m} (hq : p.2 = intCast q) :
    q ∉ s.targets := by
  intro hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  have hnormal := hn s hs.valid hs.mem p hp e he
  have hne : Chapter03.yMap n m e.projection ≠ intY e.target := by
    intro hy
    exact (hs.valid.events e he).fractional
      ⟨e.target, (yMap_eq_intY_iff _ _).mp hy⟩
  have hneg := Chapter03.projection_cut_excludes hne
  have hy := (yMap_eq_intY_iff p q).mpr hq
  change 0 ≤ @inner ℝ _ _ (Chapter03.yMap n m e.projection - intY e.target)
    (Chapter03.yMap n m p - Chapter03.yMap n m e.projection) at hnormal
  rw [hy, ← heq] at hnormal
  linarith

theorem append_invariant (d : Data n m l) {mode : Mode}
    {Q : Finset (IntVector m)} (hb : TargetBound d mode Q) (hn : NormalLaw d mode Q)
    {s : State n m} (hs : Invariant d Q s) (step : Step d mode s)
    (hf : ¬Integral step.projection) : Invariant d Q (append s step.event) := by
  have hnew := master_target_fresh d hn hs step.master_min.1 step.target_eq
  have hQ := hb s hs.valid step.point step.master_min.1 step.target step.target_eq
  refine ⟨append_valid d hs.valid ⟨step.projection_min, hf⟩, ?_, ?_⟩
  · simpa [State.targets, append, Step.event] using
      hs.nodup.append (List.nodup_singleton _) (List.disjoint_singleton.mpr hnew)
  · intro e he
    simp only [append, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hs.mem e he
    · exact hQ

theorem list_length_le_card (Q : Finset (IntVector m)) (qs : List (IntVector m))
    (hn : qs.Nodup) (hm : ∀ q ∈ qs, q ∈ Q) : qs.length ≤ Q.card := by
  classical
  calc
    qs.length = qs.toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ ≤ Q.card := Finset.card_le_card (by
      intro q hq
      exact hm q (List.mem_toFinset.mp hq))

theorem history_length_le (d : Data n m l) {Q : Finset (IntVector m)}
    {s : State n m} (hs : Invariant d Q s) : s.history.length ≤ Q.card := by
  have hm : ∀ q ∈ s.targets, q ∈ Q := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    exact hs.mem e he
  simpa [State.targets] using list_length_le_card Q s.targets hs.nodup hm

/-- Includes a possible final successful target, not only failed history. -/
theorem step_count_le (d : Data n m l) {mode : Mode}
    {Q : Finset (IntVector m)} (hb : TargetBound d mode Q) (hn : NormalLaw d mode Q)
    {s : State n m} (hs : Invariant d Q s) (step : Step d mode s) :
    s.history.length + 1 ≤ Q.card := by
  have hnew := master_target_fresh d hn hs step.master_min.1 step.target_eq
  have hQ := hb s hs.valid step.point step.master_min.1 step.target step.target_eq
  have hnodup : (s.targets ++ [step.target]).Nodup :=
    hs.nodup.append (List.nodup_singleton _) (List.disjoint_singleton.mpr hnew)
  have hmem : ∀ q ∈ s.targets ++ [step.target], q ∈ Q := by
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
      exact hs.mem e he
    · exact hQ
  simpa [State.targets] using list_length_le_card Q _ hnodup hmem

end Chapter03.FPSearch
