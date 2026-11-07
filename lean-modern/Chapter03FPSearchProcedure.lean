module

public import Chapter03FPSearchInvariant

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch
variable {n m l : ℕ}

inductive Reason (n m : ℕ) where
  | emptyMaster
  | found (point : Point n m)

def terminalProjections : Reason n m → ℕ
  | .emptyMaster => 0
  | .found _ => 1

structure LoopOutput (n m : ℕ) where
  state : State n m
  reason : Reason n m
  masters : ℕ
  projections : ℕ
  failures : ℕ

def terminalOutput (s : State n m) (r : Reason n m) : LoopOutput n m :=
  ⟨s, r, 1, terminalProjections r, 0⟩

def LoopOutput.bump (out : LoopOutput n m) : LoopOutput n m :=
  ⟨out.state, out.reason, out.masters+1, out.projections+1, out.failures+1⟩

/-- Actual first-search recursion. The success test is integrality of the
projection, regardless of whether it equals the selected integer target. -/
def run (d : Data n m l) (mode : Mode) (choose : Selector d mode) :
    (fuel : ℕ) → (s : State n m) → s.seed ∈ d.relaxation → Option (LoopOutput n m)
  | 0, _, _ => none
  | fuel+1, s, hs => by
    classical
    exact match choose s hs with
    | .empty _ => some (terminalOutput s .emptyMaster)
    | .project step =>
      if Integral step.projection then some (terminalOutput s (.found step.projection))
      else (run d mode choose fuel (append s step.event) hs).map LoopOutput.bump

theorem run_empty (d : Data n m l) (mode : Mode) (choose : Selector d mode)
    (fuel : ℕ) (s : State n m) (hs : s.seed ∈ d.relaxation)
    (he : ¬(master d mode s).Nonempty) (hc : choose s hs = .empty he) :
    run d mode choose (fuel+1) s hs = some (terminalOutput s .emptyMaster) := by
  simp [run, hc]

theorem run_integral (d : Data n m l) (mode : Mode) (choose : Selector d mode)
    (fuel : ℕ) (s : State n m) (hs : s.seed ∈ d.relaxation)
    (step : Step d mode s) (hc : choose s hs = .project step)
    (hi : Integral step.projection) : run d mode choose (fuel+1) s hs =
      some (terminalOutput s (.found step.projection)) := by
  simp [run, hc, hi]

theorem run_fractional (d : Data n m l) (mode : Mode) (choose : Selector d mode)
    (fuel : ℕ) (s : State n m) (hs : s.seed ∈ d.relaxation)
    (step : Step d mode s) (hc : choose s hs = .project step)
    (hi : ¬Integral step.projection) : run d mode choose (fuel+1) s hs =
      (run d mode choose fuel (append s step.event) hs).map LoopOutput.bump := by
  simp [run, hc, hi]

inductive Outcome (n m : ℕ) where
  | initialEmpty
  | initialOptimal (point : Point n m)
  | loop (out : LoopOutput n m)

def procedureWithFuel (d : Data n m l) (mode : Mode) (initial : Initialization d)
    (choose : Selector d mode) (fuel : ℕ) : Option (Outcome n m) := by
  classical
  exact match initial with
  | .empty _ => some .initialEmpty
  | .minimum p hp =>
    if Integral p then some (.initialOptimal p)
    else (run d mode choose fuel (initialState p) hp.1).map Outcome.loop

inductive Stop (d : Data n m l) (mode : Mode) (s : State n m) : Reason n m → Prop
  | empty (isEmpty : ¬(master d mode s).Nonempty) : Stop d mode s .emptyMaster
  | found (step : Step d mode s) (integral : Integral step.projection) :
      Stop d mode s (.found step.projection)

inductive Chain (d : Data n m l) (mode : Mode) : State n m → State n m → ℕ → Prop
  | nil (s : State n m) : Chain d mode s s 0
  | cons {s t : State n m} {k : ℕ} (step : Step d mode s)
      (fractional : ¬Integral step.projection)
      (tail : Chain d mode (append s step.event) t k) : Chain d mode s t (k+1)

theorem chain_invariant (d : Data n m l) {mode : Mode} {Q : Finset (IntVector m)}
    (hb : TargetBound d mode Q) (hn : NormalLaw d mode Q)
    {s t : State n m} {k : ℕ} (hs : Invariant d Q s) (hc : Chain d mode s t k) :
    Invariant d Q t := by
  revert hs
  induction hc with
  | nil => exact id
  | cons step hf tail ih =>
    intro hs
    exact ih (append_invariant d hb hn hs step hf)

theorem chain_length (d : Data n m l) {mode : Mode} {s t : State n m} {k : ℕ}
    (hc : Chain d mode s t k) : t.history.length = s.history.length+k := by
  induction hc with
  | nil => simp
  | cons step hf tail ih =>
    simp only [append, List.length_append, List.length_singleton] at ih
    omega

theorem run_execution (d : Data n m l) (mode : Mode) (choose : Selector d mode)
    (fuel : ℕ) (s : State n m) (hs : s.seed ∈ d.relaxation) {out : LoopOutput n m}
    (hr : run d mode choose fuel s hs = some out) :
    Chain d mode s out.state out.failures ∧ Stop d mode out.state out.reason ∧
      out.masters = out.failures+1 ∧
      out.projections = out.failures+terminalProjections out.reason ∧ out.failures < fuel := by
  induction fuel generalizing s out with
  | zero => simp [run] at hr
  | succ fuel ih =>
    cases hc : choose s hs with
    | empty he =>
      simp only [run, hc, Option.some.injEq] at hr
      subst out
      exact ⟨.nil s, .empty he, rfl, rfl, by simp [terminalOutput]⟩
    | project step =>
      classical
      by_cases hi : Integral step.projection
      · simp only [run, hc, if_pos hi, Option.some.injEq] at hr
        subst out
        exact ⟨.nil s, .found step hi, rfl, rfl, by simp [terminalOutput]⟩
      · simp only [run, hc, if_neg hi] at hr
        cases ht : run d mode choose fuel (append s step.event) hs with
        | none => simp [ht] at hr
        | some tail =>
          rw [ht] at hr
          have ho : tail.bump = out := Option.some.inj hr
          subst out
          obtain ⟨hchain, hstop, hM, hP, hK⟩ := ih (append s step.event) hs ht
          refine ⟨.cons step hi hchain, hstop, ?_, ?_, ?_⟩
          · simp only [LoopOutput.bump]; omega
          · simp only [LoopOutput.bump]; omega
          · simp only [LoopOutput.bump]; omega

theorem run_sufficient_fuel (d : Data n m l) {mode : Mode}
    {Q : Finset (IntVector m)} (hb : TargetBound d mode Q) (hn : NormalLaw d mode Q)
    (choose : Selector d mode) (fuel : ℕ) (s : State n m)
    (hs : Invariant d Q s) (hf : Q.card < s.history.length+fuel) :
    ∃ out, run d mode choose fuel s hs.valid.seed = some out := by
  induction fuel generalizing s with
  | zero => have hh := history_length_le d hs; omega
  | succ fuel ih =>
    cases hc : choose s hs.valid.seed with
    | empty he => exact ⟨terminalOutput s .emptyMaster, by simp [run, hc]⟩
    | project step =>
      classical
      by_cases hi : Integral step.projection
      · exact ⟨terminalOutput s (.found step.projection), by simp [run, hc, hi]⟩
      · have hs' := append_invariant d hb hn hs step hi
        have hf' : Q.card < (append s step.event).history.length+fuel := by
          simp only [append, List.length_append, List.length_singleton]
          omega
        obtain ⟨out, hout⟩ := ih (append s step.event) hs' hf'
        exact ⟨out.bump, by simp [run, hc, hi, hout]⟩

end Chapter03.FPSearch
