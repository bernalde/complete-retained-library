module

public import Chapter03FPSearchProcedure

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch
variable {n m l : ℕ}

def LoopCorrect (d : Data n m l) (out : LoopOutput n m) : Prop :=
  match out.reason with
  | .emptyMaster => ¬d.original.Nonempty
  | .found p => p ∈ d.original

structure LoopCounts (N : ℕ) (out : LoopOutput n m) : Prop where
  failures_eq_history : out.failures = out.state.history.length
  master_exact : out.masters = out.failures+1
  projection_exact : out.projections = out.failures+terminalProjections out.reason
  projections_le : out.projections ≤ N
  masters_le : out.masters ≤ N+1
  success_masters_le : ∀ p, out.reason = .found p → out.masters ≤ N

theorem run_initial_guarantees (d : Data n m l) (h : Analytic d) {mode : Mode}
    {Q : Finset (IntVector m)} (hb : TargetBound d mode Q) (hn : NormalLaw d mode Q)
    (choose : Selector d mode) {p : Point n m} (hp : p ∈ d.relaxation)
    {fuel : ℕ} {out : LoopOutput n m}
    (hr : run d mode choose fuel (initialState p) hp = some out) :
    Invariant d Q out.state ∧ LoopCorrect d out ∧ LoopCounts Q.card out := by
  obtain ⟨hchain, hstop, hM, hP, _⟩ := run_execution d mode choose fuel (initialState p) hp hr
  have hs := chain_invariant d hb hn (initial_invariant d Q hp) hchain
  have hlen := chain_length d hchain
  have hF : out.failures = out.state.history.length := by
    simpa only [initialState, List.length_nil, zero_add] using hlen.symm
  have hbound := history_length_le d hs
  refine ⟨hs, ?_, ⟨hF, hM, hP, ?_, ?_, ?_⟩⟩
  · generalize heq : out.reason = reason at hstop
    cases hstop with
    | empty he =>
      simpa [LoopCorrect, heq] using empty_master_infeasible d h hs.valid he
    | found step hi =>
      have hp' : step.projection ∈ d.original := ⟨step.projection_min.1, hi⟩
      simpa [LoopCorrect, heq] using hp'
  · generalize heq : out.reason = reason at hstop
    cases hstop with
    | empty he => rw [heq] at hP; simp only [terminalProjections] at hP; omega
    | found step hi =>
      have hbnd := step_count_le d hb hn hs step
      rw [heq] at hP
      simp only [terminalProjections] at hP
      omega
  · omega
  · intro z hz
    generalize heq : out.reason = reason at hstop
    cases hstop with
    | empty he => rw [heq] at hz; cases hz
    | found step hi =>
      have hbnd := step_count_le d hb hn hs step
      omega

def Outcome.Correct (d : Data n m l) : Outcome n m → Prop
  | .initialEmpty => ¬d.original.Nonempty
  | .initialOptimal p => IsMinimizer d.original d.f p
  | .loop out => LoopCorrect d out

def Outcome.masterCalls : Outcome n m → ℕ
  | .initialEmpty => 0
  | .initialOptimal _ => 0
  | .loop out => out.masters

def Outcome.projectionCalls : Outcome n m → ℕ
  | .initialEmpty => 0
  | .initialOptimal _ => 0
  | .loop out => out.projections

/-- Exactly one initialization decision is separate from the loop counts. -/
def Outcome.initializerCalls (_ : Outcome n m) : ℕ := 1

def Outcome.Counts (N : ℕ) (out : Outcome n m) : Prop :=
  out.initializerCalls = 1 ∧ out.masterCalls ≤ N+1 ∧ out.projectionCalls ≤ N ∧
    (∀ loop, out = .loop loop → LoopCounts N loop)

theorem initialized_finite_return (d : Data n m l) (h : Analytic d) {mode : Mode}
    {Q : Finset (IntVector m)} (hb : TargetBound d mode Q) (hn : NormalLaw d mode Q)
    (initial : Initialization d) (choose : Selector d mode) :
    ∃ out, procedureWithFuel d mode initial choose (Q.card+1) = some out ∧
      out.Correct d ∧ out.Counts Q.card := by
  classical
  cases initial with
  | empty he =>
    refine ⟨.initialEmpty, rfl, ?_, ?_⟩
    · rintro ⟨p, hp⟩
      exact he ⟨p, hp.1⟩
    · simp [Outcome.Counts, Outcome.initializerCalls, Outcome.masterCalls,
        Outcome.projectionCalls]
  | minimum p hp =>
    by_cases hi : Integral p
    · refine ⟨.initialOptimal p, ?_, ?_, ?_⟩
      · simp [procedureWithFuel, hi]
      · exact ⟨⟨hp.1, hi⟩, fun z hz => hp.2 z hz.1⟩
      · simp [Outcome.Counts, Outcome.initializerCalls, Outcome.masterCalls,
          Outcome.projectionCalls]
    · have hs := initial_invariant d Q hp.1
      obtain ⟨out, hout⟩ := run_sufficient_fuel d hb hn choose (Q.card+1)
        (initialState p) hs (by simp [initialState])
      obtain ⟨_, hcorrect, hcounts⟩ := run_initial_guarantees d h hb hn choose hp.1 hout
      refine ⟨.loop out, ?_, hcorrect, ?_⟩
      · simp [procedureWithFuel, hi, hout]
      · exact ⟨rfl, hcounts.masters_le, hcounts.projections_le,
          fun loop he => by cases he; exact hcounts⟩

/-- Qualified enhanced first-feasibility endpoint. NormalLaw is discharged
from actual enhanced master membership; existence is proved before universal
quantification over all exact tied initializer and selector choices. -/
theorem qualified_enhanced_first_feasibility (d : Data n m l) (h : Analytic d)
    (Q : Finset (IntVector m)) (hb : TargetBound d .enhanced Q) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d .enhanced) ∧
      ∀ (initial : Initialization d) (choose : Selector d .enhanced),
        ∃ out, procedureWithFuel d .enhanced initial choose (Q.card+1) = some out ∧
          out.Correct d ∧ out.Counts Q.card := by
  exact ⟨initialization_nonempty d h, selector_nonempty d h .enhanced,
    fun initial choose => initialized_finite_return d h hb
      (enhanced_normal_law d Q) initial choose⟩

end Chapter03.FPSearch
