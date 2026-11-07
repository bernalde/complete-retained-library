module

public import Chapter03OAExecArticleGUniversal
public import Chapter03OAExecArticleATrace

@[expose] public section

/-! The literal negative endpoint remains separate from the corrected main
finite-return theorem. It concerns only the displayed reversed incumbent guard,
with explicit C¹ initialization and the disclosed empty-master convention. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article.LiteralG

/-- The finite-lower running state and the printed L=+infinity assignment are
represented separately. For the latter we explicitly complete the undefined
(+infinity)-(+infinity) test by declaring the guard closed and the return
infeasible. G never reaches that completion, so its infinite trace is independent
of this convention. -/
inductive Phase
  | running (state : State)
  | emptyMaster

def phaseGapOpen (epsilon : ℝ) : Phase → Prop
  | .running s => gapOpen epsilon s
  | .emptyMaster => False

def emptyMasterResult : Result 1 1 := .infeasible

inductive SourceAction (epsilon : ℝ) : Phase → Phase → Prop
  | round {s t : State} (step : Step epsilon s t) :
      SourceAction epsilon (.running s) (.running t)
  | empty {s : State} (open_gap : gapOpen epsilon s) (empty : emptyExit s) :
      SourceAction epsilon (.running s) .emptyMaster

theorem empty_convention_closed (epsilon : ℝ) :
    ¬ phaseGapOpen epsilon Phase.emptyMaster ∧ emptyMasterResult=Result.infeasible :=
  ⟨id,rfl⟩

theorem source_infinite_actions (epsilon : ℝ) :
    (∀ n, SourceAction epsilon (.running (trace n)) (.running (trace (n+1)))) ∧
    (∀ n, phaseGapOpen epsilon (.running (trace n))) ∧
    (∀ n, ¬ SourceAction epsilon (.running (trace n)) .emptyMaster) := by
  refine ⟨fun n => .round (infinite_exact_step epsilon n),fun _ => trivial,?_⟩
  intro n h
  cases h with
  | empty ho he => exact (literal_infinite_execution epsilon).2.2.2.2 n he

theorem completed_round_count (n : ℕ) : (trace n).history.length=n := by
  simp [trace,history]

theorem no_restoration_invoked (n : ℕ) :
    (fiber G (scalar (chosen n:ℝ))).Nonempty :=
  ⟨scalar 0,(G_fiber_minimum _).1⟩

/-- The complete witness has the actual article source model, attained
fractional initialization, ambient convex derivatives, exact master and fixed
subsolves, fixed-x LICQ, no invoked restoration, permanently absent UB/output,
and an infinite legal source execution. No cited OA theorem or code is refuted. -/
theorem literal_published_guard_counterexecution (epsilon : ℝ) :
    IsMinimizer Gdata.relaxation Gdata.f seed ∧ ¬ integral seed ∧
    Analytic Gdata ∧ Gdata.original.Nonempty ∧
    (∀ n, IsMinimizer (master (history n) []) Prod.snd (trial n)) ∧
    (∀ n, IsMinimizer (fiber G (scalar (chosen n:ℝ)))
      (fiberObjective Gf (scalar (chosen n:ℝ))) (scalar 0)) ∧
    (∀ n, G_active (scalar (chosen n:ℝ))=∅) ∧
    (∀ n, (fiber G (scalar (chosen n:ℝ))).Nonempty) ∧
    (∀ n, SourceAction epsilon (.running (trace n)) (.running (trace (n+1)))) ∧
    (∀ n, phaseGapOpen epsilon (.running (trace n))) ∧
    (∀ n, (trace n).upper=none ∧ (trace n).output=none) ∧
    (∀ n, ¬ emptyExit (trace n)) := by
  exact ⟨G_initial_minimum,G_initial_fractional,G_analytic,⟨pt 0 0,G_original_at_zero⟩,
    trial_minimum,fun _ => G_fiber_minimum _,fun _ => G_active_empty _,no_restoration_invoked,
    (source_infinite_actions epsilon).1,(source_infinite_actions epsilon).2.1,
    (literal_infinite_execution epsilon).2.2.2.1,
    (literal_infinite_execution epsilon).2.2.2.2⟩

end Chapter03.OAExec.Article.LiteralG

#print axioms Chapter03.OAExec.Article.LiteralG.literal_published_guard_counterexecution
#print axioms Chapter03.OAExec.Article.G_fixed_LICQ
#print axioms Chapter03.OAExec.Article.LiteralG.source_infinite_actions
