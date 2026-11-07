module

public import Chapter03OASoftExecutionControl
public import Chapter03OASoftExecutionInitialized

@[expose] public section

/-! Actual initialized specialization of the qualified endpoint, retaining the
fractional ArticleI initializer and explicit zero seed-weight policy. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec Chapter03.OAExec.Controls
namespace Chapter03.OASoftExecutionAvailability.Control

def initializedSelector : OASoftExec.InitializedSelectors spec 0 := by
  classical
  exact fun seed hs => if he : seed = I.seed then he.symm ▸ continuingSelector
    else Classical.choice (selectors_nonempty ArticleI.assumptions hard_affine seed hs 0)

def initial : OAExec.Initialization spec :=
  .minimum I.seed ArticleI.seed_minimum ArticleI.seed_valid.2.1

theorem initialized_returns_optimum :
    ∃ out p, OASoftExec.execute spec 0 initializedSelector initialPolicy initial = some out ∧
      out.result = OAExec.Result.solution p ∧ IsMinimizer spec.original spec.f p ∧
      out.masters ≤ spec.box.card+1 ∧ out.fixed ≤ spec.box.card+1 ∧
      out.restorations ≤ spec.box.card := by
  obtain ⟨out,he,hc,hm,hf,hr⟩ := qualified_initialized_zero_return
    ArticleI.assumptions hard_affine initializedSelector initialPolicy initial
  cases hv : out.result with
  | infeasible =>
    have hn : ¬ spec.original.Nonempty := by simpa only [hv] using hc
    exact False.elim (hn ⟨pt (3/4) 1,ArticleI.solution_original⟩)
  | solution p =>
    exact ⟨out,p,he,hv,by simpa only [hv] using hc,hm,hf,hr⟩

end Chapter03.OASoftExecutionAvailability.Control
