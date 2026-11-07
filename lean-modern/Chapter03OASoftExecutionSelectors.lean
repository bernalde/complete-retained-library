module

public import Chapter03OASoftExecutionAvailability
public import Chapter03OASoftExecutionState

@[expose] public section

/-! Inhabited actual soft selectors, derived from accepted analytic/regularity
hypotheses and explicit hard-affine entailment, without a solution oracle. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec
namespace Chapter03.OASoftExecutionAvailability
variable {n m l r : ℕ} {d : OAExec.Data n m l r}

theorem local_available (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (seed : Point n m) (hs : SeedValid d seed)
    (epsilon : ℝ) : OASoftExec.LocalAvailability d seed epsilon := by
  intro s _ _ q
  exact requested_generation_exists h hard ⟨seed,hs.1.1⟩ seed s.history q.mem

theorem selectors_nonempty (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (seed : Point n m) (hs : SeedValid d seed)
    (epsilon : ℝ) : Nonempty (OASoftExec.Selector d seed epsilon) :=
  OASoftExec.selector_inhabited (local_available h hard seed hs epsilon)

theorem initialization_and_local_choices (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (epsilon : ℝ) :
    Nonempty (OAExec.Initialization d) ∧
    ∀ seed, SeedValid d seed →
      OASoftExec.LocalAvailability d seed epsilon ∧
      Nonempty (OASoftExec.Selector d seed epsilon) :=
  ⟨h.initialization_nonempty,fun seed hs =>
    ⟨local_available h hard seed hs epsilon,selectors_nonempty h hard seed hs epsilon⟩⟩

end Chapter03.OASoftExecutionAvailability
