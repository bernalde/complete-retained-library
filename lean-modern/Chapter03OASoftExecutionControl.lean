module

public import Chapter03OASoftExecutionControlData
public import Chapter03OASoftExecutionSelectors

@[expose] public section

/-! A genuinely fractional initialized soft transition with an unbounded first
reply and a still-open next state. This uses the actual soft RawStep relation. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec Chapter03.OAExec.Controls
namespace Chapter03.OASoftExecutionAvailability.Control

def start : OASoftExec.State spec := OASoftExec.initialState spec I.seed initialPolicy

def firstChoice : OASoftExec.MasterChoice spec I.seed start where
  point := firstPoint
  attained := false
  valid := ⟨firstPoint_mem,initial_cost_unbounded⟩

theorem start_open : OASoftExec.loopOpen spec 0 start := by
  simp [OASoftExec.loopOpen,start,OASoftExec.initialState,OAExec.loopOpen,OAExec.initialState]

def afterFirst : OASoftExec.State spec :=
  OASoftExec.advance start firstChoice ArticleI.event1 firstGeneration

theorem actual_first_step : OASoftExec.RawStep spec I.seed 0 start afterFirst :=
  .step start_open firstChoice ArticleI.event1 firstGeneration firstPoint_target

theorem afterFirst_reachable : OASoftExec.Reachable spec I.seed 0 afterFirst :=
  .next (.initial initialPolicy) actual_first_step

theorem afterFirst_open : OASoftExec.loopOpen spec 0 afterFirst := by
  intro u hu
  have he : u = ArticleI.event1.anchor := by
    simpa [afterFirst,OASoftExec.advance,start,OASoftExec.initialState,
      OAExec.initialState,OAExec.nextIncumbent,OAExec.keepBest,ArticleI.event1] using hu.symm
  subst u
  exact first_fixed_gap

/-- An inhabited actual selector that takes the displayed first reply; its
remaining decisions use the derived local availability theorem. -/
def continuingSelector : OASoftExec.Selector spec I.seed 0 := by
  classical
  let fallback := Classical.choice
    (selectors_nonempty ArticleI.assumptions hard_affine I.seed ArticleI.seed_valid 0)
  exact fun s hs ho => if he : s = start then
    he.symm ▸ (OASoftExec.Decision.next firstChoice ArticleI.event1
      firstGeneration firstPoint_target) else fallback s hs ho

theorem selector_first :
    continuingSelector start (.initial initialPolicy) start_open =
      OASoftExec.Decision.next firstChoice ArticleI.event1 firstGeneration firstPoint_target := by
  classical
  simp [continuingSelector]

theorem continuing_control :
    OAExec.SeedValid spec I.seed ∧
    Nonempty (OASoftExec.Selector spec I.seed 0) ∧
    OASoftExec.RawStep spec I.seed 0 start afterFirst ∧
    OASoftExec.Reachable spec I.seed 0 afterFirst ∧
    OASoftExec.loopOpen spec 0 afterFirst ∧
    firstGeneration.rowWeight 0 = (2000/3 : ℝ) :=
  ⟨ArticleI.seed_valid,selectors_nonempty ArticleI.assumptions hard_affine I.seed
    ArticleI.seed_valid 0,actual_first_step,afterFirst_reachable,afterFirst_open,
    first_generation_weight⟩

end Chapter03.OASoftExecutionAvailability.Control
