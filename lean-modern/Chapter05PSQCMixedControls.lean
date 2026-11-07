module

public import Chapter05PSQCMixedControlData
public import Chapter05PSQCMixedReturn

@[expose] public section

/-! One actual initialized three-decision mixed PSC run. The first decision
restores an infeasible integer fiber; the next stores the NLP optimum while
its gap remains open; the final permitted repeat closes and returns it. -/
noncomputable section
open Chapter02 Chapter02PSCExamples Chapter03.OAKKT
namespace Chapter05.PSQC.Mixed.Control

def start : Exec.State context := Exec.initialState context executionSeed

theorem executionSeed_valid : QOA.Exec.SeedValid data executionSeed :=
  ⟨seed_relaxation_minimum, zeroToken_safe seed⟩

def firstBatch : Exec.Batch context executionSeed start where
  point := (firstTrial, 5/8)
  minimum := first_master_minimum
  pool := [((firstTrial, 5/8), restorationEvent)]
  includes := by simp
  valid := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact ⟨first_master_minimum.1, restorationEvent_valid, by simp [firstTrial, pt]⟩

theorem firstBatch_events : firstBatch.events = [restorationEvent] := rfl

def afterFirst : Exec.State context := Exec.advance start firstBatch

theorem start_open : Exec.loopOpen context 0 start := by
  intro u hu
  simp [start, Exec.initialState, Exec.State.project] at hu

theorem afterFirst_lower : afterFirst.lower = 5/8 := Exec.advance_lower start firstBatch

theorem afterFirst_history : afterFirst.history = [restorationEvent] := by
  unfold afterFirst
  rw [Exec.advance_history, firstBatch_events]
  rfl

theorem afterFirst_incumbent : afterFirst.incumbent = none := by
  change (Exec.pushEvents {start with lower := firstBatch.point.2}
    firstBatch.events).incumbent = none
  rw [firstBatch_events]
  change QOA.Exec.nextIncumbent (Exec.State.project {start with lower := firstBatch.point.2})
    restorationEvent.toQOA = none
  unfold QOA.Exec.nextIncumbent
  rw [if_neg (by simp [Event.toQOA, restorationEvent, restorationData, restorationQOA])]
  rfl

theorem afterFirst_open : Exec.loopOpen context 0 afterFirst := by
  intro u hu
  change afterFirst.incumbent = some u at hu
  rw [afterFirst_incumbent] at hu
  contradiction

theorem afterFirst_reachable : Exec.Reachable context executionSeed 0 afterFirst :=
  .next .initial (.step start_open firstBatch)

def secondBatch : Exec.Batch context executionSeed afterFirst where
  point := (secondTrial, 11/16)
  minimum := by rw [afterFirst_history]; exact second_master_minimum
  pool := [((secondTrial, 11/16), feasibleEvent)]
  includes := by simp
  valid := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    refine ⟨?_, feasibleEvent_valid, by simp [secondTrial, pt]⟩
    rw [afterFirst_history]
    exact second_master_minimum.1

theorem secondBatch_events : secondBatch.events = [feasibleEvent] := rfl

def afterSecond : Exec.State context := Exec.advance afterFirst secondBatch

theorem afterSecond_lower : afterSecond.lower = 11/16 := Exec.advance_lower afterFirst secondBatch

theorem afterSecond_history : afterSecond.history = [restorationEvent, feasibleEvent] := by
  simp [afterSecond, Exec.advance_history, secondBatch_events, afterFirst_history]

theorem afterSecond_incumbent : afterSecond.incumbent = some optimum := by
  change (QOA.Exec.nextIncumbent {afterFirst.project with lower := 11/16}
    feasibleEvent.toQOA) = some optimum
  have hn : feasibleEvent.toQOA.restoration = none := rfl
  rw [QOA.Exec.nextIncumbent, if_pos hn]
  change Chapter03.OAExec.keepBest data.f afterFirst.incumbent feasibleEvent.toQOA.anchor = _
  rw [afterFirst_incumbent]
  change some feasibleEvent.anchor = some optimum
  rw [feasibleEvent_anchor]

theorem afterSecond_gap : data.f optimum-afterSecond.lower = 5/16 := by
  rw [objective_optimum, afterSecond_lower]
  norm_num

theorem afterSecond_open : Exec.loopOpen context 0 afterSecond := by
  intro u hu
  change afterSecond.incumbent = some u at hu
  rw [afterSecond_incumbent] at hu
  have he : optimum = u := Option.some.inj hu
  subst u
  change 0 < data.f optimum-afterSecond.lower
  rw [afterSecond_gap]
  norm_num

theorem afterSecond_reachable : Exec.Reachable context executionSeed 0 afterSecond :=
  .next afterFirst_reachable (.step afterFirst_open secondBatch)

def thirdBatch : Exec.Batch context executionSeed afterSecond where
  point := (optimum, 1)
  minimum := by rw [afterSecond_history]; exact third_master_minimum
  pool := [((optimum, 1), feasibleEvent)]
  includes := by simp
  valid := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    refine ⟨?_, feasibleEvent_valid, by simp [optimum, pt]⟩
    rw [afterSecond_history]
    exact third_master_minimum.1

theorem thirdBatch_events : thirdBatch.events = [feasibleEvent] := rfl

def afterThird : Exec.State context := Exec.advance afterSecond thirdBatch

theorem afterThird_lower : afterThird.lower = 1 := Exec.advance_lower afterSecond thirdBatch

theorem afterThird_history :
    afterThird.history = [restorationEvent, feasibleEvent, feasibleEvent] := by
  simp [afterThird, Exec.advance_history, thirdBatch_events, afterSecond_history]

theorem afterThird_incumbent : afterThird.incumbent = some optimum := by
  change (QOA.Exec.nextIncumbent {afterSecond.project with lower := 1}
    feasibleEvent.toQOA) = some optimum
  have hn : feasibleEvent.toQOA.restoration = none := rfl
  rw [QOA.Exec.nextIncumbent, if_pos hn]
  change Chapter03.OAExec.keepBest data.f afterSecond.incumbent feasibleEvent.anchor = _
  rw [afterSecond_incumbent, feasibleEvent_anchor]
  simp [Chapter03.OAExec.keepBest]

theorem afterThird_closed : ¬ Exec.loopOpen context 0 afterThird := by
  intro h
  have hh := h optimum afterThird_incumbent
  change 0 < data.f optimum-afterThird.lower at hh
  rw [objective_optimum, afterThird_lower] at hh
  norm_num at hh

theorem afterThird_reachable : Exec.Reachable context executionSeed 0 afterThird :=
  .next afterSecond_reachable (.step afterSecond_open thirdBatch)

theorem afterFirst_ne_start : afterFirst ≠ start := by
  intro h
  have hh := congrArg Exec.State.history h
  rw [afterFirst_history] at hh
  change [restorationEvent] = [] at hh
  contradiction

theorem afterSecond_ne_start : afterSecond ≠ start := by
  intro h
  have hh := congrArg Exec.State.history h
  rw [afterSecond_history] at hh
  change [restorationEvent, feasibleEvent] = [] at hh
  contradiction

theorem afterSecond_ne_afterFirst : afterSecond ≠ afterFirst := by
  intro h
  have hh := congrArg (fun s : Exec.State context => s.history.length) h
  rw [afterFirst_history, afterSecond_history] at hh
  norm_num at hh

/-- Only three replies are consulted. All other states use derived availability. -/
def controlSelector : Exec.Selector context executionSeed := by
  classical
  exact fun s => if h : s = start then h.symm ▸ Exec.Decision.batch firstBatch
    else if h : s = afterFirst then h.symm ▸ Exec.Decision.batch secondBatch
    else if h : s = afterSecond then h.symm ▸ Exec.Decision.batch thirdBatch
    else Classical.choice (Exec.decision_exists context executionSeed s)

theorem controlSelector_start : controlSelector start = Exec.Decision.batch firstBatch := by
  simp [controlSelector]

theorem controlSelector_afterFirst :
    controlSelector afterFirst = Exec.Decision.batch secondBatch := by
  simp [controlSelector, afterFirst_ne_start]

theorem controlSelector_afterSecond :
    controlSelector afterSecond = Exec.Decision.batch thirdBatch := by
  simp [controlSelector, afterSecond_ne_start, afterSecond_ne_afterFirst]

def actualResult : Exec.RunResult context := ⟨afterThird, QOA.Exec.Stop.stored optimum, 3⟩

theorem control_run_step (fuel : ℕ) (s : Exec.State context)
    (b : Exec.Batch context executionSeed s)
    (ho : Exec.loopOpen context 0 s) (hs : controlSelector s = Exec.Decision.batch b) :
    Exec.run controlSelector 0 (fuel+1) s =
      let r := Exec.run controlSelector 0 fuel (Exec.advance s b)
      {r with decisions := r.decisions+1} := by
  exact Exec.run_step controlSelector 0 fuel s b ho hs

/-- Actual recursive evaluation includes both continuing batches and the closing repeat. -/
theorem three_batch_run (fuel : ℕ) :
    Exec.run controlSelector 0 (fuel+3) start = actualResult := by
  rw [control_run_step (fuel+2) start firstBatch start_open controlSelector_start]
  change (let r := Exec.run controlSelector 0 (fuel+2) afterFirst
    ; {r with decisions := r.decisions+1}) = actualResult
  rw [control_run_step (fuel+1) afterFirst secondBatch afterFirst_open controlSelector_afterFirst]
  have hthird := Exec.run_one_batch_closed controlSelector 0 fuel afterSecond thirdBatch
    controlSelector_afterSecond afterSecond_open afterThird_closed afterThird_incumbent
  change Exec.run controlSelector 0 (fuel+1) afterSecond =
    ⟨afterThird, QOA.Exec.Stop.stored optimum, 1⟩ at hthird
  rw [← show afterSecond = Exec.advance afterFirst secondBatch from rfl]
  rw [hthird]
  rfl

def fractionalInitialization : QOA.Exec.Initialization data :=
  .fractional executionSeed executionSeed_valid seed_fractional

def initializedSelectors : (a : QOA.Token 1 1 1) → Exec.Selector context a := by
  classical
  exact fun a => if h : a = executionSeed then h.symm ▸ controlSelector
    else Classical.choice (Exec.selector_exists context a)

theorem initializedSelectors_seed : initializedSelectors executionSeed = controlSelector := by
  simp [initializedSelectors]

theorem initialized_run :
    Exec.solve 0 fractionalInitialization initializedSelectors =
      Exec.Answer.loop executionSeed actualResult := by
  change Exec.Answer.loop executionSeed
    (Exec.run (initializedSelectors executionSeed) 0 (data.activeY.card+1) start) = _
  rw [initializedSelectors_seed, activeY_card]
  exact congrArg (Exec.Answer.loop executionSeed) (three_batch_run 0)

theorem initialized_correct :
    Exec.AnswerCorrect 0 (Exec.Answer.loop executionSeed actualResult) := by
  have h := Exec.source_initialized_return (le_refl (0 : ℝ))
    fractionalInitialization initializedSelectors
  rw [initialized_run] at h
  exact h

theorem execution_stored_correct : Exec.StoredCorrect 0 afterThird optimum :=
  initialized_correct.2.1

theorem execution_exact_minimum : IsMinimizer data.original data.f optimum :=
  Exec.stored_zero_exact execution_stored_correct

/-- The maximum three singleton decisions are actually used. The returned value
is the stored fixed-fiber NLP point; the earlier nonlinear-infeasible master
trial is distinct. The coefficient1 PSC row uses its actual selected source. -/
theorem three_batch_stored_return :
    Exec.solve 0 fractionalInitialization initializedSelectors =
      Exec.Answer.loop executionSeed ⟨afterThird, QOA.Exec.Stop.stored optimum, 3⟩ ∧
    IsMinimizer data.original data.f optimum ∧
    afterThird.history = [restorationEvent, feasibleEvent, feasibleEvent] ∧
    afterThird.incumbent = some optimum ∧ afterThird.lower = 1 ∧
    afterFirst.incumbent = none ∧ data.f optimum-afterSecond.lower = 5/16 ∧
    secondTrial ∉ data.original ∧ secondTrial ≠ optimum ∧
    data.activeY.card+1 = 3 := by
  exact ⟨initialized_run, execution_exact_minimum, afterThird_history,
    afterThird_incumbent, afterThird_lower, afterFirst_incumbent, afterSecond_gap,
    secondTrial_not_original, secondTrial_ne_optimum, by rw [activeY_card]⟩

end Chapter05.PSQC.Mixed.Control
