module

public import Chapter05QOAControlData
public import Chapter05QOAStatic
public import Chapter05QOAState
public import Chapter05QOAReturn

@[expose] public section

/-! Actual static and return endpoint applications for the single N2 control. -/
noncomputable section
open Set Chapter02 Chapter03.OAKKT
namespace Chapter05.QOA.Control

theorem completeEvents_valid : ∀ e ∈ completeEvents, EventValid data e := by
  intro e he
  simp only [completeEvents,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · exact restorationEvent_valid
  · exact feasibleEvent_valid

theorem completeRows_safe : SafeRows data completeRows := by
  intro t ht
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp ht
  exact (completeEvents_valid e he).1

theorem completeRows_contains : ∀ e ∈ completeEvents, e.token ∈ completeRows := by
  intro e he
  exact List.mem_map.mpr ⟨e,he,rfl⟩

theorem complete_history : CompleteHistory data completeEvents := by
  intro y hy _
  rcases (mem_Y y).mp hy with rfl | rfl
  · exact ⟨restorationEvent,by simp [completeEvents],rfl⟩
  · exact ⟨feasibleEvent,by simp [completeEvents],rfl⟩

/-- The actual static endpoint supplies a stored original optimum at master value2. -/
theorem static_stored_optimum :
    ∃ e ∈ completeEvents, e.restoration = none ∧
      IsMinimizer data.original data.f e.anchor ∧ data.f e.anchor = 2 :=
  complete_master_minimum_stored_optimum regularity completeEvents_valid
    completeRows_safe completeRows_contains complete_history complete_master_minimum

theorem static_original_minimum : IsMinimizer data.original data.f optimum := by
  obtain ⟨e,he,hn,hm,_⟩ := static_stored_optimum
  simp only [completeEvents,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  · simp [restorationEvent] at hn
  · simpa only [feasibleEvent_anchor] using hm

theorem static_lifted_minimum :
    IsMinimizer (master data completeRows) Prod.snd (optimum,2) := by
  have h := original_minimizer_lifts_to_complete_master regularity
    completeEvents_valid completeRows_safe completeRows_contains complete_history
    static_original_minimum
  simpa only [data,objective_optimum] using h

/-- Equal optimal values do not make an arbitrary master optimizer original-feasible. -/
theorem static_control :
    IsMinimizer data.original data.f optimum ∧
    IsMinimizer (master data completeRows) Prod.snd (optimum,2) ∧
    IsMinimizer (master data completeRows) Prod.snd (trial,2) ∧
    trial ∉ data.original :=
  ⟨static_original_minimum,static_lifted_minimum,complete_master_minimum,trial_not_original⟩

def executionSeed : Token 2 1 1 := zeroToken seed
def start : Exec.State data := Exec.initialState data executionSeed

theorem executionSeed_valid : Exec.SeedValid data executionSeed :=
  ⟨seed_relaxation_minimum,zeroToken_safe seed⟩

def singletonBatch : Exec.Batch data executionSeed start where
  point := (trial,2)
  minimum := seed_master_minimum
  pool := [((trial,2),feasibleEvent)]
  includes := by simp
  valid := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    refine ⟨seed_master_minimum.1,feasibleEvent_valid,?_⟩
    funext i
    norm_num [trial,feasibleEvent,intCast,iv]

theorem singletonBatch_events : singletonBatch.events = [feasibleEvent] := rfl

theorem start_open : Exec.loopOpen data 0 start := by
  intro u hu
  simp [start,Exec.initialState] at hu

def afterBatch : Exec.State data := Exec.advance start singletonBatch

theorem afterBatch_reachable : Exec.Reachable data executionSeed 0 afterBatch :=
  .next .initial (.step start_open singletonBatch)

theorem afterBatch_lower : afterBatch.lower = 2 :=
  Exec.advance_lower start singletonBatch

theorem afterBatch_history : afterBatch.history = [feasibleEvent] := by
  unfold afterBatch
  rw [Exec.advance_history, singletonBatch_events]
  rfl

theorem afterBatch_incumbent : afterBatch.incumbent = some optimum := by
  change (Exec.pushEvents {start with lower := singletonBatch.point.2}
    singletonBatch.events).incumbent = some optimum
  rw [singletonBatch_events]
  change Exec.nextIncumbent {start with lower := singletonBatch.point.2}
    feasibleEvent = some optimum
  unfold Exec.nextIncumbent
  rw [if_pos (show feasibleEvent.restoration = none from rfl)]
  change some feasibleEvent.anchor = some optimum
  exact congrArg some feasibleEvent_anchor

theorem afterBatch_closed : ¬ Exec.loopOpen data 0 afterBatch := by
  intro h
  have hh := h optimum afterBatch_incumbent
  rw [afterBatch_lower] at hh
  change 0 < objective optimum - 2 at hh
  rw [objective_optimum] at hh
  norm_num at hh

/-- The only consulted reply is the literal singleton batch. Other states have
derived exact decisions, so this is a total permitted selector. -/
def controlSelector : Exec.Selector data executionSeed := by
  classical
  exact fun s => if h : s = start then h.symm ▸ Exec.Decision.batch singletonBatch
    else Classical.choice (Exec.decision_exists regularity executionSeed s)

theorem controlSelector_start :
    controlSelector start = Exec.Decision.batch singletonBatch := by
  simp [controlSelector]

def actualResult : Exec.RunResult data := ⟨afterBatch,Exec.Stop.stored optimum,1⟩

/-- Actual recursive evaluation consumes exactly one batch, for every positive fuel. -/
theorem one_batch_run (fuel : ℕ) :
    Exec.run controlSelector 0 (fuel+1) start = actualResult :=
  Exec.run_one_batch_closed controlSelector 0 fuel start singletonBatch
    controlSelector_start start_open afterBatch_closed afterBatch_incumbent

def fractionalInitialization : Exec.Initialization data :=
  .fractional executionSeed executionSeed_valid seed_fractional

def initializedSelectors : (a : Token 2 1 1) → Exec.Selector data a := by
  classical
  exact fun a => if h : a = executionSeed then h.symm ▸ controlSelector
    else Classical.choice (Exec.selector_exists regularity a)

theorem initializedSelectors_seed : initializedSelectors executionSeed = controlSelector := by
  simp [initializedSelectors]

/-- The actual fractional relaxation initializer enters this same one-batch run. -/
theorem initialized_run :
    Exec.solve 0 fractionalInitialization initializedSelectors =
      Exec.Answer.loop executionSeed actualResult := by
  change Exec.Answer.loop executionSeed
    (Exec.run (initializedSelectors executionSeed) 0 (data.activeY.card+1) start) = _
  rw [initializedSelectors_seed,one_batch_run]

theorem initialized_correct :
    Exec.AnswerCorrect 0 (Exec.Answer.loop executionSeed actualResult) := by
  have h := Exec.source_initialized_return regularity relaxation_regularity
    (le_refl (0 : ℝ)) fractionalInitialization initializedSelectors
  rw [initialized_run] at h
  exact h

theorem execution_stored_correct : Exec.StoredCorrect 0 afterBatch optimum :=
  initialized_correct.2.1

theorem execution_exact_minimum : IsMinimizer data.original data.f optimum :=
  Exec.stored_zero_exact execution_stored_correct

/-- One fractional-seed, singleton-pool execution returns the stored feasible
NLP point. The infeasible master trial is never the returned point. -/
theorem one_batch_stored_return :
    Exec.solve 0 fractionalInitialization initializedSelectors =
      Exec.Answer.loop executionSeed ⟨afterBatch,Exec.Stop.stored optimum,1⟩ ∧
    IsMinimizer data.original data.f optimum ∧
    afterBatch.history = [feasibleEvent] ∧ afterBatch.incumbent = some optimum ∧
    afterBatch.lower = 2 ∧ trial ∉ data.original ∧ trial ≠ optimum :=
  ⟨initialized_run,execution_exact_minimum,afterBatch_history,afterBatch_incumbent,
    afterBatch_lower,trial_not_original,trial_ne_optimum⟩

end Chapter05.QOA.Control
