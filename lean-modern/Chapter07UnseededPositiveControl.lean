module

public import Chapter07UnseededControls
public import Chapter07UnseededRankings

@[expose] public section

/-! An exact feasible-first unseeded control. The retained initializer differs
from the stored incumbent; a positive-gap L1 minimum actually chooses the next
restoration fiber. All decisions, ranking certificates and initializer counts
belong to the actual driver. This is an invented control, not an experiment. -/
noncomputable section
open Set Chapter02 Chapter06.Level Chapter07.UnseededExec
open Chapter07.UnseededControl Chapter07.UnseededControl.Feasible
namespace Chapter07.UnseededPositiveControl

theorem first_master_minimum : IsMinimizer (master d a0 []) Prod.snd p1 := by
  refine ⟨(initial_master_iff p1).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · change p1.1 ∈ (boxData f g).mixed
    simpa [p1] using box_point_mixed f g (13/16) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num [p1, pt, Chapter06.LevelControl.pt]
  · norm_num [p1, pt, Chapter06.LevelControl.pt]
  · intro z hz
    simpa [p0, p1] using initial_master_minimum.2 z hz

theorem after_feasible_master_iff (z : P × ℝ) :
    z ∈ master d a0 [feasibleEvent] ↔
      z.1 ∈ d.mixed ∧ z.1.1 0-z.1.2 0+3/16 ≤ 0 ∧
      (3/2)*z.1.1 0-z.1.2 0-1/8 ≤ 0 ∧ z.1.2 0-z.1.1 0 ≤ z.2 := by
  simp [master, masterBase, pscEnvelopeEpigraph, pscEnvelopeRows, origins,
    feasibleEvent, Event.rho, seed_rows_iff, optimum_rows_iff, objective_tangent,
    and_assoc]
  tauto

theorem after_feasible_master_minimum :
    IsMinimizer (master d a0 [feasibleEvent]) Prod.snd p0 := by
  refine ⟨(after_feasible_master_iff p0).mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · change p0.1 ∈ (boxData f g).mixed
    simpa [p0] using box_point_mixed f g (-3/16) 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num [p0, pt, Chapter06.LevelControl.pt]
  · norm_num [p0, pt, Chapter06.LevelControl.pt]
  · norm_num [p0, pt, Chapter06.LevelControl.pt]
  · intro z hz
    obtain ⟨_, hs, _, ho⟩ := (after_feasible_master_iff z).mp hz
    change (3/16 : ℝ) ≤ z.2
    linarith

theorem after_feasible_incumbent :
    incumbent d optimum [feasibleEvent] = optimum := by
  simp [incumbent, feasibleEvent, keepBetter]

theorem positive_gap :
    d.f (incumbent d optimum [feasibleEvent])-p0.2 = 1/16 := by
  rw [after_feasible_incumbent]
  norm_num [d, boxData, f, optimum, p0, pt, Chapter06.LevelControl.pt]

def positiveLevel : Set (P × ℝ) :=
  Unseeded.level d a0 optimum [feasibleEvent] (3/16) (1/2)

theorem positive_level_rows (z : P × ℝ) : z ∈ positiveLevel ↔
    z.1 ∈ d.mixed ∧ z.1.1 0-z.1.2 0+3/16 ≤ 0 ∧
    (3/2)*z.1.1 0-z.1.2 0-1/8 ≤ 0 ∧
    z.1.2 0-z.1.1 0 ≤ z.2 ∧ z.2 ≤ 7/32 := by
  unfold positiveLevel Unseeded.level Auxiliary.cappedMaster
  simp only [Set.mem_setOf_eq]
  rw [after_feasible_master_iff, after_feasible_incumbent]
  have hc : Chapter06.Level (3/16) (d.f optimum) (1/2) = (7/32 : ℝ) := by
    norm_num [Chapter06.Level, d, boxData, f, optimum, pt, Chapter06.LevelControl.pt]
  rw [hc]
  tauto

/-- The complete epigraph level, including the nonunique allowed heights. -/
theorem positive_level_iff (z : P × ℝ) : z ∈ positiveLevel ↔
    z.1.2 0 = 0 ∧ (-7/32 : ℝ) ≤ z.1.1 0 ∧ z.1.1 0 ≤ -3/16 ∧
      -z.1.1 0 ≤ z.2 ∧ z.2 ≤ 7/32 := by
  rw [positive_level_rows]
  constructor
  · rintro ⟨hm, hs, hu, ho, hc⟩
    rcases box_integer_cases f g hm with hy | hy
    · exact ⟨hy, by linarith, by linarith, by linarith, hc⟩
    · exfalso
      linarith
  · rintro ⟨hy, hx0, hx1, ht, hc⟩
    refine ⟨?_, by linarith, by linarith, by linarith, hc⟩
    refine ⟨(box_hard_iff f g _).mpr ⟨by linarith, by linarith,
      by linarith, by linarith⟩, iy 0, ?_⟩
    funext i
    fin_cases i
    simpa [intCast, iy, Chapter06.LevelControl.iy] using hy

theorem p0_in_positive_level : p0 ∈ positiveLevel := by
  apply (positive_level_iff p0).mpr
  norm_num [p0, pt, Chapter06.LevelControl.pt]

theorem l1_on_positive_level {z : P × ℝ} (hz : z ∈ positiveLevel) :
    SevenRankings.l1 optimum z.1 = 7/4-z.1.1 0 := by
  obtain ⟨hy, _, hx, _, _⟩ := (positive_level_iff z).mp hz
  simp only [SevenRankings.l1, Fin.sum_univ_one]
  change |z.1.1 0-3/4| + |z.1.2 0-1| = 7/4-z.1.1 0
  rw [abs_of_nonpos (by linarith), hy]
  norm_num
  ring

theorem positive_level_l1_minimum :
    IsMinimizer positiveLevel (fun z => SevenRankings.l1 optimum z.1) p0 := by
  refine ⟨p0_in_positive_level, ?_⟩
  intro z hz
  change SevenRankings.l1 optimum p0.1 ≤ SevenRankings.l1 optimum z.1
  rw [l1_on_positive_level p0_in_positive_level, l1_on_positive_level hz]
  have hx := ((positive_level_iff z).mp hz).2.2.1
  norm_num [p0, pt, Chapter06.LevelControl.pt]
  linarith

theorem positive_level_l1_value : SevenRankings.l1 optimum p0.1 = 31/16 := by
  rw [l1_on_positive_level p0_in_positive_level]
  norm_num [p0, pt, Chapter06.LevelControl.pt]

theorem final_master_iff (z : P × ℝ) :
    z ∈ master d a0 [restoredEvent, feasibleEvent] ↔
      z.1 ∈ d.mixed ∧ z.1.1 0-z.1.2 0+3/16 ≤ 0 ∧
      (3/2)*z.1.1 0-z.1.2 0-1/8 ≤ 0 ∧ (7/16 : ℝ) ≤ z.1.2 0 ∧
      z.1.2 0-z.1.1 0 ≤ z.2 := by
  simp [master, masterBase, pscEnvelopeEpigraph, pscEnvelopeRows, origins,
    feasibleEvent, restoredEvent, Event.rho, seed_rows_iff, optimum_rows_iff,
    restored_rows_iff, objective_tangent, and_assoc]
  tauto

theorem final_master_minimum :
    IsMinimizer (master d a0 [restoredEvent, feasibleEvent]) Prod.snd p2 := by
  have he : master d a0 [restoredEvent, feasibleEvent] =
      master d a0 [feasibleEvent, restoredEvent] := by
    ext z
    rw [final_master_iff, third_master_iff]
  rw [he]
  exact third_master_minimum

theorem final_incumbent :
    incumbent d optimum [restoredEvent, feasibleEvent] = optimum := by
  simp [incumbent, feasibleEvent, restoredEvent, keepBetter]

theorem final_gap :
    d.f (incumbent d optimum [restoredEvent, feasibleEvent])-p2.2 = 0 := by
  rw [final_incumbent]
  norm_num [d, boxData, f, optimum, p2, pt, Chapter06.LevelControl.pt]

def start : State d := initial d
def firstState : State d := advance start feasibleEvent
def finalState : State d := advance firstState restoredEvent

theorem first_baseline : firstState.baseline = some answer := by
  simp [firstState, start, advance, initial, feasibleEvent, answer]

theorem final_baseline : finalState.baseline = some answer :=
  advance_baseline_some firstState restoredEvent answer first_baseline

theorem distinct_anchors : a0 ≠ optimum := by
  intro he
  have hx := congrArg (fun p : P => p.1 0) he
  norm_num [a0, optimum, pt, Chapter06.LevelControl.pt] at hx

def ranking (a : P) (s : State d) : P → ℝ :=
  UnseededRankings.stateRanking d a (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => 0) (fun _ => .l1) s

def defaultSelector (a : P) : Selector d a (1/2) 0 :=
  UnseededRankings.sevenSelector regularity a (by norm_num) (by norm_num)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => .l1)

theorem default_ranked (a : P) (s : State d) :
    RankedLegal a (1/2) 0 (fun _ => ranking a s) s (defaultSelector a s).action :=
  UnseededRankings.sevenSelector_spec regularity a (by norm_num) (by norm_num)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => .l1) s

theorem first_ranking : ranking a0 firstState = SevenRankings.l1 optimum := by
  change SevenRankings.l1 (UnseededRankings.stateCentre a0 firstState) = _
  rw [UnseededRankings.stateCentre_some a0 firstState answer first_baseline]
  exact congrArg SevenRankings.l1 after_feasible_incumbent

def firstDecision : Decision d a0 (1/2) 0 start :=
  ⟨.process feasibleEvent, Or.inl ⟨rfl, p1, first_master_minimum,
    by simpa [p1, feasibleEvent] using pt_intCast (13/16) 1⟩⟩

def restorationDecision : Decision d a0 (1/2) 0 firstState := by
  refine ⟨.process restoredEvent, Or.inr ⟨answer, first_baseline, p0,
    after_feasible_master_minimum, ?_, p0, p0_in_positive_level, ?_⟩⟩
  · change ¬ (d.f (incumbent d optimum [feasibleEvent])-p0.2 ≤ 0)
    rw [positive_gap]
    norm_num
  · simpa [p0, restoredEvent] using pt_intCast (-3/16) 0

def returnDecision : Decision d a0 (1/2) 0 finalState := by
  refine ⟨.returned optimum, answer, final_baseline, ?_, p2, final_master_minimum, ?_⟩
  · exact final_incumbent.symm
  · exact le_of_eq final_gap

theorem firstDecision_ranked : RankedLegal a0 (1/2) 0
    (fun _ => ranking a0 start) start firstDecision.action := Or.inl rfl

theorem restorationDecision_ranked : RankedLegal a0 (1/2) 0
    (fun _ => ranking a0 firstState) firstState restorationDecision.action := by
  refine Or.inr ⟨answer, first_baseline, p0, after_feasible_master_minimum,
    ?_, p0, ?_, ?_⟩
  · change ¬ (d.f (incumbent d optimum [feasibleEvent])-p0.2 ≤ 0)
    rw [positive_gap]
    norm_num
  · rw [first_ranking]
    exact positive_level_l1_minimum
  · simpa [p0, restoredEvent] using pt_intCast (-3/16) 0

theorem returnDecision_ranked : RankedLegal a0 (1/2) 0
    (fun _ => ranking a0 finalState) finalState returnDecision.action := trivial

def selector : Selector d a0 (1/2) 0 :=
  withDecision (withDecision (withDecision (defaultSelector a0)
    finalState returnDecision) firstState restorationDecision) start firstDecision

theorem firstState_ne_start : firstState ≠ start := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [firstState, start, advance, initial] at hlen

theorem finalState_ne_start : finalState ≠ start := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [finalState, firstState, start, advance, initial] at hlen

theorem finalState_ne_first : finalState ≠ firstState := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [finalState, firstState, start, advance, initial] at hlen

theorem selector_start : (selector start).action = .process feasibleEvent := by
  rw [selector, withDecision_at]
  rfl

theorem selector_first : (selector firstState).action = .process restoredEvent := by
  rw [selector, withDecision_away _ _ _ _ firstState_ne_start, withDecision_at]
  rfl

theorem selector_final : (selector finalState).action = .returned optimum := by
  rw [selector, withDecision_away _ _ _ _ finalState_ne_start,
    withDecision_away _ _ _ _ finalState_ne_first, withDecision_at]
  rfl

/-- The finite overrides preserve the actual state-specific ranking certificate,
including at all states outside this concrete three-inspection trace. -/
theorem selector_ranked (s : State d) : RankedLegal a0 (1/2) 0
    (fun _ => ranking a0 s) s (selector s).action := by
  by_cases h0 : s = start
  · subst s
    rw [selector, withDecision_at]
    exact firstDecision_ranked
  by_cases h1 : s = firstState
  · subst s
    rw [selector, withDecision_away _ _ _ _ firstState_ne_start, withDecision_at]
    exact restorationDecision_ranked
  by_cases h2 : s = finalState
  · subst s
    rw [selector, withDecision_away _ _ _ _ finalState_ne_start,
      withDecision_away _ _ _ _ finalState_ne_first, withDecision_at]
    exact returnDecision_ranked
  rw [selector, withDecision_away _ _ _ _ h0, withDecision_away _ _ _ _ h1,
    withDecision_away _ _ _ _ h2]
  exact default_ranked a0 s

theorem positive_gap_exact_replay : run selector 2 start =
    ⟨finalState, .returned optimum, 2, 3⟩ := by
  calc
    run selector 2 start = countStep (run selector 1 firstState) :=
      run_process_succ selector 1 start feasibleEvent selector_start
    _ = countStep (countStep (run selector 0 finalState)) :=
      congrArg countStep (run_process_succ selector 0 firstState restoredEvent selector_first)
    _ = ⟨finalState, .returned optimum, 2, 3⟩ := by
      rw [run_returned selector 0 finalState optimum selector_final]
      rfl

def selectorFamily (a : P) : Selector d a (1/2) 0 := by
  classical
  exact if h : a = a0 then h.symm ▸ selector else defaultSelector a

theorem selectorFamily_at : selectorFamily a0 = selector := by
  simp [selectorFamily]

theorem selectorFamily_ranked (a : P) (s : State d) :
    RankedLegal a (1/2) 0 (fun _ => ranking a s) s (selectorFamily a s).action := by
  classical
  by_cases h : a = a0
  · subst a
    simpa [selectorFamily] using selector_ranked s
  · simpa [selectorFamily, h] using default_ranked a s

def execution : InitializedResult d :=
  initializeRun regularity (.attained a0 initializer_minimum) selectorFamily

theorem initialized_execution : execution =
    ⟨⟨finalState, .returned optimum, 2, 3⟩, 1⟩ := by
  change (⟨solve regularity (selectorFamily a0), 1⟩ : InitializedResult d) = _
  rw [selectorFamily_at]
  unfold solve
  rw [target_count]
  exact congrArg (fun result => (⟨result, 1⟩ : InitializedResult d)) positive_gap_exact_replay

theorem initialized_correct : Correct 0 execution.result.state execution.result.outcome :=
  (source_initialized_return regularity (by norm_num) (by norm_num)
    (.attained a0 initializer_minimum) selectorFamily).2.2.1

/-- The actual initialized run uses the positive-gap L1 route, restores the
other integer fiber, retains every row and returns after two events. -/
theorem actual_positive_gap_control :
    IsMinimizer (Unseeded.relaxation d) d.f a0 ∧ a0 ≠ optimum ∧
      firstState.baseline = some answer ∧ ranking a0 firstState = SevenRankings.l1 optimum ∧
      d.f (incumbent d optimum firstState.history)-p0.2 = 1/16 ∧
      IsMinimizer positiveLevel (fun z => ranking a0 firstState z.1) p0 ∧
      ranking a0 firstState p0.1 = 31/16 ∧
      execution.result.outcome = .returned optimum ∧ execution.result.processed = 2 ∧
      execution.result.queries = 3 ∧ execution.initializerInspections = 1 ∧
      execution.result.state.history = [restoredEvent, feasibleEvent] ∧
      execution.result.state.baseline = some answer := by
  rw [initialized_execution, first_ranking]
  exact ⟨initializer_minimum, distinct_anchors, first_baseline, rfl, positive_gap,
    positive_level_l1_minimum, positive_level_l1_value, rfl, rfl, rfl, rfl, rfl,
    final_baseline⟩

end Chapter07.UnseededPositiveControl

#print axioms Chapter07.UnseededPositiveControl.positive_level_iff
#print axioms Chapter07.UnseededPositiveControl.positive_level_l1_minimum
#print axioms Chapter07.UnseededPositiveControl.selectorFamily_ranked
#print axioms Chapter07.UnseededPositiveControl.initialized_execution
#print axioms Chapter07.UnseededPositiveControl.initialized_correct
#print axioms Chapter07.UnseededPositiveControl.actual_positive_gap_control
