module

public import Chapter04SlaterBallControl
public import Chapter04TrialHistory

@[expose] public section

/-! One accepted-model control for Chapter4 actual-trial histories. The external
objective seed comes from a feasible incumbent, not a processed fixed-NLP event.
The source loop at tolerance zero has one positive body, then stops. The zero
extension used for radius convergence is an analytic history, not an infinite
while execution. Algorithm 2.b selects strict violations; the broader printed
active-and-violated reading is not formalized by that history definition. -/

noncomputable section
open Chapter02
open scoped BigOperators
open Filter
open scoped Topology
namespace Chapter04.CenterCut.Control

theorem rows_differentiable (j : Fin 1) : Differentiable ℝ (model.g j) := by
  unfold model
  fun_prop

theorem objective_normal_norm : ‖coordinates 1 1 (model.c1, model.c2)‖ = 1 := by
  have hs : ‖coordinates 1 1 (model.c1, model.c2)‖ ^ 2 = 1 := by
    rw [norm_coordinates_sq]
    norm_num [model]
  have hn := norm_nonneg (coordinates 1 1 (model.c1, model.c2))
  nlinarith

theorem objective_normal_ne_zero : coordinates 1 1 (model.c1, model.c2) ≠ 0 := by
  intro h
  have hn := objective_normal_norm
  rw [h, norm_zero] at hn
  norm_num at hn

theorem seed_incumbent_feasible : pt 1 0 ∈ model.feasibleOn Set.univ := by
  apply (source_feasible_iff model Set.univ (pt 1 0)).mpr
  refine ⟨Set.mem_univ _, ?_, ?_, fun _ => 0, ?_, ?_⟩
  · intro j
    norm_num [model, pt]
  · exact (linear_iff _).mpr (by norm_num [pt])
  · intro i
    norm_num [model]
  · simp [pt]

theorem zero_fixed_minimizer : IsMinimizer
    (model.fixedNonlinearFiber (pt 0 0).2) model.objective (pt 0 0) := by
  refine ⟨?_, ?_⟩
  · apply (mem_fixedNonlinearFiber model _ _).mpr
    refine ⟨(linear_iff _).mpr (by norm_num [pt]), rfl, ?_⟩
    intro j
    norm_num [model, pt]
  · intro p hp
    apply zero_minimizer.2 p
    rcases (mem_fixedNonlinearFiber model _ _).mp hp with ⟨hl, hy, hg⟩
    apply (source_feasible_iff model Set.univ p).mpr
    refine ⟨Set.mem_univ _, hg, hl, fun _ => 0, ?_, ?_⟩
    · intro i
      norm_num [model]
    · simpa [pt] using hy

theorem zero_no_active_rows (j : Fin 1) : model.g j (pt 0 0) ≠ 0 := by
  norm_num [model, pt]

/-- The finite cutoff is supplied by the external feasible point `pt 1 0`.
It is not claimed to arise from an earlier exact fixed-NLP event. -/
def trialSeed : List (EuclideanPoint 1 1 × ℝ) :=
  [(coordinates 1 1 (model.c1, model.c2), 1)]

def trialEvent : TrialEvent 1 1 := (pt 0 0, some (pt 0 0))

def trialEvents (_ : ℕ) : TrialEvent 1 1 := trialEvent

/-- Only the index-zero trial has positive radius. The zero extension is
analytic data, not a continuation of the source's strict while guard. -/
def trialRadius (i : ℕ) : ℝ := if i = 0 then 1 else 0

theorem trial_seed_admissible : seedAdmissible model trialSeed := by
  intro p hp row hrow
  simp only [trialSeed, List.mem_singleton] at hrow
  subst row
  change inner ℝ (coordinates 1 1 (model.c1, model.c2)) (coordinates 1 1 p) ≤ 1
  rw [← objective_eq_inner_coordinates]
  simpa [pt] using hp.2 (pt 1 0) seed_incumbent_feasible

theorem trial_event_valid : eventValid model trialEvent := by
  change (pt 0 0 ∈ model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi) ∧
    pt 0 0 ∈ model.nonlinearRegion ∧
      IsMinimizer (model.fixedNonlinearFiber (pt 0 0).2) model.objective (pt 0 0)
  refine ⟨?_, ?_, zero_fixed_minimizer⟩
  · simp [linear_iff, cylinder_iff, pt]
  · intro j
    norm_num [model, pt]

theorem trial_event_rows_iff (q : P) (r : ℝ) :
    eventRows model trialEvent q r ↔ q.1 0 + r ≤ 0 := by
  simp only [eventRows, TrialEvent.polished, trialEvent]
  constructor
  · intro h
    simpa [objective_normal_norm, pt] using h.2
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      exact (zero_no_active_rows j hj).elim
    · simpa [objective_normal_norm, pt] using h

/-- Exact scalar form of all master constraints; the radius remains free. -/
theorem trial_master_iff (i : ℕ) (q : P) (r : ℝ) :
    (q, r) ∈ sourceMaster model trialSeed (historyPrefix trialEvents i) ↔
      (0 ≤ q.1 0 ∧ q.1 0 ≤ 1) ∧ q.2 0 = 0 ∧ q.1 0 + r ≤ 1 ∧
        (0 < i → q.1 0 + r ≤ 0) := by
  constructor
  · rintro ⟨⟨hl, hc⟩, hs, he⟩
    refine ⟨(linear_iff q).mp hl, (cylinder_iff q).mp hc, ?_, ?_⟩
    · have h := hs (coordinates 1 1 (model.c1, model.c2), 1) (by simp [trialSeed])
      simpa only [← objective_eq_inner_coordinates, objective_eq,
        objective_normal_norm, mul_one] using h
    · intro hi
      apply (trial_event_rows_iff q r).mp
      apply he trialEvent
      exact (mem_historyPrefix trialEvents i trialEvent).mpr ⟨0, hi, rfl⟩
  · rintro ⟨hl, hc, hs, he⟩
    refine ⟨⟨(linear_iff q).mpr hl, (cylinder_iff q).mpr hc⟩, ?_, ?_⟩
    · intro row hrow
      simp only [trialSeed, List.mem_singleton] at hrow
      subst row
      simpa only [← objective_eq_inner_coordinates, objective_eq,
        objective_normal_norm, mul_one] using hs
    · intro e hevent
      obtain ⟨j, hji, rfl⟩ := (mem_historyPrefix trialEvents i e).mp hevent
      apply (trial_event_rows_iff q r).mpr
      exact he (Nat.zero_lt_of_lt hji)

/-- This supplied-seed control has an exact first master as an additional
fact; the production radius endpoint does not require initial exactness. -/
theorem trial_initial_exact : ExactRadiusMax
    (sourceMaster model trialSeed (historyPrefix trialEvents 0)) (pt 0 0, 1) := by
  refine ⟨?_, ?_⟩
  · apply (trial_master_iff 0 (pt 0 0) 1).mpr
    norm_num [pt]
  · intro z hz
    have h := (trial_master_iff 0 z.1 z.2).mp hz
    change z.2 ≤ 1
    linarith [h.1.1, h.2.2.1]

theorem trial_tail_exact (i : ℕ) : ExactRadiusMax
    (sourceMaster model trialSeed (historyPrefix trialEvents (i + 1)))
    ((trialEvents (i + 1)).trial, trialRadius (i + 1)) := by
  change ExactRadiusMax
    (sourceMaster model trialSeed (historyPrefix trialEvents (i + 1))) (pt 0 0, 0)
  refine ⟨?_, ?_⟩
  · apply (trial_master_iff (i + 1) (pt 0 0) 0).mpr
    norm_num [pt]
  · intro z hz
    have h := (trial_master_iff (i + 1) z.1 z.2).mp hz
    have hr := h.2.2.2 (Nat.succ_pos i)
    change z.2 ≤ 0
    linarith [h.1.1]

/-- The actual retained first event bounds the next trial's radius. -/
theorem retained_trial_radius_control : trialRadius 1 ≤
    ‖coordinates 1 1 (trialEvents 1).trial -
      coordinates 1 1 (trialEvents 0).trial‖ := by
  apply source_retained_trial_radius_le model rows_convex rows_differentiable
    feasible_nonempty objective_normal_ne_zero trialSeed (historyPrefix trialEvents 1)
    (trialEvents 0) _ trial_event_valid (trialEvents 1).trial (trialRadius 1)
    (trial_tail_exact 0).1
  exact (mem_historyPrefix trialEvents 1 (trialEvents 0)).mpr ⟨0, by norm_num, rfl⟩

/-- Both the initial and appended masters are concrete. The strict source
guard at δ=0 permits one body and fails at the next trial; no execution
framework or infinite while run is asserted. -/
theorem trial_one_body_prefix :
    0 < trialRadius 0 ∧ ¬ 0 < trialRadius 1 ∧ trialRadius 1 ≤ trialRadius 0 := by
  refine ⟨by norm_num [trialRadius], by norm_num [trialRadius], ?_⟩
  apply source_master_radius_le_of_append model trialSeed (historyPrefix trialEvents 0)
    [trialEvents 0] ((trialEvents 0).trial, trialRadius 0)
    ((trialEvents 1).trial, trialRadius 1) trial_initial_exact
  simpa only [← historyPrefix_succ] using (trial_tail_exact 0).1

/-- Required headline application on the same data, including the analytic
zero tail. This does not make that tail an infinite source while execution. -/
theorem history_radius_control : Tendsto trialRadius atTop (𝓝 0) :=
  source_history_radius_tendsto_zero model rows_convex rows_differentiable
    compact_base feasible_nonempty objective_normal_ne_zero trialSeed trial_seed_admissible
    trialEvents trialRadius (fun _ => trial_event_valid) trial_tail_exact

end Chapter04.CenterCut.Control
