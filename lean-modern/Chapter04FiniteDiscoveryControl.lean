module

public import Chapter04TrialHistoryControl
public import Chapter04FiniteDiscovery

@[expose] public section

/-! Immediate-discovery controls on the accepted quadratic constraint model.
The supplied trial and exact polish are distinct. The zero-objective case has
an unbounded master after success; no continued exact-master oracle is asserted.
These controls do not exercise delayed discovery or a nonempty pre-discovery
history. Algorithm 2.b retains strict violations in the underlying history. -/

noncomputable section
open Chapter02
namespace Chapter04.CenterCut.Control

def discoveryEvent : TrialEvent 1 1 := (pt 1 0, some (pt 0 0))

def discoveryEvents (_ : ℕ) : TrialEvent 1 1 := discoveryEvent

def zeroModel : ModelData 1 1 1 2 :=
  { model with c1 := fun _ => 0, c2 := fun _ => 0 }

theorem discovery_trial_ne_polish : discoveryEvent.trial ≠ pt 0 0 := by
  intro h
  have hx := congrArg (fun p : P => p.1 0) h
  norm_num [discoveryEvent, TrialEvent.trial, pt] at hx

theorem discovery_event_valid : eventValid model discoveryEvent := by
  change (pt 1 0 ∈ model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi) ∧
    pt 1 0 ∈ model.nonlinearRegion ∧
      IsMinimizer (model.fixedNonlinearFiber (pt 1 0).2) model.objective (pt 0 0)
  refine ⟨?_, ?_, zero_fixed_minimizer⟩
  · simp [linear_iff, cylinder_iff, pt]
  · exact ((source_feasible_iff model Set.univ _).mp seed_incumbent_feasible).2.1

@[simp] theorem zero_objective_eq (p : P) : zeroModel.objective p = 0 := by
  simp [zeroModel, ModelData.objective, LinearForm]

theorem zero_discovery_minimizer : IsMinimizer (zeroModel.feasibleOn Set.univ)
    zeroModel.objective (pt 0 0) := by
  refine ⟨zero_feasible, ?_⟩
  intro p hp
  simp

theorem zero_discovery_event_valid : eventValid zeroModel discoveryEvent := by
  change (pt 1 0 ∈ model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi) ∧
    pt 1 0 ∈ model.nonlinearRegion ∧
      IsMinimizer (model.fixedNonlinearFiber (pt 1 0).2) zeroModel.objective (pt 0 0)
  refine ⟨discovery_event_valid.1, ?_, zero_fixed_minimizer.1, ?_⟩
  · exact ((source_feasible_iff model Set.univ _).mp seed_incumbent_feasible).2.1
  · intro p hp
    simp

/-- Every radius is feasible at every allowed center after immediate success
with zero objective. This is not a pre-discovery master. -/
theorem zero_post_discovery_master_iff (q : P) (r : ℝ) :
    (q, r) ∈ sourceMaster zeroModel [] [discoveryEvent] ↔
      q ∈ model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi := by
  constructor
  · exact fun h => h.1
  · intro hq
    refine ⟨hq, by simp, ?_⟩
    intro e he
    have heq : e = discoveryEvent := by simpa using he
    subst e
    change (∀ j, model.g j (pt 0 0) = 0 →
      model.g j (pt 0 0) + inner ℝ (euclideanGradient (model.g j) (pt 0 0))
        (coordinates 1 1 q - coordinates 1 1 (pt 0 0)) +
        r * ‖euclideanGradient (model.g j) (pt 0 0)‖ ≤ 0) ∧
      zeroModel.objective q + r * ‖coordinates 1 1 (zeroModel.c1, zeroModel.c2)‖ ≤
        zeroModel.objective (pt 0 0)
    refine ⟨fun j hj => (zero_no_active_rows j hj).elim, ?_⟩
    have hz : (zeroModel.c1, zeroModel.c2) = (0 : P) := rfl
    simp [hz]

theorem zero_post_discovery_no_max :
    ¬ ∃ w, ExactRadiusMax (sourceMaster zeroModel [] [discoveryEvent]) w := by
  intro h
  apply Chapter04.empty_seed_no_radius_max
    (model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi)
    ⟨pt 0 0, by simp [linear_iff, cylinder_iff, pt]⟩
  obtain ⟨w, hw⟩ := h
  refine ⟨w, (zero_post_discovery_master_iff w.1 w.2).mp hw.1, ?_⟩
  intro z hz
  exact hw.2 z ((zero_post_discovery_master_iff z.1 z.2).mpr hz)

/-- Apply the full finite-discovery theorem to distinct supplied trial/polish
points on the original model. Discovery is immediate; later no-success
antecedents are false, so their conditional exactness obligations hold. -/
theorem source_discovery_control :
    ∃ i : ℕ, ∃ p : P, (discoveryEvents i).polished = some p ∧
      IsMinimizer (model.feasibleOn Set.univ) model.objective p := by
  apply source_finite_optimal_polish model rows_convex rows_differentiable
    compact_base feasible_nonempty fiber_slater discoveryEvents (fun _ => 0)
  · intro i _
    exact discovery_event_valid
  · intro i hbefore
    exact (hbefore 0 (Nat.succ_pos i) ⟨pt 0 0, rfl, zero_minimizer⟩).elim

/-- The same full theorem has satisfiable hypotheses for zero objective.
It does not require an exact master after the first optimal polish. -/
theorem source_zero_discovery_control :
    ∃ i : ℕ, ∃ p : P, (discoveryEvents i).polished = some p ∧
      IsMinimizer (zeroModel.feasibleOn Set.univ) zeroModel.objective p := by
  apply source_finite_optimal_polish zeroModel rows_convex rows_differentiable
    compact_base feasible_nonempty fiber_slater discoveryEvents (fun _ => 0)
  · intro i _
    exact zero_discovery_event_valid
  · intro i hbefore
    exact (hbefore 0 (Nat.succ_pos i) ⟨pt 0 0, rfl, zero_discovery_minimizer⟩).elim

end Chapter04.CenterCut.Control
