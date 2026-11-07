module

public import Chapter04RadiusStopping
public import Chapter04FiniteDiscoveryControl

@[expose] public section

/-! A true exact-zero stopping state on the unchanged accepted model. Its
single event has distinct trial and polish. No delayed-discovery or literal
loop-execution claim is made. The accepted zero-objective analogue has no
exact post-discovery master and is not asserted to satisfy this trigger. -/

noncomputable section
namespace Chapter04.CenterCut.Control
open Chapter02

/-- The radius is free. The stored polish has no active nonlinear row, and
its objective row is exactly x+r≤0. There is no additional seed. -/
theorem stopping_master_iff (q : P) (r : ℝ) :
    (q, r) ∈ sourceMaster model [] [discoveryEvent] ↔
      (0 ≤ q.1 0 ∧ q.1 0 ≤ 1) ∧ q.2 0 = 0 ∧ q.1 0 + r ≤ 0 := by
  constructor
  · intro h
    have hrows := h.2.2 discoveryEvent (by simp)
    have hobj : model.objective q + r * ‖coordinates 1 1 (model.c1, model.c2)‖ ≤
        model.objective (pt 0 0) := hrows.2
    refine ⟨(linear_iff q).mp h.1.1, (cylinder_iff q).mp h.1.2, ?_⟩
    simpa [objective_normal_norm, pt] using hobj
  · rintro ⟨hl, hy, hr⟩
    refine ⟨⟨(linear_iff q).mpr hl, (cylinder_iff q).mpr hy⟩, by simp, ?_⟩
    intro e he
    have heq : e = discoveryEvent := by simpa using he
    subst e
    change (∀ j, model.g j (pt 0 0) = 0 →
      model.g j (pt 0 0) + inner ℝ (euclideanGradient (model.g j) (pt 0 0))
        (coordinates 1 1 q - coordinates 1 1 (pt 0 0)) +
        r * ‖euclideanGradient (model.g j) (pt 0 0)‖ ≤ 0) ∧
      model.objective q + r * ‖coordinates 1 1 (model.c1, model.c2)‖ ≤
        model.objective (pt 0 0)
    refine ⟨fun j hj => (zero_no_active_rows j hj).elim, ?_⟩
    simpa [objective_normal_norm, pt] using hr

theorem stopping_exact_zero :
    ExactRadiusMax (sourceMaster model [] [discoveryEvent]) (pt 0 0, 0) := by
  refine ⟨?_, ?_⟩
  · apply (stopping_master_iff (pt 0 0) 0).mpr
    norm_num [pt]
  · intro z hz
    obtain ⟨hl, _, hr⟩ := (stopping_master_iff z.1 z.2).mp hz
    change z.2 ≤ 0
    linarith [hl.1]

theorem stopping_stored_iff (p : P) :
    p ∈ storedPolishes [discoveryEvent] ↔ p = pt 0 0 := by
  simp [storedPolishes, discoveryEvent, TrialEvent.polished, eq_comm]

/-- The full common-threshold theorem is applied to an actual exact maximum
of radius zero. Its strict small-radius premise follows from the threshold's
positivity, rather than from an impossible pre-discovery antecedent. -/
theorem source_radius_stopping_control :
    (∃ b, IsMinimizer (storedPolishes [discoveryEvent]) model.objective b) ∧
      ∀ b, IsMinimizer (storedPolishes [discoveryEvent]) model.objective b →
        IsMinimizer (model.feasibleOn Set.univ) model.objective b := by
  obtain ⟨ρ, hρ, hcertificate⟩ := source_small_radius_best_stored model
    rows_convex rows_differentiable compact_base feasible_nonempty fiber_slater
  apply hcertificate [discoveryEvent] _ (pt 0 0, 0) stopping_exact_zero hρ
  intro e he
  have heq : e = discoveryEvent := by simpa using he
  subst e
  exact discovery_event_valid

end Chapter04.CenterCut.Control
