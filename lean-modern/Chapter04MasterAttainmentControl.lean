module

public import Chapter04MasterAttainment
public import Chapter04TrialHistoryControl

@[expose] public section

/-! Supporting nonvacuity control requested in CH04-S011/M1.
Only the earlier control's affine upper bound changes, from one to three.
One strictly infeasible event yields a nonempty valid pre-discovery history
and an attained subsequent master. No particular maximizing trial/radius,
delayed-discovery trace, finite return or extra scientific credit is claimed. -/

noncomputable section
open Chapter02
namespace Chapter04.CenterCut.AvailabilityControl
open Chapter04.CenterCut.Control (P pt pt_eta)

def model : ModelData 1 1 1 2 :=
  { Control.model with rhs := fun row => if row = 0 then 0 else 3 }

theorem linear_iff (p : P) : p ∈ model.linearRegion ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 3 := by
  simp [ModelData.linearRegion, LinearForm, model, Control.model, Fin.forall_fin_two]

theorem cylinder_iff (p : P) :
    p ∈ IntegerCylinder (n := 1) model.lo model.hi ↔ p.2 0 = 0 :=
  Control.cylinder_iff p

theorem compact_base :
    IsCompact (model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi) := by
  have heq : model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi =
      (fun x : ℝ => pt x 0) '' Set.Icc 0 3 := by
    ext p
    simp only [Set.mem_inter_iff, linear_iff, cylinder_iff, Set.mem_image,
      Set.mem_Icc]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨p.1 0, hx, ?_⟩
      simpa [hy] using pt_eta p
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
  rw [heq]
  apply isCompact_Icc.image
  unfold pt
  fun_prop

theorem rows_convex (j : Fin 1) : ConvexOn ℝ Set.univ (model.g j) :=
  Control.rows_convex j

theorem rows_differentiable (j : Fin 1) : Differentiable ℝ (model.g j) :=
  Control.rows_differentiable j

theorem zero_feasible : pt 0 0 ∈ model.feasibleOn Set.univ := by
  apply (source_feasible_iff model Set.univ (pt 0 0)).mpr
  refine ⟨Set.mem_univ _, ?_, ?_, fun _ => 0, ?_, ?_⟩
  · intro j
    norm_num [model, Control.model, pt]
  · exact (linear_iff _).mpr (by norm_num [pt])
  · intro i
    norm_num [model, Control.model]
  · simp [pt]

def event : TrialEvent 1 1 := (pt 3 0, none)

theorem strictly_violated : 0 < model.g 0 event.trial := by
  norm_num [model, Control.model, event, TrialEvent.trial, pt]

theorem event_valid : eventValid model event := by
  constructor
  · exact ⟨(linear_iff _).mpr (by norm_num [event, TrialEvent.trial, pt]),
      (cylinder_iff _).mpr rfl⟩
  · change ¬ (∀ j, model.g j event.trial ≤ 0)
    intro h
    exact (not_le_of_gt strictly_violated) (h 0)

theorem history_nonempty : ([event] : List (TrialEvent 1 1)) ≠ [] := by simp

theorem history_valid : ∀ e ∈ [event], eventValid model e := by
  intro e he
  have heq : e = event := List.mem_singleton.mp he
  subst e
  exact event_valid

theorem history_before_discovery :
    ∀ e ∈ [event], ∀ p, e.polished = some p →
      ¬ IsMinimizer (model.feasibleOn Set.univ) model.objective p := by
  intro e he p hp
  have heq : e = event := List.mem_singleton.mp he
  subst e
  simp [event, TrialEvent.polished] at hp

/-- The full availability theorem is instantiated with a valid, nonempty
history containing a strictly infeasible event and no stored polish. -/
theorem nonempty_prediscovery_master_attained :
    ∃ w : P × ℝ, ExactRadiusMax (sourceMaster model [] [event]) w :=
  source_master_attained_before_optimal_polish model rows_convex rows_differentiable
    compact_base ⟨pt 0 0, zero_feasible⟩ [event] history_nonempty
    history_valid history_before_discovery

end Chapter04.CenterCut.AvailabilityControl
