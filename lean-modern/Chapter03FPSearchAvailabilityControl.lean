module

public import Chapter03FPSearchInitialControls
public import Chapter03FPUnboundedObjectiveBoundedLimit

@[expose] public section

/-! First-search availability control, outside intended bounded-relaxation A3.
The literal first-search master is identified with the accepted old initial
master at scalar zero before transferring its actual minimizing target. -/
noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch.AvailabilityControl

def data : Data 1 1 1 := Data.fromUnbounded FPUnboundedObjectiveBounded.data
def start : State 1 1 := initialState FPUnboundedObjectiveBounded.seed

theorem relaxation_identity : data.relaxation = FPUnboundedObjectiveBounded.data.relaxation := rfl
theorem original_identity : data.original = FPUnboundedObjectiveBounded.data.original := rfl

theorem first_master_iff (mode : Mode) (p : FPUnboundedObjectiveBounded.P) :
    p ∈ master data mode start ↔ p ∈ FPUnboundedObjectiveBounded.base ∧ Integral p ∧
      1-p.1 0/4-p.2 0 ≤ 0 := by
  have ht : tangent data FPUnboundedObjectiveBounded.seed 0 p = 1-p.1 0/4-p.2 0 := FPUnboundedObjectiveBounded.row_tangent 0 p
  constructor
  · intro hp
    refine ⟨hp.1,hp.2.1,?_⟩
    have hrow := hp.2.2.1.1 0
    change tangent data FPUnboundedObjectiveBounded.seed 0 p ≤ 0 at hrow
    rwa [ht] at hrow
  · rintro ⟨hb,hi,hrow⟩
    refine ⟨hb,hi,⟨?_,?_⟩,?_⟩
    · intro j
      fin_cases j
      change tangent data FPUnboundedObjectiveBounded.seed 0 p ≤ 0
      rwa [ht]
    · simp [start,initialState]
    · simp [start,initialState]

theorem old_master_identity (mode : Mode) (p : FPUnboundedObjectiveBounded.P) :
    p ∈ master data mode start ↔
      (p,0) ∈ FPUnbounded.master FPUnboundedObjectiveBounded.data FPUnboundedObjectiveBounded.start := by
  rw [first_master_iff, FPUnboundedObjectiveBounded.initial_master_iff]
  simp only [Integral, le_refl, and_true]

theorem cost_identity (p : FPUnboundedObjectiveBounded.P) : masterCost start p =
    FPUnbounded.masterCost FPUnboundedObjectiveBounded.start (p,0) := rfl

theorem target_zero_minimum (mode : Mode) :
    IsMinimizer (master data mode start) (masterCost start) (FPUnboundedObjectiveBounded.pt 4 0) := by
  refine ⟨(old_master_identity mode _).mpr FPUnboundedObjectiveBounded.target0_master, ?_⟩
  intro p hp
  exact FPUnboundedObjectiveBounded.target0_minimum.2 (p,0) ((old_master_identity mode p).mp hp)

theorem target_one_minimum (mode : Mode) :
    IsMinimizer (master data mode start) (masterCost start) (FPUnboundedObjectiveBounded.pt 1 1) := by
  refine ⟨(old_master_identity mode _).mpr FPUnboundedObjectiveBounded.target1_master, ?_⟩
  intro p hp
  exact FPUnboundedObjectiveBounded.target1_minimum.2 (p,0) ((old_master_identity mode p).mp hp)

theorem initial_minimum : IsMinimizer data.relaxation data.f FPUnboundedObjectiveBounded.seed := FPUnboundedObjectiveBounded.seed_minimum
theorem original_minimum : IsMinimizer data.original data.f FPUnboundedObjectiveBounded.integerOptimum := FPUnboundedObjectiveBounded.original_minimum
theorem seed_fractional : ¬Integral FPUnboundedObjectiveBounded.seed := FPUnboundedObjectiveBounded.seed_not_integral

theorem projection_zero_unattained :
    ¬∃ p, IsMinimizer data.relaxation (distance (FPUnboundedObjectiveBounded.iv 0)) p := by
  simpa only [FPUnboundedObjectiveBounded.initial_region_identity, relaxation_identity] using FPUnboundedObjectiveBounded.projection_not_attained

theorem no_target_zero_step (mode : Mode) (step : Step data mode start)
    (ht : step.target = FPUnboundedObjectiveBounded.iv 0) : False := by
  exact projection_zero_unattained ⟨step.projection, by simpa [ht] using step.projection_min⟩

theorem relaxation_unbounded : ¬Bornology.IsBounded data.relaxation := FPUnboundedObjectiveBounded.relaxation_unbounded
theorem outside_A3 : ¬Analytic data := fun h => relaxation_unbounded h.bounded_relaxation

/-- Attained initialization and both tied first-master minima do not supply
the requested projection. This does not contradict the A3-qualified endpoint. -/
theorem first_search_availability_obstruction (mode : Mode) :
    IsClosed data.base ∧ Convex ℝ data.base ∧ ConvexOn ℝ data.base data.f ∧
    (∀ j, ConvexOn ℝ data.base (data.g j)) ∧
    ContDiffOn ℝ 1 data.f data.base ∧ (∀ j, ContDiffOn ℝ 1 (data.g j) data.base) ∧
    (∀ p ∈ data.relaxation, 0 ≤ data.f p ∧ data.f p ≤ 1/4) ∧
    IsMinimizer data.relaxation data.f FPUnboundedObjectiveBounded.seed ∧
    IsMinimizer data.original data.f FPUnboundedObjectiveBounded.integerOptimum ∧ ¬Integral FPUnboundedObjectiveBounded.seed ∧
    IsMinimizer (master data mode start) (masterCost start) (FPUnboundedObjectiveBounded.pt 4 0) ∧
    IsMinimizer (master data mode start) (masterCost start) (FPUnboundedObjectiveBounded.pt 1 1) ∧
    data.relaxation.Nonempty ∧
    (¬∃ p, IsMinimizer data.relaxation (distance (FPUnboundedObjectiveBounded.iv 0)) p) ∧
    ¬Bornology.IsBounded data.relaxation :=
  ⟨FPUnboundedObjectiveBounded.base_closed,FPUnboundedObjectiveBounded.base_convex,FPUnboundedObjectiveBounded.objective_convex,FPUnboundedObjectiveBounded.row_convex,
    FPUnboundedObjectiveBounded.objective_C1,FPUnboundedObjectiveBounded.row_C1,fun _ hp => FPUnboundedObjectiveBounded.objective_bounded hp,
    initial_minimum,original_minimum,seed_fractional,target_zero_minimum mode,
    target_one_minimum mode,⟨FPUnboundedObjectiveBounded.seed,initial_minimum.1⟩,
    projection_zero_unattained,relaxation_unbounded⟩

end Chapter03.FPSearch.AvailabilityControl
