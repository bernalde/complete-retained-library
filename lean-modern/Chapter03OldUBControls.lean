module

public import Chapter03FPSearchAdditiveBackground

@[expose] public section

/-! Two local held-2017 bound-assignment controls, not complete old drivers. -/
noncomputable section
open Chapter02
open Chapter03.FPUnboundedControls (xy iv scalar_distance)
open Chapter03.FP (distance)
open Chapter03.FPSearch
namespace Chapter03.OldUBControls
open Chapter03.FPBackgroundAdditive

/-- Constant shift makes the old relative cutoff strictly smaller than seed value. -/
def shiftedCost (p : P) : ℝ := data.f p + 1

theorem shifted_derivative (p : P) : HasFDerivAt shiftedCost (data.Df p) p :=
  objective_derivative p |>.add_const 1

theorem shifted_convex : ConvexOn ℝ Set.univ shiftedCost :=
  objective_convex.add_const 1

theorem shifted_tangent (a p : P) :
    shiftedCost a+data.Df a (p-a)=objectiveTangent a p+1 := by
  simp [shiftedCost,objectiveTangent]
  ring

def shiftedSeedMaster : Set (P × ℝ) :=
  {z | z.1 ∈ FPSearch.master data .basic (state 0) ∧
    objectiveTangent seed z.1 + 1 ≤ z.2 ∧
    z.2 ≤ shiftedCost seed - (1/10)*|shiftedCost seed|}

theorem shifted_initializer : IsMinimizer data.relaxation shiftedCost seed := by
  refine ⟨initializer.1, ?_⟩
  intro p hp
  exact add_le_add_left (initializer.2 p hp) 1

theorem shifted_original_optimum : IsMinimizer data.original shiftedCost optimum := by
  refine ⟨original_optimum.1, ?_⟩
  intro p hp
  exact add_le_add_left (original_optimum.2 p hp) 1

theorem shifted_seed_master_empty : shiftedSeedMaster = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨hm, ht, hc⟩
  have hx := ((basic_master_iff 0 z.1).mp hm).1
  rw [seed_tangent] at ht
  norm_num [shiftedCost, data, seed] at hc
  linarith

/-- Fractional relaxation value is not a feasible-incumbent upper bound;
the printed relative-cutoff master becomes empty despite original feasibility. -/
theorem old_relaxation_ub_countercontrol :
    IsMinimizer data.relaxation shiftedCost seed ∧ ¬ Integral seed ∧
    IsMinimizer data.original shiftedCost optimum ∧
    shiftedCost seed = 1 ∧ shiftedCost optimum = 5/4 ∧
    shiftedCost seed < shiftedCost optimum ∧ shiftedSeedMaster = ∅ := by
  refine ⟨shifted_initializer, seed_fractional, shifted_original_optimum, ?_, ?_, ?_,
    shifted_seed_master_empty⟩ <;> norm_num [shiftedCost, data, seed, optimum]

/-- First exact master with the original infinite-UB cutoff inactive. -/
def firstMaster : Set (P × ℝ) := literalMaster 0

def firstChoice : P × ℝ := (optimum, 0)
def secondPoint : P := xy 0 1
def worseProjection : P := xy 1 1

/-- The history after the first successful projection, with its actual target. -/
def afterFirst : FPSearch.State 1 1 := ⟨seed,[⟨iv 0,optimum⟩]⟩

theorem after_first_master (p : P) :
    p∈FPSearch.master data .basic afterFirst ↔
    p∈FPSearch.master data .basic (state 0) := by
  constructor
  · rintro ⟨hb,hi,hr,he⟩
    exact ⟨hb,hi,⟨hr.1,by simp [state]⟩,by simp⟩
  · rintro ⟨hb,hi,hr,he⟩
    refine ⟨hb,hi,⟨hr.1,?_⟩,by simp⟩
    intro e he j hj
    have hg := hr.1 j
    rw [tangent_exact] at hg ⊢
    exact hg

theorem after_first_reference : afterFirst.reference=optimum := by
  simp [afterFirst,FPSearch.State.reference]

def secondMaster : Set (P × ℝ) :=
  {z | z.1 ∈ FPSearch.master data .basic afterFirst ∧
    objectiveTangent seed z.1 ≤ z.2 ∧
    objectiveTangent optimum z.1 ≤ z.2 ∧ z.2 ≤ data.f optimum - delta}

def secondChoice : P × ℝ := (secondPoint, 0)

theorem optimum_tangent (p : P) :
    objectiveTangent optimum p = p.1 0-p.2 0+1/4 := by
  simp [objectiveTangent, data, optimum]
  ring

theorem first_choice_minimum :
    IsMinimizer firstMaster (fun z => |z.1.2 0-seed.2 0|) firstChoice := by
  refine ⟨?_, ?_⟩
  · apply (master_initial_iff _).mpr
    norm_num [firstChoice, optimum]
  · intro z hz
    have hy := ((master_initial_iff z).mp hz).1.2.2
    rcases hy with hy | hy <;> norm_num [firstChoice, optimum, seed, hy]

theorem first_projection_minimum :
    IsMinimizer data.relaxation (distance (iv 0)) optimum := by
  refine ⟨original_optimum.1.1, ?_⟩
  intro p hp
  simpa [scalar_distance, optimum] using sq_nonneg (p.2 0)

theorem second_choice_minimum :
    IsMinimizer secondMaster (fun z => |z.1.2 0-optimum.2 0|) secondChoice := by
  refine ⟨?_, ?_⟩
  · refine ⟨(after_first_master _).mpr ((basic_master_iff 0 _).mpr ?_), ?_, ?_, ?_⟩
    · norm_num [secondChoice, secondPoint]
    · rw [seed_tangent]; norm_num [secondChoice, secondPoint]
    · rw [optimum_tangent]; norm_num [secondChoice, secondPoint]
    · norm_num [secondChoice, data, optimum, delta]
  · rintro z ⟨hm, hs, ht, hc⟩
    have hb := (basic_master_iff 0 z.1).mp ((after_first_master _).mp hm)
    rw [optimum_tangent] at ht
    norm_num [data, optimum, delta] at hc
    rcases hb.2.2 with hy | hy
    · exfalso
      rw [hy] at ht
      linarith [hb.1]
    · norm_num [secondChoice, secondPoint, optimum, hy]

theorem second_projection_minimum :
    IsMinimizer data.relaxation (distance (iv 1)) worseProjection := by
  refine ⟨(relaxation_iff _).mpr (by norm_num [Box, worseProjection]), ?_⟩
  intro p hp
  simpa [scalar_distance, worseProjection] using sq_nonneg (1-p.2 0)

/-- Both strict success tests hold for every positive tolerance. The printed
unconditional second assignment raises UB; the min repair would preserve it. -/
theorem old_overwrite_ub_countercontrol (epsilon : ℝ) (he : 0 < epsilon) :
    IsMinimizer firstMaster (fun z => |z.1.2 0-seed.2 0|) firstChoice ∧
    IsMinimizer data.relaxation (distance (iv 0)) optimum ∧
    IsMinimizer secondMaster (fun z => |z.1.2 0-optimum.2 0|) secondChoice ∧
    IsMinimizer data.relaxation (distance (iv 1)) worseProjection ∧
    |optimum.2 0-firstChoice.1.2 0| < epsilon ∧
    |worseProjection.2 0-secondChoice.1.2 0| < epsilon ∧
    data.f optimum = 1/4 ∧ data.f worseProjection = 5/4 ∧
    data.f optimum < data.f worseProjection ∧
    min (data.f optimum) (data.f worseProjection) = data.f optimum := by
  refine ⟨first_choice_minimum, first_projection_minimum, second_choice_minimum,
    second_projection_minimum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [optimum, firstChoice] using he
  · simpa [worseProjection, secondChoice, secondPoint] using he
  all_goals norm_num [data, optimum, worseProjection]

end Chapter03.OldUBControls
