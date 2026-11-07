module

public import Chapter10RoutePadding

@[expose] public section

/-! Concrete controls for route semantics, independent of any slot encoding. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing.Controls

def A : Fin 2 := 0
def B : Fin 2 := 1

def genuine : Data 2 where
  allowed i j := decide ((i = none ∧ j = some A) ∨ (i = some A ∧ j = some B) ∨
    (i = some B ∧ j = none) ∨ (i = none ∧ j = none))
  travel i j := if i = none ∧ j = some A then 1 else
    if i = some A ∧ j = some B then 2 else if i = some B ∧ j = none then 1 else 0
  cost i j := if i = none ∧ j = some A then 1 else
    if i = some A ∧ j = some B then 2 else if i = some B ∧ j = none then 1 else 0
  opening j := if j = A then 2 else 5
  closing j := if j = A then 4 else 8
  demand j := if j = A then 3 else -3
  initialLoad := 0
  capacity := 3

theorem genuine_earliest : earliestTimes genuine none 0 [A,B] = [2,5] ∧
    earliestReturn genuine none 0 [A,B] = 6 := by
  norm_num [earliestTimes, earliestReturn, genuine, A, B]

theorem genuine_capacity : CapacityFeasible genuine [A,B] := by
  intro k hk
  have hk' : k ≤ 2 := hk
  interval_cases k <;> norm_num [prefixLoad, genuine, A, B]

theorem genuine_column : ValidColumn genuine [A,B] := by
  refine ⟨by simp, by simp [A,B], ?_, ?_, genuine_capacity⟩
  · norm_num [AllowedFrom, genuine, A, B]
  · norm_num [EarliestWithin, genuine, A, B]

theorem genuine_schedule_cost_loads :
    ScheduleFrom genuine none 0 [A,B] [2,5] 6 ∧
    edgeCostFrom genuine none [A,B] = 4 ∧
    prefixLoad genuine [A,B] 0 = 0 ∧ prefixLoad genuine [A,B] 1 = 3 ∧
    prefixLoad genuine [A,B] 2 = 0 := by
  norm_num [ScheduleFrom, edgeCostFrom, prefixLoad, genuine, A, B]

theorem genuine_nonnegative : nonnegativeTravel genuine := by
  intro i j _
  dsimp [genuine]
  split_ifs <;> norm_num

theorem genuine_ordered : orderedWindows genuine := by
  intro j
  fin_cases j <;> norm_num [genuine, A, B]

def genuineCatalogue : Catalogue genuine 1 where
  data_nonnegative := genuine_nonnegative
  data_ordered := genuine_ordered
  route _ := [A,B]
  valid _ := genuine_column

theorem genuine_incidence_selection : feasible (incidence genuineCatalogue.route) (fun _ => true) ∧
    selectedRouteCost genuine genuineCatalogue.route (fun _ => true) = 4 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [coverCount, incidence, genuineCatalogue, A, B]
  · norm_num [selectedRouteCost, genuineCatalogue, edgeCostFrom, genuine, A, B]

/-- Same genuine time-feasible route, but the first loading peak exceeds Q=2. -/
def overloaded : Data 2 := { genuine with capacity := 2 }

theorem uncapacitated_overload_control :
    ScheduleFrom overloaded none 0 [A,B] [2,5] 6 ∧
    ¬ CapacityFeasible overloaded [A,B] := by
  constructor
  · exact genuine_schedule_cost_loads.1
  · intro h
    have bad := (h 1 (by decide)).2
    norm_num [prefixLoad, overloaded, genuine, A, B] at bad

/-- A non-elementary supplied walk that satisfies clock and prefix-capacity
conditions, yet membership incidence hides the repeated customer visit. -/
def repeated : Data 2 where
  allowed _ _ := true
  travel _ _ := 0
  cost _ _ := 0
  opening _ := 0
  closing _ := 10
  demand j := if j = A then 1 else -2
  initialLoad := 0
  capacity := 2

def repeatedRoute : Fin 1 → List (Fin 2) := fun _ => [A,A,B]

theorem repeated_walk_has_schedule_capacity :
    ScheduleFrom repeated none 0 [A,A,B] [0,0,0] 0 ∧ CapacityFeasible repeated [A,A,B] := by
  constructor
  · norm_num [ScheduleFrom, repeated]
  · intro k hk
    have hk' : k ≤ 3 := hk
    interval_cases k <;> norm_num [prefixLoad, repeated, A, B]

theorem repeated_walk_incidence_mismatch :
    feasible (incidence repeatedRoute) (fun _ => true) ∧
    occurrenceCount repeatedRoute (fun _ => true) A = 2 ∧
    ¬ [A,A,B].Nodup := by
  refine ⟨?_, ?_, by simp⟩
  · intro i
    fin_cases i <;> norm_num [coverCount, incidence, repeatedRoute, A, B]
  · norm_num [occurrenceCount, repeatedRoute, A, B]

def pairA : Fin 3 := 0
def pairB : Fin 3 := 1
def pairC : Fin 3 := 2

def pairwise : Data 3 where
  allowed i j := decide ((i = none ∧ j = some pairA) ∨
    (i = some pairA ∧ j = some pairB) ∨ (i = some pairB ∧ j = some pairC) ∨
    (i = some pairC ∧ j = none) ∨ (i = none ∧ j = none))
  travel i j := if i = none ∧ j = some pairA then 2 else
    if i = some pairA ∧ j = some pairB then 1 else
    if i = some pairB ∧ j = some pairC then 2 else 0
  cost _ _ := 0
  opening j := if j = pairA then 2 else 0
  closing j := if j = pairA then 2 else if j = pairB then 3 else 4
  demand _ := 0
  initialLoad := 0
  capacity := 1

/-- Every necessary pairwise window test on this route passes. -/
theorem pairwise_necessary_tests_pass : AllowedFrom pairwise none [pairA,pairB,pairC] ∧
    pairwise.travel none (some pairA) ≤ pairwise.closing pairA ∧
    pairwise.opening pairA + pairwise.travel (some pairA) (some pairB) ≤ pairwise.closing pairB ∧
    pairwise.opening pairB + pairwise.travel (some pairB) (some pairC) ≤ pairwise.closing pairC := by
  norm_num [AllowedFrom, pairwise, pairA, pairB, pairC, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem pairwise_earliest_misses_closing :
    earliestTimes pairwise none 0 [pairA,pairB,pairC] = [2,3,5] ∧
    ¬ EarliestWithin pairwise none 0 [pairA,pairB,pairC] := by
  norm_num [earliestTimes, EarliestWithin, pairwise, pairA, pairB, pairC, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem pairwise_no_global_schedule :
    ¬ ∃ ss ret, ScheduleFrom pairwise none 0 [pairA,pairB,pairC] ss ret := by
  rw [schedule_exists_iff]
  exact pairwise_earliest_misses_closing.2

/-- Incidence feasibility permits two used routes with only one proposed
vehicle, until the missing at-most fleet cap is added. -/
def fleetData : Data 2 where
  allowed _ _ := true
  travel _ _ := 0
  cost _ _ := 0
  opening _ := 0
  closing _ := 10
  demand _ := 0
  initialLoad := 0
  capacity := 1

def singletonRoutes : Fin 2 → List (Fin 2) := fun j => [j]

theorem singleton_valid (j : Fin 2) : ValidColumn fleetData [j] := by
  refine ⟨by simp, by simp, by simp [AllowedFrom, fleetData], by norm_num [EarliestWithin, fleetData], ?_⟩
  intro k hk
  have hk' : k ≤ 1 := hk
  interval_cases k <;> norm_num [prefixLoad, fleetData]

theorem incidence_has_no_fleet_cap :
    feasible (incidence singletonRoutes) (fun _ => true) ∧
    selectedCount (fun _ : Fin 2 => true) = 2 ∧
    ¬ Nonempty ({j : Fin 2 // (fun _ : Fin 2 => true) j = true} ↪ Fin 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [coverCount, incidence, singletonRoutes, Fin.sum_univ_two]
  · rw [selectedCount_eq_sum]
    norm_num [Fin.sum_univ_two]
  · rw [fleet_assignment_iff, selectedCount_eq_sum]
    norm_num [Fin.sum_univ_two]

/-- Nonvacuity of the catalogue minimum and the reused strict-penalty adapter
on a genuine two-customer route; this is not a fresh penalty theorem. -/
theorem genuine_catalogue_minimum :
    CatalogueMin genuine genuineCatalogue.route (fun _ => true) := by
  refine ⟨(catalogue_feasible_iff genuineCatalogue _).mp genuine_incidence_selection.1, ?_⟩
  intro y hy
  have h := hy A
  cases hzero : y 0 with
  | false => simp [occurrenceCount, genuineCatalogue, hzero] at h
  | true =>
    simp [selectedRouteCost, genuineCatalogue, hzero]

theorem genuine_penalty_adapter_nonvacuous :
    energyMin (incidence genuineCatalogue.route)
      (fun j => edgeCostFrom genuine none (genuineCatalogue.route j)) 5 (fun _ => true) := by
  have hρ : (∑ j, |edgeCostFrom genuine none (genuineCatalogue.route j)|) < (5 : ℝ) := by
    norm_num [genuineCatalogue, edgeCostFrom, genuine, A, B]
  exact ((supplied_catalogue_penalty_adapter genuineCatalogue 5 hρ _).mpr genuine_catalogue_minimum).1

end Chapter10.Routing.Controls

