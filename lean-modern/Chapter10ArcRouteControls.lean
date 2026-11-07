module

public import Chapter10ArcRouteBridge
public import Chapter10ArcControls
public import Chapter10RouteControls

@[expose] public section

/-! Shared actual Data controls for the forward/reverse route interfaces. -/
noncomputable section
namespace Chapter10.Routing.Arc.BridgeControls
open Chapter10.Routing Chapter10.Routing.Arc

abbrev A : Fin 2 := Chapter10.Routing.Controls.A
abbrev B : Fin 2 := Chapter10.Routing.Controls.B

def genuineGrid : Grid 4 where
  time := ![0,2,5,6]
  distinct := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals norm_num at *
  nonnegative := by intro i; fin_cases i <;> norm_num

def genuineClock : Fin 2 → Fin 4 := ![1,2]
def genuinePath : TimedPath 2 4 where
  customers := [A,B]
  departure := 0
  returnTime := 3

def genuineX : Assignment 2 4 := encodeEdges (genuinePath.edges genuineClock)

theorem genuine_edges : genuinePath.edges genuineClock =
    [((none,0),(some A,1)),((some A,1),(some B,2)),((some B,2),(none,3))] := by
  rfl

theorem genuine_edges_nodup : (genuinePath.edges genuineClock).Nodup := by
  rw [genuine_edges]
  decide

theorem genuine_arc_literal : Literal Chapter10.Routing.Controls.genuine genuineGrid genuineX := by
  have h := timed_paths_encode_literal Chapter10.Routing.Controls.genuine genuineGrid genuineClock [genuinePath]
  apply h
  · simpa using genuine_edges_nodup
  · intro i
    fin_cases i <;> norm_num [genuinePath,A,B,Chapter10.Routing.Controls.A,Chapter10.Routing.Controls.B]
  · intro q hq e he
    have hq' : q = genuinePath := by simpa using hq
    subst q
    rw [genuine_edges] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl <;>
      norm_num [edgeValid,inWindow,genuineGrid,Chapter10.Routing.Controls.genuine,
        A,B,Chapter10.Routing.Controls.A,Chapter10.Routing.Controls.B,
        Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three]

theorem genuine_arc_cost : objective Chapter10.Routing.Controls.genuine genuineX = 4 := by
  have h := encoded_objective Chapter10.Routing.Controls.genuine genuineClock [genuinePath]
    (by simpa using genuine_edges_nodup)
  norm_num [genuineX,genuine_edges,Chapter10.Routing.Controls.genuine,
    A,B,Chapter10.Routing.Controls.A,Chapter10.Routing.Controls.B] at h ⊢
  exact h

theorem genuine_arc_rank : StrictRank genuineX (fun i => i.val) := by
  intro i j he
  obtain ⟨e,hx,hs,hd⟩ := he
  have hm : e ∈ genuinePath.edges genuineClock := by simpa [genuineX,encodeEdges] using hx
  rw [genuine_edges] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl
  · cases hs
  · have hi : A = i := Option.some.inj hs
    have hj : B = j := Option.some.inj hd
    rw [← hi,← hj]
    decide
  · cases hd

/-- This uses the exact common genuine data, route, clocks, loads, and cost.
It is both a literal grid assignment and a real position schedule. -/
theorem shared_genuine_route_arc :
    Literal Chapter10.Routing.Controls.genuine genuineGrid genuineX ∧
    objective Chapter10.Routing.Controls.genuine genuineX = 4 ∧
    ScheduleFrom Chapter10.Routing.Controls.genuine none 0 [A,B] [2,5] 6 ∧
    CapacityFeasible Chapter10.Routing.Controls.genuine [A,B] :=
  ⟨genuine_arc_literal,genuine_arc_cost,
    Chapter10.Routing.Controls.genuine_schedule_cost_loads.1,
    Chapter10.Routing.Controls.genuine_capacity⟩

/-- The exact continuous schedule exists even though the singleton time grid
intersects the customer window and has no feasible literal arc assignment. -/
theorem half_travel_continuous_grid_separation :
    AllowedFrom Controls.halfTravel none [0] ∧
    ScheduleFrom Controls.halfTravel none 0 [0] [(1:ℝ)/2] 1 ∧
    (∃ t : Fin 1, inWindow Controls.halfTravel (some 0) (Controls.zeroGrid.time t)) ∧
    ¬ ∃ x : Assignment 1 1, Feasible Controls.halfTravel Controls.zeroGrid x := by
  refine ⟨?_,?_,Controls.grid_intersection_not_representability⟩
  · norm_num [AllowedFrom,Controls.halfTravel,Controls.badWindowData]
  · norm_num [ScheduleFrom,Controls.halfTravel,Controls.badWindowData]

theorem genuine_arc_feasible : Feasible Chapter10.Routing.Controls.genuine genuineGrid genuineX :=
  (literal_iff_feasible _ _ _).mp genuine_arc_literal

theorem genuine_arrival_A : arrivalEdge genuineX genuine_arc_feasible.1 A =
    ((none,0),(some A,1)) := by
  apply arrivalEdge_eq
  · decide
  · rfl

theorem genuine_arrival_B : arrivalEdge genuineX genuine_arc_feasible.1 B =
    ((some A,1),(some B,2)) := by
  apply arrivalEdge_eq
  · decide
  · rfl

theorem genuine_departure_A : departureEdge genuineX genuine_arc_feasible.1
    genuine_arc_feasible.2.1 A = ((some A,1),(some B,2)) := by
  apply departureEdge_eq
  · decide
  · rfl

theorem genuine_departure_B : departureEdge genuineX genuine_arc_feasible.1
    genuine_arc_feasible.2.1 B = ((some B,2),(none,3)) := by
  apply departureEdge_eq
  · decide
  · rfl

theorem genuine_actual_trace : routeTrace genuineX genuine_arc_feasible.1 genuine_arc_feasible.2.1
    (fun i => i.val) genuine_arc_rank A = [A,B] := by
  apply (routeTrace_spec _ _ _ _ _ _).unique
  apply Chapter10.Routing.FinitePaths.Suffix.step (j := B)
  · simp [next,genuine_departure_A]
  · apply Chapter10.Routing.FinitePaths.Suffix.last
    simp [next,genuine_departure_B]

/-- Nonvacuous exact forward extraction, including the start and last return
coordinates; it uses the actual unique arrival/departure choices. -/
theorem genuine_actual_extracted_path : extractedPath genuineX genuine_arc_feasible.1
    genuine_arc_feasible.2.1 (fun i => i.val) genuine_arc_rank A = genuinePath := by
  simp [extractedPath,genuine_actual_trace,genuine_arrival_A,genuine_departure_B,genuinePath]

def separatedClock : Fin 2 → Fin 1 := fun _ => 0

def separatedPaths : List (TimedPath 2 1) :=
  [⟨[A],0,0⟩,⟨[B],0,0⟩]

def separatedX : Assignment 2 1 := encodeEdges (separatedPaths.flatMap (TimedPath.edges separatedClock))

theorem separated_literal : Literal Chapter10.Routing.Controls.fleetData Controls.zeroGrid separatedX := by
  apply timed_paths_encode_literal
  · decide
  · intro i
    fin_cases i <;> norm_num [separatedPaths,A,B,Chapter10.Routing.Controls.A,Chapter10.Routing.Controls.B]
  · intro q _ e _
    refine ⟨?_,?_,rfl,?_⟩
    · cases e.2.1 <;> norm_num [inWindow,Chapter10.Routing.Controls.fleetData,Controls.zeroGrid]
    · cases e.1.1 <;> norm_num [inWindow,Chapter10.Routing.Controls.fleetData,Controls.zeroGrid]
    · norm_num [Chapter10.Routing.Controls.fleetData,Controls.zeroGrid]

theorem separated_feasible : Feasible Chapter10.Routing.Controls.fleetData Controls.zeroGrid separatedX :=
  (literal_iff_feasible _ _ _).mp separated_literal

/-- Two separate depot-rooted paths are permitted by all literal arc rows;
the number of available vehicles does not occur in those rows. -/
theorem two_arc_routes_exceed_one_vehicle :
    Literal Chapter10.Routing.Controls.fleetData Controls.zeroGrid separatedX ∧
    (rootSet separatedX separated_feasible.1).card = 2 := by
  refine ⟨separated_literal,?_⟩
  rw [number_routes_is_departures]
  norm_num [depotDepartures,separatedX,chosen_encode,separatedPaths,TimedPath.edges,timedEdges,
    separatedClock,A,B,Chapter10.Routing.Controls.A,Chapter10.Routing.Controls.B,
    Finset.filter_insert,Finset.filter_singleton,Option.some_ne_none,Controls.none_ne_some]

end Chapter10.Routing.Arc.BridgeControls


