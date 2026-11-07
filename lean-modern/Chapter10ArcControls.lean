module

public import Chapter10ArcReverse
public import Chapter10ArcPaths
public import Chapter10ArcPenalty

@[expose] public section

/-! Exact source boundary witnesses; no floating numerical campaign. -/
noncomputable section
namespace Chapter10.Routing.Arc.Controls
open Chapter10.Routing
open Chapter10.Routing.Arc

theorem none_ne_some {α : Type*} (a : α) : (none : Option α) ≠ some a := by
  intro h; cases h

def zeroGrid : Grid 1 where
  time _ := 0
  distinct := fun _ _ _ => Subsingleton.elim _ _
  nonnegative _ := le_rfl

def zeroData (n : ℕ) : Data n where
  allowed _ _ := true
  travel _ _ := 0
  cost _ _ := 0
  opening _ := 0
  closing _ := 0
  demand _ := 0
  initialLoad := 0
  capacity := 0

def A : Fin 2 := 0
def B : Fin 2 := 1

def cycleEdges : List (Edge 2 1) := [((some A,0),(some B,0)),((some B,0),(some A,0))]
def cycleX : Assignment 2 1 := encodeEdges cycleEdges

theorem cycle_full_literal : Literal (zeroData 2) zeroGrid cycleX := by
  rw [literal_iff_feasible]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [arrivals,cycleX,chosen_encode,cycleEdges,A,B,Finset.filter_insert,Finset.filter_singleton,Option.some_ne_none,none_ne_some]
  · intro i s
    fin_cases i <;> fin_cases s <;> norm_num [incoming,outgoing,cycleX,chosen_encode,cycleEdges,A,B,Finset.filter_insert,Finset.filter_singleton,Option.some_ne_none,none_ne_some]
  · intro e _
    cases e.2.1 <;> simp [zeroData,zeroGrid,inWindow]
  · intro e _
    cases e.1.1 <;> simp [zeroData,zeroGrid,inWindow]
  · intro e _; rfl
  · intro e _; simp [zeroData,zeroGrid]

theorem cycle_no_depot_departures : depotDepartures cycleX = ∅ := by
  norm_num [depotDepartures,cycleX,chosen_encode,cycleEdges,A,B,Finset.filter_insert,Finset.filter_singleton,Option.some_ne_none,none_ne_some]

theorem cycle_no_strict_rank : ¬ ∃ r : Fin 2 → ℕ, StrictRank cycleX r := by
  rintro ⟨r,hr⟩
  have hab : CustomerEdge cycleX A B := ⟨((some A,0),(some B,0)),by decide,rfl,rfl⟩
  have hba : CustomerEdge cycleX B A := ⟨((some B,0),(some A,0)),by decide,rfl,rfl⟩
  have := hr A B hab
  have := hr B A hba
  omega

def negativeDepot : Data 0 := { zeroData 0 with cost := fun _ _ => -1 }
def depotLoop : Assignment 0 1 := fun _ => true

theorem negative_depot_loop_feasible : Literal negativeDepot zeroGrid depotLoop := by
  rw [literal_iff_feasible]
  refine ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_,?_,?_,?_⟩
  · intro e _; cases h : e.2.1 with
    | none => simp [inWindow,zeroGrid,h]
    | some i => exact Fin.elim0 i
  · intro e _; cases h : e.1.1 with
    | none => simp [inWindow,zeroGrid,h]
    | some i => exact Fin.elim0 i
  · intro e _; rfl
  · intro e _; simp [negativeDepot,zeroData,zeroGrid]

theorem negative_depot_projection_changes_cost :
    objective negativeDepot depotLoop = -1 ∧ objective negativeDepot (fun _ => false : Assignment 0 1) = 0 := by
  norm_num [objective,negativeDepot,depotLoop,Chapter10.bit,Fintype.sum_prod_type,Fintype.sum_option]

def badWindowGrid : Grid 3 where
  time := ![0,5,6]
  distinct := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals norm_num at *
  nonnegative := by intro i; fin_cases i <;> norm_num

def badWindowData : Data 1 where
  allowed i j := decide ((i = none ∧ j = some 0) ∨ (i = some 0 ∧ j = none))
  travel i _ := if i = none then 1 else 0
  cost _ _ := 0
  opening _ := 0
  closing _ := 1
  demand _ := 0
  initialLoad := 0
  capacity := 0

def badWindowEdges : List (Edge 1 3) := [((none,0),(some 0,1)),((some 0,1),(none,2))]
def badWindowX : Assignment 1 3 := encodeEdges badWindowEdges

theorem visit_flow_not_window : Visit badWindowX ∧ Flow badWindowX ∧
    Permitted badWindowData badWindowX ∧ Travel badWindowData badWindowGrid badWindowX ∧
    ¬ DepartureWindows badWindowData badWindowGrid badWindowX ∧
    ¬ ArrivalWindows badWindowData badWindowGrid badWindowX := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i; fin_cases i
    norm_num [arrivals,badWindowX,chosen_encode,badWindowEdges,Finset.filter_insert,Finset.filter_singleton,Option.some_ne_none,none_ne_some]
  · intro i s; fin_cases i; fin_cases s <;>
      norm_num [incoming,outgoing,badWindowX,chosen_encode,badWindowEdges,Finset.filter_insert,Finset.filter_singleton,Option.some_ne_none,none_ne_some]
  · intro e he
    have hm : e ∈ badWindowEdges := by simpa [badWindowX,encodeEdges] using he
    simp only [badWindowEdges,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> norm_num [badWindowData]
  · intro e he
    have hm : e ∈ badWindowEdges := by simpa [badWindowX,encodeEdges] using he
    simp only [badWindowEdges,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> norm_num [badWindowData,badWindowGrid,Option.some_ne_none,Matrix.cons_val_succ,Matrix.cons_val_two]
  · intro h
    have hh := h ((some 0,1),(none,2)) (by decide)
    norm_num [badWindowData,badWindowGrid,inWindow] at hh
  · intro h
    have hh := h ((none,0),(some 0,1)) (by decide)
    norm_num [badWindowData,badWindowGrid,inWindow] at hh

def halfTravel : Data 1 := { badWindowData with travel := fun _ _ => (1:ℝ)/2 }

theorem grid_intersection_not_representability :
    (∃ t : Fin 1, inWindow halfTravel (some 0) (zeroGrid.time t)) ∧
    ¬ ∃ x : Assignment 1 1, Feasible halfTravel zeroGrid x := by
  refine ⟨⟨0,by norm_num [inWindow,halfTravel,badWindowData,zeroGrid]⟩,?_⟩
  rintro ⟨x,h⟩
  obtain ⟨e,⟨hx,_⟩,_⟩ := visit_unique x h.1 0
  have ht := h.2.2.2.2.2 e hx
  norm_num [halfTravel,zeroGrid] at ht

end Chapter10.Routing.Arc.Controls
