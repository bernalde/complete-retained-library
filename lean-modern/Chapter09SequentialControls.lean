module

public import Chapter09Sequential

@[expose] public section

/-! Exact finite controls, including an input on which source sequential repair
differs from the old simultaneous cover. No numerical solver is used. -/
noncomputable section
namespace Chapter09.SequentialControls
open Source Sequential

def edgeGraph : Graph 2 where
  edges := {(0,1)}
  ordered := by
    intro e he
    have h := Finset.mem_singleton.mp he
    subst e
    decide

def emptyGraph : Graph 1 where
  edges := ∅
  ordered := by simp

def edgeList2 : List (Slot 2 2 × Slot 2 2) :=
  [((0,0),(1,0)),((0,1),(1,1))]
def slotList2 : List (Slot 2 2) := [(0,0),(0,1),(1,0),(1,1)]
def nonoptimalInput : Finset (Slot 2 2) := {(0,0),(0,1),(1,1)}
def sequentialOutput : Finset (Slot 2 2) := {(0,0),(1,1)}

theorem edgeList2_sound : ∀ e ∈ edgeList2, e ∈ spatialPairs edgeGraph 2 := by decide
theorem edgeList2_complete : ∀ e ∈ spatialPairs edgeGraph 2, e ∈ edgeList2 := by decide
theorem slotList2_complete : ∀ u : Slot 2 2, u ∈ slotList2 := by decide

theorem sequential_nonoptimal_trace :
    algorithm edgeList2 slotList2 nonoptimalInput = sequentialOutput := by decide

theorem simultaneous_nonoptimal_trace :
    Chapter09.repair (conflictPairs edgeGraph 2) nonoptimalInput = {(1,1)} := by decide

theorem distinct_sequential_and_simultaneous :
    algorithm edgeList2 slotList2 nonoptimalInput ≠
      Chapter09.repair (conflictPairs edgeGraph 2) nonoptimalInput := by
  rw [sequential_nonoptimal_trace,simultaneous_nonoptimal_trace]
  decide

theorem sequential_nonoptimal_feasible : Feasible edgeGraph sequentialOutput := by
  rw [← sequential_nonoptimal_trace]
  exact algorithm_feasible edgeGraph edgeList2 slotList2 edgeList2_complete
    slotList2_complete nonoptimalInput

theorem repeated_scan_trace :
    algorithm (edgeList2 ++ edgeList2) (slotList2 ++ slotList2) nonoptimalInput =
      sequentialOutput := by decide

theorem empty_vertex_trace :
    algorithm ([] : List (Slot 0 1 × Slot 0 1)) [] ∅ = ∅ := rfl

theorem selections_of_two {α : Type*} [DecidableEq α] (a b : α)
    (h : ∀ x : α, x = a ∨ x = b) (S : Finset α) :
    S = ∅ ∨ S = {a} ∨ S = {b} ∨ S = {a,b} := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · right; right; right
    ext x
    rcases h x with rfl | rfl <;> simp [ha,hb]
  · right; left
    have hab : a ≠ b := by intro he; subst b; exact hb ha
    ext x
    rcases h x with rfl | rfl <;> simp [ha,hb,hab,Ne.symm hab]
  · right; right; left
    have hab : a ≠ b := by intro he; subst b; exact ha hb
    ext x
    rcases h x with rfl | rfl <;> simp [ha,hb,hab,Ne.symm hab]
  · left
    ext x
    rcases h x with rfl | rfl <;> simp [ha,hb]

def edgeTie : Finset (Slot 2 1) := {(0,0),(1,0)}
def edgeList1 : List (Slot 2 1 × Slot 2 1) := [((0,0),(1,0))]
def slotList1 : List (Slot 2 1) := [(0,0),(1,0)]

theorem edge_conflict_pairs :
    conflictPairs edgeGraph 1 = {(((0 : Fin 2),0),(1,0))} := by decide

theorem edge_tie_value : uScore edgeGraph 1 1 edgeTie = 1 := by
  have hn : (0 : Slot 2 1) ≠ (1,0) := by decide
  simp only [uScore,edge_conflict_pairs]
  norm_num [score,conflicts,weight,edgeTie,hn,Finset.filter_singleton,
    Finset.filter_insert,Finset.filter_empty]

theorem edge_tie_maximum :
    isScoreMax (conflictPairs edgeGraph 1) (weight 1 1) edgeTie := by
  intro T
  have hn : (0 : Slot 2 1) ≠ (1,0) := by decide
  have h : ∀ x : Slot 2 1, x = (0,0) ∨ x = (1,0) := by
    rintro ⟨i,r⟩
    fin_cases i <;> fin_cases r <;> simp
  rcases selections_of_two (0,0) (1,0) h T with rfl | rfl | rfl | rfl <;>
    rw [edge_conflict_pairs] <;> norm_num [score,conflicts,weight,edgeTie,hn,
      Finset.filter_singleton,Finset.filter_insert,Finset.filter_empty]

theorem edge_tie_infeasible : ¬ Feasible edgeGraph edgeTie := by
  change ¬ feasible (conflictPairs edgeGraph 1) edgeTie
  rw [edge_conflict_pairs]
  simp [feasible,edgeTie]

theorem edge_tie_actual_return : algorithm edgeList1 slotList1 edgeTie = {(1,0)} := by decide

theorem edge_tie_optimal_return :
    Feasible edgeGraph (algorithm edgeList1 slotList1 edgeTie) ∧
    score (conflictPairs edgeGraph 1) (weight 1 1) edgeTie =
      ((algorithm edgeList1 slotList1 edgeTie).card : ℝ) ∧
    ∀ T : Finset (Slot 2 1), Feasible edgeGraph T →
      (T.card : ℝ) ≤ ((algorithm edgeList1 slotList1 edgeTie).card : ℝ) :=
  algorithm_optimal_return edgeGraph (weight 1 1)
    (weight_ge_one edgeGraph 1 1 le_rfl le_rfl) edgeList1 slotList1
    (by decide) (by decide) (by decide) edgeTie edge_tie_maximum

def colorTie : Finset (Slot 1 2) := {(0,0),(0,1)}
def colorList : List (Slot 1 2) := [(0,0),(0,1)]

theorem color_conflict_pairs :
    conflictPairs emptyGraph 2 = {(((0 : Fin 1),0),(0,1))} := by decide

theorem color_tie_value : uScore emptyGraph 1 1 colorTie = 1 := by
  have hn : (0 : Slot 1 2) ≠ (0,1) := by decide
  simp only [uScore,color_conflict_pairs]
  norm_num [score,conflicts,weight,colorTie,hn,Finset.filter_singleton,
    Finset.filter_insert,Finset.filter_empty]

theorem color_tie_maximum :
    isScoreMax (conflictPairs emptyGraph 2) (weight 1 1) colorTie := by
  intro T
  have hn : (0 : Slot 1 2) ≠ (0,1) := by decide
  have h : ∀ x : Slot 1 2, x = (0,0) ∨ x = (0,1) := by
    rintro ⟨i,r⟩
    fin_cases i <;> fin_cases r <;> simp
  rcases selections_of_two (0,0) (0,1) h T with rfl | rfl | rfl | rfl <;>
    rw [color_conflict_pairs] <;> norm_num [score,conflicts,weight,colorTie,hn,
      Finset.filter_singleton,Finset.filter_insert,Finset.filter_empty]

theorem color_tie_infeasible : ¬ Feasible emptyGraph colorTie := by
  change ¬ feasible (conflictPairs emptyGraph 2) colorTie
  rw [color_conflict_pairs]
  simp [feasible,colorTie]

theorem color_tie_actual_return : algorithm [] colorList colorTie = {(0,1)} := by decide

theorem color_tie_optimal_return :
    Feasible emptyGraph (algorithm [] colorList colorTie) ∧
    score (conflictPairs emptyGraph 2) (weight 1 1) colorTie =
      ((algorithm [] colorList colorTie).card : ℝ) ∧
    ∀ T : Finset (Slot 1 2), Feasible emptyGraph T →
      (T.card : ℝ) ≤ ((algorithm [] colorList colorTie).card : ℝ) :=
  algorithm_optimal_return emptyGraph (weight 1 1)
    (weight_ge_one emptyGraph 1 1 le_rfl le_rfl) [] colorList
    (by simp) (by decide) (by decide) colorTie color_tie_maximum

theorem edge_tie_nonlinear_maximum (c2 : ℝ) : isNMax edgeGraph 1 c2 edgeTie := by
  apply (isNMax_iff_unordered edgeGraph 1 c2 edgeTie).mpr
  intro T
  have h := edge_tie_maximum T
  simp only [edge_conflict_pairs,score,conflicts,Finset.filter_singleton] at h ⊢
  by_cases h0 : ((0,0) : Slot 2 1) ∈ T <;> by_cases h1 : (1,0) ∈ T <;>
    simpa [weight,edgeTie,h0,h1] using h

theorem source_unit_corollary_control :
    qNonlinear edgeGraph 1 1 1 = alpha edgeGraph 1 ∧
    Feasible edgeGraph (algorithm edgeList1 slotList1 edgeTie) ∧
    ((algorithm edgeList1 slotList1 edgeTie).card : ℝ) = alpha edgeGraph 1 :=
  corollary_9_3_1 edgeGraph (by decide) 1 1 le_rfl le_rfl (Or.inl rfl)
    edgeList1 slotList1 (by decide) (by decide) (by decide) edgeTie
    (edge_tie_nonlinear_maximum 1)

theorem color_tie_literal_maximum : isNMax emptyGraph 1 (1/2) colorTie := by
  apply (isNMax_iff_unordered emptyGraph 1 (1/2) colorTie).mpr
  norm_num only [show (2 : ℝ) * (1/2) = 1 by norm_num]
  exact color_tie_maximum

theorem repaired_color_corollary_control :
    Feasible emptyGraph (algorithm [] colorList colorTie) ∧
    ((algorithm [] colorList colorTie).card : ℝ) = alpha emptyGraph 2 := by
  obtain ⟨hf,_,ha,_⟩ := algorithm_nonlinear_repaired emptyGraph 1 (1/2)
    le_rfl (by norm_num) [] colorList (by simp) (by decide) (by decide)
    colorTie color_tie_literal_maximum
  exact ⟨hf,ha⟩

theorem k1_negative_color_control :
    Feasible edgeGraph (algorithm edgeList1 slotList1 edgeTie) ∧
    nScore edgeGraph 1 (-3) edgeTie = ((algorithm edgeList1 slotList1 edgeTie).card : ℝ) ∧
    ((algorithm edgeList1 slotList1 edgeTie).card : ℝ) = alpha edgeGraph 1 :=
  algorithm_nonlinear_k1 edgeGraph 1 (-3) le_rfl edgeList1 slotList1
    (by decide) (by decide) (by decide) edgeTie (edge_tie_nonlinear_maximum (-3))

end Chapter09.SequentialControls

#print axioms Chapter09.SequentialControls.sequential_nonoptimal_trace
#print axioms Chapter09.SequentialControls.simultaneous_nonoptimal_trace
#print axioms Chapter09.SequentialControls.distinct_sequential_and_simultaneous
#print axioms Chapter09.SequentialControls.sequential_nonoptimal_feasible
#print axioms Chapter09.SequentialControls.repeated_scan_trace
#print axioms Chapter09.SequentialControls.empty_vertex_trace
#print axioms Chapter09.SequentialControls.edge_tie_maximum
#print axioms Chapter09.SequentialControls.edge_tie_infeasible
#print axioms Chapter09.SequentialControls.edge_tie_actual_return
#print axioms Chapter09.SequentialControls.edge_tie_optimal_return
#print axioms Chapter09.SequentialControls.color_tie_maximum
#print axioms Chapter09.SequentialControls.color_tie_infeasible
#print axioms Chapter09.SequentialControls.color_tie_actual_return
#print axioms Chapter09.SequentialControls.color_tie_optimal_return
#print axioms Chapter09.SequentialControls.edge_tie_nonlinear_maximum
#print axioms Chapter09.SequentialControls.source_unit_corollary_control
#print axioms Chapter09.SequentialControls.color_tie_literal_maximum
#print axioms Chapter09.SequentialControls.repaired_color_corollary_control
#print axioms Chapter09.SequentialControls.k1_negative_color_control
