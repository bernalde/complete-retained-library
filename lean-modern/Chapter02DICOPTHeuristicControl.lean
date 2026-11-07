module

public import Chapter02DICOPTHeuristicGeometry

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
namespace Chapter02DICOPTExamples

def heuristicReturned : ℝ := min
  (heuristicData.objective heuristicOne.x heuristicOne.y)
  (heuristicData.objective heuristicMinusTwo.x heuristicMinusTwo.y)

theorem heuristic_return_suboptimal : heuristicReturned=1 ∧
    heuristicData.objective heuristicHalf.x heuristicHalf.y < heuristicReturned := by
  norm_num [heuristicReturned,heuristicOne,heuristicMinusTwo,heuristicHalf,heuristicAnchor]

theorem heuristic_initial_fractional : ¬ Binary heuristicInitial.y := by
  intro hb
  have hh := hb 0
  norm_num [heuristicInitial,heuristicAnchor] at hh

structure HeuristicCountercontrol : Prop where
  initializer_joint : Nonempty (JointKKT heuristicData (scalar 0) (triple (2/3) (1/3) 0))
  initializer_global : IsMinimizer heuristicData.relaxed
    (fun z => heuristicData.objective z.1 z.2) (heuristicInitial.x,heuristicInitial.y)
  initializer_fractional : ¬ Binary heuristicInitial.y
  first_master : IsMinimizer (masterFeasible heuristicData [heuristicInitial] ∅)
    (masterObjective heuristicData [heuristicInitial]) heuristicFirstPoint
  second_master :
    IsMinimizer (masterFeasible heuristicData [heuristicInitial,heuristicOne] {firstBinary})
      (masterObjective heuristicData [heuristicInitial,heuristicOne]) heuristicSecondPoint
  unvisited_tie :
    IsMinimizer (masterFeasible heuristicData [heuristicInitial,heuristicOne] {firstBinary})
      (masterObjective heuristicData [heuristicInitial,heuristicOne]) heuristicUnvisitedPoint
  master_values : masterObjective heuristicData [heuristicInitial] heuristicFirstPoint=0 ∧
    masterObjective heuristicData [heuristicInitial,heuristicOne] heuristicSecondPoint=0 ∧
    masterObjective heuristicData [heuristicInitial,heuristicOne] heuristicUnvisitedPoint=0
  replies_match : heuristicFirstPoint.y=heuristicOne.y ∧
    heuristicSecondPoint.y=heuristicMinusTwo.y ∧
    heuristicOne.y=realBinary firstBinary
  all_fixed_minima : ∀ a : Anchor heuristicData,
    IsMinimizer (heuristicData.fiber a.y) (fun x => heuristicData.objective x a.y) a.x
  actual_abadie : ∀ a : Anchor heuristicData,
    posTangentConeAt (heuristicData.fiber a.y) a.x=heuristicLinearized a ∧
    heuristicLinearized a={0}
  actual_affine_derivatives : ∀ (i : Fin 4) (y : RealVector 3) (x : V),
    HasFDerivAt (fun z => heuristicData.affineRow i z y)
      ((heuristicData.D i 0) • coord) x
  original_minimum : IsMinimizer heuristicData.original
    (fun z => heuristicData.objective z.1 z.2) (scalar (-(1/2)),triple 0 0 1)
  stop_values :
    heuristicData.objective heuristicOne.x heuristicOne.y = 1 ∧
    heuristicData.objective heuristicMinusTwo.x heuristicMinusTwo.y = 4 ∧
    heuristicData.objective heuristicHalf.x heuristicHalf.y = 1/4 ∧
    heuristicData.objective heuristicOne.x heuristicOne.y <
      heuristicData.objective heuristicMinusTwo.x heuristicMinusTwo.y ∧
    heuristicData.objective heuristicOne.x heuristicOne.y ≤
      heuristicData.objective heuristicMinusTwo.x heuristicMinusTwo.y ∧
    heuristicData.objective heuristicHalf.x heuristicHalf.y <
      heuristicData.objective heuristicOne.x heuristicOne.y
  returned_incumbent : heuristicReturned=1 ∧
    heuristicData.objective heuristicHalf.x heuristicHalf.y < heuristicReturned

theorem heuristic_full_countertrace : HeuristicCountercontrol where
  initializer_joint := ⟨heuristicJoint⟩
  initializer_global := heuristic_relaxed_minimum
  initializer_fractional := heuristic_initial_fractional
  first_master := heuristic_first_master_minimum
  second_master := heuristic_second_master_minimum
  unvisited_tie := heuristic_unvisited_master_minimum
  master_values := by
    norm_num [masterObjective,heuristicFirstPoint,heuristicSecondPoint,heuristicUnvisitedPoint,
      heuristicData,Fin.sum_univ_succ]
  replies_match := by
    refine ⟨rfl,rfl,?_⟩
    ext i
    fin_cases i <;> norm_num [heuristicOne,heuristicAnchor,realBinary,firstBinary,triple]
  all_fixed_minima := heuristic_fixed_minimum
  actual_abadie := heuristic_actual_abadie
  actual_affine_derivatives := heuristic_affine_derivative
  original_minimum := heuristic_original_minimum
  stop_values := heuristic_strict_weak_stop
  returned_incumbent := heuristic_return_suboptimal

end Chapter02DICOPTExamples
