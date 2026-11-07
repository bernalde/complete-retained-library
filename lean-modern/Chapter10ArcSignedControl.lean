module

public import Chapter10ArcControls
public import Chapter10FiniteAttainment

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter10.Routing.Arc.Controls
open Chapter10.Routing Chapter10.Routing.Arc Chapter10.Algebra

theorem depot_ne_customer : (none : Node 1) ≠ some 0 := by decide

def signedData : Data 1 := { zeroData 1 with cost := fun i _ => if i = none then -2 else 1 }
def signedPath : TimedPath 1 1 := ⟨[0],0,0⟩
def signedX : Assignment 1 1 := encodeEdges (signedPath.edges (fun _ => 0))

theorem signed_customer_literal : Literal signedData zeroGrid signedX := by
  have hh := timed_paths_encode_literal signedData zeroGrid (fun _ => (0 : Fin 1)) [signedPath]
  apply hh
  · decide
  · intro i; fin_cases i; decide
  · intro q hq e he
    simp only [List.mem_singleton] at hq
    subst q
    simp only [TimedPath.edges,signedPath,timedEdges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl <;> norm_num [edgeValid,signedData,zeroData,zeroGrid,inWindow]

theorem signed_customer_cost : objective signedData signedX = -1 := by
  norm_num [objective,signedData,signedX,TimedPath.edges,signedPath,timedEdges,encodeEdges,
    Chapter10.bit,Fintype.sum_prod_type,Fintype.sum_option,Fin.sum_univ_succ,Option.some_ne_none,depot_ne_customer]

theorem signed_coordinate_bound : (∑ e : Edge 1 1, |coordinateCost signedData e|) = 6 := by
  norm_num [coordinateCost,signedData,Fintype.sum_prod_type,Fintype.sum_option,Fin.sum_univ_succ,Option.some_ne_none,depot_ne_customer]

theorem signed_actual_offset : arcEnergy signedData zeroGrid 7 signedX = -1 ∧
    quadratic (arcQUBO signedData zeroGrid 7) (fun e => Chapter10.bit (signedX e)) = -8 := by
  have hp := (arc_penalty_zero_iff signedData zeroGrid signedX).mpr
    ((literal_iff_feasible signedData zeroGrid signedX).mp signed_customer_literal)
  have he : arcEnergy signedData zeroGrid 7 signedX = -1 := by
    simp [arcEnergy,hp,signed_customer_cost]
  refine ⟨he,?_⟩
  have hi := actual_arc_qubo_identity signedData zeroGrid 7 signedX
  rw [he] at hi
  norm_num at hi
  linarith

theorem signed_full_exactness :
    (IsMinOn Set.univ (arcEnergy signedData zeroGrid 7) signedX ∧
      ∃ y : Assignment 1 1, Feasible signedData zeroGrid y) ↔
    IsMinOn {y : Assignment 1 1 | Feasible signedData zeroGrid y} (objective signedData) signedX := by
  simpa using arc_minimizers_exact signedData zeroGrid Set.univ 7
    (by rw [signed_coordinate_bound]; norm_num) signedX

theorem infeasible_model_still_has_energy_minimum :
    (∃ x : Assignment 1 1, IsMinOn Set.univ (arcEnergy halfTravel zeroGrid 1) x) ∧
      ¬ ∃ x : Assignment 1 1, Feasible halfTravel zeroGrid x := by
  exact ⟨finite_domain_attainment Set.univ Set.univ_nonempty (arcEnergy halfTravel zeroGrid 1),
    grid_intersection_not_representability.2⟩

end Chapter10.Routing.Arc.Controls
