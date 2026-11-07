module

public import Chapter03OAKKT
public import Chapter03OAKKTBoundaryRestoration
public import Chapter03OAKKTBoundaryDegenerate

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAKKTBoundary

/-- The full residual-zero history consumes the actual-minimum infeasible
branch wrapper, in addition to the direct master calculation. -/
theorem zero_source_master_exclusion :
    ¬ ∃ z ∈ Chapter06.EpigraphMaster zeroData (fun _ => 0) (zeroHistory true)
      (fun _ => 0) Set.univ, z.1.2 = (0 : RealVector 0) :=
  infeasible_restoration_master_exclusion zeroSourceHistory
    (by rw [zero_fiber_empty]; simp) zero_rest_minimum zeroSumKKT

theorem zero_actual_minimum_positive : 0 < ∑ j, zeroSlacks j :=
  (rest_minimum_positive_iff_empty zeroData 0 (vec (1/2)) zeroSlacks
    zero_rest_minimum).mpr (by rw [zero_fiber_empty]; simp)

theorem zero_actual_minimum_slacks_tight (j : Fin 2) :
    zeroSlacks j = max (soft zeroData 0 j (vec (1/2))) 0 :=
  ((rest_minimizer_iff zeroData 0 (vec (1/2)) zeroSlacks).mp zero_rest_minimum).2 j

theorem zero_multiplier_sum_two : (∑ j, zeroSumKKT.lambda j) = (2 : ℝ) := by
  norm_num [zeroSumKKT,Fin.sum_univ_two]

theorem constant_fiber_empty : fiber constantData 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := hx.2 0
  norm_num [constantData] at h

theorem zero_dimensional_source_master_exclusion :
    ¬ ∃ z ∈ Chapter06.EpigraphMaster constantData (fun _ => 0) constantHistory
      (fun _ => 0) Set.univ, z.1.2 = (0 : RealVector 0) :=
  infeasible_restoration_master_exclusion constantSourceHistory
    (by rw [constant_fiber_empty]; simp) constant_rest_minimum constantSumKKT

theorem empty_rows_source_fiber_nonempty (n : ℕ) : (fiber (emptyData n) 0).Nonempty :=
  (rest_minimum_zero_iff_nonempty (emptyData n) 0 0 0
    (empty_rest_minimum n (weightedInsert 0 0))).mp (by simp)

theorem fixed_domain_source_fiber_nonempty : (fiber (intervalData 2 2) 0).Nonempty :=
  (rest_minimum_zero_iff_nonempty (intervalData 2 2) 0 (vec 2) 0
    fixed_hard_rest_minimum).mp (by simp)

/-- A separate one-anchor tangent validity control at the all-soft minimum
outside the hard physical interval. This is not a History or execution. -/
def splitOutsideTangents : TangentFamily 1 1 5 1 where
  origin := fun _ => splitPoint (3/2) 0
  selected := fun _ => Set.univ
  derivative := fun _ => splitSoftDerivative (splitPoint (3/2) 0)

theorem split_outside_anchor_preserves_original
    (p : Point 1 1) (hp : p ∈ splitSoftData.feasibleOn Set.univ) :
    (p,0) ∈ Chapter06.EpigraphMaster splitSoftData (fun _ => 0)
      splitOutsideTangents (fun _ => 0) Set.univ :=
  Chapter06.source_feasible_epigraph_in_master splitSoftData (fun _ => 0)
    splitOutsideTangents (fun _ => 0) Set.univ split_soft_convex
    (convexOn_const 0 convex_univ) (fun _ => Set.mem_univ _)
    (fun i j hj => split_soft_derivative _ j) (fun _ => hasFDerivAt_const 0 _) hp

theorem split_outside_anchor_admits_original_witness :
    (splitPoint 1 1,0) ∈ Chapter06.EpigraphMaster splitSoftData (fun _ => 0)
      splitOutsideTangents (fun _ => 0) Set.univ :=
  split_outside_anchor_preserves_original _ split_original_feasible

end Chapter03.OAKKTBoundary
