module

public import Chapter03OAKKTSource
public import Chapter03OAKKTBoundaryHistory

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAKKTBoundary

theorem rest_cost_apply {n l : ℕ} (q : RealVector (n+l)) :
    restCost (n:=n) (l:=l) q = ∑ j : Fin l, weightedV q j := by
  exact (weightedLiftObjective_apply (n:=n) (s:=l) (fun _ => 1) q).trans
    (by simp only [one_mul])

def zeroSlacks : RealVector 2 := ![1/4,0]

theorem zero_rest_primal :
    weightedInsert (vec (1/2)) zeroSlacks ∈ restSet zeroData 0 := by
  apply (restSet_insert_iff _ _ _ _).mpr
  refine ⟨fun i => Fin.elim0 i,?_,?_⟩
  · intro j; fin_cases j <;> norm_num [soft,zeroData,vec,zeroSlacks]
  · intro j; fin_cases j <;> norm_num [zeroSlacks]

theorem zero_rest_minimum :
    IsMinimizer (restSet zeroData 0) (restCost (n:=1) (l:=2))
      (weightedInsert (vec (1/2)) zeroSlacks) := by
  refine ⟨zero_rest_primal,?_⟩
  intro q hq
  obtain ⟨hh,hg,hs⟩ := (weighted_lift_rows_iff (hard zeroData 0) (soft zeroData 0) q).mp hq.2
  rw [restCost_insert,rest_cost_apply]
  simpa [zeroSlacks,Fin.sum_univ_two] using
    zero_slack_lower_bound (weightedX q) (weightedV q) hg

theorem zero_fiber_empty : fiber zeroData 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := zero_slack_lower_bound x 0 hx.2
  norm_num at h

def zeroSumKKT : SumKKT zeroData (vec (1/2)) 0 zeroSlacks where
  Dg := zeroDerivative (zeroPoint (1/2))
  lambda := fun _ => 1
  nu := 0
  mu := fun i => Fin.elim0 i
  primal := zero_rest_primal
  derivative_g := zero_derivative (zeroPoint (1/2))
  lambda_nonneg := fun _ => by norm_num
  nu_nonneg := fun _ => le_rfl
  mu_nonneg := fun i => Fin.elim0 i
  soft_compl := by intro j; fin_cases j <;> norm_num [soft,zeroData,vec,zeroSlacks]
  slack_compl := by intro j; simp
  slack_stationarity := by intro j; simp
  hard_compl := fun i => Fin.elim0 i
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    norm_num [Fin.sum_univ_two,zeroDerivative,zeroPoint,vec]

def zeroSourceHistory : History zeroData (fun _ => 0) Set.univ (zeroHistory true)
    (fun _ => 0) (vec (1/2)) 0 where
  seed := 0
  current := 1
  distinct := by decide
  initial_all := by simp [zeroHistory]
  current_origin := rfl
  current_selected := by ext j; simp [zeroHistory,zeroPoint]
  affine := by intro j hj; exact False.elim (hj (Set.mem_univ j))
  g_derivative := zero_history_actual_derivatives true
  f_derivative := fun i => zero_objective_derivative _

theorem zero_rest_value : restCost (n:=1) (l:=2) (weightedInsert (vec (1/2)) zeroSlacks)=(1/4 : ℝ) := by
  norm_num [zeroSlacks,Fin.sum_univ_two]

def splitSoftSlacks : RealVector 5 := ![1/4,0,1/2,0,0]
def splitHardSlacks : RealVector 3 := ![1,0,0]

theorem split_soft_rest_primal :
    weightedInsert (vec (3/2)) splitSoftSlacks ∈ restSet splitSoftData 0 := by
  apply (restSet_insert_iff _ _ _ _).mpr
  refine ⟨fun i => Fin.elim0 i,?_,?_⟩
  · intro j; fin_cases j <;> norm_num [soft,splitSoftData,vec,splitSoftSlacks]
  · intro j; fin_cases j <;> norm_num [splitSoftSlacks]

theorem split_soft_rest_minimum :
    IsMinimizer (restSet splitSoftData 0) (restCost (n:=1) (l:=5))
      (weightedInsert (vec (3/2)) splitSoftSlacks) := by
  refine ⟨split_soft_rest_primal,?_⟩
  intro q hq
  obtain ⟨hh,hg,hs⟩ :=
    (weighted_lift_rows_iff (hard splitSoftData 0) (soft splitSoftData 0) q).mp hq.2
  rw [restCost_insert,rest_cost_apply]
  convert split_soft_slack_lower_bound (weightedX q) (weightedV q) hg hs using 1 <;>
    norm_num [splitSoftSlacks,Fin.sum_univ_succ]

theorem split_hard_rest_primal :
    weightedInsert (vec 1) splitHardSlacks ∈ restSet splitHardData 0 := by
  apply (restSet_insert_iff _ _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro i; fin_cases i <;> norm_num [hard,linearResidual,splitHardData,LinearForm,vec]
  · intro j; fin_cases j <;> norm_num [soft,splitHardData,vec,splitHardSlacks]
  · intro j; fin_cases j <;> norm_num [splitHardSlacks]

theorem split_hard_rest_minimum :
    IsMinimizer (restSet splitHardData 0) (restCost (n:=1) (l:=3))
      (weightedInsert (vec 1) splitHardSlacks) := by
  refine ⟨split_hard_rest_primal,?_⟩
  intro q hq
  obtain ⟨hh,hg,hs⟩ :=
    (weighted_lift_rows_iff (hard splitHardData 0) (soft splitHardData 0) q).mp hq.2
  have hx : (weightedX q,0) ∈ splitHardData.linearRegion := by
    intro i
    have h := hh i
    simpa [hard,linearResidual,sub_nonpos] using h
  rw [restCost_insert,rest_cost_apply]
  simpa [splitHardSlacks,Fin.sum_univ_succ] using
    split_hard_slack_lower_bound (weightedX q) (weightedV q) hx hg hs

theorem split_soft_rest_value :
    restCost (n:=1) (l:=5) (weightedInsert (vec (3/2)) splitSoftSlacks)=(3/4 : ℝ) := by
  norm_num [splitSoftSlacks,Fin.sum_univ_succ]

theorem split_hard_rest_value :
    restCost (n:=1) (l:=3) (weightedInsert (vec 1) splitHardSlacks)=(1 : ℝ) := by
  norm_num [splitHardSlacks,Fin.sum_univ_succ]

theorem split_rest_values_differ :
    restCost (n:=1) (l:=5) (weightedInsert (vec (3/2)) splitSoftSlacks) <
    restCost (n:=1) (l:=3) (weightedInsert (vec 1) splitHardSlacks) := by
  rw [split_soft_rest_value,split_hard_rest_value]
  norm_num

theorem split_soft_anchor_outside_hard_domain :
    splitPoint (3/2) 0 ∉ splitHardData.linearRegion := by
  rw [split_hard_region]
  norm_num [splitPoint,vec]

end Chapter03.OAKKTBoundary
