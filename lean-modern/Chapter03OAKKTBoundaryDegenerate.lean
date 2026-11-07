module

public import Chapter03OAKKTSource
public import Chapter03OAKKTBoundaryRestoration
public import Chapter03

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAKKTBoundary

/-- A literal empty soft family and empty hard family, with an arbitrary number
of continuous coordinates and an empty integer carrier. -/
def emptyData (n : ℕ) : ModelData n 0 0 0 where
  g := fun j => Fin.elim0 j
  A := fun i => Fin.elim0 i
  B := fun i => Fin.elim0 i
  rhs := fun i => Fin.elim0 i
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

theorem empty_soft_cost (n : ℕ) (q : RealVector (n+0)) :
    restCost (n:=n) (l:=0) q = 0 := by simp [restCost,weightedLiftObjective]

theorem empty_soft_no_positive_total (s : RealVector 0) : ¬0 < ∑ j, s j := by simp

theorem empty_rest_domain (n : ℕ) : restSet (emptyData n) 0 = Set.univ := by
  ext q
  simp [restSet,weightedLiftRows]

theorem empty_rest_minimum (n : ℕ) (q : RealVector (n+0)) :
    IsMinimizer (restSet (emptyData n) 0) (restCost (n:=n) (l:=0)) q := by
  rw [empty_rest_domain]
  exact ⟨Set.mem_univ _,fun z hz => by simp [restCost,weightedLiftObjective]⟩

/-- The n=l=r=0 instance has a real primal minimum of value zero. -/
theorem all_empty_rest_minimum :
    IsMinimizer (restSet (emptyData 0) 0) (restCost (n:=0) (l:=0)) 0 :=
  empty_rest_minimum 0 0

theorem unbounded_coordinate_no_upper :
    ¬ ∃ U : ℝ, ∀ q ∈ restSet (emptyData 1) 0, weightedX q 0 ≤ U := by
  rintro ⟨U,hU⟩
  have h := hU (weightedInsert (vec (U+1)) (0 : RealVector 0))
    (by rw [empty_rest_domain]; trivial)
  rw [weightedX_insert] at h
  change _ ≤ _ at h
  dsimp [vec] at h
  linarith

theorem unbounded_coordinate_no_lower :
    ¬ ∃ L : ℝ, ∀ q ∈ restSet (emptyData 1) 0, L ≤ weightedX q 0 := by
  rintro ⟨L,hL⟩
  have h := hL (weightedInsert (vec (L-1)) (0 : RealVector 0))
    (by rw [empty_rest_domain]; trivial)
  rw [weightedX_insert] at h
  change _ ≤ _ at h
  dsimp [vec] at h
  linarith

/-- Zero-dimensional positive restoration is nonvacuous: one constant soft row. -/
def constantData : ModelData 0 0 1 0 where
  g := fun _ _ => 1
  A := fun i => Fin.elim0 i
  B := fun i => Fin.elim0 i
  rhs := fun i => Fin.elim0 i
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

theorem constant_rest_primal :
    weightedInsert (0 : RealVector 0) (vec 1) ∈ restSet constantData 0 := by
  apply (restSet_insert_iff _ _ _ _).mpr
  exact ⟨fun i => Fin.elim0 i,fun j => le_rfl,fun j => by norm_num [vec]⟩

theorem constant_rest_minimum :
    IsMinimizer (restSet constantData 0) (restCost (n:=0) (l:=1))
      (weightedInsert (0 : RealVector 0) (vec 1)) := by
  refine ⟨constant_rest_primal,?_⟩
  intro q hq
  have hg := ((weighted_lift_rows_iff (hard constantData 0) (soft constantData 0) q).mp hq.2).2.1 0
  rw [restCost_insert,rest_cost_apply]
  simpa [soft,constantData,vec] using hg

def constantSumKKT : SumKKT constantData 0 0 (vec 1) where
  Dg := 0
  lambda := fun _ => 1
  nu := 0
  mu := fun i => Fin.elim0 i
  primal := constant_rest_primal
  derivative_g := fun _ => hasFDerivAt_const 1 _
  lambda_nonneg := fun _ => by norm_num
  nu_nonneg := fun _ => le_rfl
  mu_nonneg := fun i => Fin.elim0 i
  soft_compl := by intro j; simp [soft,constantData,vec]
  slack_compl := by intro j; simp
  slack_stationarity := by intro j; simp
  hard_compl := fun i => Fin.elim0 i
  stationarity := by simp [restrict]

/-- The constant row is affine: only the initial all-row slot retains it. -/
def constantHistory : TangentFamily 0 0 1 2 where
  origin := 0
  selected := fun i => if i=0 then Set.univ else ∅
  derivative := 0

def constantSourceHistory : History constantData (fun _ => 0) ∅
    constantHistory (fun _ => 0) 0 0 where
  seed := 0
  current := 1
  distinct := by decide
  initial_all := by simp [constantHistory]
  current_origin := rfl
  current_selected := by ext j; simp [constantHistory,constantData]
  affine := by
    intro j hj
    refine ⟨0,0,-1,?_⟩
    intro p
    simp [constantData,LinearForm]
  g_derivative := fun _ _ => hasFDerivAt_const 1 _
  f_derivative := fun _ => hasFDerivAt_const 0 _

theorem constant_rest_value :
    restCost (n:=0) (l:=1) (weightedInsert (0 : RealVector 0) (vec 1))=(1 : ℝ) := by rw [restCost_insert]; simp [vec]

/-- Actual finite lower and upper hard rows, including both sides when lo=hi. -/
def intervalData (lo hi : ℝ) : ModelData 1 0 0 2 where
  g := fun j => Fin.elim0 j
  A := ![vec (-1),vec 1]
  B := 0
  rhs := ![-lo,hi]
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

theorem interval_hard_region (lo hi : ℝ) (x : RealVector 1) :
    (x,0) ∈ (intervalData lo hi).linearRegion ↔ lo ≤ x 0 ∧ x 0 ≤ hi := by
  simp [ModelData.linearRegion,intervalData,LinearForm,vec,Fin.forall_fin_two]

theorem interval_rest_membership (lo hi : ℝ) (q : RealVector (1+0)) :
    q ∈ restSet (intervalData lo hi) 0 ↔ lo ≤ weightedX q 0 ∧ weightedX q 0 ≤ hi := by
  simp only [restSet,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_univ,true_and,
    weighted_lift_rows_iff]
  simp [hard,linearResidual,intervalData,LinearForm,vec,Fin.forall_fin_two]

theorem inconsistent_hard_domain_empty : restSet (intervalData 1 0) 0 = ∅ := by
  ext q
  rw [interval_rest_membership]
  simp only [Set.mem_empty_iff_false,iff_false]
  intro h
  linarith [h.1,h.2]

theorem empty_hard_domain_no_minimizer :
    ¬ ∃ q, IsMinimizer (restSet (intervalData 1 0) 0) (restCost (n:=1) (l:=0)) q := by
  rintro ⟨q,hq⟩
  rw [inconsistent_hard_domain_empty] at hq
  exact hq.1

theorem fixed_hard_retains_both :
    (intervalData 2 2).A 0 0 = -1 ∧ (intervalData 2 2).A 1 0 = 1 ∧
    (intervalData 2 2).rhs 0 = -2 ∧ (intervalData 2 2).rhs 1 = 2 := by
  norm_num [intervalData,vec]

theorem fixed_hard_rest_minimum :
    IsMinimizer (restSet (intervalData 2 2) 0) (restCost (n:=1) (l:=0))
      (weightedInsert (vec 2) 0) := by
  refine ⟨(interval_rest_membership _ _ _).mpr ?_,?_⟩
  · rw [weightedX_insert]; simp [vec]
  · intro q hq; simp [restCost,weightedLiftObjective]

theorem fixed_hard_every_primal (q : RealVector (1+0))
    (hq : q ∈ restSet (intervalData 2 2) 0) : weightedX q 0 = 2 := by
  obtain ⟨hl,hu⟩ := (interval_rest_membership _ _ _).mp hq
  exact le_antisymm hu hl

/-- Reuse only the accepted static optimizer and gap facts. This conjunction
has no execution or infinite-trace conclusion and proves no general CQ theorem. -/
theorem accepted_cq_static_boundary :
    IsMinimizer Chapter03.cqOriginal Chapter03.cqCost (0,false) ∧
    IsMinimizer Chapter03.cqMaster (fun p => p.2.2) (1,false,-3/4) ∧
    Chapter03.cqCost (0,false)-((1,false,-3/4) : ℝ × Bool × ℝ).2.2=1 :=
  ⟨Chapter03.cq_original_optimal,Chapter03.cq_master_optimal,Chapter03.cq_permanent_gap⟩

end Chapter03.OAKKTBoundary
