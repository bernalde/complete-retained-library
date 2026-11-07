module

public import Chapter03FPUnboundedFarGeometry

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedFar

@[simp] theorem seed_objective : data.f seed=0 := by norm_num [data,seed,obj_line]
@[simp] theorem seed_derivative : data.Df seed=0 := by
  apply ContinuousLinearMap.ext
  intro p
  simp [data,seed,line,deriv]
@[simp] theorem seed_constraint (j : Fin 1) : data.g j seed= -610/1000000 := by
  norm_num [data,seed,obj_line]
@[simp] theorem constraint_derivative_eq (j : Fin 1) (p : P) : data.Dg j p=data.Df p := rfl
@[simp] theorem minus_constraint (j : Fin 1) : data.g j minus=0 := by
  norm_num [data,minus,obj_line]
@[simp] theorem plus_constraint (j : Fin 1) : data.g j plus=0 := by
  norm_num [data,plus,obj_line]

theorem anchors_zero : FPUnbounded.anchors data state0=[⟨seed,Set.univ⟩] := rfl
theorem anchors_one : FPUnbounded.anchors data state1=
    [⟨seed,Set.univ⟩,⟨minus,Set.univ⟩] := by
  simp [FPUnbounded.anchors,state1,state0,append,initialState,firstEvent,Event.anchor,
    nonlinear_all]

theorem seed_anchor_mem (s : State 0 2) :
    (⟨s.seed,Set.univ⟩ : Anchor 0 2 1) ∈ FPUnbounded.anchors data s := by
  simp [FPUnbounded.anchors]

theorem master_initial (z : P × ℝ) : z ∈ FPUnbounded.master data state0 ↔
    ∃ k : ℤ, z.1=integerPoint k ∧ 0 ≤ z.2 := by
  constructor
  · intro hz
    obtain ⟨hb,hi,hr,hn,hc⟩ := FPUnboundedControls.master_rows data state0 z |>.mp hz
    obtain ⟨k,hk⟩ := (base_integer_param z.1).mp ⟨hb,hi⟩
    refine ⟨k,hk,?_⟩
    have h := (hr ⟨seed,Set.univ⟩ (by rw [anchors_zero]; simp)).1
    simpa using h
  · rintro ⟨k,hk,hα⟩
    have hbase := (base_integer_param z.1).mpr ⟨k,hk⟩
    apply (FPUnboundedControls.master_rows data state0 z).mpr
    refine ⟨hbase.1,hbase.2,?_,?_,True.intro⟩
    · intro a ha
      rw [anchors_zero] at ha
      have he : a=⟨seed,Set.univ⟩ := by simpa using ha
      subst a
      constructor
      · simpa using hα
      · intro j _; norm_num
    · simp [retainedNormals,state0,initialState]

theorem first_normal_retained {z : P × ℝ} (hz : z ∈ FPUnbounded.master data state1) :
    0 ≤ firstEvent.normal z.1 := by
  apply hz.2.1 firstEvent
  · simp [state1,state0,append,initialState]
  · rfl

theorem second_objective_row (k : ℤ) (hk : 1 ≤ k) :
    data.f minus+data.Df minus (integerPoint k-minus) ≤ 0 := by
  rw [integer_point_line]
  change data.f (line (-1/1000))+data.Df (line (-1/1000))
    (line ((k:ℝ)-233/610)-line (-1/1000)) ≤ 0
  rw [tangent_line]
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  linarith

theorem second_constraint_row (j : Fin 1) (k : ℤ) (hk : 1 ≤ k) :
    data.g j minus+data.Dg j minus (integerPoint k-minus) ≤ 0 := by
  rw [integer_point_line]
  change data.g j (line (-1/1000))+data.Dg j (line (-1/1000))
    (line ((k:ℝ)-233/610)-line (-1/1000)) ≤ 0
  rw [constraint_tangent_line]
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  linarith

theorem master_second (z : P × ℝ) : z ∈ FPUnbounded.master data state1 ↔
    ∃ k : ℤ, 1 ≤ k ∧ z.1=integerPoint k ∧ 0 ≤ z.2 := by
  constructor
  · intro hz
    obtain ⟨hb,hi,hr,hn,hc⟩ := FPUnboundedControls.master_rows data state1 z |>.mp hz
    obtain ⟨k,hk⟩ := (base_integer_param z.1).mp ⟨hb,hi⟩
    have hnorm := first_normal_retained hz
    rw [hk,first_integer_normal] at hnorm
    refine ⟨k,hnorm,hk,?_⟩
    have h := (hr ⟨seed,Set.univ⟩ (by rw [anchors_one]; simp)).1
    simpa using h
  · rintro ⟨k,hk,hpoint,hα⟩
    have hbase := (base_integer_param z.1).mpr ⟨k,hpoint⟩
    apply (FPUnboundedControls.master_rows data state1 z).mpr
    refine ⟨hbase.1,hbase.2,?_,?_,True.intro⟩
    · intro a ha
      rw [anchors_one] at ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl
      · constructor
        · simpa using hα
        · intro j _; norm_num
      · constructor
        · change data.f minus+data.Df minus (z.1-minus) ≤ z.2
          rw [hpoint]
          exact (second_objective_row k hk).trans hα
        · intro j _
          change data.g j minus+data.Dg j minus (z.1-minus) ≤ 0
          rw [hpoint]
          exact second_constraint_row j k hk
    · intro e he hn
      have he' : e=firstEvent := by simpa [state1,state0,append,initialState] using he
      subst e
      rw [hpoint,first_integer_normal]
      exact hk

theorem master_third_empty : ¬(FPUnbounded.master data state2).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨k,hk⟩ := (base_integer_param z.1).mp ⟨hz.1.1,hz.1.2.1⟩
  have h0 := hz.2.1 firstEvent (by simp [state2,state1,state0,append,initialState]) rfl
  have h1 := hz.2.1 secondEvent (by simp [state2,state1,state0,append,initialState]) rfl
  rw [hk,first_integer_normal] at h0
  rw [hk,second_integer_normal] at h1
  omega

def master0 : P × ℝ := (integerPoint 0,0)
def master1 : P × ℝ := (integerPoint 1,0)

theorem master0_minimum :
    IsMinimizer (FPUnbounded.master data state0) (FPUnbounded.masterCost state0) master0 := by
  refine ⟨(master_initial master0).mpr ⟨0,rfl,le_rfl⟩,?_⟩
  intro z hz
  obtain ⟨k,hk,hα⟩ := (master_initial z).mp hz
  change l1 seed (integerPoint 0) ≤ l1 seed z.1
  rw [hk]
  exact first_cost_min k

theorem master1_minimum :
    IsMinimizer (FPUnbounded.master data state1) (FPUnbounded.masterCost state1) master1 := by
  refine ⟨(master_second master1).mpr ⟨1,le_rfl,rfl,le_rfl⟩,?_⟩
  intro z hz
  obtain ⟨k,hk,hpoint,hα⟩ := (master_second z).mp hz
  change l1 minus (integerPoint 1) ≤ l1 minus z.1
  rw [hpoint]
  exact second_cost_min k hk

theorem master0_target_unique {z : P × ℝ}
    (hz : IsMinimizer (FPUnbounded.master data state0) (FPUnbounded.masterCost state0) z) :
    z.1=integerPoint 0 := by
  obtain ⟨k,hk,hα⟩ := (master_initial z).mp hz.1
  have hc := hz.2 master0 master0_minimum.1
  change l1 seed z.1 ≤ l1 seed (integerPoint 0) at hc
  rw [hk] at hc
  exact hk.trans (congrArg integerPoint (first_cost_unique k hc))

theorem master1_target_unique {z : P × ℝ}
    (hz : IsMinimizer (FPUnbounded.master data state1) (FPUnbounded.masterCost state1) z) :
    z.1=integerPoint 1 := by
  obtain ⟨k,hk,hpoint,hα⟩ := (master_second z).mp hz.1
  have hc := hz.2 master1 master1_minimum.1
  change l1 minus z.1 ≤ l1 minus (integerPoint 1) at hc
  rw [hpoint] at hc
  exact hpoint.trans (congrArg integerPoint (second_cost_unique k hk hc))

theorem first_reply : FPUnbounded.EventReply data state0 master0 firstEvent := by
  refine ⟨integer_point_cast 0,rfl,projection_minimum_first,projection_first_nonzero⟩

theorem second_reply : FPUnbounded.EventReply data state1 master1 secondEvent := by
  refine ⟨integer_point_cast 1,rfl,projection_minimum_second,projection_second_nonzero⟩

def decision0 : FPUnbounded.Decision data none state0 :=
  .next firstEvent ⟨master0,master0_minimum,by simp [BeforeCap],first_reply⟩
def decision1 : FPUnbounded.Decision data none state1 :=
  .next secondEvent ⟨master1,master1_minimum,by simp [BeforeCap],second_reply⟩
def decision2 : FPUnbounded.Decision data none state2 :=
  .stop .emptyMaster (.emptyMaster master_third_empty)

def fallback : FPUnbounded.Selector data none :=
  Classical.choice (FPUnbounded.selector_nonempty data analytic none)
def choose : FPUnbounded.Selector data none :=
  FPUnboundedControls.patch state0 decision0
    (FPUnboundedControls.patch state1 decision1
      (FPUnboundedControls.patch state2 decision2 fallback))

theorem state1_ne_state0 : state1 ≠ state0 := by
  intro he
  have h := congrArg (fun s : State 0 2 => s.history.length) he
  norm_num [state1,state0,append,initialState] at h
theorem state2_ne_state0 : state2 ≠ state0 := by
  intro he
  have h := congrArg (fun s : State 0 2 => s.history.length) he
  norm_num [state2,state1,state0,append,initialState] at h
theorem state2_ne_state1 : state2 ≠ state1 := by
  intro he
  have h := congrArg (fun s : State 0 2 => s.history.length) he
  norm_num [state2,state1,state0,append,initialState] at h

theorem choose_zero : choose state0=decision0 := by simp [choose]
theorem choose_one : choose state1=decision1 := by
  simp [choose,FPUnboundedControls.patch,state1_ne_state0]
theorem choose_two : choose state2=decision2 := by
  simp [choose,FPUnboundedControls.patch,state2_ne_state0,state2_ne_state1]

def output : LoopOutput 0 2 := ⟨state2,.emptyMaster,2,2,3,0⟩

theorem run_three : FPUnbounded.run data choose 3 state0=some output := by
  rw [FPUnbounded.run,choose_zero]
  change (FPUnbounded.run data choose 2 state1).map (LoopOutput.bump firstEvent)=some output
  rw [FPUnbounded.run,choose_one]
  change ((FPUnbounded.run data choose 1 state2).map (LoopOutput.bump secondEvent)).map
    (LoopOutput.bump firstEvent)=some output
  rw [FPUnbounded.run,choose_two]
  rfl

theorem procedure_three :
    FPUnbounded.procedureWithFuel data (.minimum seed seed_minimum) choose 3=
      some (.loop output) := by
  have hn : seed ∉ data.original := fun h => original_empty ⟨seed,h⟩
  simp only [FPUnbounded.procedureWithFuel,hn,↓reduceDIte,↓reduceIte]
  exact congrArg (Option.map Outcome.loop) run_three

theorem actual_counts : output.bodies=2 ∧ output.projections=2 ∧
    output.masters=3 ∧ output.polishes=0 ∧ output.reason=.emptyMaster :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem actual_far_failure_control :
    FPUnbounded.Analytic data ∧ 0 < data.delta ∧
    (∀ p ∈ data.relaxation, ‖Chapter03.yMap 0 2 p‖ < 1) ∧
    (4 < ‖intY (target 0)‖ ∧ 4 < ‖intY (target 1)‖) ∧
    ¬data.original.Nonempty ∧
    FPUnbounded.procedureWithFuel data (.minimum seed seed_minimum) choose 3=
      some (.loop output) ∧
    output.bodies=2 ∧ output.projections=2 ∧ output.masters=3 ∧ output.polishes=0 := by
  exact ⟨analytic,by norm_num [data],fun _ hp => projected_norm_lt_one hp,
    selected_targets_far,original_empty,procedure_three,rfl,rfl,rfl,rfl⟩

end Chapter03.FPUnboundedFar
