module

public import Chapter03PumpOAIntegrated

@[expose] public section

/-! Unchanged Integrated data with a selected successful first pump body.
The projection is explicitly selected at the polished solution; no uniqueness
of its continuous coordinate is asserted. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.PumpOA.IntegratedWarm

abbrev I := OAExec.Integrated.spec
def pump (delta : ℝ) : FP.Data 1 1 1 1 := asFPDelta I delta
def s0 : FP.State 1 1 := FP.initialState OAExec.Integrated.seed
def event : FP.Event 1 1 :=
  ⟨target1,OAExec.Integrated.solution,none,
    some (OAExec.Integrated.solution,OAExec.Integrated.solution)⟩
def s1 : FP.State 1 1 := FP.append s0 event

theorem full_assumptions : OAExec.AvailabilityAssumptions I :=
  OAExec.Integrated.source_package

theorem master0_minimum (delta : ℝ) : IsMinimizer (FP.master (pump delta) s0)
    (FP.masterCost s0) (OAExec.Integrated.solution,5/4) := by
  have h := Integrated.inspected_master_minimum
  rw [show FP.master Integrated.pump Integrated.pumpState =
    OAExec.master I OAExec.Integrated.seed [] from
      pump_initial_master_eq I 0 OAExec.Integrated.seed] at h
  rw [show FP.master (pump delta) s0=OAExec.master I OAExec.Integrated.seed [] from
    pump_initial_master_eq I delta OAExec.Integrated.seed]
  exact h

theorem solution_distance : FP.distance target1 OAExec.Integrated.solution=0 := by
  apply (FP.distance_zero_iff _ _).mpr
  funext j
  fin_cases j
  norm_num [OAExec.Integrated.solution,pt,scalar,FP.intCast,target1]

theorem solution_fiber_minimum (delta : ℝ) :
    IsMinimizer ((pump delta).fiber target1) (pump delta).f OAExec.Integrated.solution := by
  refine ⟨⟨(OAExec.Integrated.relaxation _).mpr (by norm_num [OAExec.Integrated.solution,pt,scalar]),
    (FP.distance_zero_iff _ _).mp solution_distance⟩,?_⟩
  intro p hp
  have hx := ((OAExec.Integrated.relaxation p).mp hp.1).1
  have hy := congrFun hp.2 0
  norm_num [FP.intCast,target1] at hy
  change (1/2-1)^2+1≤(p.1 0-1)^2+p.2 0
  rw [hy]
  nlinarith [sq_nonneg (p.1 0-1/2)]

theorem reply (delta : ℝ) : FP.EventReply (pump delta) s0
    (OAExec.Integrated.solution,5/4) event := by
  refine ⟨(FP.distance_zero_iff _ _).mp solution_distance,rfl,?_,?_⟩
  · refine ⟨⟨(solution_fiber_minimum delta).1.1,trivial⟩,?_⟩
    intro p _
    change FP.distance target1 OAExec.Integrated.solution≤FP.distance target1 p
    rw [solution_distance]
    exact sq_nonneg _
  · exact ⟨solution_distance,solution_fiber_minimum delta,rfl⟩

theorem solution_tangent (p : P) :
    OAExec.Integrated.objective OAExec.Integrated.solution+
      OAExec.Integrated.Df OAExec.Integrated.solution (p-OAExec.Integrated.solution)=
        -p.1 0+p.2 0+3/4 := by
  norm_num [OAExec.Integrated.objective,OAExec.Integrated.Df,
    OAExec.Integrated.solution,pt,scalar]
  ring

theorem epigraph_eq (delta : ℝ) : FP.epigraph (pump delta) s1=
    OAExec.epigraph I OAExec.Integrated.seed [] := by
  ext z
  constructor
  · exact pump_epigraph_seed_only I delta s1
  · intro hz
    obtain ⟨hl,hy,hg,hf,_⟩ := (OAExec.epigraph_mem_iff I OAExec.Integrated.seed [] z).mp hz
    refine ⟨⟨⟨⟨Set.mem_univ _,?_⟩,hl⟩,hy⟩,?_⟩
    · intro i j hj
      fin_cases i
      · exact hg j
      · change j∈I.nonlinear ∧ 0≤I.model.g j OAExec.Integrated.solution at hj
        norm_num [I,OAExec.Integrated.spec,OAExec.Integrated.model,
          OAExec.Integrated.solution,pt,scalar] at hj
    · intro i
      fin_cases i
      · exact hf
      · change OAExec.Integrated.objective OAExec.Integrated.solution+
          OAExec.Integrated.Df OAExec.Integrated.solution
            (z.1-OAExec.Integrated.solution)≤z.2
        rw [solution_tangent]
        change OAExec.Integrated.objective OAExec.Integrated.seed+
          OAExec.Integrated.Df OAExec.Integrated.seed (z.1-OAExec.Integrated.seed)≤z.2 at hf
        rwa [OAExec.Integrated.seed_objective_tangent] at hf

theorem noGoods_iff (p : P) : FP.noGoods s1 p ↔ p.2 0≠1 := by
  simp only [FP.noGoods,s1,s0,FP.append,FP.initialState,List.nil_append,List.mem_singleton,
    forall_eq,event,Option.some_ne_none,not_false_eq_true,true_implies]
  constructor
  · intro h he
    apply h (by simp)
    funext j
    fin_cases j
    simpa [FP.intCast,target1] using he
  · intro h _ he
    apply h
    simpa [FP.intCast,target1] using congrFun he 0

theorem normals (p : P) : FP.retainedNormals s1 p ∧ FP.handoffNormals s1 p := by
  constructor
  · simp [FP.retainedNormals,s1,s0,event,FP.append,FP.initialState]
  · intro i hi _
    fin_cases i
    simp [s1,s0,event,FP.append,FP.initialState] at hi

theorem handoff_iff (delta : ℝ) (z : P×ℝ) : z∈FP.handoff (pump delta) s1 ↔
    z∈OAExec.master I OAExec.Integrated.seed [] ∧ z.1.2 0=0 := by
  change (z∈FP.epigraph (pump delta) s1 ∧ FP.handoffNormals s1 z.1 ∧ FP.noGoods s1 z.1) ↔ _
  rw [epigraph_eq,noGoods_iff]
  have he : z∈OAExec.epigraph I OAExec.Integrated.seed [] ↔
      z∈OAExec.master I OAExec.Integrated.seed [] := by
    simp [OAExec.master,OAExec.noGoods]
  rw [he]
  constructor
  · rintro ⟨hm,_,hn⟩
    exact ⟨hm,((OAExec.Integrated.master_empty_iff z).mp hm).2.1.resolve_right hn⟩
  · rintro ⟨hm,hy⟩
    exact ⟨hm,(normals z.1).2,by rw [hy]; norm_num⟩

theorem level (delta : ℝ) : (pump delta).level s1.incumbent=some (5/4-delta*(5/4)) := by
  norm_num [pump,asFPDelta,OAExec.asFP,I,OAExec.Integrated.spec,OAExec.Integrated.objective,
    OAExec.Integrated.solution,pt,scalar,FP.Data.level,FP.cutoffValue,s1,s0,event,
    FP.append,FP.initialState,abs_div]

theorem master1_iff (delta : ℝ) (z : P×ℝ) : z∈FP.master (pump delta) s1 ↔
    z∈OAExec.master I OAExec.Integrated.seed [] ∧ z.1.2 0=0 ∧
      z.2≤5/4-delta*(5/4) := by
  have hh := handoff_iff delta z
  simp only [FP.handoff,Set.mem_setOf_eq] at hh
  simp only [FP.master,Set.mem_setOf_eq,level,FP.Allows]
  have hn := normals z.1
  tauto

theorem master1_minimum (delta : ℝ) (hd : delta≤1/4) :
    IsMinimizer (FP.master (pump delta) s1) (FP.masterCost s1) OAExec.Integrated.master0 := by
  refine ⟨(master1_iff delta _).mpr ⟨OAExec.Integrated.master0_minimum.1,rfl,?_⟩,?_⟩
  · change (15/16:ℝ)≤5/4-delta*(5/4)
    linarith
  · intro z hz
    have hy := ((master1_iff delta z).mp hz).2.1
    change FP.l1 OAExec.Integrated.solution OAExec.Integrated.master0.1≤
      FP.l1 OAExec.Integrated.solution z.1
    norm_num [FP.l1,Fin.sum_univ_one,OAExec.Integrated.solution,
      OAExec.Integrated.master0,pt,scalar,hy]

theorem master1_empty (delta : ℝ) (hd : 1/4<delta) :
    ¬ (FP.master (pump delta) s1).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨hm,_,hc⟩ := (master1_iff delta z).mp hz
  have hb := OAExec.Integrated.master0_minimum.2 z hm
  change (15/16:ℝ)≤z.2 at hb
  linarith

end Chapter03.PumpOA.IntegratedWarm

#print axioms Chapter03.PumpOA.IntegratedWarm.reply
#print axioms Chapter03.PumpOA.IntegratedWarm.handoff_iff
#print axioms Chapter03.PumpOA.IntegratedWarm.master1_minimum
#print axioms Chapter03.PumpOA.IntegratedWarm.master1_empty
