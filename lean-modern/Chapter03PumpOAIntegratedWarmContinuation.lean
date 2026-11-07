module

public import Chapter03PumpOAIntegratedWarmPump

@[expose] public section

/-! Every admitted continuation selector first restores the remaining empty
fiber, then returns the saved pump incumbent from an empty residual master. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.PumpOA.IntegratedWarm

def state0 : OAExec.State I := initialState I s1
def state1 : OAExec.State I :=
  ⟨[OAExec.Integrated.event0],some OAExec.Integrated.solution,15/16⟩

theorem combined0_iff (delta : ℝ) (z : P×ℝ) : z∈master I delta s1 [] ↔
    z∈OAExec.master I OAExec.Integrated.seed [] ∧ z.1.2 0=0 := by
  rw [empty_suffix_master_eq]
  exact handoff_iff delta z

theorem combined0_minimum (delta : ℝ) :
    IsMinimizer (master I delta s1 []) Prod.snd OAExec.Integrated.master0 :=
  ⟨(combined0_iff delta _).mpr ⟨OAExec.Integrated.master0_minimum.1,rfl⟩,
    fun z hz => OAExec.Integrated.master0_minimum.2 z ((combined0_iff delta z).mp hz).1⟩

theorem choice0_unique (delta : ℝ) (q : MasterChoice I delta s1 state0) :
    q.point=OAExec.Integrated.master0 ∧ q.nextLower=15/16 := by
  have hm := combined0_minimum delta
  have hb : BddBelow (Prod.snd '' master I delta s1 state0.history) := by
    refine ⟨15/16,?_⟩
    rintro a ⟨z,hz,rfl⟩
    exact hm.2 z hz
  have hv := q.valid
  cases ha : q.attained
  · simp only [ha,Bool.false_eq_true,↓reduceIte] at hv
    exact (hv.2 hb).elim
  · simp only [ha,↓reduceIte] at hv
    have hq : IsMinimizer (OAExec.master I OAExec.Integrated.seed []) Prod.snd q.point := by
      refine ⟨((combined0_iff delta q.point).mp hv.1).1,?_⟩
      intro z hz
      exact (hv.2 OAExec.Integrated.master0 hm.1).trans (OAExec.Integrated.master0_minimum.2 z hz)
    have hp := OAExec.Integrated.master0_unique hq
    exact ⟨hp,by simp [MasterChoice.nextLower,ha,hp,OAExec.Integrated.master0]⟩

theorem first_step (delta : ℝ) (q : MasterChoice I delta s1 state0)
    (e : OAExec.Event I) (he : OAExec.EventValid I e) (hy : q.point.1.2=intCast e.target) :
    e=OAExec.Integrated.event0 ∧ advance state0 q e=state1 := by
  obtain ⟨hp,hl⟩ := choice0_unique delta q
  have ht : intCast e.target 0=0 := by
    have hh := congrFun hy 0
    rw [hp] at hh
    exact hh.symm
  have heq := OAExec.Integrated.event_of_y0 he ht
  refine ⟨heq,?_⟩
  rw [heq]
  simp [advance,hl,state0,state1,initialState,s1,s0,event,FP.append,FP.initialState,
    OAExec.nextIncumbent,OAExec.Integrated.event0]
  exact hl

theorem combined1_empty (delta : ℝ) : master I delta s1 [OAExec.Integrated.event0]=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hy0 := ((handoff_iff delta z).mp hz.1).2
  have hy1 := ((OAExec.Integrated.master_after0_iff z).mp hz.2).2.1
  linarith

theorem state0_open (epsilon : ℝ) (heps : epsilon<5/16) : OAExec.loopOpen I epsilon state0 := by
  norm_num [OAExec.loopOpen,state0,initialState,s1,s0,event,FP.append,FP.initialState,
    I,OAExec.Integrated.spec,OAExec.Integrated.objective,OAExec.Integrated.seed,
    OAExec.Integrated.solution,pt,scalar]
  linarith

theorem state1_open (epsilon : ℝ) (heps : epsilon<5/16) : OAExec.loopOpen I epsilon state1 := by
  norm_num [OAExec.loopOpen,state1,I,OAExec.Integrated.spec,OAExec.Integrated.objective,
    OAExec.Integrated.solution,pt,scalar]
  exact heps

theorem state0_closed (epsilon : ℝ) (heps : 5/16≤epsilon) : ¬ OAExec.loopOpen I epsilon state0 := by
  norm_num [OAExec.loopOpen,state0,initialState,s1,s0,event,FP.append,FP.initialState,
    I,OAExec.Integrated.spec,OAExec.Integrated.objective,OAExec.Integrated.seed,
    OAExec.Integrated.solution,pt,scalar]
  exact heps

theorem every_suffix (delta epsilon : ℝ) (heps : epsilon<5/16)
    (chooseOA : Selector I delta s1 epsilon) :
    runFuel I delta s1 epsilon chooseOA 3 state0 .initial=
      some ⟨.solution OAExec.Integrated.solution,2,1,1⟩ := by
  have ho0 := state0_open epsilon heps
  cases hc0 : chooseOA state0 .initial ho0 with
  | empty hempty =>
    have hm := (combined0_minimum delta).1
    change master I delta s1 []=∅ at hempty
    rw [hempty] at hm
    exact hm.elim
  | next q e hv hy =>
    obtain ⟨heq,hstate⟩ := first_step delta q e hv hy
    let next := advance state0 q e
    have hr : Reachable I delta s1 epsilon next := .next .initial (.step ho0 q e hv hy)
    have ho : OAExec.loopOpen I epsilon next := by
      rw [show next=state1 from hstate]
      exact state1_open epsilon heps
    have hempty : master I delta s1 next.history=∅ := by
      rw [show next=state1 from hstate]
      exact combined1_empty delta
    have hi : next.incumbent=some OAExec.Integrated.solution := by
      rw [show next=state1 from hstate]
      rfl
    cases hc1 : chooseOA next hr ho with
    | empty he =>
      have ht1 := runFuel_empty I delta s1 epsilon chooseOA 1 next hr ho he hc1
      have ht0 := runFuel_next I delta s1 epsilon chooseOA 2 state0 .initial ho0 q e hv hy hc0
      rw [ht1] at ht0
      simpa only [emptyResult,hi,heq,Option.map_some,OAExec.countStep,
        OAExec.eventRestorations,OAExec.Integrated.event0,Option.some_ne_none,
        ↓reduceIte,Nat.zero_add,Nat.add_zero] using ht0
    | next q1 e1 he1 hy1 =>
      have hm := q1.mem
      rw [hempty] at hm
      exact hm.elim

theorem every_closed_suffix (delta epsilon : ℝ) (heps : 5/16≤epsilon)
    (chooseOA : Selector I delta s1 epsilon) :
    runFuel I delta s1 epsilon chooseOA 3 state0 .initial=
      some ⟨.solution OAExec.Integrated.solution,0,0,0⟩ :=
  runFuel_closed I delta s1 epsilon chooseOA 3 state0 .initial
    (state0_closed epsilon heps) rfl

end Chapter03.PumpOA.IntegratedWarm

#print axioms Chapter03.PumpOA.IntegratedWarm.every_suffix
#print axioms Chapter03.PumpOA.IntegratedWarm.every_closed_suffix
