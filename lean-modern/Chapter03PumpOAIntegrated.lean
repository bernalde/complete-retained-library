module

public import Chapter03PumpOATransfer
public import Chapter03PumpOARun
public import Chapter03OAExistenceIntegratedEndpoint

@[expose] public section

/-! Actual cap-zero pump inspection followed by a genuine new OA restoration.
The zero completed pump history is disclosed. The nonzero-dimensional full
source package and exact two-master/two-fixed/one-restoration suffix are reused
through proved master/choice identities, not an old return theorem. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.PumpOA.Integrated

abbrev I := OAExec.Integrated.spec
def pump : FP.Data 1 1 1 1 := asFPDelta I 0
def pumpState : FP.State 1 1 := FP.initialState OAExec.Integrated.seed

theorem full_assumptions : OAExec.AvailabilityAssumptions I :=
  OAExec.Integrated.source_package

theorem pump_analytic : FP.Analytic pump :=
  asFPDelta_analytic full_assumptions (le_refl 0)

theorem inspected_master_minimum : IsMinimizer (FP.master pump pumpState)
    (FP.masterCost pumpState) (OAExec.Integrated.solution,5/4) := by
  rw [show FP.master pump pumpState=OAExec.master I OAExec.Integrated.seed [] from
    pump_initial_master_eq I 0 OAExec.Integrated.seed]
  refine ⟨(OAExec.Integrated.master_empty_iff _).mpr
    (by norm_num [OAExec.Integrated.solution,pt,scalar]),?_⟩
  intro z hz
  have hy := ((OAExec.Integrated.master_empty_iff z).mp hz).2.1
  change FP.l1 OAExec.Integrated.seed OAExec.Integrated.solution≤
    FP.l1 OAExec.Integrated.seed z.1
  rcases hy with hy|hy <;>
    norm_num [FP.l1,Fin.sum_univ_one,OAExec.Integrated.seed,
      OAExec.Integrated.solution,pt,scalar,hy,abs_div]

def pumpChoose : FP.Selector pump (some 0) := fun s => by
  classical
  exact if h : s=pumpState then h.symm ▸ .stop .handoff
      (.handoff inspected_master_minimum rfl (by simp [pumpState,FP.initialState]))
    else Classical.choice (FP.decision_nonempty pump pump_analytic (some 0) s)

def pumpOutput : FP.LoopOutput 1 1 := ⟨pumpState,.handoff,0,0,1,0⟩
def initialization : FP.Initialization pump :=
  .minimum OAExec.Integrated.seed OAExec.Integrated.seed_minimum

theorem pump_procedure : FP.procedure pump initialization pumpChoose=
    some (.loop pumpOutput) := by
  have hn : OAExec.Integrated.seed∉pump.original := by
    intro hp
    obtain ⟨_,_,_,y,_,hy⟩ :=
      (source_feasible_iff OAExec.Integrated.model Set.univ OAExec.Integrated.seed).mp hp
    exact OAExec.Integrated.seed_valid.2.2 ⟨y,hy⟩
  have hb : pump.box.card=2 := OAExec.Integrated.box_card
  simp [FP.procedure,initialization,hn,hb,FP.run,pumpChoose,pumpState,
    FP.terminalOutput,FP.terminalProjectionCount,pumpOutput]

def oldChoice {s : OAExec.State I} (q : MasterChoice I 0 pumpState s) :
    OAExec.MasterChoice I OAExec.Integrated.seed s where
  point := q.point
  attained := q.attained
  valid := by simpa only [pumpState,initial_prefix_master_eq] using q.valid

theorem first_step {s : OAExec.State I} (hs : s=OAExec.Integrated.state0)
    (q : MasterChoice I 0 pumpState s) (e : OAExec.Event I)
    (he : OAExec.EventValid I e) (hy : q.point.1.2=intCast e.target) :
    e=OAExec.Integrated.event0 ∧ advance s q e=OAExec.Integrated.state1 :=
  OAExec.Integrated.first_step hs (oldChoice q) e he hy

theorem second_step {s : OAExec.State I} (hs : s=OAExec.Integrated.state1)
    (q : MasterChoice I 0 pumpState s) (e : OAExec.Event I)
    (he : OAExec.EventValid I e) (hy : q.point.1.2=intCast e.target) :
    e=OAExec.Integrated.event1 ∧ advance s q e=OAExec.Integrated.state2 :=
  OAExec.Integrated.second_step hs (oldChoice q) e he hy

/-- Every admissible new suffix selector performs the real restoration and
fixed solve, even at positive tolerance, before the delayed gap test. -/
theorem every_suffix (epsilon : ℝ) (heps : 0≤epsilon)
    (choose : Selector I 0 pumpState epsilon) :
    runFuel I 0 pumpState epsilon choose 3 (initialState I pumpState) .initial=
      some ⟨.solution OAExec.Integrated.solution,2,2,1⟩ := by
  have ho0 := OAExec.Integrated.state0_open epsilon
  cases hc0 : choose OAExec.Integrated.state0 .initial ho0 with
  | empty hempty =>
    change master I 0 pumpState []=∅ at hempty
    have hm : OAExec.Integrated.master0∈master I 0 pumpState [] := by
      rw [pumpState,initial_prefix_master_eq]
      exact OAExec.Integrated.master0_minimum.1
    rw [hempty] at hm
    exact hm.elim
  | next q0 e0 he0 hy0 =>
    obtain ⟨heq0,hs1⟩ := first_step rfl q0 e0 he0 hy0
    let s1 := advance OAExec.Integrated.state0 q0 e0
    have hr1 : Reachable I 0 pumpState epsilon s1 := .next .initial (.step ho0 q0 e0 he0 hy0)
    have ho1 : OAExec.loopOpen I epsilon s1 := by
      rw [show s1=OAExec.Integrated.state1 from hs1]
      exact OAExec.Integrated.state1_open epsilon
    cases hc1 : choose s1 hr1 ho1 with
    | empty hempty =>
      have hm : OAExec.Integrated.master1∈master I 0 pumpState s1.history := by
        rw [show s1=OAExec.Integrated.state1 from hs1,pumpState,initial_prefix_master_eq]
        exact OAExec.Integrated.master1_minimum.1
      rw [hempty] at hm
      exact hm.elim
    | next q1 e1 he1 hy1 =>
      obtain ⟨heq1,hs2⟩ := second_step hs1 q1 e1 he1 hy1
      let s2 := advance s1 q1 e1
      have hr2 : Reachable I 0 pumpState epsilon s2 := .next hr1 (.step ho1 q1 e1 he1 hy1)
      have hi : s2.incumbent=some OAExec.Integrated.solution := by
        rw [show s2=OAExec.Integrated.state2 from hs2]; rfl
      have ho2 : ¬ OAExec.loopOpen I epsilon s2 := by
        rw [show s2=OAExec.Integrated.state2 from hs2]
        exact OAExec.Integrated.state2_closed epsilon heps
      have ht2 := runFuel_closed I 0 pumpState epsilon choose 1 s2 hr2 ho2 hi
      have ht1 := runFuel_next I 0 pumpState epsilon choose 1 s1 hr1 ho1 q1 e1 he1 hy1 hc1
      rw [ht2] at ht1
      have ht0 := runFuel_next I 0 pumpState epsilon choose 2 OAExec.Integrated.state0
        .initial ho0 q0 e0 he0 hy0 hc0
      rw [ht1] at ht0
      simpa only [OAExec.Integrated.state0,OAExec.initialState,initialState,pumpState,FP.initialState,
        heq0,heq1,Option.map_some,OAExec.countStep,OAExec.eventRestorations,
        OAExec.Integrated.event0,OAExec.Integrated.event1,Option.some_ne_none,
        ↓reduceIte,Nat.zero_add,Nat.add_zero] using ht0

end Chapter03.PumpOA.Integrated

#print axioms Chapter03.PumpOA.Integrated.full_assumptions
#print axioms Chapter03.PumpOA.Integrated.pump_procedure
#print axioms Chapter03.PumpOA.Integrated.every_suffix
