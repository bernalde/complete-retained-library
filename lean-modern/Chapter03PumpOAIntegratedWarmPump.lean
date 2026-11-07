module

public import Chapter03PumpOAIntegratedWarmGeometry

@[expose] public section

/-! A selected actual cap-one pump run, including both cutoff-dependent stops.
The first projection is deliberately selected at x=1/2, y=1. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA.IntegratedWarm

theorem states_distinct : s0≠s1 := by
  intro he
  have hh := congrArg (fun s : FP.State 1 1 => s.history.length) he
  norm_num [s0,s1,FP.append,FP.initialState] at hh

def choose (delta : ℝ) (hd : 0≤delta) : FP.Selector (pump delta) (some 1) := fun s => by
  classical
  exact if h0 : s=s0 then h0.symm ▸ .next event
      ⟨(OAExec.Integrated.solution,5/4),master0_minimum delta,
        by simp [FP.BeforeCap,s0,FP.initialState],reply delta⟩
    else if h1 : s=s1 then h1.symm ▸
      (if hs : delta≤1/4 then .stop .handoff
        (.handoff (master1_minimum delta hs) rfl (by simp [s1,s0,FP.append,FP.initialState]))
      else .stop .emptyMaster (.emptyMaster (master1_empty delta (lt_of_not_ge hs))))
    else Classical.choice (FP.decision_nonempty (pump delta)
      (asFPDelta_analytic full_assumptions hd) (some 1) s)

def stopReason (delta : ℝ) : FP.StopReason 1 :=
  if delta≤1/4 then .handoff else .emptyMaster

def output (delta : ℝ) : FP.LoopOutput 1 1 := ⟨s1,stopReason delta,1,1,2,1⟩
def initialization (delta : ℝ) : FP.Initialization (pump delta) :=
  .minimum OAExec.Integrated.seed OAExec.Integrated.seed_minimum

theorem actual_run (delta : ℝ) (hd : 0≤delta) :
    FP.run (pump delta) (choose delta hd) 3 s0=some (output delta) := by
  by_cases hs : delta≤1/4
  all_goals simp only [one_div] at hs
  all_goals simp [FP.run,choose,states_distinct,Ne.symm states_distinct,hs,
    show FP.append s0 event=s1 from rfl,FP.terminalOutput,FP.terminalProjectionCount,
    FP.LoopOutput.bump,show FP.polishCount event=1 from rfl,output,stopReason]

theorem seed_not_original (delta : ℝ) : OAExec.Integrated.seed∉(pump delta).original := by
  intro hp
  obtain ⟨_,_,_,y,_,hy⟩ :=
    (source_feasible_iff OAExec.Integrated.model Set.univ OAExec.Integrated.seed).mp hp
  exact OAExec.Integrated.seed_valid.2.2 ⟨y,hy⟩

theorem actual_procedure (delta : ℝ) (hd : 0≤delta) :
    FP.procedure (pump delta) (initialization delta) (choose delta hd)=
      some (.loop (output delta)) := by
  have hb : (pump delta).box.card=2 := OAExec.Integrated.box_card
  simp only [FP.procedure,initialization,if_neg (seed_not_original delta),hb]
  exact congrArg (Option.map FP.Outcome.loop) (actual_run delta hd)

theorem cap_stop (delta : ℝ) (hd : 0≤delta) (hs : delta≤1/4) :
    FP.procedure (pump delta) (initialization delta) (choose delta hd)=
      some (.loop ⟨s1,.handoff,1,1,2,1⟩) := by
  simpa only [output,stopReason,if_pos hs] using actual_procedure delta hd

theorem empty_stop (delta : ℝ) (hd : 0≤delta) (hs : 1/4<delta) :
    FP.procedure (pump delta) (initialization delta) (choose delta hd)=
      some (.loop ⟨s1,.emptyMaster,1,1,2,1⟩) := by
  simpa only [output,stopReason,if_neg (not_le.mpr hs)] using actual_procedure delta hd

theorem history_preserved : s1.history=[event] ∧
    s1.incumbent=some OAExec.Integrated.solution ∧ s1.lastSuccess=some 0 ∧
    event.projection=OAExec.Integrated.solution ∧
    event.success=some (OAExec.Integrated.solution,OAExec.Integrated.solution) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

end Chapter03.PumpOA.IntegratedWarm

#print axioms Chapter03.PumpOA.IntegratedWarm.cap_stop
#print axioms Chapter03.PumpOA.IntegratedWarm.empty_stop
#print axioms Chapter03.PumpOA.IntegratedWarm.history_preserved
