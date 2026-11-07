module

public import Chapter03PumpOAC2Masters
public import Chapter03PumpOAComposition

@[expose] public section

/-! C2's unchanged cap-two pump history is consumed by three actual new fixed
solves. The discarded late normal had excluded the returned strict improver.
This selected exact suffix complements the universal main theorem. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.FPTrace
namespace Chapter03.PumpOA.C2

def state0 : OAExec.State spec := initialState spec C2.s2
def state1 : OAExec.State spec := ⟨[eventOne],some C2.one,0⟩
def state2 : OAExec.State spec := ⟨[eventOne,eventOther],some C2.one,4/81⟩
def state3 : OAExec.State spec := ⟨[eventOne,eventOther,eventOne],some C2.one,10/81⟩

def choice0 : MasterChoice spec (37/81) C2.s2 state0 := ⟨(C2.one,0),true,master0_minimum⟩
def choice1 : MasterChoice spec (37/81) C2.s2 state1 := ⟨(C2.other,4/81),true,master1_minimum⟩
def choice2 : MasterChoice spec (37/81) C2.s2 state2 := ⟨(C2.one,10/81),true,master2_minimum⟩

theorem same_one : C2.one.2=intCast eventOne.target := by
  rw [← eventOne_anchor]
  rfl
theorem same_other : C2.other.2=intCast eventOther.target := by
  rw [← eventOther_anchor]
  rfl

theorem advance0 : advance state0 choice0 eventOne=state1 := by
  norm_num [advance,state0,initialState,state1,OAExec.nextIncumbent,OAExec.keepBest,
    choice0,MasterChoice.nextLower,eventOne_anchor,eventOne,OAExec.Event.anchor,
    C2.s2,C2.s1,C2.s0,FP.append,FP.initialState,C2.e0,C2.e1,
    spec,C2.d,C2.data,C2.q,C2.Dq,C2.zero,C2.one,C2.pt,intCast,corner]
  funext j
  fin_cases j <;> norm_num [FP.intCast,Chapter03.OAKKT.intCast]

theorem advance1 : advance state1 choice1 eventOther=state2 := by
  norm_num [advance,state1,state2,OAExec.nextIncumbent,OAExec.keepBest,
    choice1,MasterChoice.nextLower,eventOther_anchor,eventOther,OAExec.Event.anchor,
    spec,C2.d,C2.data,C2.q,C2.Dq,C2.one,C2.other,C2.pt,intCast,corner]

theorem advance2 : advance state2 choice2 eventOne=state3 := by
  norm_num [advance,state2,state3,OAExec.nextIncumbent,OAExec.keepBest,
    choice2,MasterChoice.nextLower,eventOne_anchor,eventOne,OAExec.Event.anchor,
    spec,C2.d,C2.data,C2.q,C2.Dq,C2.one,C2.pt,intCast,corner]

theorem open0 : OAExec.loopOpen spec 0 state0 := by
  norm_num [OAExec.loopOpen,state0,initialState,C2.s2,C2.s1,C2.s0,FP.append,
    FP.initialState,C2.e0,C2.e1,spec,C2.d,C2.data,C2.q,C2.zero,C2.seed,C2.pt]
theorem open1 : OAExec.loopOpen spec 0 state1 := by
  norm_num [OAExec.loopOpen,state1,spec,C2.d,C2.data,C2.q,C2.one,C2.pt]
theorem open2 : OAExec.loopOpen spec 0 state2 := by
  norm_num [OAExec.loopOpen,state2,spec,C2.d,C2.data,C2.q,C2.one,C2.pt]
theorem closed3 : ¬ OAExec.loopOpen spec 0 state3 := by
  norm_num [OAExec.loopOpen,state3,spec,C2.d,C2.data,C2.q,C2.one,C2.pt]

theorem states_distinct : state0≠state1 ∧ state0≠state2 ∧ state1≠state2 := by
  repeat' constructor
  all_goals intro h
  all_goals have hh := congrArg (fun s : OAExec.State spec => s.history.length) h
  all_goals norm_num [state0,state1,state2,initialState] at hh

def choose : Selector spec (37/81) C2.s2 0 := fun s hs ho => by
  classical
  exact if h0 : s=state0 then h0.symm ▸ .next choice0 eventOne eventOne_valid same_one
    else if h1 : s=state1 then h1.symm ▸ .next choice1 eventOther eventOther_valid same_other
    else if h2 : s=state2 then h2.symm ▸ .next choice2 eventOne eventOne_valid same_one
    else (Classical.choice (selector_inhabited (local_available source_package (37/81)
      C2.s2 seed_valid 0))) s hs ho

theorem actual_suffix : runFuel spec (37/81) C2.s2 0 choose 5 state0 .initial=
    some ⟨.solution C2.one,3,3,0⟩ := by
  rcases states_distinct with ⟨h01,h02,h12⟩
  have hc0 : choose state0 .initial open0=.next choice0 eventOne eventOne_valid same_one := by
    simp [choose]
  have hr1 : Reachable spec (37/81) C2.s2 0 state1 := by
    rw [← advance0]
    exact .next .initial (.step open0 choice0 eventOne eventOne_valid same_one)
  have hc1 : choose state1 hr1 open1=.next choice1 eventOther eventOther_valid same_other := by
    simp [choose,Ne.symm h01]
  have hr2 : Reachable spec (37/81) C2.s2 0 state2 := by
    rw [← advance1]
    exact .next hr1 (.step open1 choice1 eventOther eventOther_valid same_other)
  have hc2 : choose state2 hr2 open2=.next choice2 eventOne eventOne_valid same_one := by
    simp [choose,Ne.symm h02,Ne.symm h12]
  have hr3 : Reachable spec (37/81) C2.s2 0 state3 := by
    rw [← advance2]
    exact .next hr2 (.step open2 choice2 eventOne eventOne_valid same_one)
  have ht3 := runFuel_closed spec (37/81) C2.s2 0 choose 2 state3 hr3 closed3
    (show state3.incumbent=some C2.one from rfl)
  have ht2 := runFuel_next spec (37/81) C2.s2 0 choose 2 state2 hr2 open2
    choice2 eventOne eventOne_valid same_one hc2
  simp only [advance2] at ht2
  rw [ht3] at ht2
  have ht1 := runFuel_next spec (37/81) C2.s2 0 choose 3 state1 hr1 open1
    choice1 eventOther eventOther_valid same_other hc1
  simp only [advance1] at ht1
  rw [ht2] at ht1
  have ht0 := runFuel_next spec (37/81) C2.s2 0 choose 4 state0 .initial open0
    choice0 eventOne eventOne_valid same_one hc0
  simp only [advance0] at ht0
  rw [ht1] at ht0
  simpa [Option.map_some,OAExec.countStep,OAExec.eventRestorations,eventOne,eventOther] using ht0

def chooseOA : Selectors spec (37/81) 0 := fun P hs => by
  classical
  by_cases h : P=C2.s2
  · subst P; exact choose
  · exact Classical.choice (selector_inhabited (local_available source_package (37/81) P hs 0))

theorem chooseOA_here (hs : OAExec.SeedValid spec C2.s2.seed) :
    chooseOA C2.s2 hs=choose := by simp [chooseOA]

def pumpInitialization : FP.Initialization (asFPDelta spec (37/81)) :=
  adapter_exact.symm ▸ C2.initialization
def pumpChoose : FP.Selector (asFPDelta spec (37/81)) (some 2) :=
  adapter_exact.symm ▸ C2.chooseCapTwo

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem composed_execution : execute source_package (37/81) (by norm_num) 0 (some 2)
    pumpInitialization pumpChoose chooseOA=
      some ⟨⟨1,2,2,3,1⟩,⟨.solution C2.one,3,3,0⟩⟩ := by
  rw [execute_of_loop source_package (37/81) (by norm_num) 0 (some 2)
    pumpInitialization pumpChoose chooseOA capTwo_procedure_exact]
  have hb : spec.box.card=4 := C2.box_card 1 0 (37/81)
  simp only [C2.capTwoOutput,hb,chooseOA_here]
  have ht := actual_suffix
  change runFuel spec (37/81) C2.s2 0 choose 5 (initialState spec C2.s2) .initial = _ at ht
  rw [ht]
  rfl

theorem actual_filtered_improvement :
    FP.procedure (asFPDelta spec (37/81)) pumpInitialization pumpChoose=
        some (.loop C2.capTwoOutput) ∧
    ¬ FP.retainedNormals C2.s2 C2.one ∧
    (C2.one,spec.f C2.one)∈FP.handoff (asFPDelta spec (37/81)) C2.s2 ∧
    spec.f C2.one<spec.f C2.zero ∧
    execute source_package (37/81) (by norm_num) 0 (some 2)
      pumpInitialization pumpChoose chooseOA=
        some ⟨⟨1,2,2,3,1⟩,⟨.solution C2.one,3,3,0⟩⟩ := by
  refine ⟨capTwo_procedure_exact,C2.late_normal_excludes_better.2,?_,
    C2.unsafe_transfer_witness.2.1,composed_execution⟩
  rw [adapter_exact]
  exact C2.unsafe_transfer_witness.2.2.2

end Chapter03.PumpOA.C2

#print axioms Chapter03.PumpOA.C2.actual_suffix
#print axioms Chapter03.PumpOA.C2.composed_execution
#print axioms Chapter03.PumpOA.C2.actual_filtered_improvement
