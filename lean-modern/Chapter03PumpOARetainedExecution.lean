module

public import Chapter03PumpOARetainedGeometry
public import Chapter03PumpOACounts

@[expose] public section

/-! Selected actual pump choices, followed by EVERY admissible zero-tolerance
OA suffix. The failed event precedes success, so its nontrivial normal survives.
The success no-good and retained normal make the residual master empty. The
unchanged composed procedure returns the saved original minimizer. This does
not assert uniqueness of all pump choices or irredundancy of the normal. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.PumpOA.Retained

theorem states_distinct : s0≠s1 ∧ s0≠s2 ∧ s1≠s2 := by
  repeat' constructor
  all_goals intro h
  all_goals have hh := congrArg (fun s : FP.State 1 1 => s.history.length) h
  all_goals norm_num [s2,s1,s0,FP.append,FP.initialState] at hh

def choose : FP.Selector pump none := fun s => by
  classical
  exact if h0 : s=s0 then h0.symm ▸ .next e0
      ⟨master0,master0_minimum,by simp [FP.BeforeCap],reply0⟩
    else if h1 : s=s1 then h1.symm ▸ .next e1
      ⟨master1,master1_minimum,by simp [FP.BeforeCap],reply1⟩
    else if h2 : s=s2 then h2.symm ▸ .stop .emptyMaster (.emptyMaster master2_empty)
    else Classical.choice (FP.decision_nonempty pump pump_analytic none s)

def output : FP.LoopOutput 1 1 := ⟨s2,.emptyMaster,2,2,3,1⟩
def initialization : FP.Initialization pump := .minimum seed seed_minimum

theorem actual_run : FP.run pump choose 3 s0=some output := by
  rcases states_distinct with ⟨h01,h02,h12⟩
  simp [FP.run,choose,h01,h02,h12,Ne.symm h01,Ne.symm h02,Ne.symm h12,
    show FP.append s0 e0=s1 from rfl,show FP.append s1 e1=s2 from rfl,
    FP.terminalOutput,FP.LoopOutput.bump,FP.terminalProjectionCount,
    show FP.polishCount e0=0 from rfl,show FP.polishCount e1=1 from rfl,output]

theorem actual_procedure : FP.procedure pump initialization choose=some (.loop output) := by
  have hb : pump.box.card=2 := box_card
  simp only [FP.procedure,initialization,if_neg seed_not_original,hb]
  exact congrArg (Option.map FP.Outcome.loop) actual_run

theorem combined_empty (H : List (OAExec.Event spec)) : master spec 0 s2 H=∅ := by
  change FP.handoff pump s2 ∩ OAExec.master spec s2.seed H=∅
  rw [handoff_empty]
  simp

/-- Every admissible suffix selector reaches the incumbent-aware empty branch.
This quantifier does not range over alternate pump histories. -/
theorem every_suffix (chooseOA : Selector spec 0 s2 0) (fuel : ℕ) :
    runFuel spec 0 s2 0 chooseOA (fuel+1) (initialState spec s2) .initial=
      some ⟨.solution solution,1,0,0⟩ := by
  have ho : OAExec.loopOpen spec 0 (initialState spec s2) := by
    simp only [OAExec.loopOpen,initialState,show s2.incumbent=some solution from rfl,
      Option.some.injEq,forall_eq']
    norm_num [spec,s2,s1,s0,e0,e1,FP.append,FP.initialState,objective,seed,
      solution,OAExec.Integrated.solution,pt,scalar]
  cases hc : chooseOA (initialState spec s2) .initial ho with
  | empty he =>
    simpa only [emptyResult,initialState,show s2.incumbent=some solution from rfl] using
      runFuel_empty spec 0 s2 0 chooseOA fuel (initialState spec s2) .initial ho he hc
  | next q e hv hy =>
    have hm := q.mem
    rw [combined_empty] at hm
    exact hm.elim

theorem composed_saved (chooseOA : Selectors spec 0 0) :
    execute source_package 0 (le_refl 0) 0 none initialization choose chooseOA=
      some ⟨⟨1,2,2,3,1⟩,⟨.solution solution,1,0,0⟩⟩ := by
  rw [execute_of_loop source_package 0 (le_refl 0) 0 none initialization choose chooseOA
    actual_procedure]
  simp only [output,box_card]
  rw [every_suffix]
  rfl

/-- Full source endpoint instantiated with the actual selected pump execution;
all legal suffix selectors return the displayed original optimum and counts. -/
theorem control_certificate : Nonempty (Selectors spec 0 0) ∧
    ∀ chooseOA : Selectors spec 0 0,
      execute source_package 0 (le_refl 0) 0 none initialization choose chooseOA=
        some ⟨⟨1,2,2,3,1⟩,⟨.solution solution,1,0,0⟩⟩ ∧
      OAExec.ReturnCertificate spec 0 (.solution solution) ∧
      CountBounds spec none ⟨⟨1,2,2,3,1⟩,⟨.solution solution,1,0,0⟩⟩ := by
  have h := qualified_source_pump_oa source_package 0 (le_refl 0) 0 (le_refl 0) none
  refine ⟨h.2.2.1,?_⟩
  intro chooseOA
  obtain ⟨out,he,hc,hb⟩ := h.2.2.2 initialization choose chooseOA
  rw [composed_saved chooseOA] at he
  cases Option.some.inj he
  exact ⟨composed_saved chooseOA,hc,hb⟩

theorem returned_original_minimum : IsMinimizer spec.original spec.f solution := by
  obtain ⟨chooseOA⟩ := control_certificate.1
  exact OAExec.zero_certificate_exact (control_certificate.2 chooseOA).2.1

end Chapter03.PumpOA.Retained
