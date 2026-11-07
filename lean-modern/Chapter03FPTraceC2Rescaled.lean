module

public import Chapter03FPTraceC2Runs

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C2

def rD : Data 0 2 0 0 := data 10 (-370/81) 2
def rE1 : Event 0 2 := ⟨corner 0 1,one,some (-2),some (one,one)⟩
def rS2 : State 0 2 := append s1 rE1

theorem r_analytic : Analytic rD := analytic _ _ _ (by norm_num) (by norm_num)
theorem r_values : rD.f zero=0 ∧ rD.f one= -10/3 ∧ rD.delta=2 := by
  norm_num [rD,data,q,zero,one,pt]
theorem r_level1 : rD.level s1.incumbent=some (-2) := by
  norm_num [rD,data,Data.level,s1,s0,e0,append,initialState,cutoffValue,q,zero,pt,abs_div,max_def]
theorem r_level2 : rD.level rS2.incumbent=some (-10) := by
  norm_num [rD,data,Data.level,rS2,rE1,append,cutoffValue,q,one,pt,abs_div,max_def]

theorem r_master1_mem : (one,-2) ∈ master rD s1 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨(fun row => Fin.elim0 row),⟨corner 0 1,?_,?_⟩,(fun i j => Fin.elim0 j),?_,?_,?_,?_⟩
  · norm_num [IntegerBox,rD,data,model,corner,Fin.forall_fin_two]
  · simpa [one] using point_cast 0 1
  · intro i
    fin_cases i <;>
      norm_num [family,anchors,s1,s0,append,initialState,e0,Event.anchor,rD,data,q,Dq,seed,zero,one,pt]
  · simp [retainedNormals,s1,s0,append,initialState,e0]
  · simp [noGoods,s1,s0,append,initialState,e0,one,intCast,corner,pt,funext_iff,Fin.forall_fin_two]
  · rw [r_level1]; exact le_rfl

theorem r_master1_min : IsMinimizer (master rD s1) (masterCost s1) (one,-2) := by
  refine ⟨r_master1_mem,?_⟩
  intro z hz
  have hn := hz.2.2.1 e0 (by simp [s1,s0,append,initialState]) (by simp [e0])
  change l1 zero one ≤ l1 zero z.1
  rcases master_point_cases 10 (-370/81) 2 s1 hz with h|h|h|h
  · exact False.elim (hn (by rw [h];simpa [zero,e0] using point_cast 0 0))
  all_goals rw [h]
  all_goals norm_num [l1_two,zero,one,other,both,pt]

theorem r_reply1 : EventReply rD s1 (one,-2) rE1 := by
  refine ⟨by simpa [one,rE1] using point_cast 0 1,r_level1.symm,?_,?_⟩
  · rw [r_level1]
    simpa [one,rD,rE1] using integer_projection_min 10 (-370/81) 2 (some (-2)) 0 1 (by
      refine ⟨(relaxation_iff _ _ _ _).mpr (by norm_num [pt]),?_⟩
      norm_num [Allows,data,q,pt])
  · refine ⟨by norm_num [rE1,distance_two,corner,one,pt],?_,?_⟩
    · simpa [one,rD,rE1] using integer_fiber_min 10 (-370/81) 2 0 1
        ((relaxation_iff _ _ _ _).mpr (by norm_num [pt]))
    · refine ⟨Or.inr rfl,?_⟩
      norm_num [s1,s0,append,initialState,e0,rE1,rD,data,q,zero,one,pt]

theorem r_master2_empty : ¬(master rD rS2).Nonempty := by
  rintro ⟨z,hz⟩
  have hb := ((FPAdapters.master_source_rows_iff _ _ _).mp hz).2.2.2.1 ⟨0,by decide⟩
  have hc := hz.2.2.2
  rw [r_level2] at hc
  have hl : (-370/81:ℝ) ≤ z.2 := by
    norm_num [family,anchors,rS2,s1,s0,append,initialState,rE1,e0,Event.anchor,rD,data,q,Dq,seed,pt] at hb
    linarith [hb]
  change z.2 ≤ -10 at hc
  linarith

def chooseRescaled : Selector rD none := fun s => by
  classical
  exact if h0 : s=s0 then h0.symm ▸ .next e0 ⟨(zero,-370/81),master0_min 10 (-370/81) 2,by simp [BeforeCap],reply0 10 (-370/81) 2⟩
    else if h1 : s=s1 then h1.symm ▸ .next rE1 ⟨(one,-2),r_master1_min,by simp [BeforeCap],r_reply1⟩
    else if h2 : s=rS2 then h2.symm ▸ .stop .emptyMaster (.emptyMaster r_master2_empty)
    else Classical.choice (decision_nonempty rD r_analytic none s)

def rescaledOutput : LoopOutput 0 2 := ⟨rS2,.emptyMaster,2,2,3,2⟩

theorem rescaled_run : run rD chooseRescaled 5 s0=some rescaledOutput := by
  have h10 : s1 ≠ s0 := states_distinct.1.symm
  have h20 : rS2 ≠ s0 := by
    intro h;have he := congrArg (fun s : State 0 2 => s.history.length) h
    norm_num [rS2,s1,s0,append,initialState] at he
  have h21 : rS2 ≠ s1 := by
    intro h;have he := congrArg (fun s : State 0 2 => s.history.length) h
    norm_num [rS2,s1,s0,append,initialState] at he
  simp [run,chooseRescaled,h10,h20,h21,show append s0 e0=s1 from rfl,
    show append s1 rE1=rS2 from rfl,terminalOutput,LoopOutput.bump,terminalProjectionCount,
    show polishCount e0=1 from rfl,show polishCount rE1=1 from rfl,rescaledOutput]

def r_initialization : Initialization rD := .minimum seed (seed_minimizer 10 (-370/81) 2 (by norm_num))
theorem rescaled_procedure : procedure rD r_initialization chooseRescaled=some (.loop rescaledOutput) := by
  simp only [procedure,r_initialization,if_neg (show seed ∉ rD.original from seed_not_original 10 (-370/81) 2),show rD.box.card=4 from box_card _ _ _]
  exact congrArg (Option.map Outcome.loop) rescaled_run

theorem rescaled_saved_state : rS2.incumbent=some one ∧ rS2.reference=one ∧
    rS2.lastSuccess=some 1 := ⟨rfl,rfl,rfl⟩

end Chapter03.FPTrace.C2
