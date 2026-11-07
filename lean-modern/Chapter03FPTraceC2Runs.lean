module

public import Chapter03FPTraceC2Geometry

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C2

theorem states_distinct : s0 ≠ s1 ∧ s0 ≠ s2 ∧ s0 ≠ s3 ∧ s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3 := by
  have lengths : s0.history.length=0 ∧ s1.history.length=1 ∧ s2.history.length=2 ∧ s3.history.length=3 := by
    norm_num [s0,s1,s2,s3,append,initialState]
  rcases lengths with ⟨h0,h1,h2,h3⟩
  repeat' constructor
  all_goals intro h
  all_goals have he := congrArg (fun s : State 0 2 => s.history.length) h
  all_goals norm_num [s0,s1,s2,s3,append,initialState] at he

def chooseUnlimited : Selector d none := fun s => by
  classical
  exact if h0 : s=s0 then h0.symm ▸ .next e0 ⟨(zero,0),master0_min 1 0 (37/81),by simp [BeforeCap],reply0 1 0 (37/81)⟩
    else if h1 : s=s1 then h1.symm ▸ .next e1 ⟨(one,0),master1_min,by simp [BeforeCap],reply1⟩
    else if h2 : s=s2 then h2.symm ▸ .next e2 ⟨(other,0),master2_min,by simp [BeforeCap],reply2⟩
    else if h3 : s=s3 then h3.symm ▸ .stop .emptyMaster (.emptyMaster master3_empty)
    else Classical.choice (decision_nonempty d d_analytic none s)

def chooseCapTwo : Selector d (some 2) := fun s => by
  classical
  exact if h0 : s=s0 then h0.symm ▸ .next e0 ⟨(zero,0),master0_min 1 0 (37/81),by simp [BeforeCap,s0,initialState],reply0 1 0 (37/81)⟩
    else if h1 : s=s1 then h1.symm ▸ .next e1 ⟨(one,0),master1_min,by simp [BeforeCap,s1,s0,append,initialState],reply1⟩
    else if h2 : s=s2 then h2.symm ▸ .stop .handoff (.handoff master2_min rfl (by simp [s2,s1,s0,append,initialState]))
    else Classical.choice (decision_nonempty d d_analytic (some 2) s)

def unlimitedOutput : LoopOutput 0 2 := ⟨s3,.emptyMaster,3,3,4,1⟩
def capTwoOutput : LoopOutput 0 2 := ⟨s2,.handoff,2,2,3,1⟩

theorem unlimited_run : run d chooseUnlimited 5 s0=some unlimitedOutput := by
  rcases states_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  simp [run,chooseUnlimited,h01,h02,h03,h12,h13,h23,Ne.symm h01,Ne.symm h02,Ne.symm h03,
    Ne.symm h12,Ne.symm h13,Ne.symm h23,show append s0 e0=s1 from rfl,show append s1 e1=s2 from rfl,show append s2 e2=s3 from rfl,terminalOutput,LoopOutput.bump,
    terminalProjectionCount,show polishCount e0=1 from rfl,show polishCount e1=0 from rfl,show polishCount e2=0 from rfl,unlimitedOutput]

theorem capTwo_run : run d chooseCapTwo 5 s0=some capTwoOutput := by
  rcases states_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  simp [run,chooseCapTwo,h01,h02,h03,h12,h13,h23,Ne.symm h01,Ne.symm h02,Ne.symm h12,
    show append s0 e0=s1 from rfl,show append s1 e1=s2 from rfl,terminalOutput,LoopOutput.bump,terminalProjectionCount,show polishCount e0=1 from rfl,show polishCount e1=0 from rfl,capTwoOutput]

def initialization : Initialization d := .minimum seed (seed_minimizer 1 0 (37/81) (by norm_num))

theorem unlimited_procedure : procedure d initialization chooseUnlimited=some (.loop unlimitedOutput) := by
  simp only [procedure,initialization,if_neg (show seed ∉ d.original from seed_not_original 1 0 (37/81)),show d.box.card=4 from box_card _ _ _]
  exact congrArg (Option.map Outcome.loop) unlimited_run

theorem capTwo_procedure : procedure d initialization chooseCapTwo=some (.loop capTwoOutput) := by
  simp only [procedure,initialization,if_neg (show seed ∉ d.original from seed_not_original 1 0 (37/81)),show d.box.card=4 from box_card _ _ _]
  exact congrArg (Option.map Outcome.loop) capTwo_run

theorem stored_vs_latest : s2.incumbent=some zero ∧ s2.reference=seed ∧
    s2.lastSuccess=some 0 ∧ zero ≠ seed ∧ s3.incumbent=some zero ∧ s3.reference=seed := by
  refine ⟨rfl,rfl,rfl,?_,rfl,rfl⟩
  intro h
  have he := congrArg (fun p : P => p.2 0) h
  norm_num [zero,seed,pt] at he

theorem better_original : one ∈ d.original ∧ d.f one=10/81 ∧ d.f zero=37/81 := by
  refine ⟨?_,by norm_num [d,data,q,one,pt],by norm_num [d,data,q,zero,pt]⟩
  apply fiber_subset_original d (corner 0 1)
  exact ⟨(relaxation_iff _ _ _ _).mpr (by norm_num [one,pt]),by simpa [one] using point_cast 0 1⟩

theorem late_normal_excludes_better : e1.normal one= -5/9 ∧ ¬retainedNormals s2 one := by
  constructor
  · norm_num [normal_two,e1,seed,one,corner,pt]
  · intro h
    have he := h e1 (by simp [s2,s1,s0,append,initialState]) rfl
    norm_num [normal_two,e1,seed,one,corner,pt] at he

end Chapter03.FPTrace.C2
