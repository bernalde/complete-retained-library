module

public import Chapter03FPTraceC3Geometry

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C3

theorem states_distinct : s0 ≠ s1 ∧ s0 ≠ s2 ∧ s0 ≠ s3 ∧ s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3 := by
  have lengths : s0.history.length=0 ∧ s1.history.length=1 ∧ s2.history.length=2 ∧ s3.history.length=3 := by
    norm_num [s0,s1,s2,s3,append,initialState]
  rcases lengths with ⟨h0,h1,h2,h3⟩
  repeat' constructor
  all_goals intro h
  all_goals have he := congrArg (fun s : State 1 2 => s.history.length) h
  all_goals norm_num [s0,s1,s2,s3,append,initialState] at he

def chooseUnlimited : Selector d none := fun s => by
  classical
  exact if h0 : s=s0 then h0.symm ▸ .next e0 ⟨(pt 1 0 0,1),master0_min,by simp [BeforeCap],reply0⟩
    else if h1 : s=s1 then h1.symm ▸ .next e1 ⟨(pt 1 0 1,1),master1_min,by simp [BeforeCap],reply1⟩
    else if h2 : s=s2 then h2.symm ▸ .next e2 ⟨(proj2,29/20),master2_min,by simp [BeforeCap],reply2⟩
    else if h3 : s=s3 then h3.symm ▸ .stop .emptyMaster (.emptyMaster master3_empty)
    else Classical.choice (decision_nonempty d d_analytic none s)

def chooseCapTwo : Selector d (some 2) := fun s => by
  classical
  exact if h0 : s=s0 then h0.symm ▸ .next e0 ⟨(pt 1 0 0,1),master0_min,by simp [BeforeCap,s0,initialState],reply0⟩
    else if h1 : s=s1 then h1.symm ▸ .next e1 ⟨(pt 1 0 1,1),master1_min,by simp [BeforeCap,s1,s0,append,initialState],reply1⟩
    else if h2 : s=s2 then h2.symm ▸ .stop .handoff (.handoff master2_min rfl (by simp [s2,s1,s0,append,initialState]))
    else Classical.choice (decision_nonempty d d_analytic (some 2) s)

def unlimitedOutput : LoopOutput 1 2 := ⟨s3,.emptyMaster,3,3,4,1⟩
def capTwoOutput : LoopOutput 1 2 := ⟨s2,.handoff,2,2,3,0⟩

theorem unlimited_run : run d chooseUnlimited 5 s0=some unlimitedOutput := by
  rcases states_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  simp [run,chooseUnlimited,h01,h02,h03,h12,h13,h23,Ne.symm h01,Ne.symm h02,Ne.symm h03,
    Ne.symm h12,Ne.symm h13,Ne.symm h23,show append s0 e0=s1 from rfl,show append s1 e1=s2 from rfl,show append s2 e2=s3 from rfl,terminalOutput,LoopOutput.bump,
    terminalProjectionCount,show polishCount e0=0 from rfl,show polishCount e1=0 from rfl,show polishCount e2=1 from rfl,unlimitedOutput]

theorem capTwo_run : run d chooseCapTwo 5 s0=some capTwoOutput := by
  rcases states_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  simp [run,chooseCapTwo,h01,h02,h03,h12,h13,h23,Ne.symm h01,Ne.symm h02,Ne.symm h12,
    show append s0 e0=s1 from rfl,show append s1 e1=s2 from rfl,terminalOutput,LoopOutput.bump,terminalProjectionCount,show polishCount e0=0 from rfl,show polishCount e1=0 from rfl,capTwoOutput]

def initialization : Initialization d := .minimum seed seed_minimizer

theorem unlimited_procedure : procedure d initialization chooseUnlimited=some (.loop unlimitedOutput) := by
  simp only [procedure,initialization,if_neg (show seed ∉ d.original from seed_not_original),show d.box.card=4 from box_card]
  exact congrArg (Option.map Outcome.loop) unlimited_run

theorem capTwo_procedure : procedure d initialization chooseCapTwo=some (.loop capTwoOutput) := by
  simp only [procedure,initialization,if_neg (show seed ∉ d.original from seed_not_original),show d.box.card=4 from box_card]
  exact congrArg (Option.map Outcome.loop) capTwo_run

theorem stored_polished : s3.incumbent=some polished ∧ s3.reference=polished ∧
    s3.lastSuccess=some 2 ∧ s2.incumbent=none ∧ s2.reference=proj1 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem original_coordinates {p : P} (hp : p ∈ d.original) : p.2=intCast (corner 1 0) := by
  have hr := original_subset_relaxation d hp
  have line := ((relaxation_iff _).mp hr).2.2.2.2.2.2
  obtain ⟨_,_,_,y,hy,he⟩ := (source_feasible_iff model Set.univ p).mp hp
  rcases integer_corner_cases y hy with h|h|h|h
  all_goals rw [h] at he
  · norm_num [he,intCast,corner] at line
  · norm_num [he,intCast,corner] at line
  · exact he
  · norm_num [he,intCast,corner] at line

theorem polished_global_minimum : IsMinimizer d.original d.f polished := by
  refine ⟨fiber_subset_original d (corner 1 0) polishing.1,?_⟩
  intro p hp
  exact polishing.2 p ⟨original_subset_relaxation d hp,original_coordinates hp⟩

end Chapter03.FPTrace.C3
