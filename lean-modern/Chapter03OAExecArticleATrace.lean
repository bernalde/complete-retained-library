module

public import Chapter03OAExecArticleGTrace

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

def Azero : Event Adata := A_event (fun _ => 0)
  (by intro i; norm_num [A,boxModel,scalar])
def Aone : Event Adata := A_event (fun _ => 1)
  (by intro i; norm_num [A,boxModel,scalar])
theorem Azero_valid : EventValid Adata Azero := A_event_valid _ _
theorem Aone_valid : EventValid Adata Aone := A_event_valid _ _
def Astate0 := initialState Adata (pt 0 (1/2))

theorem Aminimum0 : IsMinimizer (master Adata (pt 0 (1/2)) []) Prod.snd (pt 0 0,0) := by
  refine ⟨?_,fun z hz => A_master_height_nonneg [] hz⟩
  rw [master_mem_iff]
  refine ⟨?_,?_,?_,?_,by simp,by simp [noGoods]⟩
  · exact (box_hard (-1) 1 _ _).mpr (by norm_num [pt,scalar])
  · apply (box_integer_iff (-1) 1 _ _).mpr
    norm_num [pt,scalar]
  · intro j
    norm_num [Adata,A,boxModel,Adg,quadratic,quadraticD,pt,scalar]
  · norm_num [Adata,Af,Adf,quadratic,quadraticD,pt,scalar]

def Achoice0 : MasterChoice Adata (pt 0 (1/2)) Astate0 :=
  ⟨(pt 0 0,0),true,Aminimum0⟩
def Astate1 := advance Astate0 Achoice0 Azero

theorem Aminimum1 : IsMinimizer (master Adata (pt 0 (1/2)) [Azero]) Prod.snd
    (pt 0 1,0) := by
  refine ⟨?_,fun z hz => A_master_height_nonneg [Azero] hz⟩
  rw [master_mem_iff]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact (box_hard (-1) 1 _ _).mpr (by norm_num [pt,scalar])
  · apply (box_integer_iff (-1) 1 _ _).mpr
    norm_num [pt,scalar]
  · intro j
    norm_num [Adata,A,boxModel,Adg,quadratic,quadraticD,pt,scalar]
  · norm_num [Adata,Af,Adf,quadratic,quadraticD,pt,scalar]
  · intro e he
    have heq := List.mem_singleton.mp he
    subst e
    rw [A_event_rows Azero Azero_valid]
    norm_num [Azero,A_event,LiteralG.tangent,pt,scalar]
  · intro e he hn
    have heq := List.mem_singleton.mp he
    subst e
    intro hh
    have hh0 := congrFun hh 0
    norm_num [pt,Chapter03.OAKKT.intCast,Azero,A_event,scalar] at hh0

def Achoice1 : MasterChoice Adata (pt 0 (1/2)) Astate1 :=
  ⟨(pt 0 1,0),true,Aminimum1⟩
def Astate2 := advance Astate1 Achoice1 Aone

theorem Achoice0_y : Achoice0.point.1.2=intCast Azero.target := by
  ext i; fin_cases i; norm_num [Achoice0,Azero,A_event,pt,Chapter03.OAKKT.intCast,scalar]
theorem Achoice1_y : Achoice1.point.1.2=intCast Aone.target := by
  ext i; fin_cases i; norm_num [Achoice1,Aone,A_event,pt,Chapter03.OAKKT.intCast,scalar]

theorem A_two_master_empty : master Adata (pt 0 (1/2)) [Azero,Aone]=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨y,hy,hzy⟩ := master_integer hz
  have hn := ((master_mem_iff _ _ _ _).mp hz).2.2.2.2.2
  rcases (binary_box (-1) 1 _ y).mp hy with hb | hb
  · apply hn Azero (by simp) (by simp [Azero,A_event])
    rw [hzy]
    ext i
    fin_cases i
    simp [Chapter03.OAKKT.intCast,Azero,A_event,hb]
  · apply hn Aone (by simp) (by simp [Aone,A_event])
    rw [hzy]
    ext i
    fin_cases i
    simp [Chapter03.OAKKT.intCast,Aone,A_event,hb]

def Adecision0 : Decision Adata (pt 0 (1/2)) Astate0 :=
  .next Achoice0 Azero Azero_valid Achoice0_y
def Adecision1 : Decision Adata (pt 0 (1/2)) Astate1 :=
  .next Achoice1 Aone Aone_valid Achoice1_y
def Adecision2 : Decision Adata (pt 0 (1/2)) Astate2 := .empty A_two_master_empty

def Apolicy : Selector Adata (pt 0 (1/2)) 0 :=
  overrideDecision (overrideDecision (overrideDecision
    (Classical.choice (A_selectors_exist 0)) Astate2 Adecision2)
    Astate1 Adecision1) Astate0 Adecision0

theorem Aopen0 : loopOpen Adata 0 Astate0 := by simp [Astate0,initialState,loopOpen]
theorem Aopen1 : loopOpen Adata 0 Astate1 := by
  simp [loopOpen,Astate1,Astate0,advance,nextIncumbent,Azero,A_event,initialState]
theorem Aopen2 : loopOpen Adata 0 Astate2 := by
  simp [loopOpen,Astate2,Astate1,Astate0,advance,nextIncumbent,Azero,Aone,A_event,initialState]

theorem Astate10 : Astate1≠Astate0 := by
  intro h
  have hh := congrArg (fun s : State Adata => s.history.length) h
  norm_num [Astate1,Astate0,advance,initialState] at hh
theorem Astate20 : Astate2≠Astate0 := by
  intro h
  have hh := congrArg (fun s : State Adata => s.history.length) h
  norm_num [Astate2,Astate1,Astate0,advance,initialState] at hh
theorem Astate21 : Astate2≠Astate1 := by
  intro h
  have hh := congrArg (fun s : State Adata => s.history.length) h
  norm_num [Astate2,Astate1,Astate0,advance,initialState] at hh

/-- Two actual positive restorations are followed by the third master's
genuine empty exit; counts distinguish decisions from fixed/restoration solves. -/
theorem A_three_master_run :
    runFuel Adata (pt 0 (1/2)) 0 Apolicy 3 Astate0 .initial=
      some ⟨.infeasible,3,2,2⟩ := by
  have hr1 : Reachable Adata (pt 0 (1/2)) 0 Astate1 :=
    .next .initial (.step Aopen0 Achoice0 Azero Azero_valid Achoice0_y)
  have hr2 : Reachable Adata (pt 0 (1/2)) 0 Astate2 :=
    .next hr1 (.step Aopen1 Achoice1 Aone Aone_valid Achoice1_y)
  have hc0 : Apolicy Astate0 .initial Aopen0=Adecision0 := overrideDecision_at _ _ _ _ _
  have hc1 : Apolicy Astate1 hr1 Aopen1=Adecision1 := by
    rw [Apolicy,overrideDecision_other _ _ _ _ _ _ Astate10,overrideDecision_at]
  have hc2 : Apolicy Astate2 hr2 Aopen2=Adecision2 := by
    rw [Apolicy,overrideDecision_other _ _ _ _ _ _ Astate20,
      overrideDecision_other _ _ _ _ _ _ Astate21,overrideDecision_at]
  have ht2 : runFuel Adata (pt 0 (1/2)) 0 Apolicy 1 Astate2 hr2=
      some ⟨.infeasible,1,0,0⟩ := by
    rw [runFuel,dif_pos Aopen2,hc2]
    rfl
  have ht1 := runFuel_next Apolicy 1 Astate1 hr1 Aopen1 Achoice1 Aone Aone_valid
    Achoice1_y hc1 _ ht2
  have ht0 := runFuel_next Apolicy 2 Astate0 .initial Aopen0 Achoice0 Azero Azero_valid
    Achoice0_y hc0 _ ht1
  simpa [countStep,eventRestorations,Azero,Aone,A_event] using ht0

end Chapter03.OAExec.Article

#print axioms Chapter03.OAExec.Article.A_three_master_run
