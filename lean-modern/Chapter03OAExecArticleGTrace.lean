module

public import Chapter03OAExecArticleReturns

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

theorem overrideDecision_other {n m l r : ℕ} {d : Data n m l r} {seed : Point n m}
    {epsilon : ℝ} (base : Selector d seed epsilon) (s0 : State d)
    (decision : Decision d seed s0) (s : State d) (hs : Reachable d seed epsilon s)
    (ho : loopOpen d epsilon s) (hne : s≠s0) :
    overrideDecision base s0 decision s hs ho=base s hs ho := by
  simp [overrideDecision,hne]

theorem runFuel_next {n m l r : ℕ} {d : Data n m l r} {seed : Point n m}
    {epsilon : ℝ} (choose : Selector d seed epsilon) (fuel : ℕ) (s : State d)
    (hs : Reachable d seed epsilon s) (ho : loopOpen d epsilon s)
    (q : MasterChoice d seed s) (e : Event d) (hv : EventValid d e)
    (hy : q.point.1.2=intCast e.target)
    (hc : choose s hs ho=.next q e hv hy) (out : Output n m)
    (ht : runFuel d seed epsilon choose fuel (advance s q e)
      (.next hs (.step ho q e hv hy))=some out) :
    runFuel d seed epsilon choose (fuel+1) s hs=some (countStep e out) := by
  rw [runFuel,dif_pos ho,hc]
  change (runFuel d seed epsilon choose fuel (advance s q e) _).map (countStep e)=_
  rw [ht]
  rfl

def Gzero : Event Gdata := G_event (fun _ => 0)
  (by intro i; norm_num [G,boxModel,scalar])
def Gone : Event Gdata := G_event (fun _ => 1)
  (by intro i; norm_num [G,boxModel,scalar])
theorem Gzero_valid : EventValid Gdata Gzero := G_event_valid _ _
theorem Gone_valid : EventValid Gdata Gone := G_event_valid _ _

def Gstate0 := initialState Gdata (pt 0 (1/2))

theorem Gminimum0 : IsMinimizer (master Gdata (pt 0 (1/2)) []) Prod.snd (pt 0 0,0) := by
  rw [G_master_literal [] (by simp)]
  simpa [LiteralG.history,LiteralG.trial,LiteralG.chosen,LiteralG.anchor] using
    LiteralG.trial_minimum 0

def Gchoice0 : MasterChoice Gdata (pt 0 (1/2)) Gstate0 :=
  ⟨(pt 0 0,0),true,Gminimum0⟩
def Gstate1 : State Gdata := advance Gstate0 Gchoice0 Gzero

theorem Gminimum1 : IsMinimizer (master Gdata (pt 0 (1/2)) [Gzero]) Prod.snd
    (pt 0 1,0) := by
  rw [G_master_literal [Gzero] (by simpa using Gzero_valid)]
  simpa [LiteralG.history,LiteralG.trial,LiteralG.chosen,LiteralG.anchor,Gzero,G_event] using
    LiteralG.trial_minimum 1

def Gchoice1 : MasterChoice Gdata (pt 0 (1/2)) Gstate1 :=
  ⟨(pt 0 1,0),true,Gminimum1⟩
def Gstate2 : State Gdata := advance Gstate1 Gchoice1 Gone

theorem Gminimum2 : IsMinimizer (master Gdata (pt 0 (1/2)) [Gzero,Gone]) Prod.snd
    (pt 0 1,1/4) := by
  rw [G_master_literal [Gzero,Gone] (by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact Gzero_valid
    · simpa using List.mem_singleton.mp he ▸ Gone_valid)]
  simpa [LiteralG.history,LiteralG.trial,LiteralG.chosen,LiteralG.anchor,Gzero,Gone,G_event,List.range_succ] using
    LiteralG.trial_minimum 2

def Gchoice2 : MasterChoice Gdata (pt 0 (1/2)) Gstate2 :=
  ⟨(pt 0 1,1/4),true,Gminimum2⟩
def Gstate3 : State Gdata := advance Gstate2 Gchoice2 Gone

theorem Gchoice0_y : Gchoice0.point.1.2=intCast Gzero.target := by
  ext i; fin_cases i; norm_num [Gchoice0,Gzero,G_event,pt,Chapter03.OAKKT.intCast,scalar]
theorem Gchoice1_y : Gchoice1.point.1.2=intCast Gone.target := by
  ext i; fin_cases i; norm_num [Gchoice1,Gone,G_event,pt,Chapter03.OAKKT.intCast,scalar]
theorem Gchoice2_y : Gchoice2.point.1.2=intCast Gone.target := by
  ext i; fin_cases i; norm_num [Gchoice2,Gone,G_event,pt,Chapter03.OAKKT.intCast,scalar]

def Gdecision0 : Decision Gdata (pt 0 (1/2)) Gstate0 :=
  .next Gchoice0 Gzero Gzero_valid Gchoice0_y
def Gdecision1 : Decision Gdata (pt 0 (1/2)) Gstate1 :=
  .next Gchoice1 Gone Gone_valid Gchoice1_y
def Gdecision2 : Decision Gdata (pt 0 (1/2)) Gstate2 :=
  .next Gchoice2 Gone Gone_valid Gchoice2_y

def Gpolicy : Selector Gdata (pt 0 (1/2)) 0 :=
  overrideDecision (overrideDecision (overrideDecision
    (Classical.choice (G_selectors_exist 0)) Gstate2 Gdecision2)
    Gstate1 Gdecision1) Gstate0 Gdecision0

theorem Gincumbents : Gstate1.incumbent=some (pt 0 0) ∧
    Gstate2.incumbent=some (pt 0 0) ∧ Gstate3.incumbent=some (pt 0 0) := by
  norm_num [Gstate0,Gstate1,Gstate2,Gstate3,advance,nextIncumbent,keepBest,
    initialState,Gzero,Gone,G_event,Event.anchor,Gdata,Gf,quadratic,
    Chapter03.OAKKT.intCast,scalar,Chapter03.OAKKT.Controls.pt]
  ext i
  norm_num [Chapter03.OAKKT.intCast,Chapter02DICOPTExamples.scalar]

theorem Gopen0 : loopOpen Gdata 0 Gstate0 := by simp [Gstate0,initialState,loopOpen]
theorem Gopen1 : loopOpen Gdata 0 Gstate1 := by
  intro p hp
  rw [Gincumbents.1] at hp
  cases hp
  norm_num [Gdata,Gf,quadratic,Gstate1,advance,Gchoice0,MasterChoice.nextLower,pt,scalar]
theorem Gopen2 : loopOpen Gdata 0 Gstate2 := by
  intro p hp
  rw [Gincumbents.2.1] at hp
  cases hp
  norm_num [Gdata,Gf,quadratic,Gstate2,advance,Gchoice1,MasterChoice.nextLower,pt,scalar]

theorem Gstate10 : Gstate1≠Gstate0 := by
  intro h
  have hh := congrArg (fun s : State Gdata => s.history.length) h
  norm_num [Gstate1,Gstate0,advance,initialState] at hh
theorem Gstate20 : Gstate2≠Gstate0 := by
  intro h
  have hh := congrArg (fun s : State Gdata => s.history.length) h
  norm_num [Gstate2,Gstate1,Gstate0,advance,initialState] at hh
theorem Gstate21 : Gstate2≠Gstate1 := by
  intro h
  have hh := congrArg (fun s : State Gdata => s.history.length) h
  norm_num [Gstate2,Gstate1,Gstate0,advance,initialState] at hh

theorem G_corrected_three_round_run :
    runFuel Gdata (pt 0 (1/2)) 0 Gpolicy 3 Gstate0 .initial=
      some ⟨.solution (pt 0 0),3,3,0⟩ := by
  have hr1 : Reachable Gdata (pt 0 (1/2)) 0 Gstate1 :=
    .next .initial (.step Gopen0 Gchoice0 Gzero Gzero_valid Gchoice0_y)
  have hr2 : Reachable Gdata (pt 0 (1/2)) 0 Gstate2 :=
    .next hr1 (.step Gopen1 Gchoice1 Gone Gone_valid Gchoice1_y)
  have hr3 : Reachable Gdata (pt 0 (1/2)) 0 Gstate3 :=
    .next hr2 (.step Gopen2 Gchoice2 Gone Gone_valid Gchoice2_y)
  have hc0 : Gpolicy Gstate0 .initial Gopen0=Gdecision0 := overrideDecision_at _ _ _ _ _
  have hc1 : Gpolicy Gstate1 hr1 Gopen1=Gdecision1 := by
    rw [Gpolicy,overrideDecision_other _ _ _ _ _ _ Gstate10,overrideDecision_at]
  have hc2 : Gpolicy Gstate2 hr2 Gopen2=Gdecision2 := by
    rw [Gpolicy,overrideDecision_other _ _ _ _ _ _ Gstate20,
      overrideDecision_other _ _ _ _ _ _ Gstate21,overrideDecision_at]
  have ht3 := runFuel_closed Gpolicy 0 Gstate3 hr3 (pt 0 0) Gincumbents.2.2
    (by norm_num [Gdata,Gf,quadratic,Gstate3,advance,Gchoice2,MasterChoice.nextLower,pt,scalar])
  have ht2 := runFuel_next Gpolicy 0 Gstate2 hr2 Gopen2 Gchoice2 Gone Gone_valid
    Gchoice2_y hc2 _ ht3
  have ht1 := runFuel_next Gpolicy 1 Gstate1 hr1 Gopen1 Gchoice1 Gone Gone_valid
    Gchoice1_y hc1 _ ht2
  have ht0 := runFuel_next Gpolicy 2 Gstate0 .initial Gopen0 Gchoice0 Gzero Gzero_valid
    Gchoice0_y hc0 _ ht1
  simpa [countStep,eventRestorations,Gzero,Gone,G_event] using ht0

end Chapter03.OAExec.Article

#print axioms Chapter03.OAExec.Article.G_corrected_three_round_run
