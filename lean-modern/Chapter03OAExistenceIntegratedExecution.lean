module

public import Chapter03OAExistenceIntegratedMasters
public import Chapter03OAExecArticleGTrace

@[expose] public section

/-! All legal choices of the existing driver, not a selected favorable trace.
Both actual open histories have unique master and fixed/restoration replies.
The first restoration creates no incumbent, so every nonnegative tolerance
still reaches the second solve before the delayed gap test returns. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.OAExec.Integrated

def state0 : State spec := initialState spec seed
def state1 : State spec := ⟨[event0],none,15/16⟩
def state2 : State spec := ⟨[event0,event1],some solution,5/4⟩

theorem first_step {s : State spec} (hs : s=state0) (q : MasterChoice spec seed s)
    (e : Event spec) (he : EventValid spec e) (hy : q.point.1.2=intCast e.target) :
    e=event0 ∧ advance s q e=state1 := by
  subst s
  have hq := choice0_unique rfl q
  have ht : intCast e.target 0=0 := by
    have h := congrArg (fun v : V => v 0) hy
    simpa [hq.1,master0,pt,scalar] using h.symm
  have ee := event_of_y0 he ht
  refine ⟨ee,?_⟩
  rw [ee]
  simp [advance,nextIncumbent,event0,state0,initialState,state1,hq.2]
  exact hq.2

theorem second_step {s : State spec} (hs : s=state1) (q : MasterChoice spec seed s)
    (e : Event spec) (he : EventValid spec e) (hy : q.point.1.2=intCast e.target) :
    e=event1 ∧ advance s q e=state2 := by
  subst s
  have hq := choice1_unique rfl q
  have ht : intCast e.target 0=1 := by
    have h := congrArg (fun v : V => v 0) hy
    simpa [hq.1,master1,solution,pt,scalar] using h.symm
  have ee := event_of_y1 he ht
  refine ⟨ee,?_⟩
  rw [ee]
  simp [advance,nextIncumbent,event1,state1,state2,hq.2,keepBest,Event.anchor,
    solution,pt]
  exact hq.2

theorem state0_open (epsilon : ℝ) : loopOpen spec epsilon state0 := by
  simp [loopOpen,state0,initialState]

theorem state1_open (epsilon : ℝ) : loopOpen spec epsilon state1 := by
  simp [loopOpen,state1]

theorem state2_closed (epsilon : ℝ) (heps : 0≤epsilon) : ¬ loopOpen spec epsilon state2 := by
  intro h
  have hg := h solution rfl
  norm_num [spec,objective,state2,solution,pt,scalar] at hg
  exact (not_lt_of_ge heps) hg

theorem reachable_states (epsilon : ℝ) (heps : 0≤epsilon) {s : State spec}
    (hs : Reachable spec seed epsilon s) : s=state0 ∨ s=state1 ∨ s=state2 := by
  induction hs with
  | initial => exact Or.inl rfl
  | next before step ih =>
    cases step with
    | step ho q e he hy =>
      rcases ih with h|h|h
      · exact Or.inr (Or.inl (first_step h q e he hy).2)
      · exact Or.inr (Or.inr (second_step h q e he hy).2)
      · exact False.elim ((state2_closed epsilon heps) (h ▸ ho))

/-- This equality quantifies over every selector and all exact admitted
replies. It counts the actual source-ordered recursion, with unused fuel. -/
theorem every_selector_run (epsilon : ℝ) (heps : 0≤epsilon)
    (choose : Selector spec seed epsilon) :
    runFuel spec seed epsilon choose 3 state0 .initial=
      some ⟨.solution solution,2,2,1⟩ := by
  have ho0 := state0_open epsilon
  cases hc0 : choose state0 .initial ho0 with
  | empty hempty =>
    have hm : master0∈master spec seed state0.history := master0_minimum.1
    rw [hempty] at hm
    exact hm.elim
  | next q0 e0 he0 hy0 =>
    obtain ⟨heq0,hs1⟩ := first_step rfl q0 e0 he0 hy0
    let s1 := advance state0 q0 e0
    have hr1 : Reachable spec seed epsilon s1 := .next .initial (.step ho0 q0 e0 he0 hy0)
    have ho1 : loopOpen spec epsilon s1 := by
      change loopOpen spec epsilon (advance state0 q0 e0)
      rw [hs1]
      exact state1_open epsilon
    cases hc1 : choose s1 hr1 ho1 with
    | empty hempty =>
      have hm : master1∈master spec seed s1.history := by
        simpa only [s1,hs1,state1] using master1_minimum.1
      rw [hempty] at hm
      exact hm.elim
    | next q1 e1 he1 hy1 =>
      obtain ⟨heq1,hs2⟩ := second_step hs1 q1 e1 he1 hy1
      let s2 := advance s1 q1 e1
      have hr2 : Reachable spec seed epsilon s2 := .next hr1 (.step ho1 q1 e1 he1 hy1)
      have hi : s2.incumbent=some solution := by rw [show s2=state2 from hs2]; rfl
      have hg : spec.f solution-s2.lower≤epsilon := by
        rw [show s2=state2 from hs2]
        norm_num [spec,objective,state2,solution,pt,scalar]
        exact heps
      have ht2 := Article.runFuel_closed choose 1 s2 hr2 solution hi hg
      have ht1 := Article.runFuel_next choose 1 s1 hr1 ho1 q1 e1 he1 hy1 hc1 _ ht2
      have ht0 := Article.runFuel_next choose 2 state0 .initial ho0 q0 e0 he0 hy0 hc0 _ ht1
      simpa only [heq0,heq1,countStep,eventRestorations,event0,event1,Option.some_ne_none,
        ↓reduceIte,Nat.zero_add,Nat.add_zero] using ht0

theorem box_card : spec.box.card=2 := Article.box_card_two 0 1 (fun _ => 0)

/-- Every possible exact initialization is the unique fractional seed; the
existing initialized execution therefore returns this same concrete result. -/
theorem every_initialized_run (epsilon : ℝ) (heps : 0≤epsilon)
    (choose : InitializedSelectors spec epsilon) (initial : Initialization spec) :
    execute spec epsilon choose initial=some ⟨.solution solution,2,2,1⟩ := by
  cases initial with
  | empty he =>
    have hm := seed_minimum.1
    rw [he] at hm
    exact hm.elim
  | minimum p hm hd =>
    have hp := seed_unique hm
    subst p
    have hi := seed_valid.2.2
    have hr := every_selector_run epsilon heps (choose seed ⟨hm,hd,hi⟩)
    simpa only [execute,dif_neg hi,box_card,state0] using hr

end Chapter03.OAExec.Integrated
