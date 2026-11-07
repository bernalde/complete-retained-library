module

public import Chapter03OAExecRun
public import Chapter03OAExecArticleOtherAvailability

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

def overrideDecision {n m l r : ℕ} {d : Data n m l r} {seed : Point n m}
    {epsilon : ℝ} (base : Selector d seed epsilon) (s0 : State d)
    (decision : Decision d seed s0) : Selector d seed epsilon := by
  classical
  intro s hs ho
  exact if h : s=s0 then h.symm ▸ decision else base s hs ho

theorem overrideDecision_at {n m l r : ℕ} {d : Data n m l r} {seed : Point n m}
    {epsilon : ℝ} (base : Selector d seed epsilon) (s : State d)
    (decision : Decision d seed s) (hs : Reachable d seed epsilon s)
    (ho : loopOpen d epsilon s) : overrideDecision base s decision s hs ho=decision := by
  simp [overrideDecision]

theorem runFuel_closed {n m l r : ℕ} {d : Data n m l r} {seed : Point n m}
    {epsilon : ℝ} (choose : Selector d seed epsilon) (fuel : ℕ) (s : State d)
    (hs : Reachable d seed epsilon s) (p : Point n m)
    (hi : s.incumbent=some p) (hg : d.f p-s.lower≤epsilon) :
    runFuel d seed epsilon choose fuel s hs=some ⟨.solution p,0,0,0⟩ := by
  have ho : ¬ loopOpen d epsilon s := fun h => not_lt_of_ge hg (h p hi)
  rw [runFuel,dif_neg ho]
  have hp : closedPoint ho=p := Option.some.inj ((closedPoint_spec ho).1.symm.trans hi)
  rw [hp]

def TfirstEvent : Event Tdata := T_event (fun _ => 1)
  (by intro i; norm_num [T,boxModel,scalar])

theorem TfirstEvent_valid : EventValid Tdata TfirstEvent := T_event_valid _ _

theorem Tfirst_minimum : IsMinimizer (master Tdata (pt 0 (1/4)) []) Prod.snd
    (pt 0 1,0) := by
  refine ⟨?_,?_⟩
  · rw [T_master_iff [] (by simp)]
    norm_num [pt,scalar]
  · intro z hz
    have h := (T_master_iff [] (by simp) z).mp hz
    exact h.1.1.trans h.2.2.1

def TfirstChoice : MasterChoice Tdata (pt 0 (1/4))
    (initialState Tdata (pt 0 (1/4))) := ⟨(pt 0 1,0),true,Tfirst_minimum⟩

theorem Tfirst_same_y : TfirstChoice.point.1.2=intCast TfirstEvent.target := by
  ext i
  fin_cases i
  norm_num [TfirstChoice,TfirstEvent,T_event,pt,intCast,scalar]

def TfirstDecision : Decision Tdata (pt 0 (1/4)) (initialState Tdata (pt 0 (1/4))) :=
  .next TfirstChoice TfirstEvent TfirstEvent_valid Tfirst_same_y

def Tpolicy : Selector Tdata (pt 0 (1/4)) (9/16) :=
  overrideDecision (Classical.choice (T_selectors_exist (9/16)))
    (initialState Tdata (pt 0 (1/4))) TfirstDecision

def Tafter : State Tdata := advance (initialState Tdata (pt 0 (1/4))) TfirstChoice TfirstEvent

theorem Tafter_incumbent : Tafter.incumbent=some (pt 0 1) := by
  simp [Tafter,advance,nextIncumbent,keepBest,TfirstEvent,T_event,Event.anchor,
    initialState,intCast,scalar,pt,Chapter03.OAKKT.Controls.pt]
  ext i
  norm_num [Chapter03.OAKKT.intCast,Chapter02DICOPTExamples.scalar]

theorem Tafter_gap_equality : Tdata.f (pt 0 1)-Tafter.lower=9/16 := by
  norm_num [Tdata,Tf,linearQuadratic,Tafter,advance,TfirstChoice,
    MasterChoice.nextLower,pt,scalar]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual recursive driver returns at equality after one selected fixed
solve, with cost9/16 although the alternative integral fiber costs1/16. -/
theorem T_positive_tolerance_run :
    runFuel Tdata (pt 0 (1/4)) (9/16) Tpolicy 3
      (initialState Tdata (pt 0 (1/4))) .initial=
      some ⟨.solution (pt 0 1),1,1,0⟩ := by
  have ho : loopOpen Tdata (9/16) (initialState Tdata (pt 0 (1/4))) := by
    simp [loopOpen,initialState]
  rw [runFuel,dif_pos ho]
  have hc : Tpolicy _ Reachable.initial ho=TfirstDecision :=
    overrideDecision_at _ _ _ _ _
  rw [hc]
  change (runFuel Tdata (pt 0 (1/4)) (9/16) Tpolicy 2 Tafter _).map _=_
  rw [runFuel_closed _ _ _ _ (pt 0 1) Tafter_incumbent (le_of_eq Tafter_gap_equality)]
  simp [countStep,eventRestorations,TfirstEvent,T_event]

theorem T_solution_feasible (b : ℤ) (hb : b=0 ∨ b=1) :
    pt 0 (b:ℝ) ∈ Tdata.original := by
  rw [Data.original,source_feasible_iff]
  refine ⟨Set.mem_univ _,?_,?_,fun _ => b,?_,?_⟩
  · intro j
    norm_num [Tdata,T,boxModel,xSquareRow,pt,scalar]
  · exact (T_fiber_minimum (scalar (b:ℝ))).1.1
  · intro i
    rcases hb with rfl | rfl <;> norm_num [Tdata,T,boxModel,scalar]
  · ext i
    fin_cases i
    rfl

theorem T_positive_output_guarantee :
    ReturnCertificate Tdata (9/16) (.solution (pt 0 1)) ∧
    ¬ IsMinimizer Tdata.original Tdata.f (pt 0 1) := by
  constructor
  · refine ⟨by simpa using T_solution_feasible 1 (Or.inr rfl),?_⟩
    intro z hz
    have hx := ((T_relaxation z).mp (original_subset_relaxation Tdata hz)).1
    change Tf (pt 0 1) ≤ Tf z+9/16
    norm_num [Tf,linearQuadratic,pt,scalar]
    nlinarith [sq_nonneg (z.2 0-1/4)]
  · intro hm
    have h := hm.2 (pt 0 0) (by simpa using T_solution_feasible 0 (Or.inl rfl))
    norm_num [Tdata,Tf,linearQuadratic,pt,scalar] at h

end Chapter03.OAExec.Article

#print axioms Chapter03.OAExec.Article.T_positive_tolerance_run
#print axioms Chapter03.OAExec.Article.T_positive_output_guarantee
