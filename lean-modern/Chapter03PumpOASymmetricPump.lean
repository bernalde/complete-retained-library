module

public import Chapter03PumpOAScalarSource

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA.Symmetric

def s0 : FP.State 0 1 := FP.initialState seed
def e0 : FP.Event 0 1 := ⟨iv 0,pt 0,none,some (pt 0,pt 0)⟩
def s1 : FP.State 0 1 := FP.append s0 e0
def e1 : FP.Event 0 1 := ⟨iv 1,pt 1,some (1/4),some (pt 1,pt 0)⟩
def s2 : FP.State 0 1 := FP.append s1 e1

theorem integer_point_cases (p : P)
    (hp : ∃ y∈IntegerBox model.lo model.hi, p.2=FP.intCast y) :
    p=pt 0 ∨ p=pt 1 := by
  obtain ⟨y,hy,he⟩ := hp
  rcases binary hy with rfl|rfl
  · left; apply point_ext; simpa [FP.intCast,iv,pt] using congrFun he 0
  · right; apply point_ext; simpa [FP.intCast,iv,pt] using congrFun he 0

theorem master0_mem : (pt 0,0)∈FP.master pump s0 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨(fun j => Fin.elim0 j),⟨iv 0,iv_mem 0 (Or.inl rfl),by funext j; norm_num [pt,FP.intCast,iv]⟩,
    (fun _ j => Fin.elim0 j),?_,?_,?_,?_⟩
  · intro i; fin_cases i
    exact (tangent_seed (pt 0)).le
  · simp [FP.retainedNormals,s0,FP.initialState]
  · simp [FP.noGoods,s0,FP.initialState]
  · trivial

theorem master0_minimum : IsMinimizer (FP.master pump s0) (FP.masterCost s0) (pt 0,0) := by
  refine ⟨master0_mem,?_⟩
  intro z hz
  rcases integer_point_cases z.1 (FPAdapters.epigraph_integer_box hz.1) with h|h
  all_goals change FP.l1 seed (pt 0)≤FP.l1 seed z.1
  all_goals rw [h]
  all_goals norm_num [FP.l1,Fin.sum_univ_one,seed,pt]

theorem level1 : pump.level s1.incumbent=some (1/4) := by
  norm_num [pump,asFPDelta,OAExec.asFP,spec,FP.Data.level,FP.cutoffValue,
    s1,s0,e0,FP.append,FP.initialState,pt]

theorem master1_mem : (pt 1,1/4)∈FP.master pump s1 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨(fun j => Fin.elim0 j),⟨iv 1,iv_mem 1 (Or.inr rfl),by funext j; norm_num [pt,FP.intCast,iv]⟩,
    (fun _ j => Fin.elim0 j),?_,?_,?_,?_⟩
  · intro i; fin_cases i
    · change pump.f seed+pump.Df seed (pt 1-seed)≤1/4
      rw [tangent_seed]; norm_num
    · change pump.f (pt 0)+pump.Df (pt 0) (pt 1-pt 0)≤1/4
      rw [tangent_zero]; norm_num [pt]
  · simp [FP.retainedNormals,s1,s0,e0,FP.append,FP.initialState]
  · intro e he _ hsame
    have heq : e=e0 := by simpa [s1,s0,FP.append,FP.initialState] using he
    have hh := congrFun hsame 0
    norm_num [heq,e0,pt,FP.intCast,iv] at hh
  · rw [level1]; exact le_rfl

theorem master1_minimum : IsMinimizer (FP.master pump s1) (FP.masterCost s1) (pt 1,1/4) := by
  refine ⟨master1_mem,?_⟩
  intro z hz
  have hn := hz.2.2.1 e0 (by simp [s1,s0,FP.append,FP.initialState]) (by simp [e0])
  rcases integer_point_cases z.1 (FPAdapters.epigraph_integer_box hz.1) with h|h
  · exact False.elim (hn (by rw [h]; funext j; norm_num [e0,pt,FP.intCast,iv]))
  · change FP.l1 (pt 0) (pt 1)≤FP.l1 (pt 0) z.1
    rw [h]

theorem fiber_minimum (k : ℤ) (hk : k=0 ∨ k=1) :
    IsMinimizer (pump.fiber (iv k)) pump.f (pt (k:ℝ)) := by
  refine ⟨⟨?_,point_cast k⟩,?_⟩
  · apply (relaxation _).mpr
    rcases hk with rfl|rfl <;> norm_num [pt]
  · intro p hp
    have he : p=pt (k:ℝ) := point_ext (congrFun hp.2 0)
    rw [he]

theorem projection_minimum (k : ℤ) (level : Option ℝ)
    (hp : pt (k:ℝ)∈pump.region level) :
    IsMinimizer (pump.region level) (FP.distance (iv k)) (pt (k:ℝ)) := by
  refine ⟨hp,?_⟩
  intro p _
  rw [distance,distance]
  norm_num only [iv,pt,sub_self,zero_pow]
  exact sq_nonneg _

theorem reply0 : FP.EventReply pump s0 (pt 0,0) e0 := by
  refine ⟨by funext j; norm_num [e0,pt,FP.intCast,iv],rfl,?_,?_⟩
  · simpa [e0,s0,FP.initialState,FP.Data.level] using projection_minimum 0 none
      ⟨(relaxation _).mpr (by norm_num [pt]),trivial⟩
  · refine ⟨?_,by simpa [e0] using fiber_minimum 0 (Or.inl rfl),rfl⟩
    norm_num [distance,e0,iv,pt]

theorem reply1 : FP.EventReply pump s1 (pt 1,1/4) e1 := by
  refine ⟨by funext j; norm_num [e1,pt,FP.intCast,iv],level1.symm,?_,?_⟩
  · rw [level1]
    have hp : pt (1:ℤ)∈pump.region (some (1/4)) := by
      refine ⟨(relaxation _).mpr (by norm_num [pt]),?_⟩
      norm_num [FP.Allows,pump,asFPDelta,OAExec.asFP,spec,pt]
    simpa [e1] using projection_minimum 1 (some (1/4)) hp
  · refine ⟨?_,by simpa [e1] using fiber_minimum 1 (Or.inr rfl),?_⟩
    · norm_num [distance,e1,iv,pt]
    · norm_num [FP.BestChoice,s1,s0,FP.append,FP.initialState,e0,e1,
        pump,asFPDelta,OAExec.asFP,spec,pt]

theorem no_remaining_integer (z : P×ℝ) (hi : z∈FP.epigraph pump s2)
    (hn : FP.noGoods s2 z.1) : False := by
  have h0 := hn e0 (by simp [s2,s1,s0,FP.append,FP.initialState]) (by simp [e0])
  have h1 := hn e1 (by simp [s2,s1,s0,FP.append,FP.initialState]) (by simp [e1])
  rcases integer_point_cases z.1 (FPAdapters.epigraph_integer_box hi) with h|h
  · exact h0 (by rw [h]; funext j; norm_num [e0,pt,FP.intCast,iv])
  · exact h1 (by rw [h]; funext j; norm_num [e1,pt,FP.intCast,iv])

theorem master2_empty : ¬ (FP.master pump s2).Nonempty := by
  rintro ⟨z,hz⟩
  exact no_remaining_integer z hz.1 hz.2.2.1

theorem handoff_empty : FP.handoff pump s2=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact no_remaining_integer z hz.1 hz.2.2

theorem states_distinct : s0≠s1 ∧ s0≠s2 ∧ s1≠s2 := by
  repeat' constructor
  all_goals intro h
  all_goals have hh := congrArg (fun s : FP.State 0 1 => s.history.length) h
  all_goals norm_num [s2,s1,s0,FP.append,FP.initialState] at hh

def choose : FP.Selector pump none := fun s => by
  classical
  exact if h0 : s=s0 then h0.symm ▸ .next e0
      ⟨(pt 0,0),master0_minimum,by simp [FP.BeforeCap],reply0⟩
    else if h1 : s=s1 then h1.symm ▸ .next e1
      ⟨(pt 1,1/4),master1_minimum,by simp [FP.BeforeCap],reply1⟩
    else if h2 : s=s2 then h2.symm ▸ .stop .emptyMaster (.emptyMaster master2_empty)
    else Classical.choice (FP.decision_nonempty pump pump_analytic none s)

def output : FP.LoopOutput 0 1 := ⟨s2,.emptyMaster,2,2,3,2⟩
def initialization : FP.Initialization pump := .minimum seed seed_minimum

theorem actual_run : FP.run pump choose 3 s0=some output := by
  rcases states_distinct with ⟨h01,h02,h12⟩
  simp [FP.run,choose,h01,h02,h12,Ne.symm h01,Ne.symm h02,Ne.symm h12,
    show FP.append s0 e0=s1 from rfl,show FP.append s1 e1=s2 from rfl,
    FP.terminalOutput,FP.LoopOutput.bump,FP.terminalProjectionCount,
    show FP.polishCount e0=1 from rfl,show FP.polishCount e1=1 from rfl,output]

theorem seed_not_original : seed∉pump.original := by
  intro h
  obtain ⟨_,_,_,y,_,hy⟩ := (source_feasible_iff model Set.univ seed).mp h
  exact seed_not_integral ⟨y,hy⟩

theorem actual_procedure : FP.procedure pump initialization choose=some (.loop output) := by
  simp only [FP.procedure,initialization,if_neg seed_not_original,box_card]
  exact congrArg (Option.map FP.Outcome.loop) actual_run

theorem stored_tie : s2.incumbent=some (pt 0) ∧ s2.history=[e0,e1] ∧
    pump.f (pt 0)=pump.f (pt 1) := by
  refine ⟨rfl,rfl,?_⟩
  norm_num [pump,asFPDelta,OAExec.asFP,spec,pt]

end Chapter03.PumpOA.Symmetric

#print axioms Chapter03.PumpOA.Symmetric.actual_procedure
#print axioms Chapter03.PumpOA.Symmetric.handoff_empty
#print axioms Chapter03.PumpOA.Symmetric.stored_tie
