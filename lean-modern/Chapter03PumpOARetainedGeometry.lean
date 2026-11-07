module

public import Chapter03PumpOARetainedSource
public import Chapter03FPAdapters

@[expose] public section

/-! Exact failed-then-successful pump geometry. The normal is nonzero and
survives the strict timestamp filter. Its irredundancy relative to tangents
is not asserted; the tangent at the failed projection has the same threshold. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.PumpOA.Retained

def s0 : FP.State 1 1 := FP.initialState seed
def e0 : FP.Event 1 1 := ⟨target0,projection,none,none⟩
def s1 : FP.State 1 1 := FP.append s0 e0
def e1 : FP.Event 1 1 := ⟨target1,solution,none,some (solution,solution)⟩
def s2 : FP.State 1 1 := FP.append s1 e1
def master0 : P×ℝ := (pt (-159/160) 0,51/20)
def master1 : P×ℝ := (solution,17/4)

theorem integer_y_cases (p : P)
    (hp : ∃ y∈IntegerBox model.lo model.hi, p.2=FP.intCast y) :
    p.2 0=0 ∨ p.2 0=1 := by
  obtain ⟨y,hy,he⟩ := hp
  have hv := congrFun he 0
  rcases target_cases y hy with rfl|rfl
  · exact Or.inl (by simpa [FP.intCast,target0] using hv)
  · exact Or.inr (by simpa [FP.intCast,target1] using hv)

theorem normal_formula (p : P) : e0.normal p=(7/16)*(p.2 0-7/16) := by
  simp [FP.Event.normal,e0,projection,pt,scalar,target0,FP.intY,FP.intCast,
    Chapter03.yMap,PiLp.inner_apply,Fin.sum_univ_one,mul_comm]

theorem normal_tight : e0.normal projection=0 := by
  rw [normal_formula]; norm_num [projection,pt,scalar]

theorem normal_excludes_target (p : P) (hy : p.2=FP.intCast target0) :
    e0.normal p=-(49/256:ℝ) := by
  rw [normal_formula,hy]; norm_num [FP.intCast,target0]

theorem seed_constraint_tangent (p : P) (j : Fin 1) :
    model.g j seed+Dg seed j (p-seed)=(2/5)*p.1 0-p.2 0+159/400 := by
  norm_num [model,OAExec.Integrated.model,Dg,OAExec.Integrated.Dg,seed,pt,scalar]
  ring

theorem seed_objective_tangent (p : P) :
    objective seed+Df seed (p-seed)=-(8/5)*p.1 0+4*p.2 0+24/25 := by
  norm_num [objective,Df,seed,pt,scalar]
  ring

theorem projection_constraint_tangent (p : P) (j : Fin 1) :
    model.g j projection+Dg projection j (p-projection)=7/16-p.2 0 := by
  norm_num [model,OAExec.Integrated.model,Dg,OAExec.Integrated.Dg,projection,pt,scalar]

theorem projection_objective_tangent (p : P) :
    objective projection+Df projection (p-projection)=1-2*p.1 0+4*p.2 0 := by
  norm_num [objective,Df,projection,pt,scalar]
  ring

theorem master0_mem : master0∈FP.master pump s0 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨?_,⟨target0,target0_mem,?_⟩,?_,?_,?_,?_,?_⟩
  · intro j; fin_cases j
    norm_num [pump,asFPDelta,OAExec.asFP,spec,model,OAExec.Integrated.model,
      LinearForm,master0,pt,scalar,Fin.sum_univ_one]
  · funext j; fin_cases j; norm_num [master0,pt,scalar,FP.intCast,target0]
  · intro i j _; fin_cases i
    change model.g j seed+Dg seed j (master0.1-seed)≤0
    rw [seed_constraint_tangent]; norm_num [master0,pt,scalar]
  · intro i; fin_cases i
    change objective seed+Df seed (master0.1-seed)≤master0.2
    rw [seed_objective_tangent]; norm_num [master0,pt,scalar]
  · simp [FP.retainedNormals,s0,FP.initialState]
  · simp [FP.noGoods,s0,FP.initialState]
  · trivial

theorem master0_minimum : IsMinimizer (FP.master pump s0) (FP.masterCost s0) master0 := by
  refine ⟨master0_mem,?_⟩
  intro z hz
  rcases integer_y_cases z.1 (FPAdapters.epigraph_integer_box hz.1) with hy|hy
  all_goals change FP.l1 seed master0.1≤FP.l1 seed z.1
  all_goals norm_num [FP.l1,Fin.sum_univ_one,seed,master0,pt,scalar,hy,abs_div]

theorem master1_mem : master1∈FP.master pump s1 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨?_,⟨target1,target1_mem,?_⟩,?_,?_,?_,?_,?_⟩
  · intro j; fin_cases j
    norm_num [pump,asFPDelta,OAExec.asFP,spec,model,OAExec.Integrated.model,
      LinearForm,master1,solution,OAExec.Integrated.solution,pt,scalar,Fin.sum_univ_one]
  · funext j; fin_cases j
    norm_num [master1,solution,OAExec.Integrated.solution,pt,scalar,FP.intCast,target1]
  · intro i j _; fin_cases i
    · change model.g j seed+Dg seed j (master1.1-seed)≤0
      rw [seed_constraint_tangent]
      norm_num [master1,solution,OAExec.Integrated.solution,pt,scalar]
    · change model.g j projection+Dg projection j (master1.1-projection)≤0
      rw [projection_constraint_tangent]
      norm_num [master1,solution,OAExec.Integrated.solution,pt,scalar]
  · intro i; fin_cases i
    · change objective seed+Df seed (master1.1-seed)≤master1.2
      rw [seed_objective_tangent]
      norm_num [master1,solution,OAExec.Integrated.solution,pt,scalar]
    · change objective projection+Df projection (master1.1-projection)≤master1.2
      rw [projection_objective_tangent]
      norm_num [master1,solution,OAExec.Integrated.solution,pt,scalar]
  · intro e he _
    have heq : e=e0 := by simpa [s1,s0,FP.append,FP.initialState] using he
    rw [heq,normal_formula]
    norm_num [master1,solution,OAExec.Integrated.solution,pt,scalar]
  · simp [FP.noGoods,s1,s0,e0,FP.append,FP.initialState]
  · trivial

theorem master1_minimum : IsMinimizer (FP.master pump s1) (FP.masterCost s1) master1 := by
  refine ⟨master1_mem,?_⟩
  intro z hz
  have hn := hz.2.1 e0 (by simp [s1,s0,FP.append,FP.initialState]) rfl
  rw [normal_formula] at hn
  rcases integer_y_cases z.1 (FPAdapters.epigraph_integer_box hz.1) with hy|hy
  · rw [hy] at hn; norm_num at hn
  · change FP.l1 projection master1.1≤FP.l1 projection z.1
    norm_num [FP.l1,Fin.sum_univ_one,projection,master1,solution,
      OAExec.Integrated.solution,pt,scalar,hy]

theorem reply0 : FP.EventReply pump s0 master0 e0 := by
  refine ⟨?_,rfl,projection0_minimum,?_⟩
  · funext j; fin_cases j; norm_num [master0,e0,pt,scalar,FP.intCast,target0]
  · change FP.distance target0 projection≠0
    rw [distance]; norm_num [target0,projection,pt,scalar]

theorem reply1 : FP.EventReply pump s1 master1 e1 := by
  refine ⟨?_,rfl,projection1_minimum,?_,fixed_minimum,rfl⟩
  · funext j; fin_cases j
    norm_num [master1,e1,solution,OAExec.Integrated.solution,pt,scalar,FP.intCast,target1]
  · change FP.distance target1 solution=0
    rw [distance]; norm_num [target1,solution,OAExec.Integrated.solution,pt,scalar]

theorem retained_timestamp : s2.history=[e0,e1] ∧ s2.lastSuccess=some 1 ∧
    s2.incumbent=some solution ∧ (0:ℕ)<1 := by
  exact ⟨rfl,rfl,rfl,by decide⟩

theorem handoff_keeps_normal (p : P) : FP.handoffNormals s2 p ↔ 0≤e0.normal p := by
  constructor
  · intro h
    exact h ⟨0,by decide⟩ rfl (by
      intro k hk
      have : k=1 := Option.some.inj hk.symm
      subst k
      change (0:ℕ)<1
      decide)
  · intro h i hi _
    fin_cases i
    · exact h
    · simp [s2,s1,s0,FP.append,FP.initialState,e1] at hi

theorem no_remaining_integer (z : P×ℝ) (hi : z∈FP.epigraph pump s2)
    (hn : 0≤e0.normal z.1) (hc : FP.noGoods s2 z.1) : False := by
  have hs := hc e1 (by simp [s2,s1,s0,FP.append,FP.initialState]) (by simp [e1])
  rw [normal_formula] at hn
  rcases integer_y_cases z.1 (FPAdapters.epigraph_integer_box hi) with hy|hy
  · rw [hy] at hn; norm_num at hn
  · apply hs
    funext j; fin_cases j
    simpa [e1,FP.intCast,target1] using hy

theorem master2_empty : ¬ (FP.master pump s2).Nonempty := by
  rintro ⟨z,hz⟩
  exact no_remaining_integer z hz.1
    (hz.2.1 e0 (by simp [s2,s1,s0,FP.append,FP.initialState]) rfl) hz.2.2.1

theorem handoff_empty : FP.handoff pump s2=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact no_remaining_integer z hz.1 ((handoff_keeps_normal z.1).mp hz.2.1) hz.2.2

end Chapter03.PumpOA.Retained
