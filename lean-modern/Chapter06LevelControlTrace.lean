module

public import Chapter06LevelControlData
public import Chapter06LevelExecution

@[expose] public section

/-! Exact source-level two-event trace of the repaired fresh-bound driver.
The selectors are level feasible; no projection-minimality claim is made. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter06.Level
namespace Chapter06.LevelControl

def restoreEvent : Event d := ⟨iy 2,restored,some (1/2),fiber_two_infeasible,restoration_minimum⟩
def polishEvent : Event d := ⟨iy 1,optimum,none,feasible_minimum⟩

@[simp] theorem incumbent_restoration : incumbent d seed [restoreEvent]=seed := rfl
@[simp] theorem incumbent_polish : incumbent d seed [polishEvent,restoreEvent]=optimum := by
  norm_num [incumbent,polishEvent,restoreEvent,keepBetter,optimum_value,seed_value]

def trial0 : P × ℝ := (pt 0 2,-5)
def trial1 : P × ℝ := (optimum,-2)
def closing : P × ℝ := (optimum,-7/4)

theorem master0_iff (z : P × ℝ) : z ∈ master d seed [] ↔
    z.1 ∈ d.mixed ∧ 2*z.1.1 0-2*z.1.2 0-1≤z.2 := by
  simp [master,pscEnvelopeEpigraph,masterBase,seed_rows,origins,pscEnvelopeRows]
  norm_num [objective_tangent,seed,pt]

theorem master1_iff (z : P × ℝ) : z ∈ master d seed [restoreEvent] ↔
    z.1 ∈ d.mixed ∧ d.g 0 z.1≤0 ∧ 2*z.1.1 0-2*z.1.2 0-1≤z.2 := by
  have hrows := restoration_rows z.1
  norm_num [restored,pt] at hrows
  simp [master,pscEnvelopeEpigraph,masterBase,seed_rows,origins,pscEnvelopeRows,
    restoreEvent,Event.rho,restoration_rows,and_assoc]
  norm_num [objective_tangent,seed,restored,pt,hrows]

theorem master2_iff (z : P × ℝ) : z ∈ master d seed [polishEvent,restoreEvent] ↔
    z.1 ∈ d.mixed ∧ d.g 0 z.1≤0 ∧
      (2*z.1.1 0-2*z.1.2 0-1≤z.2) ∧ (z.1.1 0-2*z.1.2 0-1/4≤z.2) := by
  have hrows := restoration_rows z.1
  norm_num [restored,pt] at hrows
  simp [master,pscEnvelopeEpigraph,masterBase,seed_rows,origins,pscEnvelopeRows,
    polishEvent,restoreEvent,Event.rho,optimum_rows,restoration_rows,and_assoc]
  norm_num [objective_tangent,seed,restored,optimum,pt,hrows,and_assoc,and_left_comm,and_comm]
  tauto

theorem mixed_pt (x : ℝ) (y : ℤ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤(y:ℝ)) (hy2 : (y:ℝ)≤2) : pt x y ∈ d.mixed := by
  exact ⟨(hard_iff _).mpr ⟨hx0,hx1,hy0,hy2⟩,iy y,rfl⟩

theorem master0_minimum : IsMinimizer (master d seed []) Prod.snd trial0 := by
  refine ⟨(master0_iff _).mpr ⟨?_,by norm_num [trial0,pt]⟩,?_⟩
  · convert mixed_pt 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;>
      norm_num [trial0, pt]
  · intro z hz
    obtain ⟨hm,ht⟩ := (master0_iff z).mp hz
    have hh := (hard_iff z.1).mp hm.1
    change (-5:ℝ)≤z.2
    linarith

theorem master1_minimum : IsMinimizer (master d seed [restoreEvent]) Prod.snd trial1 := by
  refine ⟨(master1_iff _).mpr ⟨(feasibleFiber_original d (iy 1) optimum_fiber).1,?_,?_⟩,?_⟩
  · norm_num [trial1,d,optimum,pt]
  · norm_num [trial1,optimum,pt]
  · intro z hz
    obtain ⟨hm,hg,ht⟩ := (master1_iff z).mp hz
    change z.1.2 0-z.1.1 0-1/2≤0 at hg
    change (-2:ℝ)≤z.2
    linarith

theorem mixed_soft_y_le_one {q : P} (hq : q∈d.mixed) (hg : d.g 0 q≤0) : q.2 0≤1 := by
  have hh := (hard_iff q).mp hq.1
  obtain ⟨y,hy⟩ := hq.2
  have he : q.2 0=(y 0:ℝ) := congrFun hy 0
  change q.2 0-q.1 0-1/2≤0 at hg
  have hlt : (y 0:ℝ)<2 := by linarith
  have hint : y 0<2 := by exact_mod_cast hlt
  have hle : (y 0:ℝ)≤1 := by exact_mod_cast (show y 0≤1 by omega)
  linarith

theorem master2_minimum : IsMinimizer (master d seed [polishEvent,restoreEvent]) Prod.snd closing := by
  refine ⟨(master2_iff _).mpr ⟨(feasibleFiber_original d (iy 1) optimum_fiber).1,?_,?_,?_⟩,?_⟩
  · norm_num [closing,d,optimum,pt]
  · norm_num [closing,optimum,pt]
  · norm_num [closing,optimum,pt]
  · intro z hz
    obtain ⟨hm,hg,h0,h1⟩ := (master2_iff z).mp hz
    have hy := mixed_soft_y_le_one hm hg
    change z.1.2 0-z.1.1 0-1/2≤0 at hg
    change (-7/4:ℝ)≤z.2
    linarith

theorem optimum_global_minimum : IsMinimizer d.original d.f optimum := by
  refine ⟨feasibleFiber_original d (iy 1) optimum_fiber,?_⟩
  intro q hq
  rw [optimum_value]
  exact master_lower_bound regularity master2_minimum hq

def chooseMaster (H : List (Event d)) : {p // IsMinimizer (master d seed H) Prod.snd p} := by
  classical
  by_cases h0 : H=[]
  · subst H; exact ⟨trial0,master0_minimum⟩
  by_cases h1 : H=[restoreEvent]
  · subst H; exact ⟨trial1,master1_minimum⟩
  by_cases h2 : H=[polishEvent,restoreEvent]
  · subst H; exact ⟨closing,master2_minimum⟩
  exact (Exec.exactSelector regularity seed_feasible (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)≤1)).master H

def chooseEvent (q : P) (hq : q∈d.mixed) :
    {e : Event d // q.2=Chapter06.Level.intCast e.target} := by
  classical
  by_cases h2 : q.2=Chapter06.Level.intCast (iy 2)
  · exact ⟨restoreEvent,h2⟩
  by_cases h1 : q.2=Chapter06.Level.intCast (iy 1)
  · exact ⟨polishEvent,h1⟩
  exact (Exec.exactSelector regularity seed_feasible (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)≤1)).event q hq

def select : Exec.Selector d seed (1/2) where
  master := chooseMaster
  trial H p hp := ⟨p,level_available regularity seed_feasible hp (by norm_num) (by norm_num)⟩
  event := chooseEvent

@[simp] theorem selected_master0 : (select.master []).val=trial0 := by
  simp [select,chooseMaster]
@[simp] theorem selected_master1 : (select.master [restoreEvent]).val=trial1 := by
  simp [select,chooseMaster]
@[simp] theorem selected_master2 : (select.master [polishEvent,restoreEvent]).val=closing := by
  simp [select,chooseMaster]

theorem chooseEvent_two {q : P} (hq : q∈d.mixed)
    (hy : q.2=Chapter06.Level.intCast (iy 2)) : (chooseEvent q hq).val=restoreEvent := by
  simp [chooseEvent,hy]

theorem chooseEvent_one {q : P} (hq : q∈d.mixed)
    (hy : q.2=Chapter06.Level.intCast (iy 1)) : (chooseEvent q hq).val=polishEvent := by
  have hn : q.2≠Chapter06.Level.intCast (iy 2) := by
    intro he
    have hh := Chapter06.Level.intCast_injective (hy.symm.trans he)
    have h0 := congrFun hh 0
    norm_num [iy] at h0
  have hn' : Chapter06.Level.intCast (iy 1)≠Chapter06.Level.intCast (iy 2) := by
    intro he; exact hn (hy.trans he)
  simp [chooseEvent,hy,hn']

theorem nextEvent0 : Exec.nextEvent select []=restoreEvent := by
  change (chooseEvent (select.master []).val.1 _).val=restoreEvent
  apply chooseEvent_two
  rw [selected_master0]
  funext i
  change (2:ℝ)=((2:ℤ):ℝ)
  norm_num

theorem nextEvent1 : Exec.nextEvent select [restoreEvent]=polishEvent := by
  change (chooseEvent (select.master [restoreEvent]).val.1 _).val=polishEvent
  apply chooseEvent_one
  rw [selected_master1]
  funext i
  change (1:ℝ)=((1:ℤ):ℝ)
  norm_num

theorem targets_exact : targets d regularity={iy 0,iy 1,iy 2} := by
  classical
  ext y
  rw [mem_targets]
  constructor
  · rintro ⟨p,hp,hy⟩
    have hh := (hard_iff p).mp hp
    have he : p.2 0=(y 0:ℝ) := congrFun hy 0
    have h0 : (0:ℝ)≤(y 0:ℝ) := by linarith
    have h2 : (y 0:ℝ)≤2 := by linarith
    have hi0 : 0≤y 0 := by exact_mod_cast h0
    have hi2 : y 0≤2 := by exact_mod_cast h2
    have hc : y 0=0 ∨ y 0=1 ∨ y 0=2 := by omega
    rcases hc with hy0 | hy1 | hy2
    · have heq : y=iy 0 := by funext i; fin_cases i; exact hy0
      simp [heq]
    · have heq : y=iy 1 := by funext i; fin_cases i; exact hy1
      simp [heq]
    · have heq : y=iy 2 := by funext i; fin_cases i; exact hy2
      simp [heq]
  · intro hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨pt 0 0,(hard_iff _).mpr (by norm_num [pt]),by
        funext i; change (0:ℝ)=((0:ℤ):ℝ); norm_num⟩
    · exact ⟨pt 0 1,(hard_iff _).mpr (by norm_num [pt]),by
        funext i; change (1:ℝ)=((1:ℤ):ℝ); norm_num⟩
    · exact ⟨pt 0 2,(hard_iff _).mpr (by norm_num [pt]),by
        funext i; change (2:ℝ)=((2:ℤ):ℝ); norm_num⟩

theorem targets_card : (targets d regularity).card=3 := by
  classical
  norm_num [targets_exact,iy,funext_iff,Fin.forall_fin_one]

theorem run_zero : Exec.run select 0 3 [] =
    ⟨[polishEvent,restoreEvent],some optimum,2,3⟩ := by
  have ho0 : ¬(d.f (incumbent d seed [])-(select.master []).val.2≤0) := by
    rw [selected_master0]
    norm_num [incumbent,seed_value,trial0]
  have ho1 : ¬(d.f (incumbent d seed [restoreEvent])-
      (select.master [restoreEvent]).val.2≤0) := by
    rw [incumbent_restoration,selected_master1]
    norm_num [seed_value,trial1]
  have hc2 : d.f (incumbent d seed [polishEvent,restoreEvent])-
      (select.master [polishEvent,restoreEvent]).val.2≤0 := by
    rw [incumbent_polish,selected_master2]
    norm_num [optimum_value,closing]
  rw [Exec.run_open_succ select 2 [] ho0,nextEvent0,
    Exec.run_open_succ select 1 [restoreEvent] ho1,nextEvent1,
    Exec.run_closed select 1 [polishEvent,restoreEvent] hc2]
  simp [Exec.countStep,Exec.closedResult]

theorem solve_zero : Exec.solve regularity select 0 =
    ⟨[polishEvent,restoreEvent],some optimum,2,3⟩ := by
  rw [Exec.solve,targets_card]
  exact run_zero

theorem solve_six : Exec.solve regularity select 6=⟨[],some seed,0,1⟩ := by
  unfold Exec.solve
  rw [Exec.run_closed select _ [] (by
    rw [selected_master0]
    norm_num [incumbent,seed_value,trial0])]
  rfl

theorem zero_stored_correct : Exec.StoredCorrect d seed 0
    [polishEvent,restoreEvent] optimum := by
  obtain ⟨u,hu,hcorrect⟩ :=
    (Exec.source_seeded_return regularity seed_feasible
      (by norm_num : (0:ℝ)<1/2) (by norm_num) (by norm_num : (0:ℝ)≤0) select).2.2.1
  rw [solve_zero] at hu hcorrect
  cases Option.some.inj hu
  exact hcorrect

theorem six_stored_correct : Exec.StoredCorrect d seed 6 [] seed := by
  obtain ⟨u,hu,hcorrect⟩ :=
    (Exec.source_seeded_return regularity seed_feasible
      (by norm_num : (0:ℝ)<1/2) (by norm_num) (by norm_num : (0:ℝ)≤6) select).2.2.1
  rw [solve_six] at hu hcorrect
  cases Option.some.inj hu
  exact hcorrect

theorem epsilon_six_nonexact : d.f seed-d.f optimum=11/4 ∧ d.f optimum<d.f seed := by
  norm_num [seed_value,optimum_value]

end Chapter06.LevelControl

#print axioms Chapter06.LevelControl.restoreEvent
#print axioms Chapter06.LevelControl.polishEvent
#print axioms Chapter06.LevelControl.incumbent_restoration
#print axioms Chapter06.LevelControl.incumbent_polish
#print axioms Chapter06.LevelControl.trial0
#print axioms Chapter06.LevelControl.trial1
#print axioms Chapter06.LevelControl.closing
#print axioms Chapter06.LevelControl.master0_iff
#print axioms Chapter06.LevelControl.master1_iff
#print axioms Chapter06.LevelControl.master2_iff
#print axioms Chapter06.LevelControl.mixed_pt
#print axioms Chapter06.LevelControl.master0_minimum
#print axioms Chapter06.LevelControl.master1_minimum
#print axioms Chapter06.LevelControl.mixed_soft_y_le_one
#print axioms Chapter06.LevelControl.master2_minimum
#print axioms Chapter06.LevelControl.optimum_global_minimum
#print axioms Chapter06.LevelControl.chooseMaster
#print axioms Chapter06.LevelControl.chooseEvent
#print axioms Chapter06.LevelControl.select
#print axioms Chapter06.LevelControl.selected_master0
#print axioms Chapter06.LevelControl.selected_master1
#print axioms Chapter06.LevelControl.selected_master2
#print axioms Chapter06.LevelControl.chooseEvent_two
#print axioms Chapter06.LevelControl.chooseEvent_one
#print axioms Chapter06.LevelControl.nextEvent0
#print axioms Chapter06.LevelControl.nextEvent1
#print axioms Chapter06.LevelControl.targets_exact
#print axioms Chapter06.LevelControl.targets_card
#print axioms Chapter06.LevelControl.run_zero
#print axioms Chapter06.LevelControl.solve_zero
#print axioms Chapter06.LevelControl.solve_six
#print axioms Chapter06.LevelControl.zero_stored_correct
#print axioms Chapter06.LevelControl.six_stored_correct
#print axioms Chapter06.LevelControl.epsilon_six_nonexact
