module

public import Chapter07UnseededControlData
public import Chapter07UnseededExecution

@[expose] public section

/-! Exact retained-cut master sequences for the two nonlinear unseeded controls.
No historical numerical performance or executable commercial solver is claimed. -/
noncomputable section
open Set Chapter02 Chapter06.Level
namespace Chapter07.UnseededControl

theorem box_point_mixed (f g : P → ℝ) (x : ℝ) (y : ℤ)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hy0 : (0:ℝ) ≤ y) (hy1 : (y:ℝ) ≤ 1) :
    pt x (y : ℝ) ∈ (boxData f g).mixed :=
  ⟨(box_hard_iff f g _).mpr ⟨hx0,hx1,hy0,hy1⟩,iy y,pt_intCast x y⟩

namespace Feasible

def p0 : P × ℝ := (pt (-3/16) 0,3/16)
def p1 : P × ℝ := (pt (13/16) 1,3/16)
def p2 : P × ℝ := (optimum,1/4)

theorem seed_rows_iff (q : P) : selectedRows d a0 0 q ↔
    q.1 0-q.2 0+3/16 ≤ 0 := by
  rw [selected_single_iff d a0 q 0 (by norm_num [d,boxData,g,a0,pt,Chapter06.LevelControl.pt])]
  rw [soft_tangent]
  norm_num [a0,pt,Chapter06.LevelControl.pt]
  constructor <;> intro h <;> linarith

theorem restored_rows_iff (q : P) : selectedRows d restored (7/16) q ↔
    (7/16:ℝ) ≤ q.2 0 := by
  rw [selected_single_iff d restored q (7/16)
    (by norm_num [d,boxData,g,restored,pt,Chapter06.LevelControl.pt])]
  rw [soft_tangent]
  norm_num [restored,pt,Chapter06.LevelControl.pt]

theorem optimum_rows_iff (q : P) : selectedRows d optimum 0 q ↔
    (3/2)*q.1 0-q.2 0-1/8 ≤ 0 := by
  rw [selected_single_iff d optimum q 0
    (by norm_num [d,boxData,g,optimum,pt,Chapter06.LevelControl.pt])]
  rw [soft_tangent]
  norm_num [optimum,pt,Chapter06.LevelControl.pt]
  constructor <;> intro h <;> linarith

theorem initial_master_iff (z : P × ℝ) : z ∈ master d a0 [] ↔
    z.1 ∈ d.mixed ∧ z.1.1 0-z.1.2 0+3/16 ≤ 0 ∧ z.1.2 0-z.1.1 0 ≤ z.2 := by
  simp [master,masterBase,pscEnvelopeEpigraph,pscEnvelopeRows,origins,
    seed_rows_iff,objective_tangent,and_assoc]

theorem second_master_iff (z : P × ℝ) : z ∈ master d a0 [restoredEvent] ↔
    z.1 ∈ d.mixed ∧ z.1.1 0-z.1.2 0+3/16 ≤ 0 ∧
      (7/16:ℝ) ≤ z.1.2 0 ∧ z.1.2 0-z.1.1 0 ≤ z.2 := by
  simp [master,masterBase,pscEnvelopeEpigraph,pscEnvelopeRows,origins,
    restoredEvent,Event.rho,seed_rows_iff,restored_rows_iff,objective_tangent,and_assoc]
  tauto

theorem third_master_iff (z : P × ℝ) : z ∈ master d a0 [feasibleEvent,restoredEvent] ↔
    z.1 ∈ d.mixed ∧ z.1.1 0-z.1.2 0+3/16 ≤ 0 ∧
      (3/2)*z.1.1 0-z.1.2 0-1/8 ≤ 0 ∧ (7/16:ℝ) ≤ z.1.2 0 ∧
      z.1.2 0-z.1.1 0 ≤ z.2 := by
  simp [master,masterBase,pscEnvelopeEpigraph,pscEnvelopeRows,origins,
    feasibleEvent,restoredEvent,Event.rho,seed_rows_iff,optimum_rows_iff,
    restored_rows_iff,objective_tangent,and_assoc]
  tauto

theorem initial_master_minimum : IsMinimizer (master d a0 []) Prod.snd p0 := by
  refine ⟨(initial_master_iff p0).mpr ⟨?_,?_,?_⟩,?_⟩
  · change p0.1 ∈ (boxData f g).mixed
    simpa [p0] using box_point_mixed f g (-3/16) 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num [p0,pt,Chapter06.LevelControl.pt]
  · norm_num [p0,pt,Chapter06.LevelControl.pt]
  · intro z hz
    obtain ⟨_,hs,ho⟩ := (initial_master_iff z).mp hz
    change (3/16:ℝ) ≤ z.2
    linarith

theorem second_master_minimum : IsMinimizer (master d a0 [restoredEvent]) Prod.snd p1 := by
  refine ⟨(second_master_iff p1).mpr ⟨?_,?_,?_,?_⟩,?_⟩
  · change p1.1 ∈ (boxData f g).mixed
    simpa [p1] using box_point_mixed f g (13/16) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num [p1,pt,Chapter06.LevelControl.pt]
  · norm_num [p1,pt,Chapter06.LevelControl.pt]
  · norm_num [p1,pt,Chapter06.LevelControl.pt]
  · intro z hz
    obtain ⟨_,hs,_,ho⟩ := (second_master_iff z).mp hz
    change (3/16:ℝ) ≤ z.2
    linarith

theorem third_master_minimum :
    IsMinimizer (master d a0 [feasibleEvent,restoredEvent]) Prod.snd p2 := by
  refine ⟨(third_master_iff p2).mpr ⟨?_,?_,?_,?_,?_⟩,?_⟩
  · change p2.1 ∈ (boxData f g).mixed
    simpa [p2,optimum] using box_point_mixed f g (3/4) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num [p2,optimum,pt,Chapter06.LevelControl.pt]
  · norm_num [p2,optimum,pt,Chapter06.LevelControl.pt]
  · norm_num [p2,optimum,pt,Chapter06.LevelControl.pt]
  · norm_num [p2,optimum,pt,Chapter06.LevelControl.pt]
  · intro z hz
    obtain ⟨hm,_,hf,hr,ho⟩ := (third_master_iff z).mp hz
    change (1/4:ℝ) ≤ z.2
    rcases box_integer_cases f g hm with hy | hy <;> linarith

/-- The restoration event is legitimate even though its anchor violates the
initial OA row; source events require hard-fiber membership instead. -/
theorem restoration_outside_initial_base : restored ∉ masterBase d a0 [] := by
  intro h
  have hs := (seed_rows_iff restored).mp h.2.1
  norm_num [restored,pt,Chapter06.LevelControl.pt] at hs

theorem warm_incumbent :
    incumbent d optimum [feasibleEvent,restoredEvent] = optimum := by
  simp [incumbent,feasibleEvent,restoredEvent,keepBetter]

theorem exact_closing_gap :
    d.f (incumbent d optimum [feasibleEvent,restoredEvent])-p2.2 = 0 := by
  rw [warm_incumbent]
  norm_num [d,boxData,f,optimum,p2,pt,Chapter06.LevelControl.pt]

theorem exact_optimum : ∀ q ∈ d.original, d.f optimum ≤ d.f q := by
  intro q hq
  have h := master_lower_bound regularity third_master_minimum hq
  norm_num [p2,d,boxData,f,optimum,pt,Chapter06.LevelControl.pt] at h ⊢
  exact h

theorem feasible_slater_witness :
    pt 0 1 ∈ d.feasibleFiber (iy 1) ∧ d.g 0 (pt 0 1) = -9/16 := by
  refine ⟨⟨⟨(box_hard_iff _ _ _).mpr ?_,by simpa using pt_intCast 0 1⟩,?_⟩,?_⟩
  · norm_num [pt,Chapter06.LevelControl.pt]
  · intro j; norm_num [d,boxData,g,pt,Chapter06.LevelControl.pt]
  · norm_num [d,boxData,g,pt,Chapter06.LevelControl.pt]

theorem target_count : (targets d regularity).card = 2 := box_target_count f g regularity

end Feasible
namespace Infeasible

def p0 : P × ℝ := (pt 0 0,0)
def p1 : P × ℝ := (pt 0 1,0)

theorem seed_rows (q : P) : selectedRows d a0 0 q := by
  intro j hj
  norm_num [d,boxData,g,a0,pt,Chapter06.LevelControl.pt] at hj

theorem restored0_rows_iff (q : P) : selectedRows d restored0 (3/16) q ↔
    (3/16:ℝ) ≤ q.2 0 := by
  rw [selected_single_iff d restored0 q (3/16)
    (by norm_num [d,boxData,g,restored0,pt,Chapter06.LevelControl.pt])]
  rw [soft_tangent]
  norm_num [restored0,pt,Chapter06.LevelControl.pt]

theorem restored1_rows_iff (q : P) : selectedRows d restored1 (3/16) q ↔
    q.2 0 ≤ 13/16 := by
  rw [selected_single_iff d restored1 q (3/16)
    (by norm_num [d,boxData,g,restored1,pt,Chapter06.LevelControl.pt])]
  rw [soft_tangent]
  norm_num [restored1,pt,Chapter06.LevelControl.pt]
  constructor <;> intro h <;> linarith

theorem initial_master_iff (z : P × ℝ) : z ∈ master d a0 [] ↔
    z.1 ∈ d.mixed ∧ 0 ≤ z.2 := by
  simp [master,masterBase,pscEnvelopeEpigraph,pscEnvelopeRows,origins,
    seed_rows,objective_tangent,a0,pt,Chapter06.LevelControl.pt,and_assoc]
  intro _ _
  simpa [a0,pt,Chapter06.LevelControl.pt] using seed_rows z.1

theorem second_master_iff (z : P × ℝ) : z ∈ master d a0 [event0] ↔
    z.1 ∈ d.mixed ∧ (3/16:ℝ) ≤ z.1.2 0 ∧ 0 ≤ z.2 := by
  simp [master,masterBase,pscEnvelopeEpigraph,pscEnvelopeRows,origins,
    event0,Event.rho,seed_rows,restored0_rows_iff,objective_tangent,
    a0,restored0,pt,Chapter06.LevelControl.pt,and_assoc]
  have hs := seed_rows z.1
  have hr := restored0_rows_iff z.1
  simp [a0,pt,Chapter06.LevelControl.pt] at hs
  norm_num [restored0,pt,Chapter06.LevelControl.pt] at hr
  tauto

theorem third_master_iff (z : P × ℝ) : z ∈ master d a0 [event1,event0] ↔
    z.1 ∈ d.mixed ∧ z.1.2 0 ≤ 13/16 ∧ (3/16:ℝ) ≤ z.1.2 0 ∧ 0 ≤ z.2 := by
  simp [master,masterBase,pscEnvelopeEpigraph,pscEnvelopeRows,origins,
    event1,event0,Event.rho,seed_rows,restored1_rows_iff,restored0_rows_iff,
    objective_tangent,a0,restored0,restored1,pt,Chapter06.LevelControl.pt,and_assoc]
  have hs := seed_rows z.1
  have h0 := restored0_rows_iff z.1
  have h1 := restored1_rows_iff z.1
  simp [a0,pt,Chapter06.LevelControl.pt] at hs
  norm_num [restored0,restored1,pt,Chapter06.LevelControl.pt] at h0 h1
  tauto

theorem initial_master_minimum : IsMinimizer (master d a0 []) Prod.snd p0 := by
  refine ⟨(initial_master_iff p0).mpr ⟨?_,by norm_num [p0]⟩,?_⟩
  · change p0.1 ∈ (boxData f g).mixed
    simpa [p0] using box_point_mixed f g 0 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro z hz
    exact ((initial_master_iff z).mp hz).2

theorem second_master_minimum : IsMinimizer (master d a0 [event0]) Prod.snd p1 := by
  refine ⟨(second_master_iff p1).mpr ⟨?_,?_,by norm_num [p1]⟩,?_⟩
  · change p1.1 ∈ (boxData f g).mixed
    simpa [p1] using box_point_mixed f g 0 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num [p1,pt,Chapter06.LevelControl.pt]
  · intro z hz
    exact ((second_master_iff z).mp hz).2.2

theorem third_master_empty : ¬ (master d a0 [event1,event0]).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨hm,hu,hl,_⟩ := (third_master_iff z).mp hz
  rcases box_integer_cases f g hm with hy | hy <;> linarith

theorem continuous_feasible_integer_infeasible :
    (Unseeded.relaxation d).Nonempty ∧ ¬ d.original.Nonempty :=
  ⟨⟨a0,initializer_minimum.1⟩,Unseeded.master_empty_original_empty regularity third_master_empty⟩

theorem target_count : (targets d regularity).card = 2 := box_target_count f g regularity

end Infeasible

/-! These finite overrides choose actual legal exact subproblem solutions.
The default selector remains available on every other state. -/
open Chapter07.UnseededExec

namespace Feasible

def s0 : State d := initial d
def s1 : State d := advance s0 restoredEvent
def s2 : State d := advance s1 feasibleEvent

def answer : {u : P // u ∈ d.original} :=
  ⟨optimum, feasibleEvent.feasible_original rfl⟩

theorem s2_baseline : s2.baseline = some answer := by
  simp [s2,s1,s0,advance,initial,restoredEvent,feasibleEvent,answer]

def decision0 : Decision d a0 (1/2) 0 s0 :=
  ⟨.process restoredEvent, Or.inl ⟨rfl,p0,initial_master_minimum,
    by simpa [p0,restoredEvent] using pt_intCast (-3/16) 0⟩⟩

def decision1 : Decision d a0 (1/2) 0 s1 := by
  refine ⟨.process feasibleEvent, Or.inl ⟨?_,p1,second_master_minimum,?_⟩⟩
  · simp [s1,s0,advance,initial,restoredEvent]
  · simpa [p1,feasibleEvent] using pt_intCast (13/16) 1

def decision2 : Decision d a0 (1/2) 0 s2 := by
  refine ⟨.returned optimum,answer,s2_baseline,?_,p2,third_master_minimum,?_⟩
  · exact warm_incumbent.symm
  · exact le_of_eq exact_closing_gap

def select : Selector d a0 (1/2) 0 :=
  withDecision (withDecision (withDecision
    (exactSelector regularity a0 (by norm_num) (by norm_num))
    s2 decision2) s1 decision1) s0 decision0

theorem select0 : (select s0).action = .process restoredEvent := by
  rw [select,withDecision_at]
  rfl

theorem s1_ne_s0 : s1 ≠ s0 := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [s1,s0,advance,initial] at hlen

theorem s2_ne_s0 : s2 ≠ s0 := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [s2,s1,s0,advance,initial] at hlen

theorem s2_ne_s1 : s2 ≠ s1 := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [s2,s1,s0,advance,initial] at hlen

theorem select1 : (select s1).action = .process feasibleEvent := by
  rw [select,withDecision_away _ _ _ _ s1_ne_s0,withDecision_at]
  rfl

theorem select2 : (select s2).action = .returned optimum := by
  rw [select,withDecision_away _ _ _ _ s2_ne_s0,
    withDecision_away _ _ _ _ s2_ne_s1,withDecision_at]
  rfl

/-- The actual driver returns after exactly two processed fibers and three
master queries, retaining the original initializer and both event cuts. -/
theorem exact_replay : run select 2 s0 = ⟨s2,.returned optimum,2,3⟩ := by
  calc
    run select 2 s0 = countStep (run select 1 s1) :=
      run_process_succ select 1 s0 restoredEvent select0
    _ = countStep (countStep (run select 0 s2)) :=
      congrArg countStep (run_process_succ select 0 s1 feasibleEvent select1)
    _ = ⟨s2,.returned optimum,2,3⟩ := by
      rw [run_returned select 0 s2 optimum select2]
      rfl

theorem exact_source_control :
    IsMinimizer (Unseeded.relaxation d) d.f a0 ∧
    (run select 2 s0).outcome = .returned optimum ∧
    (run select 2 s0).processed = 2 ∧ (run select 2 s0).queries = 3 ∧
    (run select 2 s0).state.history = [feasibleEvent,restoredEvent] ∧
    (run select 2 s0).state.baseline = some answer := by
  rw [exact_replay]
  exact ⟨initializer_minimum,rfl,rfl,rfl,rfl,s2_baseline⟩

end Feasible
namespace Infeasible

def s0 : State d := initial d
def s1 : State d := advance s0 event0
def s2 : State d := advance s1 event1

def decision0 : Decision d a0 (1/2) 0 s0 :=
  ⟨.process event0, Or.inl ⟨rfl,p0,initial_master_minimum,
    by simpa [p0,event0] using pt_intCast 0 0⟩⟩

def decision1 : Decision d a0 (1/2) 0 s1 := by
  refine ⟨.process event1, Or.inl ⟨?_,p1,second_master_minimum,?_⟩⟩
  · simp [s1,s0,advance,initial,event0]
  · simpa [p1,event1] using pt_intCast 0 1

def decision2 : Decision d a0 (1/2) 0 s2 := ⟨.infeasible,third_master_empty⟩

def select : Selector d a0 (1/2) 0 :=
  withDecision (withDecision (withDecision
    (exactSelector regularity a0 (by norm_num) (by norm_num))
    s2 decision2) s1 decision1) s0 decision0

theorem select0 : (select s0).action = .process event0 := by
  rw [select,withDecision_at]
  rfl

theorem s1_ne_s0 : s1 ≠ s0 := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [s1,s0,advance,initial] at hlen

theorem s2_ne_s0 : s2 ≠ s0 := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [s2,s1,s0,advance,initial] at hlen

theorem s2_ne_s1 : s2 ≠ s1 := by
  intro h
  have hlen := congrArg (fun s : State d => s.history.length) h
  norm_num [s2,s1,s0,advance,initial] at hlen

theorem select1 : (select s1).action = .process event1 := by
  rw [select,withDecision_away _ _ _ _ s1_ne_s0,withDecision_at]
  rfl

theorem select2 : (select s2).action = .infeasible := by
  rw [select,withDecision_away _ _ _ _ s2_ne_s0,
    withDecision_away _ _ _ _ s2_ne_s1,withDecision_at]
  rfl

/-- A continuously feasible but integer-infeasible problem is detected by
the actual third master query, after exactly two legitimate restorations. -/
theorem exact_replay : run select 2 s0 = ⟨s2,.infeasible,2,3⟩ := by
  calc
    run select 2 s0 = countStep (run select 1 s1) :=
      run_process_succ select 1 s0 event0 select0
    _ = countStep (countStep (run select 0 s2)) :=
      congrArg countStep (run_process_succ select 0 s1 event1 select1)
    _ = ⟨s2,.infeasible,2,3⟩ := by
      rw [run_infeasible select 0 s2 select2]
      rfl

theorem exact_source_control :
    IsMinimizer (Unseeded.relaxation d) d.f a0 ∧
    (run select 2 s0).outcome = .infeasible ∧
    (run select 2 s0).processed = 2 ∧ (run select 2 s0).queries = 3 ∧
    (run select 2 s0).state.history = [event1,event0] ∧
    (run select 2 s0).state.baseline = none := by
  rw [exact_replay]
  refine ⟨initializer_minimum,rfl,rfl,rfl,rfl,?_⟩
  simp [s2,s1,s0,advance,initial,event0,event1]

end Infeasible

end Chapter07.UnseededControl

#print axioms Chapter07.UnseededControl.Feasible.seed_rows_iff
#print axioms Chapter07.UnseededControl.Feasible.restored_rows_iff
#print axioms Chapter07.UnseededControl.Feasible.optimum_rows_iff
#print axioms Chapter07.UnseededControl.Feasible.initial_master_iff
#print axioms Chapter07.UnseededControl.Feasible.second_master_iff
#print axioms Chapter07.UnseededControl.Feasible.third_master_iff
#print axioms Chapter07.UnseededControl.Feasible.initial_master_minimum
#print axioms Chapter07.UnseededControl.Feasible.second_master_minimum
#print axioms Chapter07.UnseededControl.Feasible.third_master_minimum
#print axioms Chapter07.UnseededControl.Feasible.restoration_outside_initial_base
#print axioms Chapter07.UnseededControl.Feasible.warm_incumbent
#print axioms Chapter07.UnseededControl.Feasible.exact_closing_gap
#print axioms Chapter07.UnseededControl.Feasible.exact_optimum
#print axioms Chapter07.UnseededControl.Feasible.feasible_slater_witness
#print axioms Chapter07.UnseededControl.Feasible.target_count
#print axioms Chapter07.UnseededControl.Infeasible.seed_rows
#print axioms Chapter07.UnseededControl.Infeasible.restored0_rows_iff
#print axioms Chapter07.UnseededControl.Infeasible.restored1_rows_iff
#print axioms Chapter07.UnseededControl.Infeasible.initial_master_iff
#print axioms Chapter07.UnseededControl.Infeasible.second_master_iff
#print axioms Chapter07.UnseededControl.Infeasible.third_master_iff
#print axioms Chapter07.UnseededControl.Infeasible.initial_master_minimum
#print axioms Chapter07.UnseededControl.Infeasible.second_master_minimum
#print axioms Chapter07.UnseededControl.Infeasible.third_master_empty
#print axioms Chapter07.UnseededControl.Infeasible.continuous_feasible_integer_infeasible
#print axioms Chapter07.UnseededControl.Infeasible.target_count

#print axioms Chapter07.UnseededControl.Feasible.exact_replay
#print axioms Chapter07.UnseededControl.Feasible.exact_source_control
#print axioms Chapter07.UnseededControl.Infeasible.exact_replay
#print axioms Chapter07.UnseededControl.Infeasible.exact_source_control
