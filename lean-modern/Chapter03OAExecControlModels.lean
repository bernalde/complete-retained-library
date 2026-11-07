module

public import Chapter03OAExecControlU
public import Chapter03OAExecControlI
public import Chapter03OAExecHistory

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Controls

def target0 : IntVector 1 := fun _ => 0
def target1 : IntVector 1 := fun _ => 1

theorem target0_mem : target0∈IntegerBox (scalar 0) (scalar 1) := by
  intro i; norm_num [target0,scalar]
theorem target1_mem : target1∈IntegerBox (scalar 0) (scalar 1) := by
  intro i; norm_num [target1,scalar]

theorem target_cases (y : IntVector 1) (hy : y∈IntegerBox (scalar 0) (scalar 1)) :
    y=target0 ∨ y=target1 := by
  have hyl : (0:ℝ)≤(y 0:ℝ) := (hy 0).1
  have hyu : (y 0:ℝ)≤(1:ℝ) := (hy 0).2
  have hl : (0:ℤ)≤y 0 := by exact_mod_cast hyl
  have hu : y 0≤(1:ℤ) := by exact_mod_cast hyu
  have hh : y 0=0 ∨ y 0=1 := by omega
  rcases hh with h|h
  · left; funext i; fin_cases i; exact h
  · right; funext i; fin_cases i; exact h

@[simp] theorem cast_target0 : intCast target0=scalar 0 := by ext i; simp [intCast,target0,scalar]
@[simp] theorem cast_target1 : intCast target1=scalar 1 := by ext i; simp [intCast,target1,scalar]

theorem event_ext {n m l r : ℕ} {d : Data n m l r} {e e' : Event d}
    (ht : e.target=e'.target) (hx : e.x=e'.x) (hs : e.restoration=e'.restoration) : e=e' := by
  cases e; cases e'; simp_all

namespace U
def spec : Data 1 1 5 0 where
  model := data
  f := objective
  Df := Df
  Dg := Dg
  domain := Set.univ

theorem analytic : Analytic spec where
  convex_f := objective_convex
  convex_g := row_convex
  original_domain := by intro p hp; trivial
  derivative_f := by intro p hp; exact objective_derivative p
  derivative_g := by intro p hp j; exact row_derivative p j

def event0 : Event spec where
  target := target0
  target_mem := target0_mem
  x := scalar 0
  restoration := none
def event1 : Event spec where
  target := target1
  target_mem := target1_mem
  x := scalar 0
  restoration := none

@[simp] theorem event0_anchor : event0.anchor=pt 0 0 := by simp [Event.anchor,event0,pt]
@[simp] theorem event1_anchor : event1.anchor=pt 0 1 := by simp [Event.anchor,event1,pt]

theorem event0_valid : EventValid spec event0 := by
  refine ⟨Set.mem_univ _,?_⟩
  change IsMinimizer (fiber data (intCast target0)) (fiberObjective objective (intCast target0))
    (scalar 0) ∧ Nonempty (FixedKKT data objective (scalar 0) (intCast target0))
  rw [cast_target0]
  exact ⟨fixed_minimum 0 (Or.inl rfl),⟨fixedKKT 0 (Or.inl rfl)⟩⟩

theorem event1_valid : EventValid spec event1 := by
  refine ⟨Set.mem_univ _,?_⟩
  change IsMinimizer (fiber data (intCast target1)) (fiberObjective objective (intCast target1))
    (scalar 0) ∧ Nonempty (FixedKKT data objective (scalar 0) (intCast target1))
  rw [cast_target1]
  exact ⟨fixed_minimum 1 (Or.inr rfl),⟨fixedKKT 1 (Or.inr rfl)⟩⟩

theorem valid_event_cases {e : Event spec} (he : EventValid spec e) : e=event0 ∨ e=event1 := by
  have ht := target_cases e.target e.target_mem
  have hr : e.restoration=none := by
    by_contra hn
    apply event_empty he hn
    rcases ht with ht|ht
    · exact ⟨scalar 0,by simpa [spec,ht] using (fixed_minimum 0 (Or.inl rfl)).1⟩
    · exact ⟨scalar 0,by simpa [spec,ht] using (fixed_minimum 1 (Or.inr rfl)).1⟩
  have hm := event_fixed_minimum he hr
  rcases ht with ht|ht
  · have hx : e.x=scalar 0 := fixed_unique 0 (by simpa [spec,ht] using hm)
    exact Or.inl (event_ext ht hx hr)
  · have hx : e.x=scalar 0 := fixed_unique 1 (by simpa [spec,ht] using hm)
    exact Or.inr (event_ext ht hx hr)

end U

namespace I
def spec : Data 1 1 3 0 where
  model := data
  f := objective
  Df _ := Df
  Dg := Dg
  domain := Set.univ

theorem analytic : Analytic spec where
  convex_f := objective_convex
  convex_g := row_convex
  original_domain := by intro p hp; trivial
  derivative_f := by intro p hp; exact objective_derivative p
  derivative_g := by intro p hp j; exact row_derivative p j

def event0 : Event spec where
  target := target0
  target_mem := target0_mem
  x := scalar 0
  restoration := some slack
def event1 : Event spec where
  target := target1
  target_mem := target1_mem
  x := scalar (3/4)
  restoration := none

@[simp] theorem event0_anchor : event0.anchor=pt 0 0 := by simp [Event.anchor,event0,pt]
@[simp] theorem event1_anchor : event1.anchor=pt (3/4) 1 := by simp [Event.anchor,event1,pt]

theorem event0_valid : EventValid spec event0 := by
  refine ⟨Set.mem_univ _,?_⟩
  change ¬ (fiber data (intCast target0)).Nonempty ∧
    IsMinimizer (restSet data (intCast target0)) restCost (weightedInsert (scalar 0) slack)
  rw [cast_target0]
  exact ⟨zero_fiber_empty,restoration_minimum⟩

theorem event1_valid : EventValid spec event1 := by
  refine ⟨Set.mem_univ _,?_⟩
  change IsMinimizer (fiber data (intCast target1)) (fiberObjective objective (intCast target1))
    (scalar (3/4)) ∧ Nonempty (FixedKKT data objective (scalar (3/4)) (intCast target1))
  rw [cast_target1]
  exact ⟨fixed_minimum,⟨fixedKKT⟩⟩

theorem valid_event_cases {e : Event spec} (he : EventValid spec e) : e=event0 ∨ e=event1 := by
  rcases target_cases e.target e.target_mem with ht|ht
  · cases hr : e.restoration with
    | none =>
      have hm := event_fixed_minimum he hr
      exfalso
      apply zero_fiber_empty
      exact ⟨e.x,by simpa [spec,ht] using hm.1⟩
    | some s =>
      have hm := event_restoration_minimum he hr
      have hu := restoration_unique (by simpa [spec,ht] using hm)
      exact Or.inl (event_ext ht hu.1 (by simpa [hu.2,event0] using hr))
  · have hr : e.restoration=none := by
      by_contra hn
      apply event_empty he hn
      exact ⟨scalar (3/4),by simpa [spec,ht] using fixed_minimum.1⟩
    have hm := event_fixed_minimum he hr
    have hx := fixed_unique (by simpa [spec,ht] using hm)
    exact Or.inr (event_ext ht hx hr)

end I
end Chapter03.OAExec.Controls
