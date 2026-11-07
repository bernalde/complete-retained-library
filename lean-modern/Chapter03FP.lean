module

public import Chapter03FPReturn
public import Chapter03FPDriver

@[expose] public section

/-! Qualified exact feasibility-pump procedure. The actual convex nonlinear
model, finite integer box, optimizer choices, retained cuts, cutoffs, no-goods,
polishing, initialization and timestamp-filtered handoff are all explicit.
This candidate theorem does not execute the subsequent OA/DICOPT algorithm. -/
noncomputable section
open Chapter02
namespace Chapter03.FP
variable {n m l r : ℕ}

structure Counts where
  relaxations : ℕ
  bodies : ℕ
  projections : ℕ
  masters : ℕ
  polishes : ℕ

def Outcome.counts : Outcome n m → Counts
  | .initialInfeasible => ⟨1,0,0,0,0⟩
  | .initialOptimal _ => ⟨1,0,0,0,0⟩
  | .loop out => ⟨1,out.bodies,out.projections,out.masters,out.polishes⟩

structure CountBounds (d : Data n m l r) (cap : Option ℕ) (out : Outcome n m) : Prop where
  relaxation_exact : out.counts.relaxations=1
  bodies_bound : out.counts.bodies≤d.box.card
  projections_bound : out.counts.projections≤d.box.card
  masters_bound : out.counts.masters≤d.box.card+1
  polishes_bound : out.counts.polishes≤out.counts.bodies
  cap_bound : ∀ b, cap=some b → out.counts.bodies≤b ∧ out.counts.projections≤b
  early_exact : ∀ p, out=.initialInfeasible ∨ out=.initialOptimal p →
    out.counts.bodies=0 ∧ out.counts.projections=0 ∧ out.counts.masters=0 ∧ out.counts.polishes=0
  loop_exact : ∀ o, out=.loop o → LoopBounds d cap o

/-- Disjoint semantic results retain the actual chosen initializer and actual
completed run; an early return never introduces a fabricated fractional state. -/
def ReturnClaims (d : Data n m l r) (cap : Option ℕ) (initial : Initialization d)
    (out : Outcome n m) : Prop :=
  match initial,out with
  | .empty _,.initialInfeasible => ¬d.original.Nonempty
  | .minimum p _,.initialOptimal q => q=p ∧ IsMinimizer d.original d.f q
  | .minimum p _,.loop o => p ∉ d.original ∧
      Chain d cap (initialState p) o.bodies o.polishes o.state ∧
      Stop d cap o.state o.reason ∧ Invariant d o.state ∧
      SafeHandoff d o.state ∧ (o.reason=.handoff ∨ TerminalCertificate d o.state)
  | _,_ => False

theorem early_infeasible_countBounds (d : Data n m l r) (cap : Option ℕ) :
    CountBounds d cap (.initialInfeasible) := by
  refine ⟨rfl,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,le_rfl,?_,?_,?_⟩
  · intro b _; exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  · intro _ _; exact ⟨rfl,rfl,rfl,rfl⟩
  · intro o ho; cases ho

theorem early_optimal_countBounds (d : Data n m l r) (cap : Option ℕ) (p : Point n m) :
    CountBounds d cap (.initialOptimal p) := by
  refine ⟨rfl,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,le_rfl,?_,?_,?_⟩
  · intro b _; exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  · intro _ _; exact ⟨rfl,rfl,rfl,rfl⟩
  · intro o ho; cases ho

theorem loop_countBounds (d : Data n m l r) {cap : Option ℕ} {o : LoopOutput n m}
    (h : LoopBounds d cap o) : CountBounds d cap (.loop o) := by
  refine ⟨rfl,h.bodies_bound,h.projections_bound,h.masters_bound,h.polishes_bound,?_,?_,?_⟩
  · intro b hb; exact ⟨h.cap_bodies b hb,h.cap_projections b hb⟩
  · intro p hp; rcases hp with hp | hp <;> cases hp
  · intro o' ho; cases ho; exact h

theorem procedure_returns (d : Data n m l r) (h : Analytic d) (cap : Option ℕ)
    (initial : Initialization d) (choose : Selector d cap) :
    ∃ out, procedure d initial choose=some out ∧ ReturnClaims d cap initial out ∧
      CountBounds d cap out := by
  classical
  cases initial with
  | empty he =>
    refine ⟨.initialInfeasible,rfl,?_,early_infeasible_countBounds d cap⟩
    exact fun ⟨p,hp⟩ => he ⟨p,original_subset_relaxation d hp⟩
  | minimum p hp =>
    by_cases hi : p∈d.original
    · refine ⟨.initialOptimal p,by simp [procedure,hi],⟨rfl,hi,?_⟩,
        early_optimal_countBounds d cap p⟩
      intro q hq
      exact hp.2 q (original_subset_relaxation d hq)
    · obtain ⟨o,ho⟩ := run_sufficient_fuel d h choose (d.box.card+1) (initialState p)
        (initial_invariant d hp.1) (by simp [initialState])
      obtain ⟨hs,hb⟩ := run_initial_bounds d h choose hp.1 ho
      obtain ⟨hc,ht,_⟩ := run_execution d choose (d.box.card+1) (initialState p) ho
      refine ⟨.loop o,by simp [procedure,hi,ho],?_,loop_countBounds d hb⟩
      exact ⟨hi,hc,ht,hs,safe_handoff d h hs,stop_certificate d h hs ht⟩

/-- The handoff comparison theorem applies to every actually reachable prefix,
including states that the uncapped interpreter would continue from. -/
theorem reachable_safe_handoff (d : Data n m l r) (h : Analytic d) {cap : Option ℕ}
    {seed : Point n m} (hseed : IsMinimizer d.relaxation d.f seed)
    {k q : ℕ} {s : State n m} (hc : Chain d cap (initialState seed) k q s) :
    SafeHandoff d s :=
  safe_handoff d h (chain_invariant d h (initial_invariant d hseed.1) hc)

/-- One substantive procedure endpoint. All exact initializer/selector choices
and all nonnegative delta values represented by Analytic are admitted. Finite
return, exact counters, incumbent gap and every-prefix handoff are derived. -/
theorem qualified_source_pump (d : Data n m l r) (h : Analytic d) (cap : Option ℕ) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d cap) ∧
    (∀ initial : Initialization d, ∀ choose : Selector d cap,
      ∃ out, procedure d initial choose=some out ∧ ReturnClaims d cap initial out ∧
        CountBounds d cap out) ∧
    (∀ seed, IsMinimizer d.relaxation d.f seed → ∀ k q s,
      Chain d cap (initialState seed) k q s → SafeHandoff d s) := by
  exact ⟨initialization_nonempty d h,selector_nonempty d h cap,
    procedure_returns d h cap,fun _ hseed _ _ _ hc => reachable_safe_handoff d h hseed hc⟩

end Chapter03.FP

#print axioms Chapter03.FP.qualified_source_pump
