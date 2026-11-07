module

public import Chapter03FPUnboundedValidity
public import Chapter03FPUnboundedProgress

@[expose] public section

noncomputable section
open Chapter02
open Chapter03.FP
namespace Chapter03.FPUnbounded
variable {n m l : ℕ}

structure Counts where
  relaxations : ℕ
  bodies : ℕ
  projections : ℕ
  masters : ℕ
  polishes : ℕ

def outcomeCounts : Outcome n m → Counts
  | .initialInfeasible => ⟨1,0,0,0,0⟩
  | .initialOptimal _ => ⟨1,0,0,0,0⟩
  | .loop out => ⟨1,out.bodies,out.projections,out.masters,out.polishes⟩

structure CountBounds (B : ℕ) (cap : Option ℕ) (out : Outcome n m) : Prop where
  relaxation_exact : (outcomeCounts out).relaxations=1
  bodies_bound : (outcomeCounts out).bodies≤B
  projections_bound : (outcomeCounts out).projections≤B+1
  masters_bound : (outcomeCounts out).masters≤B+1
  polishes_bound : (outcomeCounts out).polishes≤(outcomeCounts out).bodies
  cap_bound : ∀ b, cap=some b → (outcomeCounts out).bodies≤b ∧ (outcomeCounts out).projections≤b
  early_exact : ∀ p, out=.initialInfeasible ∨ out=.initialOptimal p →
    (outcomeCounts out).bodies=0 ∧ (outcomeCounts out).projections=0 ∧ (outcomeCounts out).masters=0 ∧ (outcomeCounts out).polishes=0
  loop_exact : ∀ o, out=.loop o → LoopCounts cap o

/-- Disjoint semantic results retain the actual chosen initializer and actual
completed run; an early return never introduces a fabricated fractional state. -/
def ReturnClaims (d : Data n m l) (cap : Option ℕ) (initial : Initialization d)
    (out : Outcome n m) : Prop :=
  match initial,out with
  | .empty _,.initialInfeasible => ¬d.original.Nonempty
  | .minimum p _,.initialOptimal q => q=p ∧ IsMinimizer d.original d.f q
  | .minimum p _,.loop o => p ∉ d.original ∧
      Chain d cap (initialState p) o.bodies o.polishes o.state ∧
      Stop d cap o.state o.reason ∧ Invariant d o.state ∧
      SafeHandoff d o.state ∧ (o.reason=.handoff ∨ TerminalCertificate d o.state)
  | _,_ => False

theorem early_infeasible_countBounds (B : ℕ) (cap : Option ℕ) :
    CountBounds B cap (.initialInfeasible : Outcome n m) := by
  refine ⟨rfl,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,le_rfl,?_,?_,?_⟩
  · intro b _; exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  · intro _ _; exact ⟨rfl,rfl,rfl,rfl⟩
  · intro o ho; cases ho

theorem early_optimal_countBounds (B : ℕ) (cap : Option ℕ) (p : Point n m) :
    CountBounds B cap (.initialOptimal p) := by
  refine ⟨rfl,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,le_rfl,?_,?_,?_⟩
  · intro b _; exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  · intro _ _; exact ⟨rfl,rfl,rfl,rfl⟩
  · intro o ho; cases ho

theorem loop_countBounds {B : ℕ} {cap : Option ℕ} {o : LoopOutput n m}
    (h : LoopCounts cap o) (hb : o.bodies ≤ B) : CountBounds B cap (.loop o) := by
  have ht : terminalProjectionCount o.reason ≤ 1 := by cases o.reason <;> simp [terminalProjectionCount]
  refine ⟨rfl,hb,?_,?_,h.polishes_bound,?_,?_,?_⟩
  · change o.projections ≤ B+1
    have := h.projection_exact
    omega
  · change o.masters ≤ B+1
    have := h.master_exact
    omega
  · intro b hb; exact ⟨h.cap_bodies b hb,h.cap_projections b hb⟩
  · intro p hp; rcases hp with hp | hp <;> cases hp
  · intro o' ho; cases ho; exact h

/-- Sufficient fuel is derived from source data and actual compact-anchor
progress. It is noncomputable and is not a numerical runtime estimate. -/
def procedure (d : Data n m l) (h : Analytic d) (hd : 0 < d.delta)
    {cap : Option ℕ} (initial : Initialization d) (choose : Selector d cap) :
    Option (Outcome n m) :=
  procedureWithFuel d initial choose (historyBound d h hd+1)

/-- Finite caps also work at delta zero. Master inspection precedes the cap. -/
def cappedProcedure (d : Data n m l) (b : ℕ) (initial : Initialization d)
    (choose : Selector d (some b)) : Option (Outcome n m) :=
  procedureWithFuel d initial choose (b+1)

theorem returned_claims (d : Data n m l) (h : Analytic d) {cap : Option ℕ}
    (initial : Initialization d) (choose : Selector d cap) (fuel : ℕ) {out : Outcome n m}
    (hout : procedureWithFuel d initial choose fuel = some out) :
    ReturnClaims d cap initial out := by
  classical
  cases initial with
  | empty he =>
    have ho : out = .initialInfeasible := by simpa [procedureWithFuel] using hout.symm
    subst out
    exact fun ⟨p,hp⟩ => he ⟨p,original_subset_relaxation d hp⟩
  | minimum p hp =>
    by_cases hi : p ∈ d.original
    · have ho : out = .initialOptimal p := by simpa [procedureWithFuel,hi] using hout.symm
      subst out
      exact ⟨rfl,hi,fun q hq => hp.2 q (original_subset_relaxation d hq)⟩
    · simp only [procedureWithFuel,hi,↓reduceIte] at hout
      cases hr : run d choose fuel (initialState p) with
      | none => simp [hr] at hout
      | some o =>
        have ho : out = .loop o := by simpa [hr] using hout.symm
        subst out
        obtain ⟨hs,_⟩ := run_initial_counts d h choose hp.1 hr
        obtain ⟨hc,ht,_⟩ := run_execution d choose fuel (initialState p) hr
        exact ⟨hi,hc,ht,hs,safe_handoff d h hs,stop_certificate d h hs ht⟩

theorem procedure_returns (d : Data n m l) (h : Analytic d) (hd : 0 < d.delta)
    (cap : Option ℕ) (initial : Initialization d) (choose : Selector d cap) :
    ∃ out, procedure d h hd initial choose = some out ∧ ReturnClaims d cap initial out ∧
      CountBounds (historyBound d h hd) cap out := by
  classical
  cases initial with
  | empty he =>
    refine ⟨.initialInfeasible,rfl,?_,early_infeasible_countBounds _ cap⟩
    exact fun ⟨p,hp⟩ => he ⟨p,original_subset_relaxation d hp⟩
  | minimum p hp =>
    by_cases hi : p∈d.original
    · refine ⟨.initialOptimal p,by simp [procedure,procedureWithFuel,hi],⟨rfl,hi,?_⟩,
        early_optimal_countBounds _ cap p⟩
      intro q hq
      exact hp.2 q (original_subset_relaxation d hq)
    · obtain ⟨o,ho⟩ := run_sufficient_fuel d h hd choose (historyBound d h hd+1) (initialState p)
        (initial_invariant d hp.1) (by simp [initialState])
      obtain ⟨hs,hb⟩ := run_initial_counts d h choose hp.1 ho
      have hlen := history_length_bound d h hd hs
      have hbody : o.bodies ≤ historyBound d h hd := by rw [hb.bodies_eq_history]; exact hlen
      have hret : procedure d h hd (.minimum p hp) choose = some (.loop o) := by
        simp [procedure,procedureWithFuel,hi,ho]
      exact ⟨.loop o,hret,returned_claims d h (.minimum p hp) choose _ hret,loop_countBounds hb hbody⟩

theorem cappedProcedure_returns (d : Data n m l) (h : Analytic d) (b : ℕ)
    (initial : Initialization d) (choose : Selector d (some b)) :
    ∃ out, cappedProcedure d b initial choose = some out ∧ ReturnClaims d (some b) initial out ∧
      CountBounds b (some b) out := by
  classical
  cases initial with
  | empty he =>
    refine ⟨.initialInfeasible,rfl,?_,early_infeasible_countBounds _ _⟩
    exact fun ⟨p,hp⟩ => he ⟨p,original_subset_relaxation d hp⟩
  | minimum p hp =>
    by_cases hi : p∈d.original
    · refine ⟨.initialOptimal p,by simp [cappedProcedure,procedureWithFuel,hi],⟨rfl,hi,?_⟩,
        early_optimal_countBounds _ _ p⟩
      intro q hq
      exact hp.2 q (original_subset_relaxation d hq)
    · obtain ⟨o,ho⟩ := run_cap_sufficient_fuel d choose (b+1) (initialState p)
        (by simp [initialState]) (by simp [initialState])
      obtain ⟨_,hb⟩ := run_initial_counts d h choose hp.1 ho
      have hret : cappedProcedure d b (.minimum p hp) choose = some (.loop o) := by
        simp [cappedProcedure,procedureWithFuel,hi,ho]
      exact ⟨.loop o,hret,returned_claims d h (.minimum p hp) choose _ hret,
        loop_countBounds hb (hb.cap_bodies b rfl)⟩

/-- The handoff comparison theorem applies to every actually reachable prefix,
including states that the uncapped interpreter would continue from. -/
theorem reachable_safe_handoff (d : Data n m l) (h : Analytic d) {cap : Option ℕ}
    {seed : Point n m} (hseed : IsMinimizer d.relaxation d.f seed)
    {k q : ℕ} {s : State n m} (hc : Chain d cap (initialState seed) k q s) :
    SafeHandoff d s :=
  safe_handoff d h (chain_invariant d h (initial_invariant d hseed.1) hc)

end Chapter03.FPUnbounded
