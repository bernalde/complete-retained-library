module

public import Chapter02DICOPTState

@[expose] public section

/-! The actual bound/no-good recursion. Every selector obeys literal master
minimization, certified fixed-fiber replies, and the bound test. Freshness and
strict finite progress are derived from source no-good feasibility. This module
contains the structural recursion; analytic existence and original-objective
soundness are proved in Chapter02DICOPTProcedure. -/
noncomputable section
namespace Chapter02.DICOPT
variable {n m e l r : ℕ}

inductive Result (n m : ℕ)
  | infeasible
  | solution (point : RealVector n × RealVector m)

def ReturnCertificate (d : Data n m e l r) : Result n m → Prop
  | .infeasible => ¬ d.original.Nonempty
  | .solution p => IsMinimizer d.original (pointObjective d) p

def competitive (d : Data n m e l r) (s : State d)
    (q : MasterPoint d s.history) : Prop :=
  ∀ u, s.incumbent = some u → s.value q < pointObjective d u

/-- The paper's permitted bound stopping option, with explicit empty-master
completion. The bound is for remaining assignments; the invariant separately
accounts for all processed fibers. -/
inductive Stop (d : Data n m e l r) (s : State d) : Result n m → Prop
  | empty_none (empty : s.master = ∅) (incumbent : s.incumbent = none) :
      Stop d s .infeasible
  | empty_some (empty : s.master = ∅) {u : RealVector n × RealVector m}
      (incumbent : s.incumbent = some u) : Stop d s (.solution u)
  | bound {q : MasterPoint d s.history} {u : RealVector n × RealVector m}
      (master : IsMinimizer s.master s.value q)
      (incumbent : s.incumbent = some u)
      (test : pointObjective d u ≤ s.value q) : Stop d s (.solution u)

/-- A continuation asks for a literal attained AP master and an actual source
reply on its binary fiber. No constructor contains freshness or progress. -/
inductive Continue (d : Data n m e l r) : State d → State d → Prop
  | step {s : State d} {q : MasterPoint d s.history} {b : FiberReply d}
      (master : IsMinimizer s.master s.value q)
      (test : competitive d s q) (same_y : q.y = realBinary b.binary) :
      Continue d s (append d s b)

theorem continue_invariant (d : Data n m e l r) {s t : State d}
    (hs : Invariant d s) (h : Continue d s t) : Invariant d t := by
  cases h with
  | step _ _ _ => exact append_invariant d hs _

theorem continue_remaining_lt (d : Data n m e l r) {s t : State d}
    (h : Continue d s t) : t.remaining < s.remaining := by
  cases h with
  | step hq _ hy => exact append_remaining_lt d _ _ hq.1 _ hy

inductive Chain (d : Data n m e l r) : State d → ℕ → State d → Prop
  | nil (s : State d) : Chain d s 0 s
  | cons {s t u : State d} {k : ℕ} (step : Continue d s t)
      (tail : Chain d t k u) : Chain d s (k+1) u

def Completed (d : Data n m e l r) (s : State d) (k : ℕ)
    (result : Result n m) : Prop := ∃ t, Chain d s k t ∧ Stop d t result

theorem chain_invariant (d : Data n m e l r) {s t : State d} {k : ℕ}
    (hs : Invariant d s) (h : Chain d s k t) : Invariant d t := by
  revert hs
  induction h with
  | nil _ => exact id
  | cons hstep _ ih =>
    intro hs
    exact ih (continue_invariant d hs hstep)

theorem chain_remaining_bound (d : Data n m e l r) {s t : State d} {k : ℕ}
    (h : Chain d s k t) : k + t.remaining ≤ s.remaining := by
  induction h with
  | nil _ => omega
  | cons hstep _ ih =>
    have := continue_remaining_lt d hstep
    omega

theorem chain_length_bound (d : Data n m e l r) {s t : State d} {k : ℕ}
    (h : Chain d s k t) : k ≤ s.remaining := by
  have := chain_remaining_bound d h
  omega

inductive Decision (d : Data n m e l r) (s : State d)
  | stop (result : Result n m) (valid : Stop d s result)
  | next (t : State d) (valid : Continue d s t)

/-- Every returned feasible NLP anchor carries its own actual KKT certificate
and signed convexity. This does not quantify over arbitrary local solver replies. -/
def Selector (d : Data n m e l r) :=
  ∀ s : State d, Invariant d s → Decision d s

/-- Fuel counts master decisions. A terminal inspection consumes one; every
continuation solves one binary fiber and appends its exact no-good row. -/
def run (d : Data n m e l r) (choose : Selector d) :
    ℕ → (s : State d) → Invariant d s → Option (Result n m × ℕ)
  | 0, _, _ => none
  | fuel + 1, s, hs =>
    match choose s hs with
    | .stop result _ => some (result,0)
    | .next t hstep =>
      (run d choose fuel t (continue_invariant d hs hstep)).map
        (fun out => (out.1,out.2+1))

theorem run_completed (d : Data n m e l r) (choose : Selector d)
    (fuel : ℕ) (s : State d) (hs : Invariant d s)
    {result : Result n m} {k : ℕ}
    (h : run d choose fuel s hs = some (result,k)) :
    Completed d s k result ∧ k < fuel := by
  induction fuel generalizing s result k with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hc : choose s hs with
    | stop out hstop =>
      simp only [run,hc,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨⟨s,.nil s,hstop⟩, Nat.succ_pos _⟩
    | next t hstep =>
      simp only [run,hc] at h
      cases hr : run d choose fuel t (continue_invariant d hs hstep) with
      | none => simp [hr] at h
      | some out =>
        rcases out with ⟨out,j⟩
        simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨⟨u,hchain,hstop⟩,hj⟩ := ih t (continue_invariant d hs hstep) hr
        exact ⟨⟨u,.cons hstep hchain,hstop⟩, Nat.succ_lt_succ hj⟩

theorem run_sufficient_fuel (d : Data n m e l r) (choose : Selector d)
    (fuel : ℕ) (s : State d) (hs : Invariant d s)
    (hfuel : s.remaining < fuel) :
    ∃ result k, run d choose fuel s hs = some (result,k) := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    cases hc : choose s hs with
    | stop result hstop => exact ⟨result,0,by simp [run,hc]⟩
    | next t hstep =>
      have hlt := continue_remaining_lt d hstep
      have ht := continue_invariant d hs hstep
      obtain ⟨result,k,hk⟩ := ih t ht (by omega)
      exact ⟨result,k+1,by simp [run,hc,hk]⟩

/-- Every admitted exact selector, not merely one fortunate sequence, follows
this recursion and returns within the finite binary cardinality plus inspection. -/
theorem driver_finite_return (d : Data n m e l r) (choose : Selector d)
    (a : Anchor d) : ∃ result k,
      run d choose (Fintype.card (BVector m)+1) (initialState a)
        (initial_invariant a) = some (result,k) ∧
      Completed d (initialState a) k result ∧
      k ≤ Fintype.card (BVector m) ∧ k+1 ≤ Fintype.card (BVector m)+1 := by
  obtain ⟨result,k,hk⟩ := run_sufficient_fuel d choose
    (Fintype.card (BVector m)+1) (initialState a) (initial_invariant a)
    (by rw [initial_remaining]; omega)
  have hcompleted := (run_completed d choose _ _ (initial_invariant a) hk).1
  have hbound : k ≤ Fintype.card (BVector m) := by
    obtain ⟨t,hchain,_⟩ := hcompleted
    simpa only [initial_remaining] using chain_length_bound d hchain
  exact ⟨result,k,hk,hcompleted,hbound,by omega⟩

/-- An exact infeasible reply changes no incumbent and adds no tangent anchor;
it only retains the history and appends the literal integer no-good. -/
theorem infeasible_append_semantics (d : Data n m e l r) (s : State d)
    (b : FiberReply d) (hb : b.anchor = none) :
    (append d s b).history = s.history ∧
    (append d s b).incumbent = s.incumbent ∧
    (append d s b).seen = insert b.binary s.seen := by
  refine ⟨?_, ?_, seen_append d s b⟩
  · rw [history_append, hb]
    simp
  · simp [append,hb]

end Chapter02.DICOPT
