module

public import Chapter02OAState
public import Mathlib.Tactic

@[expose] public section

/-! Counted executions and a fuel interpreter for the concrete retained-history
OA procedure. All allowed exact choices obey the same bound. Progress is
derived by Chapter02OAState from the source model, never an oracle premise.
The fuel counts mathematical master decisions, not numerical solver runtime. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

/-- Exactly `k` concrete continuation steps, with no terminal claim. -/
inductive OAChain (d : ModelData n m l r) (epsilon : ℝ) :
    OAState n m → ℕ → OAState n m → Prop
  | nil (s : OAState n m) : OAChain d epsilon s 0 s
  | cons {s t u : OAState n m} {k : ℕ}
      (step : OAContinue d epsilon s t) (tail : OAChain d epsilon t k u) :
      OAChain d epsilon s (k + 1) u

/-- A completed execution has a final permitted stop, in addition to its
counted continuing fiber steps. Thus it uses `k+1` master decisions. -/
def OACompleted (d : ModelData n m l r) (epsilon : ℝ) (s : OAState n m)
    (k : ℕ) (result : OAResult n m) : Prop :=
  ∃ t, OAChain d epsilon s k t ∧ OAStop d epsilon t result

theorem oa_chain_invariant (d : ModelData n m l r) {epsilon : ℝ}
    {s t : OAState n m} {k : ℕ} (hs : OAInvariant d s)
    (h : OAChain d epsilon s k t) : OAInvariant d t := by
  revert hs
  induction h with
  | nil _ => exact id
  | cons hstep _ ih =>
    intro hs
    exact ih (oa_continue_invariant d hs hstep)

/-- Every finite continuation chain satisfies the remaining-cardinality
bound; this quantifies over all exact choices and all ties. -/
theorem oa_chain_remaining_bound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) {s t : OAState n m} {k : ℕ}
    (hs : OAInvariant d s) (h : OAChain d epsilon s k t) :
    k + oaRemaining d t ≤ oaRemaining d s := by
  revert hs
  induction h with
  | nil _ => intro _; omega
  | cons hstep _ ih =>
    intro hs
    have hlt := oa_continue_remaining_lt d hconv hdiff hCQ hepsilon hs hstep
    have htail := ih (oa_continue_invariant d hs hstep)
    omega

theorem oa_chain_length_bound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) {s t : OAState n m} {k : ℕ}
    (hs : OAInvariant d s) (h : OAChain d epsilon s k t) :
    k ≤ oaRemaining d s := by
  have := oa_chain_remaining_bound d hconv hdiff hCQ hepsilon hs h
  omega

theorem oa_completed_sound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hepsilon : 0 ≤ epsilon)
    {s : OAState n m} {k : ℕ} {result : OAResult n m}
    (hs : OAInvariant d s) (h : OACompleted d epsilon s k result) :
    OAReturnCertificate d epsilon result := by
  obtain ⟨t, hchain, hstop⟩ := h
  exact oa_stop_sound d hconv hdiff hepsilon (oa_chain_invariant d hs hchain) hstop

theorem oa_completed_length_bound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) {s : OAState n m} {k : ℕ} {result : OAResult n m}
    (hs : OAInvariant d s) (h : OACompleted d epsilon s k result) :
    k ≤ oaRemaining d s ∧ k + 1 ≤ oaRemaining d s + 1 := by
  obtain ⟨t, hchain, _⟩ := h
  have hk := oa_chain_length_bound d hconv hdiff hCQ hepsilon hs hchain
  exact ⟨hk, Nat.add_le_add_right hk 1⟩

/-- Legal decision data. No constructor asks for a fresh integer or a decrease. -/
inductive OADecision (d : ModelData n m l r) (epsilon : ℝ) (s : OAState n m)
  | stop (result : OAResult n m) (valid : OAStop d epsilon s result)
  | next (t : OAState n m) (valid : OAContinue d epsilon s t)

/-- Arbitrary full-state exact choices, including optional early feasible
return or continuation at the same feasible master point. -/
def OASelector (d : ModelData n m l r) (epsilon : ℝ) :=
  ∀ s : OAState n m, OAInvariant d s → OADecision d epsilon s

theorem oa_selector_exists (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) : Nonempty (OASelector d epsilon) := by
  classical
  have hex (s : OAState n m) : Nonempty (OADecision d epsilon s) := by
    rcases oa_step_total d epsilon hbase hdiff s with ⟨result, hs⟩ | ⟨t, ht⟩
    · exact ⟨.stop result hs⟩
    · exact ⟨.next t ht⟩
  exact ⟨fun s _ => Classical.choice (hex s)⟩

/-- `none` means fuel exhaustion only. A successful output records the actual
result and number of continuing fiber steps; terminal decisions use one fuel. -/
def oaRun (d : ModelData n m l r) {epsilon : ℝ} (choose : OASelector d epsilon) :
    ℕ → (s : OAState n m) → OAInvariant d s → Option (OAResult n m × ℕ)
  | 0, _, _ => none
  | fuel + 1, s, hs =>
    match choose s hs with
    | .stop result _ => some (result, 0)
    | .next t hstep =>
      (oaRun d choose fuel t (oa_continue_invariant d hs hstep)).map
        (fun out => (out.1, out.2 + 1))

/-- Every nonexhausted output carries an actual completed execution. -/
theorem oa_run_completed (d : ModelData n m l r) {epsilon : ℝ}
    (choose : OASelector d epsilon) (fuel : ℕ) (s : OAState n m)
    (hs : OAInvariant d s) {result : OAResult n m} {k : ℕ}
    (h : oaRun d choose fuel s hs = some (result,k)) :
    OACompleted d epsilon s k result ∧ k < fuel := by
  induction fuel generalizing s result k with
  | zero => simp [oaRun] at h
  | succ fuel ih =>
    cases hchoice : choose s hs with
    | stop out hstop =>
      simp only [oaRun, hchoice, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨s,.nil s,hstop⟩, Nat.succ_pos _⟩
    | next t hstep =>
      simp only [oaRun,hchoice] at h
      cases hr : oaRun d choose fuel t (oa_continue_invariant d hs hstep) with
      | none => simp [hr] at h
      | some out =>
        rcases out with ⟨out,j⟩
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨⟨u,hchain,hstop⟩,hj⟩ := ih t (oa_continue_invariant d hs hstep) hr
        exact ⟨⟨u,.cons hstep hchain,hstop⟩, Nat.succ_lt_succ hj⟩

theorem oa_run_sound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hepsilon : 0 ≤ epsilon)
    (choose : OASelector d epsilon) (fuel : ℕ) (s : OAState n m)
    (hs : OAInvariant d s) {result : OAResult n m} {k : ℕ}
    (h : oaRun d choose fuel s hs = some (result,k)) :
    OAReturnCertificate d epsilon result :=
  oa_completed_sound d hconv hdiff hepsilon hs (oa_run_completed d choose fuel s hs h).1

/-- Exhaustion requires as many actual continuations as the supplied fuel. -/
theorem oa_run_exhausted_chain (d : ModelData n m l r) {epsilon : ℝ}
    (choose : OASelector d epsilon) (fuel : ℕ) (s : OAState n m)
    (hs : OAInvariant d s) (h : oaRun d choose fuel s hs = none) :
    ∃ t, OAChain d epsilon s fuel t := by
  induction fuel generalizing s with
  | zero => exact ⟨s,.nil s⟩
  | succ fuel ih =>
    cases hchoice : choose s hs with
    | stop result hstop => simp [oaRun,hchoice] at h
    | next t hstep =>
      have hrun : oaRun d choose fuel t (oa_continue_invariant d hs hstep) = none := by
        simpa only [oaRun,hchoice,Option.map_eq_none_iff] using h
      obtain ⟨u,hu⟩ := ih t (oa_continue_invariant d hs hstep) hrun
      exact ⟨u,.cons hstep hu⟩

/-- Every selector returns with sufficient fuel; no lucky-run existence or
fairness premise substitutes for concrete strict progress. -/
theorem oa_run_sufficient_fuel (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) (choose : OASelector d epsilon) (fuel : ℕ)
    (s : OAState n m) (hs : OAInvariant d s) (hfuel : oaRemaining d s < fuel) :
    ∃ result k, oaRun d choose fuel s hs = some (result,k) := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    cases hchoice : choose s hs with
    | stop result hstop =>
      exact ⟨result,0,by simp [oaRun,hchoice]⟩
    | next t hstep =>
      have hlt := oa_continue_remaining_lt d hconv hdiff hCQ hepsilon hs hstep
      have ht := oa_continue_invariant d hs hstep
      obtain ⟨result,k,hk⟩ := ih t ht (by omega)
      exact ⟨result,k+1,by simp [oaRun,hchoice,hk]⟩

/-- Every completed execution from initialization has the source-sized bound. -/
theorem oa_completed_init_bound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ)
    {k : ℕ} {result : OAResult n m}
    (h : OACompleted d epsilon (oaInit warm) k result) :
    k ≤ (oaBox d).card ∧ k + 1 ≤ (oaBox d).card + 1 := by
  simpa only [oa_init_remaining] using oa_completed_length_bound d hconv hdiff hCQ
    hepsilon (oa_init_invariant d warm hwarm) h

theorem oa_chain_init_bound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ)
    {k : ℕ} {t : OAState n m} (h : OAChain d epsilon (oaInit warm) k t) :
    k ≤ (oaBox d).card := by
  simpa only [oa_init_remaining] using oa_chain_length_bound d hconv hdiff hCQ
    hepsilon (oa_init_invariant d warm hwarm) h

/-- Literal finite return for every exact selector, with a concrete execution,
both step counts, and the lower-bound/gap return certificate. -/
theorem oa_driver_finite_return (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) (choose : OASelector d epsilon)
    (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    ∃ result k,
      oaRun d choose ((oaBox d).card + 1) (oaInit warm)
        (oa_init_invariant d warm hwarm) = some (result,k) ∧
      OACompleted d epsilon (oaInit warm) k result ∧
      k ≤ (oaBox d).card ∧ k + 1 ≤ (oaBox d).card + 1 ∧
      OAReturnCertificate d epsilon result := by
  have hs := oa_init_invariant d warm hwarm
  obtain ⟨result,k,hk⟩ := oa_run_sufficient_fuel d hconv hdiff hCQ hepsilon
    choose ((oaBox d).card + 1) (oaInit warm) hs (by rw [oa_init_remaining]; omega)
  have hcompleted := (oa_run_completed d choose _ _ hs hk).1
  have hbound := oa_completed_init_bound d hconv hdiff hCQ hepsilon warm hwarm hcompleted
  exact ⟨result,k,hk,hcompleted,hbound.1,hbound.2,
    oa_completed_sound d hconv hdiff hepsilon hs hcompleted⟩

theorem oa_completed_solution_within (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hepsilon : 0 ≤ epsilon)
    {s : OAState n m} {k : ℕ} {p : Point n m} (hs : OAInvariant d s)
    (h : OACompleted d epsilon s k (.solution p)) : ObjectiveWithin d epsilon p :=
  oa_certificate_objectiveWithin d (oa_completed_sound d hconv hdiff hepsilon hs h)

theorem oa_completed_zero_optimal (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    {s : OAState n m} {k : ℕ} {p : Point n m} (hs : OAInvariant d s)
    (h : OACompleted d 0 s k (.solution p)) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective p :=
  oa_certificate_zero_optimal d (oa_completed_sound d hconv hdiff le_rfl hs h)

theorem oa_chain_of_sequence (d : ModelData n m l r) {epsilon : ℝ}
    (states : ℕ → OAState n m)
    (hsteps : ∀ i, OAContinue d epsilon (states i) (states (i+1)))
    (start k : ℕ) : OAChain d epsilon (states start) k (states (start+k)) := by
  induction k generalizing start with
  | zero => simpa using OAChain.nil (d := d) (epsilon := epsilon) (states start)
  | succ k ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 k] using
      OAChain.cons (hsteps start) (ih (start+1))

/-- No infinite sequence of permitted continuing decisions starts from an
invariant state. This follows from the bound on every finite prefix. -/
theorem oa_no_infinite_continuations (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) (states : ℕ → OAState n m)
    (hzero : OAInvariant d (states 0)) :
    ¬ (∀ i, OAContinue d epsilon (states i) (states (i+1))) := by
  intro hsteps
  have hchain := oa_chain_of_sequence d states hsteps 0 (oaRemaining d (states 0)+1)
  have hb := oa_chain_length_bound d hconv hdiff hCQ hepsilon hzero hchain
  omega

/-- All source hypotheses jointly provide nonempty exact selectors and finite
return for every selector. Existence of a legal oracle is proved, not assumed. -/
theorem oa_procedure_exists_and_returns (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    Nonempty (OASelector d epsilon) ∧
      ∀ choose : OASelector d epsilon, ∃ result k,
        oaRun d choose ((oaBox d).card+1) (oaInit warm)
          (oa_init_invariant d warm hwarm) = some (result,k) ∧
        OACompleted d epsilon (oaInit warm) k result ∧
        k ≤ (oaBox d).card ∧ k+1 ≤ (oaBox d).card+1 ∧
        OAReturnCertificate d epsilon result :=
  ⟨oa_selector_exists d epsilon hbase hdiff,
    fun choose => oa_driver_finite_return d hconv hdiff hCQ hepsilon choose warm hwarm⟩

/-- Exact zero-tolerance interpretation of the returned data. -/
def OAExactCertificate (d : ModelData n m l r) : OAResult n m → Prop
  | .infeasible => ¬ (d.feasibleOn Set.univ).Nonempty
  | .solution p => IsMinimizer (d.feasibleOn Set.univ) d.objective p

theorem oa_driver_exact_finite_return (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (choose : OASelector d 0) (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    ∃ result k,
      oaRun d choose ((oaBox d).card+1) (oaInit warm)
        (oa_init_invariant d warm hwarm) = some (result,k) ∧
      OACompleted d 0 (oaInit warm) k result ∧
      k ≤ (oaBox d).card ∧ k+1 ≤ (oaBox d).card+1 ∧
      OAExactCertificate d result := by
  obtain ⟨result,k,hrun,hcompleted,hk,hdec,hcert⟩ :=
    oa_driver_finite_return d hconv hdiff hCQ le_rfl choose warm hwarm
  refine ⟨result,k,hrun,hcompleted,hk,hdec,?_⟩
  cases result with
  | infeasible => exact hcert
  | solution p => exact oa_certificate_zero_optimal d hcert

/-- The ordinary stops only: early original-feasible master return is disabled.
This is a protocol restriction, not a new stopping condition. -/
inductive OABasicStop (d : ModelData n m l r) (epsilon : ℝ) (s : OAState n m) :
    OAResult n m → Prop
  | empty (h : oaMaster d s.history = ∅) : OABasicStop d epsilon s .infeasible
  | gap {q u : Point n m} (master : IsMinimizer (oaMaster d s.history) d.objective q)
      (incumbent : s.incumbent = some u)
      (test : d.objective u ≤ d.objective q + epsilon) :
      OABasicStop d epsilon s (.solution u)

theorem oa_basic_stop_is_stop (d : ModelData n m l r) {epsilon : ℝ}
    {s : OAState n m} {result : OAResult n m}
    (h : OABasicStop d epsilon s result) : OAStop d epsilon s result := by
  cases h with
  | empty h => exact .empty h
  | gap hm hi ht => exact .gap hm hi ht

def OABasicCompleted (d : ModelData n m l r) (epsilon : ℝ) (s : OAState n m)
    (k : ℕ) (result : OAResult n m) : Prop :=
  ∃ t, OAChain d epsilon s k t ∧ OABasicStop d epsilon t result

theorem oa_basic_completed_is_completed (d : ModelData n m l r) {epsilon : ℝ}
    {s : OAState n m} {k : ℕ} {result : OAResult n m}
    (h : OABasicCompleted d epsilon s k result) : OACompleted d epsilon s k result := by
  obtain ⟨t,hchain,hstop⟩ := h
  exact ⟨t,hchain,oa_basic_stop_is_stop d hstop⟩

def oaDecisionWithoutEarly {d : ModelData n m l r} {epsilon : ℝ}
    {s : OAState n m} : OADecision d epsilon s → Prop
  | .stop result _ => OABasicStop d epsilon s result
  | .next _ _ => True

structure OABasicSelector (d : ModelData n m l r) (epsilon : ℝ) where
  choose : OASelector d epsilon
  ordinary : ∀ s hs, oaDecisionWithoutEarly (choose s hs)

/-- Compactness and exact subproblem attainment provide ordinary selectors
even if early feasible return is entirely disabled. -/
theorem oa_basic_selector_exists (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    Nonempty (OABasicSelector d epsilon) := by
  classical
  have hex (s : OAState n m) : ∃ decision : OADecision d epsilon s,
      oaDecisionWithoutEarly decision := by
    rcases oa_master_reply d s.history hbase with hempty | ⟨q,hq⟩
    · exact ⟨.stop .infeasible (.empty hempty),.empty hempty⟩
    · by_cases hgap : ∃ u, s.incumbent = some u ∧ d.objective u ≤ d.objective q+epsilon
      · obtain ⟨u,hu,ht⟩ := hgap
        exact ⟨.stop (.solution u) (.gap hq hu ht),.gap hq hu ht⟩
      · have hc : oaCompetitive d epsilon s q := by
          intro u hu
          exact lt_of_not_ge (fun h => hgap ⟨u,hu,h⟩)
        obtain ⟨y,hy,hqy,hL⟩ := oa_master_integer_witness d s.history q hq.1
        obtain ⟨b,hb,hby⟩ := oa_fiber_reply_exists d y hy hbase hL hdiff
        exact ⟨.next (oaAppend d s b) (.step hq hc hb (by simpa [hby] using hqy)),True.intro⟩
  exact ⟨⟨fun s _ => Classical.choose (hex s),fun s _ => Classical.choose_spec (hex s)⟩⟩

theorem oa_basic_run_completed (d : ModelData n m l r) {epsilon : ℝ}
    (choose : OABasicSelector d epsilon) (fuel : ℕ) (s : OAState n m)
    (hs : OAInvariant d s) {result : OAResult n m} {k : ℕ}
    (h : oaRun d choose.choose fuel s hs = some (result,k)) :
    OABasicCompleted d epsilon s k result := by
  induction fuel generalizing s result k with
  | zero => simp [oaRun] at h
  | succ fuel ih =>
    cases hchoice : choose.choose s hs with
    | stop out hstop =>
      have hord := choose.ordinary s hs
      simp only [hchoice,oaDecisionWithoutEarly] at hord
      simp only [oaRun,hchoice,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨s,.nil s,hord⟩
    | next t hstep =>
      simp only [oaRun,hchoice] at h
      cases hr : oaRun d choose.choose fuel t (oa_continue_invariant d hs hstep) with
      | none => simp [hr] at h
      | some out =>
        rcases out with ⟨out,j⟩
        simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨u,hchain,hstop⟩ := ih t (oa_continue_invariant d hs hstep) hr
        exact ⟨u,.cons hstep hchain,hstop⟩

theorem oa_driver_without_early_finite_return (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) (choose : OABasicSelector d epsilon)
    (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    ∃ result k,
      oaRun d choose.choose ((oaBox d).card+1) (oaInit warm)
        (oa_init_invariant d warm hwarm) = some (result,k) ∧
      OABasicCompleted d epsilon (oaInit warm) k result ∧
      k ≤ (oaBox d).card ∧ k+1 ≤ (oaBox d).card+1 ∧
      OAReturnCertificate d epsilon result := by
  obtain ⟨result,k,hrun,_,hk,hdec,hcert⟩ :=
    oa_driver_finite_return d hconv hdiff hCQ hepsilon choose.choose warm hwarm
  exact ⟨result,k,hrun,oa_basic_run_completed d choose _ _ _ hrun,hk,hdec,hcert⟩

/-- With no nonlinear rows, two continuations are impossible even when early
feasible return is disabled. No CQ or incumbent invariant is needed for this bound. -/
theorem oa_zero_rows_chain_bound (d : ModelData n m 0 r) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s t : OAState n m} {k : ℕ}
    (h : OAChain d epsilon s k t) : k ≤ 1 := by
  cases h with
  | nil _ => omega
  | cons hstep htail =>
    cases htail with
    | nil _ => omega
    | cons hsecond _ =>
      exact False.elim (oa_zero_rows_no_two_continuations d hepsilon hstep hsecond)

theorem oa_zero_rows_completed_bound (d : ModelData n m 0 r) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s : OAState n m} {k : ℕ} {result : OAResult n m}
    (h : OACompleted d epsilon s k result) : k ≤ 1 ∧ k+1 ≤ 2 := by
  obtain ⟨t,hchain,_⟩ := h
  have hk := oa_zero_rows_chain_bound d hepsilon hchain
  omega

theorem oa_zero_rows_run_bound (d : ModelData n m 0 r) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (choose : OASelector d epsilon)
    (s : OAState n m) (hs : OAInvariant d s) :
    ∃ result k, oaRun d choose 2 s hs = some (result,k) ∧
      OACompleted d epsilon s k result ∧ k ≤ 1 ∧ k+1 ≤ 2 ∧
      OAReturnCertificate d epsilon result := by
  cases hr : oaRun d choose 2 s hs with
  | none =>
    obtain ⟨t,hchain⟩ := oa_run_exhausted_chain d choose 2 s hs hr
    have hb := oa_zero_rows_chain_bound d hepsilon hchain
    omega
  | some out =>
    rcases out with ⟨result,k⟩
    have hcompleted := (oa_run_completed d choose 2 s hs hr).1
    have hbound := oa_zero_rows_completed_bound d hepsilon hcompleted
    exact ⟨result,k,rfl,hcompleted,hbound.1,hbound.2,
      oa_completed_sound d (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
        hepsilon hs hcompleted⟩

end Chapter02

#print axioms Chapter02.oa_chain_invariant
#print axioms Chapter02.oa_chain_remaining_bound
#print axioms Chapter02.oa_chain_length_bound
#print axioms Chapter02.oa_completed_sound
#print axioms Chapter02.oa_completed_length_bound
#print axioms Chapter02.oa_selector_exists
#print axioms Chapter02.oa_run_completed
#print axioms Chapter02.oa_run_sound
#print axioms Chapter02.oa_run_exhausted_chain
#print axioms Chapter02.oa_run_sufficient_fuel
#print axioms Chapter02.oa_completed_init_bound
#print axioms Chapter02.oa_chain_init_bound
#print axioms Chapter02.oa_driver_finite_return
#print axioms Chapter02.oa_completed_solution_within
#print axioms Chapter02.oa_completed_zero_optimal
#print axioms Chapter02.oa_chain_of_sequence
#print axioms Chapter02.oa_no_infinite_continuations
#print axioms Chapter02.oa_procedure_exists_and_returns
#print axioms Chapter02.oa_driver_exact_finite_return
#print axioms Chapter02.oa_basic_stop_is_stop
#print axioms Chapter02.oa_basic_completed_is_completed
#print axioms Chapter02.oa_basic_selector_exists
#print axioms Chapter02.oa_basic_run_completed
#print axioms Chapter02.oa_driver_without_early_finite_return
#print axioms Chapter02.oa_zero_rows_chain_bound
#print axioms Chapter02.oa_zero_rows_completed_bound
#print axioms Chapter02.oa_zero_rows_run_bound
