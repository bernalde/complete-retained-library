module

public import Chapter03OAExistenceUnboundedMasters

@[expose] public section

/-! Every initializer is the unique fractional seed. Every exact selector of
the unchanged driver returns infeasibility with exactly three master decisions,
two fixed decisions and two individual-slack restorations. Source availability
is obtained from the new complete package, not supplied as a callback. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec.UnboundedControl

/-- Both actual first master replies use the unbounded branch and preserve the
initial lower value, for arbitrary feasible choices and every tolerance. -/
theorem first_two_choices {epsilon : ℝ}
    (q0 : MasterChoice spec seed (initialState spec seed))
    (e0 : Event spec) (hv0 : EventValid spec e0)
    (hy0 : q0.point.1.2 = intCast e0.target)
    (q1 : MasterChoice spec seed (advance (initialState spec seed) q0 e0)) :
    q0.attained = false ∧ q1.attained = false ∧
      (advance (initialState spec seed) q0 e0).lower = 0 ∧ q1.nextLower = 0 := by
  have h0 := short_choice_unbounded (epsilon := epsilon) .initial (by simp [initialState]) q0
  have hr : Reachable spec seed epsilon (advance (initialState spec seed) q0 e0) :=
    .next .initial (.step (by simp [loopOpen,initialState]) q0 e0 hv0 hy0)
  have h1 := short_choice_unbounded hr (by simp [advance,initialState]) q1
  refine ⟨h0,h1,?_,?_⟩
  · simp [advance,MasterChoice.nextLower,h0,initialState,spec,seed,pt]
  · simp [MasterChoice.nextLower,h1,advance,h0,initialState,spec,seed,pt]

theorem second_target_distinct
    (q0 : MasterChoice spec seed (initialState spec seed))
    (e0 : Event spec) (hv0 : EventValid spec e0)
    (q1 : MasterChoice spec seed (advance (initialState spec seed) q0 e0))
    (e1 : Event spec) (hy1 : q1.point.1.2 = intCast e1.target) :
    e1.target ≠ e0.target := by
  intro he
  have hn : e0.restoration ≠ none := by rw [valid_event_restoration hv0]; simp
  exact q1.mem.2 e0 (by simp [advance,initialState]) hn
    (hy1.trans (congrArg intCast he))

theorem two_distinct_events_empty {e0 e1 : Event spec}
    (hv0 : EventValid spec e0) (hv1 : EventValid spec e1)
    (hne : e1.target ≠ e0.target) : master spec seed [e0,e1] = ∅ := by
  obtain ⟨b,rfl⟩ := valid_event_form hv0
  obtain ⟨c,rfl⟩ := valid_event_form hv1
  fin_cases b <;> fin_cases c
  · exact False.elim (hne rfl)
  · exact both_master_empty _ (by simp) (by simp)
  · exact both_master_empty _ (by simp) (by simp)
  · exact False.elim (hne rfl)

theorem box_card : spec.box.card = 2 := by
  classical
  have he : spec.box = {target 0,target 1} := by
    ext y
    simp only [Data.box,Set.Finite.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · exact target_cases y
    · rintro (rfl | rfl)
      · exact target_mem 0
      · exact target_mem 1
  rw [he]
  have ht : target 0 ≠ target 1 := by
    intro h
    have hh := target_injective h
    norm_num at hh
  simp [ht]

theorem reachable_incumbent_none {epsilon : ℝ} {s : State spec}
    (hs : Reachable spec seed epsilon s) : s.incumbent = none := by
  cases hi : s.incumbent with
  | none => rfl
  | some p =>
    exact False.elim (original_empty
      ⟨p,(reachable_invariant analytic seed_valid hs).feasible p hi⟩)

theorem reachable_open {epsilon : ℝ} {s : State spec}
    (hs : Reachable spec seed epsilon s) : loopOpen spec epsilon s := by
  simp [loopOpen,reachable_incumbent_none hs]

theorem empty_master_history_length (H : List (Event spec))
    (hv : ∀ e ∈ H, EventValid spec e) (he : master spec seed H = ∅) :
    2 ≤ H.length := by
  by_contra hn
  have hne := (short_master_unbounded H hv (by omega)).1
  rw [he] at hne
  exact Set.not_nonempty_empty hne

theorem execution_shape {epsilon : ℝ} {s : State spec} {out : Output 2 1}
    (hx : Execution spec seed epsilon s out) (hs : Reachable spec seed epsilon s) :
    out.result = .infeasible ∧ out.masters = out.fixed+1 ∧
      out.restorations = out.fixed ∧ 2 ≤ out.fixed+s.history.length := by
  induction hx with
  | @gap s p hi ht =>
    rw [reachable_incumbent_none hs] at hi
    cases hi
  | @empty s ho he =>
    have hl := empty_master_history_length s.history
      (reachable_invariant analytic seed_valid hs).history.2 he
    exact ⟨rfl,rfl,rfl,by simpa using hl⟩
  | @step s ho q e he hy out tail ih =>
    have htail := ih (.next hs (.step ho q e he hy))
    have hrest : eventRestorations e = 1 := by
      simp [eventRestorations,valid_event_restoration he]
    rcases htail with ⟨hr,hm,hf,hl⟩
    refine ⟨hr,?_,?_,?_⟩
    · simp only [countStep]
      omega
    · simp only [countStep,hrest]
      omega
    · simp only [advance,List.length_append,List.length_singleton] at hl
      simp only [countStep]
      omega

theorem exact_loop_counts {epsilon : ℝ} {choose : Selector spec seed epsilon}
    {out : Output 2 1}
    (hr : runFuel spec seed epsilon choose (spec.box.card+1)
      (initialState spec seed) .initial = some out)
    (hmasters : out.masters ≤ spec.box.card+1) :
    out.result = .infeasible ∧ out.masters = 3 ∧ out.fixed = 2 ∧ out.restorations = 2 := by
  have hx := runFuel_execution spec seed epsilon choose _ _ .initial hr
  obtain ⟨hres,hm,hf,hl⟩ := execution_shape hx .initial
  rw [box_card] at hmasters
  simp only [initialState,List.length_nil,Nat.add_zero] at hl
  exact ⟨hres,by omega,by omega,by omega⟩

theorem every_selector_return {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (Selector spec seed epsilon) ∧
    ∀ choose : Selector spec seed epsilon, ∃ out,
      runFuel spec seed epsilon choose 3 (initialState spec seed) .initial = some out ∧
      ReturnCertificate spec epsilon out.result ∧ out.result = .infeasible ∧
      out.masters = 3 ∧ out.fixed = 2 ∧ out.restorations = 2 := by
  refine ⟨selector_inhabited (assumptions.local_available seed seed_valid epsilon),?_⟩
  intro choose
  obtain ⟨out,hr,hc,hm,_,_⟩ := finite_return_with_counts analytic seed_valid heps choose
  have hh := exact_loop_counts hr hm
  refine ⟨out,?_,hc,hh⟩
  simpa only [box_card] using hr

/-- Actual invocation of the complete source-assumption endpoint, followed by
exact counts for every initializer and every selector of its unchanged execute.
The continuous domain is unbounded; fixed-fiber LICQ is vacuous here. -/
theorem every_initialized_selector_return {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (Initialization spec) ∧ Nonempty (InitializedSelectors spec epsilon) ∧
    ∀ (choose : InitializedSelectors spec epsilon) (initial : Initialization spec),
      ∃ out, execute spec epsilon choose initial = some out ∧
        ReturnCertificate spec epsilon out.result ∧ out.result = .infeasible ∧
        out.masters = 3 ∧ out.fixed = 2 ∧ out.restorations = 2 := by
  have source := article_source_initialized_finite_return bounds spec bounds_encoding
    analytic domain_article bounded_relaxation fixed_licq heps
  refine ⟨source.1,source.2.2.1,?_⟩
  intro choose initial
  obtain ⟨out,hr,hc,hm,_,_⟩ := source.2.2.2 choose initial
  refine ⟨out,hr,hc,?_⟩
  cases initial with
  | empty he =>
    have hp := seed_minimum.1
    rw [he] at hp
    exact False.elim hp
  | minimum p hp hd =>
    have he := (relaxation_iff p).mp hp.1
    subst p
    simp only [execute,dif_neg seed_fractional] at hr
    exact exact_loop_counts hr hm

end Chapter03.OAExec.UnboundedControl

#print axioms Chapter03.OAExec.UnboundedControl.every_selector_return
#print axioms Chapter03.OAExec.UnboundedControl.every_initialized_selector_return
