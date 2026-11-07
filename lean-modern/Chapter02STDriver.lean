module

public import Chapter02STProgress
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

/-! Counted complete cycles and raw two-stage traces for the single-tree repair.
Initialization solves the actual nonlinear root and permits integral roots to
continue into the seeded LP tree. Selector existence is classical exact-reply
classification, not numerical solver termination. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

def stInitial (d : ModelData n m l r) (q : Point n m)
    (warm : Option (Point n m) := none) : STState n m l :=
  ⟨[⟨q,Set.univ⟩],oaInit warm,[⟨bbRootNode d,(d.objective q : WithBot ℝ)⟩],none⟩

inductive STInitialize (d : ModelData n m l r) (warm : Option (Point n m)) :
    OAResult n m ⊕ STState n m l → Prop
  | empty (he : d.relaxationOn Set.univ = ∅) : STInitialize d warm (.inl .infeasible)
  | unbounded (h : ∀ B : ℝ, ∃ q ∈ d.relaxationOn Set.univ, d.objective q < B) :
      STInitialize d warm (.inl .infeasible)
  | unattained (hn : (d.relaxationOn Set.univ).Nonempty)
      (hb : BddBelow (d.objective '' d.relaxationOn Set.univ))
      (ha : ¬ ∃ q, IsMinimizer (d.relaxationOn Set.univ) d.objective q) :
      STInitialize d warm (.inl .infeasible)
  | integral (q : Point n m)
      (hq : IsMinimizer (d.relaxationOn Set.univ) d.objective q)
      (hi : BBIntegerPoint q) : STInitialize d warm (.inl (.solution q))
  | seeded (q : Point n m)
      (hq : IsMinimizer (d.relaxationOn Set.univ) d.objective q) :
      STInitialize d warm (.inr (stInitial d q warm))

theorem st_initialize_exists (d : ModelData n m l r) (warm : Option (Point n m)) :
    ∃ out, STInitialize d warm out := by
  obtain ⟨reply⟩ := bb_reply_exists d d.objective (bbRootNode d)
  cases reply with
  | empty he => exact ⟨_,.empty (by simpa only [bb_root_region] using he)⟩
  | minimum q hq => exact ⟨_,.seeded q (by simpa only [bb_root_region] using hq)⟩
  | unbounded hu => exact ⟨_,.unbounded (by simpa only [bb_root_region] using hu)⟩
  | unattained hn hb ha => exact ⟨_,.unattained
      (by simpa only [bb_root_region] using hn)
      (by simpa only [bb_root_region] using hb)
      (by simpa only [bb_root_region] using ha)⟩

theorem st_initial_invariant (d : ModelData n m l r) (q : Point n m)
    (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hq : IsMinimizer (d.relaxationOn Set.univ) d.objective q) :
    STInvariant d (stInitial d q warm) := by
  refine ⟨oa_init_invariant d warm hw,?_,?_,?_⟩
  · intro b hb
    simp only [stInitial,stFrontier,Option.toList_none,List.nil_append,
      List.mem_singleton] at hb
    subst b
    exact bb_refines_refl _
  · intro b hb p hp
    simp only [stInitial,stFrontier,Option.toList_none,List.nil_append,
      List.mem_singleton] at hb
    subst b
    have hpp := bb_feasible_subset_region d (bbRootNode d) hp
    have hh := hq.2 p (by simpa only [bb_root_region] using hpp)
    simpa using hh
  · intro p hp
    exact Or.inl ⟨⟨bbRootNode d,(d.objective q : WithBot ℝ)⟩,
      by simp [stInitial,stFrontier],by simpa only [bb_root_feasible] using hp⟩

theorem st_initial_ready (d : ModelData n m l r) (q : Point n m)
    (warm : Option (Point n m)) : (stInitial d q warm).working = none := rfl

theorem st_initial_potential (d : ModelData n m l r) (q : Point n m)
    (warm : Option (Point n m)) :
    stPotential d (stInitial d q warm) = (bbRootNode d).weight + (oaBox d).card := by
  classical
  simp [stPotential,stTreeWeight,stFrontier,stInitial,oaRemaining,oaSeen,oaInit]

theorem st_initialize_tree_invariant (d : ModelData n m l r)
    (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    {s : STState n m l} (h : STInitialize d warm (.inr s)) :
    STInvariant d s ∧ s.working = none ∧
      stPotential d s = (bbRootNode d).weight + (oaBox d).card := by
  cases h with
  | seeded q hq => exact ⟨st_initial_invariant d q warm hw hq,rfl,
      st_initial_potential d q warm⟩

theorem st_initialize_return_sound (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (warm : Option (Point n m)) {out : OAResult n m}
    (h : STInitialize d warm (.inl out)) : OAReturnCertificate d epsilon out := by
  cases h with
  | empty hh =>
    rintro ⟨p,hp⟩
    have hp' := bb_feasible_subset_region d (bbRootNode d)
      (by simpa only [bb_root_feasible] using hp)
    simp only [bb_root_region,hh,Set.mem_empty_iff_false] at hp'
  | unbounded hu =>
    have hh := bb_bad_unbounded_empty d d.objective hbase (fun j => (hdiff j).continuous)
      (linearForm_continuous d.c1 d.c2).continuousOn (bb_refines_refl (bbRootNode d))
      (by simpa only [bb_root_region] using hu)
    change ¬ (d.feasibleOn Set.univ).Nonempty
    rw [bb_root_feasible] at hh
    rw [hh]
    exact Set.not_nonempty_empty
  | unattained hn hb ha =>
    have hh := bb_bad_unattained_empty d d.objective hbase (fun j => (hdiff j).continuous)
      (linearForm_continuous d.c1 d.c2).continuousOn (bb_refines_refl (bbRootNode d))
      (by simpa only [bb_root_region] using hn)
      (by simpa only [bb_root_region] using hb)
      (by simpa only [bb_root_region] using ha)
    change ¬ (d.feasibleOn Set.univ).Nonempty
    rw [bb_root_feasible] at hh
    rw [hh]
    exact Set.not_nonempty_empty
  | integral q hq hi =>
    have hqf : q ∈ d.feasibleOn Set.univ := by
      rw [← bb_root_feasible,bb_feasible_mem_iff,bb_root_region]
      exact ⟨hq.1,hi⟩
    refine ⟨hqf,d.objective q,?_,by linarith⟩
    intro p hp
    exact hq.2 p (by
      have hpp := bb_feasible_subset_region d (bbRootNode d)
        (by simpa only [bb_root_feasible] using hp)
      simpa only [bb_root_region] using hpp)

inductive STTrace (d : ModelData n m l r) : ℕ → STState n m l → STState n m l → Prop
  | nil (s : STState n m l) : STTrace d 0 s s
  | cons {k s t u} (step : STProcess d s t) (tail : STTrace d k t u) :
      STTrace d (k+1) s u

inductive STMicroTrace (d : ModelData n m l r) : ℕ → STState n m l → STState n m l → Prop
  | nil (s : STState n m l) : STMicroTrace d 0 s s
  | cons {k s t u} (step : STStep d s t) (tail : STMicroTrace d k t u) :
      STMicroTrace d (k+1) s u

theorem st_trace_trans (d : ModelData n m l r) {k j : ℕ} {s t u : STState n m l}
    (h : STTrace d k s t) (h' : STTrace d j t u) : STTrace d (k+j) s u := by
  induction h with
  | nil s => simpa using h'
  | cons step tail ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using STTrace.cons step (ih h')

theorem st_trace_append_step (d : ModelData n m l r) {k : ℕ} {s t u : STState n m l}
    (h : STTrace d k s t) (step : STProcess d t u) : STTrace d (k+1) s u :=
  st_trace_trans d h (.cons step (.nil u))

theorem st_micro_trace_trans (d : ModelData n m l r) {k j : ℕ} {s t u : STState n m l}
    (h : STMicroTrace d k s t) (h' : STMicroTrace d j t u) : STMicroTrace d (k+j) s u := by
  induction h with
  | nil s => simpa using h'
  | cons step tail ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using STMicroTrace.cons step (ih h')

theorem st_trace_micro (d : ModelData n m l r) {k : ℕ} {s t : STState n m l}
    (h : STTrace d k s t) : STMicroTrace d (2*k) s t := by
  induction h with
  | nil s => exact .nil s
  | cons step tail ih =>
    obtain ⟨w,hsel,hres⟩ := step
    simpa [Nat.mul_add,Nat.add_assoc] using
      STMicroTrace.cons (.select hsel) (STMicroTrace.cons (.resolve hres) ih)

theorem st_trace_invariant (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    {k : ℕ} {s t : STState n m l} (hs : STInvariant d s) (h : STTrace d k s t) :
    STInvariant d t := by
  induction h with
  | nil s => exact hs
  | cons step tail ih => exact ih (st_process_preserves_invariant d hbase hconv hdiff hs step)

theorem st_micro_trace_invariant (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    {k : ℕ} {s t : STState n m l} (hs : STInvariant d s) (h : STMicroTrace d k s t) :
    STInvariant d t := by
  induction h with
  | nil s => exact hs
  | cons step tail ih => exact ih (st_step_preserves_invariant d hbase hconv hdiff hs step)

theorem st_trace_potential_bound (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    {k : ℕ} {s t : STState n m l} (hs : STInvariant d s) (h : STTrace d k s t) :
    k+stPotential d t ≤ stPotential d s := by
  induction h with
  | nil s => omega
  | cons step tail ih =>
    have hp := st_process_potential_drop d hconv hdiff hCQ hs step
    have ht := ih (st_process_preserves_invariant d hbase hconv hdiff hs step)
    omega

theorem st_micro_trace_potential_bound (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    {k : ℕ} {s t : STState n m l} (hs : STInvariant d s) (h : STMicroTrace d k s t) :
    k+stPhasePotential d t ≤ stPhasePotential d s := by
  induction h with
  | nil s => omega
  | cons step tail ih =>
    have hp := st_step_phase_drop d hconv hdiff hCQ hs step
    have ht := ih (st_step_preserves_invariant d hbase hconv hdiff hs step)
    omega

theorem st_every_trace_length_bound (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    {k : ℕ} {s t : STState n m l} (hs : STInvariant d s) (h : STTrace d k s t) :
    k ≤ stPotential d s := by
  have hh := st_trace_potential_bound d hbase hconv hdiff hCQ hs h
  omega

theorem st_no_infinite_raw_execution (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (s : ℕ → STState n m l) (hs : STInvariant d (s 0)) :
    ¬ ∀ k, STStep d (s k) (s (k+1)) := by
  intro h
  have ht : ∀ k, STMicroTrace d k (s 0) (s k) := by
    intro k
    induction k with
    | zero => exact .nil _
    | succ k ih => exact st_micro_trace_trans d ih (.cons (h k) (.nil _))
  have hh := st_micro_trace_potential_bound d hbase hconv hdiff hCQ hs
    (ht (stPhasePotential d (s 0)+1))
  omega

theorem st_not_prunable_competitive (d : ModelData n m l r) (o : OAState n m)
    (q : Point n m) (hp : ¬ bbPrunable .weak d.objective o.incumbent (d.objective q)) :
    oaCompetitive d 0 o q := by
  intro u hu
  have hh : ¬ d.objective u ≤ d.objective q := by
    simpa [bbPrunable,hu] using hp
  simpa using lt_of_not_ge hh

theorem st_resolve_exists (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (s : STState n m l) (hs : STInvariant d s) (hw : s.working.isSome = true) :
    ∃ t, STResolve d s t := by
  classical
  rcases s with ⟨seeds,o,live,working⟩
  cases working with
  | none => simp at hw
  | some b =>
    obtain ⟨reply⟩ := st_lp_reply_exists d seeds o.history b.node
    cases reply with
    | empty h => exact ⟨_,.empty h⟩
    | unbounded h => exact ⟨_,.unbounded h⟩
    | unattained hn hb ha => exact ⟨_,.unattained hn hb ha⟩
    | minimum q hq =>
      by_cases hp : bbPrunable .weak d.objective o.incumbent (d.objective q)
      · exact ⟨_,.prune hq hp⟩
      · have hc := st_not_prunable_competitive d o q hp
        by_cases hi : BBIntegerPoint q
        · obtain ⟨batch,hb,hy⟩ := st_lp_fiber_reply d seeds o.history b.node hbase hdiff
            (hs.refines b (by simp [stFrontier])) hq.1 hi
          exact ⟨_,.callback hq hc hb hy⟩
        · obtain ⟨i,hf⟩ := bb_fractional_coordinate hi
          exact ⟨_,.branch i hq hc hf⟩

theorem st_process_exists (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (s : STState n m l) (hs : STInvariant d s)
    (hw : s.working = none) (hl : s.live ≠ []) : ∃ t, STProcess d s t := by
  rcases s with ⟨seeds,o,live,working⟩
  cases working with
  | some b => cases hw
  | none =>
    cases live with
    | nil => exact (hl rfl).elim
    | cons b post =>
      have hsel := STSelect.choose seeds o [] post b
      obtain ⟨t,ht⟩ := st_resolve_exists d hbase hdiff _
        (st_select_preserves_invariant d hs hsel) rfl
      exact ⟨t,_,hsel,ht⟩

theorem st_trace_ready (d : ModelData n m l r) {k : ℕ} {s t : STState n m l}
    (hs : s.working = none) (h : STTrace d k s t) : t.working = none := by
  induction h with
  | nil s => exact hs
  | cons step tail ih => exact ih (st_process_ready step).2

theorem st_step_from_ready {d : ModelData n m l r} {s t : STState n m l}
    (hs : s.working = none) (h : STStep d s t) : STSelect s t := by
  cases h with
  | select h => exact h
  | resolve h => cases h <;> cases hs

theorem st_select_target_working {s t : STState n m l} (h : STSelect s t) :
    t.working.isSome = true := by cases h; rfl

theorem st_step_from_working {d : ModelData n m l r} {s t : STState n m l}
    (hs : s.working.isSome = true) (h : STStep d s t) : STResolve d s t := by
  cases h with
  | select h => cases h; cases hs
  | resolve h => exact h

/-- Every raw ready-to-ready trace is an exact sequence of complete cycles.
This preserves arbitrary working-phase replies, not only a fixed reply policy. -/
theorem st_micro_ready_cycles (d : ModelData n m l r) {j : ℕ}
    {s t : STState n m l} (hs : s.working = none) (ht : t.working = none)
    (h : STMicroTrace d j s t) : ∃ k, j=2*k ∧ STTrace d k s t := by
  induction j using Nat.strong_induction_on generalizing s t with
  | h j ih =>
    cases h with
    | nil s => exact ⟨0,rfl,.nil s⟩
    | @cons k s w t step tail =>
      have hsel := st_step_from_ready hs step
      have hw := st_select_target_working hsel
      cases tail with
      | nil => simp [ht] at hw
      | @cons a w v t step' tail' =>
        have hres := st_step_from_working hw step'
        obtain ⟨k,hk,htrace⟩ := ih a (by omega) (st_resolve_ready hres) ht tail'
        exact ⟨k+1,by omega,.cons ⟨w,hsel,hres⟩ htrace⟩

def STDecisionLegal (d : ModelData n m l r) (epsilon : ℝ) (s : STState n m l) :
    OAResult n m ⊕ STState n m l → Prop
  | .inl out => STStop d epsilon s out
  | .inr t => STProcess d s t

/-- The selector chooses a complete selection/resolution cycle in ready states.
Its correctness domain is derived from source initialization at public endpoints.
Raw two-stage traces are independently bounded and exactly correspond to cycles. -/
def STSelector (d : ModelData n m l r) (epsilon : ℝ) :=
  ∀ s : STState n m l, {c : OAResult n m ⊕ STState n m l //
    STInvariant d s → s.working = none → STDecisionLegal d epsilon s c}

theorem st_selector_exists (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) : Nonempty (STSelector d epsilon) := by
  classical
  have hex : ∀ s : STState n m l, Nonempty {c : OAResult n m ⊕ STState n m l //
      STInvariant d s → s.working = none → STDecisionLegal d epsilon s c} := by
    intro s
    by_cases hv : STInvariant d s ∧ s.working = none
    · by_cases he : s.live = []
      · cases hi : s.oa.incumbent with
        | none => exact ⟨⟨.inl .infeasible,fun _ _ => .infeasible hv.2 he hi⟩⟩
        | some q => exact ⟨⟨.inl (.solution q),fun _ _ => .exhausted hv.2 he hi⟩⟩
      · obtain ⟨t,ht⟩ := st_process_exists d hbase hdiff s hv.1 hv.2 he
        exact ⟨⟨.inr t,fun _ _ => ht⟩⟩
    · exact ⟨⟨.inl .infeasible,fun hs hr => (hv ⟨hs,hr⟩).elim⟩⟩
  exact ⟨fun s => Classical.choice (hex s)⟩

inductive STDriverState (n m l : ℕ)
  | active (state : STState n m l)
  | stopped (state : STState n m l) (out : OAResult n m)

def stRun (d : ModelData n m l r) (epsilon : ℝ) (choose : STSelector d epsilon)
    (initial : STState n m l) : ℕ → STDriverState n m l
  | 0 => .active initial
  | k+1 => match stRun d epsilon choose initial k with
    | .stopped s out => .stopped s out
    | .active s => match (choose s).val with
      | .inl out => .stopped s out
      | .inr t => .active t

theorem st_run_invariant (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (choose : STSelector d epsilon) (initial : STState n m l)
    (hi : STInvariant d initial) (hr : initial.working = none) (k : ℕ) :
    match stRun d epsilon choose initial k with
    | .active s => STTrace d k initial s ∧ STInvariant d s ∧ s.working = none
    | .stopped s out => ∃ j<k, STTrace d j initial s ∧ STInvariant d s ∧ STStop d epsilon s out := by
  induction k with
  | zero => exact ⟨.nil initial,hi,hr⟩
  | succ k ih =>
    simp only [stRun]
    cases hh : stRun d epsilon choose initial k with
    | active s =>
      rw [hh] at ih
      have hlegal := (choose s).property ih.2.1 ih.2.2
      cases hc : (choose s).val with
      | inl out =>
        simp only [hc,STDecisionLegal] at hlegal ⊢
        exact ⟨k,by omega,ih.1,ih.2.1,hlegal⟩
      | inr t =>
        simp only [hc,STDecisionLegal] at hlegal ⊢
        exact ⟨st_trace_append_step d ih.1 hlegal,
          st_process_preserves_invariant d hbase hconv hdiff ih.2.1 hlegal,
          (st_process_ready hlegal).2⟩
    | stopped s out =>
      rw [hh] at ih
      obtain ⟨j,hj,htrace,hs,hstop⟩ := ih
      exact ⟨j,by omega,htrace,hs,hstop⟩

theorem st_every_selector_finite_return (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (choose : STSelector d epsilon) (initial : STState n m l)
    (hi : STInvariant d initial) (hr : initial.working = none) :
    ∃ s out, stRun d epsilon choose initial (stPotential d initial+1) = .stopped s out := by
  have h := st_run_invariant d epsilon hbase hconv hdiff choose initial hi hr
    (stPotential d initial+1)
  cases hh : stRun d epsilon choose initial (stPotential d initial+1) with
  | active s =>
    rw [hh] at h
    have hb := st_every_trace_length_bound d hbase hconv hdiff hCQ hi h.1
    omega
  | stopped s out => exact ⟨s,out,rfl⟩

theorem st_stopped_run_trace (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (choose : STSelector d epsilon) (initial : STState n m l)
    (hi : STInvariant d initial) (hr : initial.working = none)
    {k : ℕ} {s : STState n m l} {out : OAResult n m}
    (h : stRun d epsilon choose initial k = .stopped s out) :
    ∃ j ≤ stPotential d initial, j<k ∧ STTrace d j initial s ∧
      STInvariant d s ∧ STStop d epsilon s out := by
  have hh := st_run_invariant d epsilon hbase hconv hdiff choose initial hi hr k
  rw [h] at hh
  obtain ⟨j,hj,ht,hs,hstop⟩ := hh
  exact ⟨j,st_every_trace_length_bound d hbase hconv hdiff hCQ hi ht,hj,ht,hs,hstop⟩

/-- Source-initialized endpoint: no invariant, progress or reply-existence oracle
is a premise. The two-stage execution has exactly twice the process count. -/
theorem st_every_initialized_selector_returns (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (choose : STSelector d epsilon) {s : STState n m l}
    (hinit : STInitialize d warm (.inr s)) :
    ∃ t out k, k ≤ (bbRootNode d).weight+(oaBox d).card ∧
      STTrace d k s t ∧ STMicroTrace d (2*k) s t ∧ STStop d epsilon t out ∧
      stRun d epsilon choose s ((bbRootNode d).weight+(oaBox d).card+1) = .stopped t out ∧
      OAReturnCertificate d epsilon out := by
  obtain ⟨hi,hr,hp⟩ := st_initialize_tree_invariant d warm hw hinit
  obtain ⟨t,out,hret⟩ := st_every_selector_finite_return d epsilon hbase hconv hdiff hCQ
    choose s hi hr
  obtain ⟨k,hk,_,ht,hInv,hStop⟩ := st_stopped_run_trace d epsilon hbase hconv hdiff hCQ
    choose s hi hr hret
  exact ⟨t,out,k,by simpa only [hp] using hk,ht,st_trace_micro d ht,hStop,
    by simpa only [hp] using hret,st_stop_sound d he hInv hStop⟩

theorem st_source_selector_exists_and_returns (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (hCQ : OAFiberSlater d)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ) :
    ∃ choose : STSelector d epsilon, ∀ initial, STInitialize d warm initial →
      match initial with
      | .inl out => OAReturnCertificate d epsilon out
      | .inr s => ∃ t out k, k ≤ (bbRootNode d).weight+(oaBox d).card ∧
          STTrace d k s t ∧ STMicroTrace d (2*k) s t ∧ STStop d epsilon t out ∧
          stRun d epsilon choose s ((bbRootNode d).weight+(oaBox d).card+1) = .stopped t out ∧
          OAReturnCertificate d epsilon out := by
  have hd : ∀ j, Differentiable ℝ (d.g j) := fun j => (hC1 j).differentiable (by norm_num)
  obtain ⟨choose⟩ := st_selector_exists d epsilon hbase hd
  refine ⟨choose,?_⟩
  intro initial hinit
  cases initial with
  | inl out => exact st_initialize_return_sound d hbase hd he warm hinit
  | inr s => exact st_every_initialized_selector_returns d hbase hconv hd hCQ epsilon he warm hw choose hinit

theorem st_source_no_infinite_raw_execution (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (s : ℕ → STState n m l) (hinit : STInitialize d warm (.inr (s 0))) :
    ¬ ∀ k, STStep d (s k) (s (k+1)) :=
  st_no_infinite_raw_execution d hbase hconv hdiff hCQ s
    (st_initialize_tree_invariant d warm hw hinit).1

theorem st_trace_global_bound_mono (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {k : ℕ} {s t : STState n m l}
    (hs : STInvariant d s) (h : STTrace d k s t) : stGlobalBound d s ≤ stGlobalBound d t := by
  induction h with
  | nil s => exact le_rfl
  | cons step tail ih =>
    exact (st_process_global_bound_mono d hs step).trans
      (ih (st_process_preserves_invariant d hbase hconv hdiff hs step))

theorem st_trace_incumbent_nonincreasing (d : ModelData n m l r)
    {k : ℕ} {s t : STState n m l} (h : STTrace d k s t) :
    bbIncBound d.objective t.oa.incumbent ≤ bbIncBound d.objective s.oa.incumbent := by
  induction h with
  | nil s => exact le_rfl
  | cons step tail ih => exact ih.trans (st_process_incumbent_nonincreasing d step)

theorem st_initialized_trace_global_bound_mono (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    {k : ℕ} {s t : STState n m l} (hi : STInitialize d warm (.inr s))
    (h : STTrace d k s t) : stGlobalBound d s ≤ stGlobalBound d t :=
  st_trace_global_bound_mono d hbase hconv hdiff
    (st_initialize_tree_invariant d warm hw hi).1 h

theorem st_initialized_micro_trace_bound (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    {k : ℕ} {s t : STState n m l} (hi : STInitialize d warm (.inr s))
    (h : STMicroTrace d k s t) :
    k ≤ 2*((bbRootNode d).weight+(oaBox d).card)+1 := by
  obtain ⟨hs,hr,hp⟩ := st_initialize_tree_invariant d warm hw hi
  have hb := st_micro_trace_potential_bound d hbase hconv hdiff hCQ hs h
  simp only [stPhasePotential,hr,Option.isNone_none,Bool.true_eq,if_true,hp] at hb
  omega

theorem st_initialized_ready_micro_trace_bound (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    {j : ℕ} {s t : STState n m l} (hi : STInitialize d warm (.inr s))
    (hr : t.working = none) (h : STMicroTrace d j s t) :
    ∃ k, j=2*k ∧ k ≤ (bbRootNode d).weight+(oaBox d).card ∧ STTrace d k s t := by
  obtain ⟨hs,hsr,hp⟩ := st_initialize_tree_invariant d warm hw hi
  obtain ⟨k,hk,ht⟩ := st_micro_ready_cycles d hsr hr h
  exact ⟨k,hk,by simpa only [hp] using
    st_every_trace_length_bound d hbase hconv hdiff hCQ hs ht,ht⟩

theorem st_initialized_stop_sound (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    {k : ℕ} {s t : STState n m l} {out : OAResult n m}
    (hi : STInitialize d warm (.inr s)) (h : STMicroTrace d k s t)
    (hstop : STStop d epsilon t out) : OAReturnCertificate d epsilon out :=
  st_stop_sound d he (st_micro_trace_invariant d hbase hconv hdiff
    (st_initialize_tree_invariant d warm hw hi).1 h) hstop

def STExactOutcome (d : ModelData n m l r) : OAResult n m → Prop
  | .infeasible => ¬ (d.feasibleOn Set.univ).Nonempty
  | .solution p => IsMinimizer (d.feasibleOn Set.univ) d.objective p

theorem st_zero_certificate_exact (d : ModelData n m l r) (out : OAResult n m)
    (h : OAReturnCertificate d 0 out) : STExactOutcome d out := by
  cases out with
  | infeasible => exact h
  | solution p => exact oa_certificate_zero_optimal d h

theorem st_every_initialized_selector_exact_return (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (warm : Option (Point n m))
    (hw : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (choose : STSelector d 0) {s : STState n m l}
    (hinit : STInitialize d warm (.inr s)) :
    ∃ t out k, k ≤ (bbRootNode d).weight+(oaBox d).card ∧
      STTrace d k s t ∧ STMicroTrace d (2*k) s t ∧ STStop d 0 t out ∧
      stRun d 0 choose s ((bbRootNode d).weight+(oaBox d).card+1) = .stopped t out ∧
      STExactOutcome d out := by
  obtain ⟨t,out,k,hk,ht,hm,hs,hr,hcert⟩ := st_every_initialized_selector_returns d
    hbase hconv hdiff hCQ 0 le_rfl warm hw choose hinit
  exact ⟨t,out,k,hk,ht,hm,hs,hr,st_zero_certificate_exact d out hcert⟩

end Chapter02


#print axioms Chapter02.st_initialize_exists
#print axioms Chapter02.st_initial_invariant
#print axioms Chapter02.st_initial_ready
#print axioms Chapter02.st_initial_potential
#print axioms Chapter02.st_initialize_tree_invariant
#print axioms Chapter02.st_initialize_return_sound
#print axioms Chapter02.st_trace_trans
#print axioms Chapter02.st_trace_append_step
#print axioms Chapter02.st_micro_trace_trans
#print axioms Chapter02.st_trace_micro
#print axioms Chapter02.st_trace_invariant
#print axioms Chapter02.st_micro_trace_invariant
#print axioms Chapter02.st_trace_potential_bound
#print axioms Chapter02.st_micro_trace_potential_bound
#print axioms Chapter02.st_every_trace_length_bound
#print axioms Chapter02.st_no_infinite_raw_execution
#print axioms Chapter02.st_not_prunable_competitive
#print axioms Chapter02.st_resolve_exists
#print axioms Chapter02.st_process_exists
#print axioms Chapter02.st_trace_ready
#print axioms Chapter02.st_step_from_ready
#print axioms Chapter02.st_select_target_working
#print axioms Chapter02.st_step_from_working
#print axioms Chapter02.st_micro_ready_cycles
#print axioms Chapter02.st_selector_exists
#print axioms Chapter02.st_run_invariant
#print axioms Chapter02.st_every_selector_finite_return
#print axioms Chapter02.st_stopped_run_trace
#print axioms Chapter02.st_every_initialized_selector_returns
#print axioms Chapter02.st_source_selector_exists_and_returns
#print axioms Chapter02.st_source_no_infinite_raw_execution
#print axioms Chapter02.st_trace_global_bound_mono
#print axioms Chapter02.st_trace_incumbent_nonincreasing
#print axioms Chapter02.st_initialized_trace_global_bound_mono
#print axioms Chapter02.st_initialized_micro_trace_bound
#print axioms Chapter02.st_initialized_ready_micro_trace_bound
#print axioms Chapter02.st_initialized_stop_sound
#print axioms Chapter02.st_zero_certificate_exact
#print axioms Chapter02.st_every_initialized_selector_exact_return
