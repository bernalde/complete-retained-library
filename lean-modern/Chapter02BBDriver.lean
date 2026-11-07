module

public import Chapter02BBState
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

/-! Every-choice finite exact NLP-BB execution. Processing counts occurrences;
the final empty-heap inspection is one additional decision. Selector existence
is classical mathematical classification, not numerical NLP runtime. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

inductive BBTrace (d : ModelData n m l r) (f : Point n m → ℝ) (policy : BBPolicy) :
    ℕ → BBState n m → BBState n m → Prop
  | nil (s : BBState n m) : BBTrace d f policy 0 s s
  | cons {k s t u} (step : BBProcess d f policy s t) (tail : BBTrace d f policy k t u) :
      BBTrace d f policy (k + 1) s u

theorem bb_trace_trans (d : ModelData n m l r) (f : Point n m → ℝ) (policy : BBPolicy)
    {k j : ℕ} {s t u : BBState n m} (h : BBTrace d f policy k s t)
    (h' : BBTrace d f policy j t u) : BBTrace d f policy (k + j) s u := by
  induction h with
  | nil s => simpa using h'
  | cons step tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using BBTrace.cons step (ih h')

theorem bb_trace_append_step (d : ModelData n m l r) (f : Point n m → ℝ) (policy : BBPolicy)
    {k : ℕ} {s t u : BBState n m} (h : BBTrace d f policy k s t)
    (step : BBProcess d f policy t u) : BBTrace d f policy (k + 1) s u :=
  bb_trace_trans d f policy h (.cons step (.nil u))

theorem bb_trace_potential_bound (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) {k : ℕ} {s t : BBState n m} (h : BBTrace d f policy k s t) :
    k + bbPotential t ≤ bbPotential s := by
  induction h with
  | nil s => simp
  | cons step tail ih =>
    have hs := bb_process_potential_drop d f policy step
    omega

theorem bb_every_trace_length_bound (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) {k : ℕ} {s t : BBState n m} (h : BBTrace d f policy k s t) :
    k ≤ bbPotential s := by
  have hh := bb_trace_potential_bound d f policy h
  omega

theorem bb_trace_reachable (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m)) {k : ℕ} {s t : BBState n m}
    (hs : BBReachable d f policy warm s) (h : BBTrace d f policy k s t) :
    BBReachable d f policy warm t := by
  induction h with
  | nil s => exact hs
  | cons step tail ih => exact ih (.next hs step)

theorem bb_trace_global_bound_mono (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j)) (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi))
    {k : ℕ} {s t : BBState n m} (hs : BBInvariant d f s) (h : BBTrace d f policy k s t) :
    bbGlobalBound f s ≤ bbGlobalBound f t := by
  induction h with
  | nil s => exact le_rfl
  | cons step tail ih =>
    exact (bb_process_global_bound_mono d f policy hs step).trans
      (ih (bb_process_preserves_invariant d f policy hbase hg hf hs step))

theorem bb_trace_incumbent_bound_nonincreasing (d : ModelData n m l r)
    (f : Point n m → ℝ) (policy : BBPolicy) {k : ℕ} {s t : BBState n m}
    (h : BBTrace d f policy k s t) : bbIncBound f t.incumbent ≤ bbIncBound f s.incumbent := by
  induction h with
  | nil s => exact le_rfl
  | cons step tail ih => exact ih.trans (bb_process_incumbent_bound_nonincreasing d f policy step)

theorem bb_process_exists_of_live_ne_nil (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (s : BBState n m) (hne : s.live ≠ []) :
    ∃ t, BBProcess d f policy s t := by
  classical
  rcases s with ⟨live, inc⟩
  cases live with
  | nil => exact (hne rfl).elim
  | cons b post =>
    obtain ⟨reply⟩ := bb_reply_exists d f b.node
    cases reply with
    | empty h => exact ⟨⟨post, inc⟩, .empty (pre := []) h⟩
    | unbounded h => exact ⟨⟨post, inc⟩, .unbounded (pre := []) h⟩
    | unattained hn hb hh => exact ⟨⟨post, inc⟩, .unattained (pre := []) hn hb hh⟩
    | minimum q hq =>
      by_cases hp : bbPrunable policy f inc (f q)
      · exact ⟨⟨post, inc⟩, .prune (pre := []) hq hp⟩
      · by_cases hi : BBIntegerPoint q
        · exact ⟨⟨post, bbUpdate policy f inc q⟩, .integral (pre := []) hq hp hi⟩
        · obtain ⟨i, hf⟩ := bb_fractional_coordinate hi
          exact ⟨⟨bbChildren b i q f ++ post, inc⟩, .branch (pre := []) i hq hp hf⟩

theorem bb_no_process_of_empty_live (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) {s t : BBState n m} (he : s.live = []) :
    ¬ BBProcess d f policy s t := by
  intro h
  have hp := bb_process_potential_drop d f policy h
  have hz := (bb_potential_eq_zero_iff s).2 he
  omega

theorem bb_maximal_iff_empty_live (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (s : BBState n m) :
    (¬ ∃ t, BBProcess d f policy s t) ↔ s.live = [] := by
  constructor
  · intro h
    by_contra hn
    exact h (bb_process_exists_of_live_ne_nil d f policy s hn)
  · intro h ⟨t, ht⟩
    exact bb_no_process_of_empty_live d f policy h ht

theorem bb_no_infinite_execution (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (s : ℕ → BBState n m) :
    ¬ ∀ k, BBProcess d f policy (s k) (s (k + 1)) := by
  intro h
  have ht : ∀ k, BBTrace d f policy k (s 0) (s k) := by
    intro k
    induction k with
    | zero => exact .nil _
    | succ k ih => exact bb_trace_append_step d f policy ih (h k)
  have hh := bb_every_trace_length_bound d f policy (ht (bbPotential (s 0) + 1))
  omega

def BBDecisionLegal (d : ModelData n m l r) (f : Point n m → ℝ) (policy : BBPolicy)
    (s : BBState n m) : Option (Point n m) ⊕ BBState n m → Prop
  | .inl out => s.live = [] ∧ out = s.incumbent
  | .inr t => BBProcess d f policy s t

def BBSelector (d : ModelData n m l r) (f : Point n m → ℝ) (policy : BBPolicy) :=
  ∀ s : BBState n m, {c : Option (Point n m) ⊕ BBState n m // BBDecisionLegal d f policy s c}

theorem bb_selector_exists (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) : Nonempty (BBSelector d f policy) := by
  classical
  have hex : ∀ s, Nonempty {c : Option (Point n m) ⊕ BBState n m //
      BBDecisionLegal d f policy s c} := by
    intro s
    by_cases he : s.live = []
    · exact ⟨⟨.inl s.incumbent, he, rfl⟩⟩
    · obtain ⟨t, ht⟩ := bb_process_exists_of_live_ne_nil d f policy s he
      exact ⟨⟨.inr t, ht⟩⟩
  exact ⟨fun s => Classical.choice (hex s)⟩

inductive BBDriverState (n m : ℕ)
  | active (state : BBState n m)
  | stopped (state : BBState n m) (out : Option (Point n m))

def bbRun (d : ModelData n m l r) (f : Point n m → ℝ) (policy : BBPolicy)
    (choose : BBSelector d f policy) (initial : BBState n m) : ℕ → BBDriverState n m
  | 0 => .active initial
  | k + 1 => match bbRun d f policy choose initial k with
    | .stopped s out => .stopped s out
    | .active s => match (choose s).val with
      | .inl out => .stopped s out
      | .inr t => .active t

theorem bb_run_invariant (d : ModelData n m l r) (f : Point n m → ℝ) (policy : BBPolicy)
    (choose : BBSelector d f policy) (initial : BBState n m) (k : ℕ) :
    match bbRun d f policy choose initial k with
    | .active s => BBTrace d f policy k initial s
    | .stopped s out => ∃ j < k, BBTrace d f policy j initial s ∧
        s.live = [] ∧ out = s.incumbent := by
  induction k with
  | zero => exact .nil initial
  | succ k ih =>
    simp only [bbRun]
    cases hr : bbRun d f policy choose initial k with
    | active s =>
      rw [hr] at ih
      have hlegal := (choose s).property
      cases hc : (choose s).val with
      | inl out =>
        simp only [hc, BBDecisionLegal] at hlegal ⊢
        exact ⟨k, by omega, ih, hlegal⟩
      | inr t =>
        simp only [hc, BBDecisionLegal] at hlegal ⊢
        exact bb_trace_append_step d f policy ih hlegal
    | stopped s out =>
      rw [hr] at ih
      rcases ih with ⟨j, hj, ht, he, ho⟩
      exact ⟨j, by omega, ht, he, ho⟩

theorem bb_every_selector_finite_return (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (choose : BBSelector d f policy) (initial : BBState n m) :
    ∃ s out, bbRun d f policy choose initial (bbPotential initial + 1) = .stopped s out := by
  have h := bb_run_invariant d f policy choose initial (bbPotential initial + 1)
  cases hr : bbRun d f policy choose initial (bbPotential initial + 1) with
  | active s =>
    rw [hr] at h
    have hh := bb_every_trace_length_bound d f policy h
    omega
  | stopped s out => exact ⟨s, out, rfl⟩

theorem bb_stopped_run_trace (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (choose : BBSelector d f policy) (initial : BBState n m)
    {k : ℕ} {s : BBState n m} {out : Option (Point n m)}
    (h : bbRun d f policy choose initial k = .stopped s out) :
    ∃ j ≤ bbPotential initial, j < k ∧ BBTrace d f policy j initial s ∧
      s.live = [] ∧ out = s.incumbent := by
  have hi := bb_run_invariant d f policy choose initial k
  rw [h] at hi
  obtain ⟨j, hj, ht, he, ho⟩ := hi
  exact ⟨j, bb_every_trace_length_bound d f policy ht, hj, ht, he, ho⟩

theorem bb_stopped_run_exists (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (initial : BBState n m) :
    ∃ choose : BBSelector d f policy, ∃ s out,
      bbRun d f policy choose initial (bbPotential initial + 1) = .stopped s out := by
  obtain ⟨choose⟩ := bb_selector_exists d f policy
  exact ⟨choose, bb_every_selector_finite_return d f policy choose initial⟩

def BBOutcome (d : ModelData n m l r) (f : Point n m → ℝ) : Option (Point n m) → Prop
  | none => d.feasibleOn Set.univ = ∅
  | some q => IsMinimizer (d.feasibleOn Set.univ) f q

theorem bb_return_correct (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi))
    (choose : BBSelector d f policy) {k : ℕ} {s : BBState n m}
    {out : Option (Point n m)}
    (h : bbRun d f policy choose (bbInitial d warm) k = .stopped s out) :
    BBOutcome d f out := by
  obtain ⟨j, hj, hjk, ht, he, ho⟩ := bb_stopped_run_trace d f policy choose _ h
  have hs := bb_trace_reachable d f policy warm BBReachable.initial ht
  cases out with
  | none =>
    exact bb_reachable_empty_live_infeasible d f policy warm hwarm hbase hg hf hs he ho.symm
  | some q =>
    exact bb_reachable_empty_live_optimal d f policy warm hwarm hbase hg hf hs he q ho.symm

/-- All actual selectors return after at most the literal root weight in node
processes. The displayed run includes one final empty-heap inspection. -/
theorem bb_every_selector_exact_return (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi))
    (choose : BBSelector d f policy) :
    ∃ (s : BBState n m) (out : Option (Point n m)) (j : ℕ),
      j ≤ (bbRootNode d).weight ∧ BBTrace d f policy j (bbInitial d warm) s ∧
      s.live = [] ∧ out = s.incumbent ∧
      bbRun d f policy choose (bbInitial d warm) ((bbRootNode d).weight + 1) = .stopped s out ∧
      BBOutcome d f out := by
  obtain ⟨s, out, h⟩ := bb_every_selector_finite_return d f policy choose (bbInitial d warm)
  obtain ⟨j, hj, hjk, ht, he, ho⟩ := bb_stopped_run_trace d f policy choose _ h
  refine ⟨s, out, j, ?_, ht, he, ho, ?_, bb_return_correct d f policy warm hwarm hbase hg hf choose h⟩
  · simpa [bb_initial_potential] using hj
  · simpa [bb_initial_potential] using h

theorem bb_exact_stopped_run_exists (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi)) :
    ∃ choose : BBSelector d f policy, ∃ s out,
      bbRun d f policy choose (bbInitial d warm) ((bbRootNode d).weight + 1) = .stopped s out ∧
      BBOutcome d f out := by
  obtain ⟨choose⟩ := bb_selector_exists d f policy
  obtain ⟨s, out, j, hj, ht, he, ho, hrun, hout⟩ :=
    bb_every_selector_exact_return d f policy warm hwarm hbase hg hf choose
  exact ⟨choose, s, out, hrun, hout⟩

/-- Thesis wrapper: finite real bounds, compact mixed affine base, linear
objective, globally convex C1 rows. Convexity is an unused source premise in
exact global-minimum semantics; C1 is used only to obtain row continuity. -/
theorem bb_source_every_selector_exact_return (d : ModelData n m l r)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (_hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) (hC1 : ∀ j, ContDiff ℝ 1 (d.g j))
    (choose : BBSelector d d.objective policy) :
    ∃ (s : BBState n m) (out : Option (Point n m)) (j : ℕ),
      j ≤ (bbRootNode d).weight ∧ BBTrace d d.objective policy j (bbInitial d warm) s ∧
      s.live = [] ∧ out = s.incumbent ∧
      bbRun d d.objective policy choose (bbInitial d warm) ((bbRootNode d).weight + 1) = .stopped s out ∧
      BBOutcome d d.objective out :=
  bb_every_selector_exact_return d d.objective policy warm hwarm hbase
    (fun j => (hC1 j).continuous) (linearForm_continuous d.c1 d.c2).continuousOn choose

theorem bb_reachable_maximal_correct (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi)) {s : BBState n m}
    (hs : BBReachable d f policy warm s) (hmax : ¬ ∃ t, BBProcess d f policy s t) :
    BBOutcome d f s.incumbent := by
  have he := (bb_maximal_iff_empty_live d f policy s).1 hmax
  cases hi : s.incumbent with
  | none => exact bb_reachable_empty_live_infeasible d f policy warm hwarm hbase hg hf hs he hi
  | some q => exact bb_reachable_empty_live_optimal d f policy warm hwarm hbase hg hf hs he q hi

theorem bb_reachable_step_global_bound_mono (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi)) {s t : BBState n m}
    (hs : BBReachable d f policy warm s) (step : BBProcess d f policy s t) :
    bbGlobalBound f s ≤ bbGlobalBound f t :=
  bb_process_global_bound_mono d f policy
    (bb_reachable_invariant d f policy warm hwarm hbase hg hf hs) step

end Chapter02


#print axioms Chapter02.bb_trace_trans
#print axioms Chapter02.bb_trace_append_step
#print axioms Chapter02.bb_trace_potential_bound
#print axioms Chapter02.bb_every_trace_length_bound
#print axioms Chapter02.bb_trace_reachable
#print axioms Chapter02.bb_trace_global_bound_mono
#print axioms Chapter02.bb_trace_incumbent_bound_nonincreasing
#print axioms Chapter02.bb_process_exists_of_live_ne_nil
#print axioms Chapter02.bb_no_process_of_empty_live
#print axioms Chapter02.bb_maximal_iff_empty_live
#print axioms Chapter02.bb_no_infinite_execution
#print axioms Chapter02.bb_selector_exists
#print axioms Chapter02.bb_run_invariant
#print axioms Chapter02.bb_every_selector_finite_return
#print axioms Chapter02.bb_stopped_run_trace
#print axioms Chapter02.bb_stopped_run_exists
#print axioms Chapter02.bb_return_correct
#print axioms Chapter02.bb_every_selector_exact_return
#print axioms Chapter02.bb_exact_stopped_run_exists
#print axioms Chapter02.bb_source_every_selector_exact_return
#print axioms Chapter02.bb_reachable_maximal_correct
#print axioms Chapter02.bb_reachable_step_global_bound_mono
