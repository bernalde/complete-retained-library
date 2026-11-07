module

public import Chapter05QOAAvailability
public import Chapter05QOAFiber
public import Chapter05QOAState

@[expose] public section

/-! Exact repaired QOA return for every permitted selector. Availability and
fresh-primary progress are conclusions, not selector fields. The finite bound
counts master decisions/batches, not all fixed solves in arbitrary finite pools.
All stored returns preserve their actual feasible-event provenance. -/
noncomputable section
open Set Chapter02 Chapter03.OAKKT
namespace Chapter05.QOA.Exec
variable {n p m r : ℕ} {d : Data n p m r}
attribute [local instance] Classical.propDecidable

theorem successor_open_fresh (hr : Regularity d) {seed : Token n p m}
    (hs : seed.Safe d) {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State d}
    (hi : Invariant d s) (b : Batch d seed s)
    (ho : loopOpen d epsilon (advance s b)) :
    ¬ ∃ e ∈ s.history, e.target = b.primaryEvent.target := by
  rintro ⟨e, he, hey⟩
  have het : e.token ∈ rows seed s.history :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, he, rfl⟩)
  have hy : b.point.1.2 = intCast e.target := by
    rw [hey]
    exact b.primaryEvent_spec.2
  obtain ⟨hn, hle⟩ := event_master_same_fiber hr (hi.history e he) het b.minimum.1 hy
  have hnxt := advance_invariant hr hs hi b
  obtain ⟨u, hu, hdom⟩ := hnxt.dominates e
    (by rw [advance_history]; exact List.mem_append_left _ he) hn
  have hg := ho u hu
  rw [advance_lower] at hg
  linarith

theorem reachable_open_primaries_nodup (hr : Regularity d)
    (hR : RelaxationRegularity d) {seed : Token n p m} (hs : SeedValid d seed)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State d}
    (h : Reachable d seed epsilon s) (ho : loopOpen d epsilon s) : s.primaries.Nodup := by
  induction h with
  | initial => simp [initialState]
  | @next s t before step ih =>
    cases step with
    | step hopen b =>
      rw [advance_primaries]
      have hf := successor_open_fresh hr hs.2 heps
        (reachable_invariant hr hR hs before) b ho
      have hn : b.primaryEvent.target ∉ s.primaries := by
        intro hy
        exact hf (reachable_primary_processed before _ hy)
      simpa using (ih hopen).append (List.nodup_singleton _)
        (by
          intro a ha hb
          have he := List.mem_singleton.mp hb
          subst a
          exact hn ha)

theorem reachable_open_chain_bound (hr : Regularity d)
    (hR : RelaxationRegularity d) {seed : Token n p m} (hs : SeedValid d seed)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State d}
    (h : Reachable d seed epsilon s) (ho : loopOpen d epsilon s) :
    s.primaries.length ≤ d.activeY.card := by
  classical
  have hn := reachable_open_primaries_nodup hr hR hs heps h ho
  have hsub : s.primaries.toFinset ⊆ d.activeY := by
    intro y hy
    exact reachable_primary_active hr hR hs h y (List.mem_toFinset.mp hy)
  calc
    s.primaries.length = s.primaries.toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ ≤ d.activeY.card := Finset.card_le_card hsub

theorem reachable_total_chain_bound (hr : Regularity d)
    (hR : RelaxationRegularity d) {seed : Token n p m} (hs : SeedValid d seed)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State d}
    (h : Reachable d seed epsilon s) : s.primaries.length ≤ d.activeY.card + 1 := by
  cases h with
  | initial => simp [initialState]
  | next before step =>
    cases step with
    | step hopen b =>
      have hb := reachable_open_chain_bound hr hR hs heps before hopen
      simpa only [advance_primaries, List.length_append, List.length_singleton] using
        Nat.add_le_add_right hb 1

theorem activeY_card_le (d : Data n p m r) : d.activeY.card ≤ d.Y.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- All batches except possibly the last have an open successor. A closed
reachable state admits no further RawStep, by its defining open-gap premise. -/
def continuingBatches (epsilon : ℝ) (s : State d) : ℕ :=
  if loopOpen d epsilon s then s.primaries.length else s.primaries.length - 1

theorem continuingBatches_initial (d : Data n p m r) (seed : Token n p m)
    (epsilon : ℝ) : continuingBatches epsilon (initialState d seed) = 0 := by
  simp [continuingBatches, initialState]

/-- The counter increases exactly on batches whose successor remains open. -/
theorem continuingBatches_step {seed : Token n p m} {epsilon : ℝ} {s t : State d}
    (h : RawStep d seed epsilon s t) :
    continuingBatches epsilon t = continuingBatches epsilon s +
      if loopOpen d epsilon t then 1 else 0 := by
  cases h with
  | step ho b =>
    by_cases hn : loopOpen d epsilon (advance s b)
    · simp only [continuingBatches, if_pos ho, if_pos hn,
        advance_primaries, List.length_append, List.length_singleton]
    · simp only [continuingBatches, if_pos ho, if_neg hn,
        advance_primaries, List.length_append, List.length_singleton]
      omega

theorem closed_no_step {seed : Token n p m} {epsilon : ℝ} {s t : State d}
    (hc : ¬ loopOpen d epsilon s) : ¬ RawStep d seed epsilon s t := by
  intro h
  cases h with
  | step ho _ => exact hc ho

theorem reachable_continuing_batches_bound (hr : Regularity d)
    (hR : RelaxationRegularity d) {seed : Token n p m} (hs : SeedValid d seed)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State d}
    (h : Reachable d seed epsilon s) : continuingBatches epsilon s ≤ d.activeY.card := by
  by_cases ho : loopOpen d epsilon s
  · simpa only [continuingBatches, if_pos ho] using
      reachable_open_chain_bound hr hR hs heps h ho
  · have hb := reachable_total_chain_bound hr hR hs heps h
    simp only [continuingBatches, if_neg ho]
    omega

/-- Every exact empty-master certificate or finite valid batch is permitted. -/
inductive Decision (d : Data n p m r) (seed : Token n p m) (s : State d) where
  | empty (certificate : ¬ (master d seed s.history).Nonempty)
  | batch (reply : Batch d seed s)

theorem decision_exists (hr : Regularity d) (seed : Token n p m) (s : State d) :
    Nonempty (Decision d seed s) := by
  classical
  by_cases hne : (master d seed s.history).Nonempty
  · obtain ⟨q, hq⟩ := master_minimum_exists hr.X_compact (rows seed s.history)
      (List.cons_ne_nil _ _) hne
    obtain ⟨y, hy, hqy, hx⟩ := ((master_mem_iff d (rows seed s.history) q).mp hq.1).1
    obtain ⟨e, hey, he⟩ := event_exists hr y hy ⟨q.1.1, hx⟩
    refine ⟨Decision.batch ⟨q, hq, [(q,e)], by simp, ?_⟩⟩
    intro v hv
    have hv' : v = (q,e) := List.mem_singleton.mp hv
    subst v
    exact ⟨hq.1, he, by simpa only [hey] using hqy⟩
  · exact ⟨Decision.empty hne⟩

abbrev Selector (d : Data n p m r) (seed : Token n p m) :=
  (s : State d) → Decision d seed s

theorem selector_exists (hr : Regularity d) (seed : Token n p m) :
    Nonempty (Selector d seed) :=
  ⟨fun s => Classical.choice (decision_exists hr seed s)⟩

theorem closed_gap_incumbent {epsilon : ℝ} {s : State d}
    (hc : ¬ loopOpen d epsilon s) :
    ∃ u, s.incumbent = some u ∧ d.f u - s.lower ≤ epsilon := by
  classical
  by_contra h
  apply hc
  intro u hu
  exact lt_of_not_ge (fun hle => h ⟨u,hu,hle⟩)

inductive Stop (d : Data n p m r) where
  | exhausted
  | infeasible
  | stored (point : Point n p)

structure RunResult (d : Data n p m r) where
  state : State d
  stop : Stop d
  decisions : ℕ

def closedResult (epsilon : ℝ) (s : State d) (hc : ¬ loopOpen d epsilon s) :
    RunResult d :=
  ⟨s, Stop.stored (Classical.choose (closed_gap_incumbent hc)), 0⟩

/-- The supplied selector can make any permitted exact choices. The gap test
follows each entire batch. A closed initial gap consumes no master decision. -/
def run {seed : Token n p m} (select : Selector d seed) (epsilon : ℝ) :
    ℕ → State d → RunResult d
  | 0, s => if hc : loopOpen d epsilon s then ⟨s, Stop.exhausted, 0⟩
      else closedResult epsilon s hc
  | fuel+1, s => if hc : loopOpen d epsilon s then
      match select s with
      | Decision.empty _ => ⟨s, Stop.infeasible, 1⟩
      | Decision.batch b =>
        let result := run select epsilon fuel (advance s b)
        {result with decisions := result.decisions + 1}
      else closedResult epsilon s hc

theorem run_closed {seed : Token n p m} (select : Selector d seed)
    (epsilon : ℝ) (fuel : ℕ) (s : State d) (hc : ¬ loopOpen d epsilon s) :
    run select epsilon fuel s = closedResult epsilon s hc := by
  cases fuel <;> simp only [run, dif_neg hc]

theorem closedResult_eq {epsilon : ℝ} {s : State d} (hc : ¬ loopOpen d epsilon s)
    {u : Point n p} (hu : s.incumbent = some u) :
    closedResult epsilon s hc = ⟨s, Stop.stored u, 0⟩ := by
  have hh := (Classical.choose_spec (closed_gap_incumbent hc)).1
  have he : Classical.choose (closed_gap_incumbent hc) = u := Option.some.inj (hh.symm.trans hu)
  simp only [closedResult, he]

/-- Actual one-batch evaluation, used by the source control. The selector is
otherwise arbitrary; its later choices are not consulted after the gap closes. -/
theorem run_one_batch_closed {seed : Token n p m} (select : Selector d seed)
    (epsilon : ℝ) (fuel : ℕ) (s : State d) (b : Batch d seed s)
    (hsel : select s = Decision.batch b) (ho : loopOpen d epsilon s)
    (hc : ¬ loopOpen d epsilon (advance s b)) {u : Point n p}
    (hu : (advance s b).incumbent = some u) :
    run select epsilon (fuel+1) s = ⟨advance s b, Stop.stored u, 1⟩ := by
  simp only [run, dif_pos ho, hsel]
  rw [run_closed select epsilon fuel _ hc, closedResult_eq hc hu]

def StoredCorrect (epsilon : ℝ) (s : State d) (u : Point n p) : Prop :=
  s.incumbent = some u ∧ u ∈ d.original ∧
    (∃ e ∈ s.history, e.restoration = none ∧ e.anchor = u) ∧
    ∀ z ∈ d.original, d.f u ≤ d.f z + epsilon

def StopCorrect (epsilon : ℝ) (s : State d) : Stop d → Prop
  | Stop.exhausted => False
  | Stop.infeasible => ¬ d.original.Nonempty
  | Stop.stored u => StoredCorrect epsilon s u

theorem stored_correct {epsilon : ℝ} {s : State d} (hi : Invariant d s)
    {u : Point n p} (hu : s.incumbent = some u) (hg : d.f u - s.lower ≤ epsilon) :
    StoredCorrect epsilon s u := by
  refine ⟨hu, hi.feasible u hu, hi.provenance u hu, ?_⟩
  intro z hz
  have hl := hi.lower z hz
  linarith

theorem closedResult_correct {epsilon : ℝ} {s : State d} (hi : Invariant d s)
    (hc : ¬ loopOpen d epsilon s) :
    StopCorrect epsilon (closedResult epsilon s hc).state
      (closedResult epsilon s hc).stop := by
  obtain ⟨hu, hg⟩ := Classical.choose_spec (closed_gap_incumbent hc)
  exact stored_correct hi hu hg

theorem empty_master_correct (hr : Regularity d) {seed : Token n p m}
    (hs : seed.Safe d) {s : State d} (hi : Invariant d s)
    (he : ¬ (master d seed s.history).Nonempty) : ¬ d.original.Nonempty := by
  rintro ⟨z, hz⟩
  exact he ⟨(z,d.f z), master_relaxation hr (history_safe hs hi.history) ⟨hz,le_rfl⟩⟩

/-- Fuel suffices for every selector because each continuing batch has a new
primary fiber, proved above from actual support and restoration exclusion. -/
theorem run_correct_of_fuel (hr : Regularity d) (hR : RelaxationRegularity d)
    {seed : Token n p m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (select : Selector d seed) (fuel : ℕ) (s : State d)
    (hreach : Reachable d seed epsilon s)
    (hfuel : d.activeY.card < s.primaries.length + fuel) :
    Reachable d seed epsilon (run select epsilon fuel s).state ∧
    StopCorrect epsilon (run select epsilon fuel s).state (run select epsilon fuel s).stop ∧
    (run select epsilon fuel s).decisions ≤ fuel := by
  induction fuel generalizing s with
  | zero =>
    have hc : ¬ loopOpen d epsilon s := by
      intro ho
      have hb := reachable_open_chain_bound hr hR hs heps hreach ho
      omega
    simpa only [run, dif_neg hc, closedResult] using
      And.intro hreach (And.intro (closedResult_correct
        (reachable_invariant hr hR hs hreach) hc) (Nat.le_refl 0))
  | succ fuel ih =>
    by_cases ho : loopOpen d epsilon s
    · cases hd : select s with
      | empty he =>
        simp only [run, dif_pos ho, hd]
        exact ⟨hreach, empty_master_correct hr hs.2
          (reachable_invariant hr hR hs hreach) he, by omega⟩
      | batch b =>
        have hn : Reachable d seed epsilon (advance s b) :=
          Reachable.next hreach (RawStep.step ho b)
        have hf : d.activeY.card < (advance s b).primaries.length + fuel := by
          simp only [advance_primaries, List.length_append, List.length_singleton]
          omega
        obtain ⟨hrec, hcorrect, hcount⟩ := ih (advance s b) hn hf
        simpa only [run, dif_pos ho, hd] using
          And.intro hrec (And.intro hcorrect (Nat.add_le_add_right hcount 1))
    · simpa only [run, dif_neg ho, closedResult] using
        And.intro hreach (And.intro (closedResult_correct
          (reachable_invariant hr hR hs hreach) ho) (Nat.zero_le (fuel+1)))

theorem source_selector_finite_return (hr : Regularity d) (hR : RelaxationRegularity d)
    {seed : Token n p m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (select : Selector d seed) :
    let result := run select epsilon (d.activeY.card + 1) (initialState d seed)
    Reachable d seed epsilon result.state ∧
    StopCorrect epsilon result.state result.stop ∧ result.decisions ≤ d.activeY.card + 1 := by
  apply run_correct_of_fuel hr hR hs heps select _ _ Reachable.initial
  simp [initialState]

theorem stored_zero_exact {s : State d} {u : Point n p} (h : StoredCorrect 0 s u) :
    IsMinimizer d.original d.f u := by
  exact ⟨h.2.1, fun z hz => by simpa only [add_zero] using h.2.2.2 z hz⟩

theorem relaxation_integral_minimum (hR : RelaxationRegularity d)
    {z : Point n p} (hz : IsMinimizer d.relaxation d.f z)
    (hy : ∃ y ∈ d.Y, z.2 = intCast y) : IsMinimizer d.original d.f z := by
  obtain ⟨y, hy, hzy⟩ := hy
  refine ⟨⟨⟨y,hy,hzy,?_⟩,hz.1.2.2.2⟩,?_⟩
  · refine ⟨hz.1.1,?_⟩
    intro i
    have he : (z.1,intCast y) = z := Prod.ext rfl hzy.symm
    simpa only [he] using hz.1.2.2.1 i
  · exact fun q hq => hz.2 q (original_subset_relaxation hR hq)

/-- Initialization covers every exact relaxation reply and every safe seed
scale; an integral relaxation minimizer returns directly, without an NLP loop. -/
inductive Initialization (d : Data n p m r) where
  | empty (certificate : ¬ d.relaxation.Nonempty)
  | integral (seed : Token n p m) (valid : SeedValid d seed)
      (integer : ∃ y ∈ d.Y, seed.anchor.2 = intCast y)
  | fractional (seed : Token n p m) (valid : SeedValid d seed)
      (noninteger : ¬ ∃ y ∈ d.Y, seed.anchor.2 = intCast y)

theorem initialization_exists (hr : Regularity d) (hR : RelaxationRegularity d) :
    Nonempty (Initialization d) := by
  classical
  by_cases hne : d.relaxation.Nonempty
  · obtain ⟨z,hz⟩ := relaxation_minimum_exists hr hR hne
    let seed : Token n p m := ⟨z,0,fun _ => 0⟩
    have hs : SeedValid d seed := ⟨hz,zero_token_safe hr z⟩
    by_cases hy : ∃ y ∈ d.Y, z.2 = intCast y
    · exact ⟨Initialization.integral seed hs hy⟩
    · exact ⟨Initialization.fractional seed hs hy⟩
  · exact ⟨Initialization.empty hne⟩

inductive Answer (d : Data n p m r) where
  | infeasible
  | initial (point : Point n p)
  | loop (seed : Token n p m) (result : RunResult d)

def solve (epsilon : ℝ) (init : Initialization d)
    (select : (seed : Token n p m) → Selector d seed) : Answer d :=
  match init with
  | Initialization.empty _ => Answer.infeasible
  | Initialization.integral seed _ _ => Answer.initial seed.anchor
  | Initialization.fractional seed _ _ =>
    Answer.loop seed (run (select seed) epsilon (d.activeY.card+1) (initialState d seed))

def AnswerCorrect (epsilon : ℝ) : Answer d → Prop
  | Answer.infeasible => ¬ d.original.Nonempty
  | Answer.initial z => IsMinimizer d.original d.f z
  | Answer.loop seed result => Reachable d seed epsilon result.state ∧
      StopCorrect epsilon result.state result.stop ∧ result.decisions ≤ d.activeY.card+1

/-- Every permitted initialization and every exact selector terminate correctly.
The loop branch returns a stored feasible NLP point, with actual provenance;
positive tolerance gives only the displayed approximation guarantee. -/
theorem source_initialized_return (hr : Regularity d) (hR : RelaxationRegularity d)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) (init : Initialization d)
    (select : (seed : Token n p m) → Selector d seed) :
    AnswerCorrect epsilon (solve epsilon init select) := by
  cases init with
  | empty he =>
    rintro ⟨z,hz⟩
    exact he ⟨z,original_subset_relaxation hR hz⟩
  | integral seed hs hy => exact relaxation_integral_minimum hR hs.1 hy
  | fractional seed hs hy => exact source_selector_finite_return hr hR hs heps (select seed)

end Chapter05.QOA.Exec
