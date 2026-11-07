module

public import Chapter05PSQCMixedState
public import Chapter05PSQCMixedMaster

@[expose] public section

/-! Concrete mixed PSC/OA finite stored return. Existing QOA storage and
initialization are reused through exact projections. Progress is derived from
the actual mixed rows, with no freshness or termination premise. -/
noncomputable section
open Set Chapter02 Chapter03.OAKKT
namespace Chapter05.PSQC.Mixed.Exec
variable {p q m l s nw nv : ℕ} {c : Context p q m l s nw nv}
attribute [local instance] Classical.propDecidable

theorem advance_invariant {seed : QOA.Token (p+q) m l} (hs : seed.Safe c.qd)
    {a : State c} (hi : Invariant c a) (b : Batch c seed a) :
    Invariant c (advance a b) := by
  have hl : Invariant c {a with lower := b.point.2} :=
    ⟨hi.1, ⟨hi.2.history, master_lower_bound c seed hs a.history hi.1 b.minimum,
      hi.2.feasible, hi.2.provenance, hi.2.dominates⟩⟩
  have hf := pushEvents_invariant _ hl b.events b.events_valid
  exact ⟨hf.1, ⟨hf.2.history, hf.2.lower, hf.2.feasible, hf.2.provenance, hf.2.dominates⟩⟩

theorem reachable_invariant {seed : QOA.Token (p+q) m l}
    (hs : QOA.Exec.SeedValid c.qd seed) {epsilon : ℝ} {a : State c}
    (h : Reachable c seed epsilon a) : Invariant c a := by
  induction h with
  | initial => exact initial_invariant hs
  | next _ step ih =>
    cases step with
    | step _ b => exact advance_invariant hs.2 ih b

theorem reachable_primary_active {seed : QOA.Token (p+q) m l}
    (hs : QOA.Exec.SeedValid c.qd seed) {epsilon : ℝ} {a : State c}
    (h : Reachable c seed epsilon a) : ∀ y ∈ a.primaries, y ∈ c.qd.activeY := by
  intro y hy
  obtain ⟨e, he, rfl⟩ := reachable_primary_processed h y hy
  exact QOA.event_active (event_toQOA_valid ((reachable_invariant hs h).1 e he))

theorem successor_open_fresh {seed : QOA.Token (p+q) m l} (hs : seed.Safe c.qd)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {a : State c} (hi : Invariant c a)
    (b : Batch c seed a) (ho : loopOpen c epsilon (advance a b)) :
    ¬ ∃ e ∈ a.history, e.target = b.primaryEvent.target := by
  rintro ⟨e, he, hey⟩
  have hy : b.point.1.2 = intCast e.target := by rw [hey]; exact b.primaryEvent_spec.2
  obtain ⟨hn, hle⟩ := event_master_same_fiber c (hi.1 e he) he b.minimum.1 hy
  have hnxt := advance_invariant hs hi b
  have hem : e.toQOA ∈ (advance a b).project.history := by
    apply List.mem_map.mpr
    refine ⟨e, ?_, rfl⟩
    rw [advance_history]
    exact List.mem_append_left _ he
  obtain ⟨u, hu, hdom⟩ := hnxt.2.dominates e.toQOA hem hn
  have hg := ho u hu
  change epsilon < c.qd.f u - (advance a b).lower at hg
  rw [advance_lower] at hg
  change c.qd.f u ≤ c.qd.f e.anchor at hdom
  linarith

-- The finite-count lemmas below use the accepted N2 induction pattern with
-- the new concrete mixed freshness theorem and reachable invariant.
theorem reachable_open_primaries_nodup {seed : QOA.Token (p+q) m l} (hs : QOA.Exec.SeedValid c.qd seed)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State c}
    (h : Reachable c seed epsilon s) (ho : loopOpen c epsilon s) : s.primaries.Nodup := by
  induction h with
  | initial => simp [initialState]
  | @next s t before step ih =>
    cases step with
    | step hopen b =>
      rw [advance_primaries]
      have hf := successor_open_fresh hs.2 heps
        (reachable_invariant hs before) b ho
      have hn : b.primaryEvent.target ∉ s.primaries := by
        intro hy
        exact hf (reachable_primary_processed before _ hy)
      simpa using (ih hopen).append (List.nodup_singleton _)
        (by
          intro a ha hb
          have he := List.mem_singleton.mp hb
          subst a
          exact hn ha)

theorem reachable_open_chain_bound {seed : QOA.Token (p+q) m l} (hs : QOA.Exec.SeedValid c.qd seed)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State c}
    (h : Reachable c seed epsilon s) (ho : loopOpen c epsilon s) :
    s.primaries.length ≤ c.qd.activeY.card := by
  classical
  have hn := reachable_open_primaries_nodup hs heps h ho
  have hsub : s.primaries.toFinset ⊆ c.qd.activeY := by
    intro y hy
    exact reachable_primary_active hs h y (List.mem_toFinset.mp hy)
  calc
    s.primaries.length = s.primaries.toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ ≤ c.qd.activeY.card := Finset.card_le_card hsub

theorem reachable_total_chain_bound {seed : QOA.Token (p+q) m l} (hs : QOA.Exec.SeedValid c.qd seed)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State c}
    (h : Reachable c seed epsilon s) : s.primaries.length ≤ c.qd.activeY.card + 1 := by
  cases h with
  | initial => simp [initialState]
  | next before step =>
    cases step with
    | step hopen b =>
      have hb := reachable_open_chain_bound hs heps before hopen
      simpa only [advance_primaries, List.length_append, List.length_singleton] using
        Nat.add_le_add_right hb 1

/-- All batches except possibly the last have an open successor. A closed
reachable state admits no further RawStep, by its defining open-gap premise. -/
def continuingBatches (epsilon : ℝ) (s : State c) : ℕ :=
  if loopOpen c epsilon s then s.primaries.length else s.primaries.length - 1

theorem continuingBatches_initial (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (epsilon : ℝ) : continuingBatches epsilon (initialState c seed) = 0 := by
  simp [continuingBatches, initialState]

/-- The counter increases exactly on batches whose successor remains open. -/
theorem continuingBatches_step {seed : QOA.Token (p+q) m l} {epsilon : ℝ} {s t : State c}
    (h : RawStep c seed epsilon s t) :
    continuingBatches epsilon t = continuingBatches epsilon s +
      if loopOpen c epsilon t then 1 else 0 := by
  cases h with
  | step ho b =>
    by_cases hn : loopOpen c epsilon (advance s b)
    · simp only [continuingBatches, if_pos ho, if_pos hn,
        advance_primaries, List.length_append, List.length_singleton]
    · simp only [continuingBatches, if_pos ho, if_neg hn,
        advance_primaries, List.length_append, List.length_singleton]
      omega

theorem closed_no_step {seed : QOA.Token (p+q) m l} {epsilon : ℝ} {s t : State c}
    (hc : ¬ loopOpen c epsilon s) : ¬ RawStep c seed epsilon s t := by
  intro h
  cases h with
  | step ho _ => exact hc ho

theorem reachable_continuing_batches_bound {seed : QOA.Token (p+q) m l} (hs : QOA.Exec.SeedValid c.qd seed)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State c}
    (h : Reachable c seed epsilon s) : continuingBatches epsilon s ≤ c.qd.activeY.card := by
  by_cases ho : loopOpen c epsilon s
  · simpa only [continuingBatches, if_pos ho] using
      reachable_open_chain_bound hs heps h ho
  · have hb := reachable_total_chain_bound hs heps h
    simp only [continuingBatches, if_neg ho]
    omega

/-- An actual empty mixed master or any finite valid batch is permitted. -/
inductive Decision (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (a : State c) where
  | empty (certificate : ¬ (Mixed.master c seed a.history).Nonempty)
  | batch (reply : Batch c seed a)

theorem decision_exists (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (a : State c) : Nonempty (Decision c seed a) := by
  classical
  by_cases hne : (Mixed.master c seed a.history).Nonempty
  · obtain ⟨z, hz⟩ := master_minimum_exists c seed a.history hne
    obtain ⟨y, hy, hzy, hx⟩ := ((master_mem_iff c seed a.history z).mp hz.1).1
    obtain ⟨e, hey, he⟩ := event_exists c y hy ⟨z.1.1, hx⟩
    refine ⟨Decision.batch ⟨z, hz, [(z,e)], by simp, ?_⟩⟩
    intro v hv
    have hv' : v = (z,e) := List.mem_singleton.mp hv
    subst v
    exact ⟨hz.1, he, by simpa only [hey] using hzy⟩
  · exact ⟨Decision.empty hne⟩

abbrev Selector (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l) :=
  (a : State c) → Decision c seed a

theorem selector_exists (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l) :
    Nonempty (Selector c seed) := ⟨fun a => Classical.choice (decision_exists c seed a)⟩

theorem closed_gap_incumbent {epsilon : ℝ} {a : State c}
    (hc : ¬ loopOpen c epsilon a) :
    ∃ u, a.incumbent = some u ∧ c.qd.f u - a.lower ≤ epsilon :=
  QOA.Exec.closed_gap_incumbent hc

structure RunResult (c : Context p q m l s nw nv) where
  state : State c
  stop : QOA.Exec.Stop c.qd
  decisions : ℕ

def closedResult (epsilon : ℝ) (a : State c) (hc : ¬ loopOpen c epsilon a) : RunResult c :=
  ⟨a, QOA.Exec.Stop.stored (Classical.choose (closed_gap_incumbent hc)), 0⟩

/-- Gap inspection follows each entire batch; zero fuel can return a closed state. -/
def run {seed : QOA.Token (p+q) m l} (select : Selector c seed) (epsilon : ℝ) :
    ℕ → State c → RunResult c
  | 0, a => if hc : loopOpen c epsilon a then ⟨a, QOA.Exec.Stop.exhausted, 0⟩
      else closedResult epsilon a hc
  | fuel+1, a => if hc : loopOpen c epsilon a then
      match select a with
      | Decision.empty _ => ⟨a, QOA.Exec.Stop.infeasible, 1⟩
      | Decision.batch b =>
        let result := run select epsilon fuel (advance a b)
        {result with decisions := result.decisions + 1}
      else closedResult epsilon a hc

theorem run_closed {seed : QOA.Token (p+q) m l} (select : Selector c seed)
    (epsilon : ℝ) (fuel : ℕ) (a : State c) (hc : ¬ loopOpen c epsilon a) :
    run select epsilon fuel a = closedResult epsilon a hc := by
  cases fuel <;> simp only [run, dif_neg hc]

theorem closedResult_eq {epsilon : ℝ} {a : State c} (hc : ¬ loopOpen c epsilon a)
    {u : Point (p+q) m} (hu : a.incumbent = some u) :
    closedResult epsilon a hc = ⟨a, QOA.Exec.Stop.stored u, 0⟩ := by
  have hh := (Classical.choose_spec (closed_gap_incumbent hc)).1
  have he : Classical.choose (closed_gap_incumbent hc) = u := Option.some.inj (hh.symm.trans hu)
  simp only [closedResult, he]

theorem run_one_batch_closed {seed : QOA.Token (p+q) m l} (select : Selector c seed)
    (epsilon : ℝ) (fuel : ℕ) (a : State c) (b : Batch c seed a)
    (hsel : select a = Decision.batch b) (ho : loopOpen c epsilon a)
    (hc : ¬ loopOpen c epsilon (advance a b)) {u : Point (p+q) m}
    (hu : (advance a b).incumbent = some u) :
    run select epsilon (fuel+1) a = ⟨advance a b, QOA.Exec.Stop.stored u, 1⟩ := by
  simp only [run, dif_pos ho, hsel]
  rw [run_closed select epsilon fuel _ hc, closedResult_eq hc hu]

/-- Accepted projected storage correctness plus the actual decorated-event provenance. -/
def StoredCorrect (epsilon : ℝ) (a : State c) (u : Point (p+q) m) : Prop :=
  QOA.Exec.StoredCorrect epsilon a.project u ∧
    ∃ e ∈ a.history, e.toQOA.restoration = none ∧ e.anchor = u

def StopCorrect (epsilon : ℝ) (a : State c) : QOA.Exec.Stop c.qd → Prop
  | QOA.Exec.Stop.exhausted => False
  | QOA.Exec.Stop.infeasible => ¬ c.qd.original.Nonempty
  | QOA.Exec.Stop.stored u => StoredCorrect epsilon a u

theorem stored_correct {epsilon : ℝ} {a : State c} (hi : Invariant c a)
    {u : Point (p+q) m} (hu : a.incumbent = some u) (hg : c.qd.f u - a.lower ≤ epsilon) :
    StoredCorrect epsilon a u :=
  ⟨QOA.Exec.stored_correct hi.2 hu hg, invariant_source_provenance hi hu⟩

theorem closedResult_correct {epsilon : ℝ} {a : State c} (hi : Invariant c a)
    (hc : ¬ loopOpen c epsilon a) :
    StopCorrect epsilon (closedResult epsilon a hc).state (closedResult epsilon a hc).stop := by
  obtain ⟨hu, hg⟩ := Classical.choose_spec (closed_gap_incumbent hc)
  exact stored_correct hi hu hg

theorem empty_master_correct {seed : QOA.Token (p+q) m l} (hs : seed.Safe c.qd)
    {a : State c} (hi : Invariant c a)
    (he : ¬ (Mixed.master c seed a.history).Nonempty) : ¬ c.qd.original.Nonempty :=
  original_empty_of_master_empty c seed hs a.history hi.1 he


theorem run_correct_of_fuel {seed : QOA.Token (p+q) m l} (hs : QOA.Exec.SeedValid c.qd seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (select : Selector c seed) (fuel : ℕ) (s : State c)
    (hreach : Reachable c seed epsilon s)
    (hfuel : c.qd.activeY.card < s.primaries.length + fuel) :
    Reachable c seed epsilon (run select epsilon fuel s).state ∧
    StopCorrect epsilon (run select epsilon fuel s).state (run select epsilon fuel s).stop ∧
    (run select epsilon fuel s).decisions ≤ fuel := by
  induction fuel generalizing s with
  | zero =>
    have hc : ¬ loopOpen c epsilon s := by
      intro ho
      have hb := reachable_open_chain_bound hs heps hreach ho
      omega
    simpa only [run, dif_neg hc, closedResult] using
      And.intro hreach (And.intro (closedResult_correct
        (reachable_invariant hs hreach) hc) (Nat.le_refl 0))
  | succ fuel ih =>
    by_cases ho : loopOpen c epsilon s
    · cases hd : select s with
      | empty he =>
        simp only [run, dif_pos ho, hd]
        exact ⟨hreach, empty_master_correct hs.2
          (reachable_invariant hs hreach) he, by omega⟩
      | batch b =>
        have hn : Reachable c seed epsilon (advance s b) :=
          Reachable.next hreach (RawStep.step ho b)
        have hf : c.qd.activeY.card < (advance s b).primaries.length + fuel := by
          simp only [advance_primaries, List.length_append, List.length_singleton]
          omega
        obtain ⟨hrec, hcorrect, hcount⟩ := ih (advance s b) hn hf
        simpa only [run, dif_pos ho, hd] using
          And.intro hrec (And.intro hcorrect (Nat.add_le_add_right hcount 1))
    · simpa only [run, dif_neg ho, closedResult] using
        And.intro hreach (And.intro (closedResult_correct
          (reachable_invariant hs hreach) ho) (Nat.zero_le (fuel+1)))

theorem source_selector_finite_return {seed : QOA.Token (p+q) m l} (hs : QOA.Exec.SeedValid c.qd seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (select : Selector c seed) :
    let result := run select epsilon (c.qd.activeY.card + 1) (initialState c seed)
    Reachable c seed epsilon result.state ∧
    StopCorrect epsilon result.state result.stop ∧ result.decisions ≤ c.qd.activeY.card + 1 := by
  apply run_correct_of_fuel hs heps select _ _ Reachable.initial
  simp [initialState]

theorem stored_zero_exact {a : State c} {u : Point (p+q) m} (h : StoredCorrect 0 a u) :
    IsMinimizer c.qd.original c.qd.f u := QOA.Exec.stored_zero_exact h.1

theorem initialization_exists (c : Context p q m l s nw nv) :
    Nonempty (QOA.Exec.Initialization c.qd) :=
  QOA.Exec.initialization_exists (qoa_regularity c) (relaxation_regularity c)

inductive Answer (c : Context p q m l s nw nv) where
  | infeasible
  | initial (point : Point (p+q) m)
  | loop (seed : QOA.Token (p+q) m l) (result : RunResult c)

def solve (epsilon : ℝ) (init : QOA.Exec.Initialization c.qd)
    (select : (seed : QOA.Token (p+q) m l) → Selector c seed) : Answer c :=
  match init with
  | QOA.Exec.Initialization.empty _ => Answer.infeasible
  | QOA.Exec.Initialization.integral seed _ _ => Answer.initial seed.anchor
  | QOA.Exec.Initialization.fractional seed _ _ =>
    Answer.loop seed (run (select seed) epsilon (c.qd.activeY.card+1) (initialState c seed))

def AnswerCorrect (epsilon : ℝ) : Answer c → Prop
  | Answer.infeasible => ¬ c.qd.original.Nonempty
  | Answer.initial z => IsMinimizer c.qd.original c.qd.f z
  | Answer.loop seed result => Reachable c seed epsilon result.state ∧
      StopCorrect epsilon result.state result.stop ∧ result.decisions ≤ c.qd.activeY.card+1

/-- Every permitted exact initialization and selector returns correctly. The
stored branch carries actual decorated-event provenance; ε=0 is exact. -/
theorem source_initialized_return {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (init : QOA.Exec.Initialization c.qd)
    (select : (seed : QOA.Token (p+q) m l) → Selector c seed) :
    AnswerCorrect epsilon (solve epsilon init select) := by
  cases init with
  | empty he =>
    rintro ⟨z, hz⟩
    exact he ⟨z, QOA.original_subset_relaxation (relaxation_regularity c) hz⟩
  | integral seed hs hy =>
    exact QOA.Exec.relaxation_integral_minimum (relaxation_regularity c) hs.1 hy
  | fractional seed hs hy => exact source_selector_finite_return hs heps (select seed)

theorem activeY_card_le (c : Context p q m l s nw nv) :
    c.qd.activeY.card ≤ c.integers.card := QOA.Exec.activeY_card_le c.qd

theorem source_selector_integer_bound {seed : QOA.Token (p+q) m l}
    (hs : QOA.Exec.SeedValid c.qd seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (select : Selector c seed) :
    (run select epsilon (c.qd.activeY.card+1) (initialState c seed)).decisions ≤
      c.integers.card + 1 :=
  (source_selector_finite_return hs heps select).2.2.trans
    (Nat.add_le_add_right (activeY_card_le c) 1)

theorem run_step {seed : QOA.Token (p+q) m l} (select : Selector c seed)
    (epsilon : ℝ) (fuel : ℕ) (a : State c) (b : Batch c seed a)
    (ho : loopOpen c epsilon a) (hsel : select a = Decision.batch b) :
    run select epsilon (fuel+1) a =
      let r := run select epsilon fuel (advance a b)
      {r with decisions := r.decisions+1} := by
  simp only [run, dif_pos ho, hsel]

#print axioms decision_exists
#print axioms successor_open_fresh
#print axioms source_initialized_return
#print axioms source_selector_integer_bound
#print axioms stored_zero_exact
end Chapter05.PSQC.Mixed.Exec

