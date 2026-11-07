module

public import Chapter07UnseededModel

@[expose] public section

/-!
Qualified unseeded Chapter 7 execution. The initial continuous minimizer a0 is
retained by every master, including after the first feasible fiber. Histories
only grow. Exact subproblem selections contain no progress or success premise.
-/
noncomputable section
open Set Chapter02
namespace Chapter07.UnseededExec
open Chapter06.Level

variable {n m l r : ℕ} {d : Data n m l r}

structure State (d : Data n m l r) where
  history : List (Event d)
  baseline : Option {u : Point n m // u ∈ d.original}

def initial (d : Data n m l r) : State d := ⟨[], none⟩

def Invariant (s : State d) : Prop :=
  (s.baseline = none → ∀ e ∈ s.history, e.slack ≠ none) ∧
  (∀ u, s.baseline = some u → ∃ e ∈ s.history, e.slack = none ∧ u.val = e.anchor)

def advance (s : State d) (e : Event d) : State d :=
  ⟨e :: s.history, match s.baseline with
    | some u => some u
    | none => if h : e.slack = none then some ⟨e.anchor, e.feasible_original h⟩ else none⟩

theorem initial_invariant : Invariant (initial d) := by
  simp [Invariant, initial]

theorem advance_history (s : State d) (e : Event d) :
    (advance s e).history = e :: s.history := rfl

theorem advance_invariant {s : State d} (hs : Invariant s) (e : Event d) :
    Invariant (advance s e) := by
  rcases hs with ⟨hn, hu⟩
  cases hb : s.baseline with
  | none =>
    by_cases he : e.slack = none
    · constructor
      · simp [advance, hb, he]
      · intro u h
        have hx : (⟨e.anchor, e.feasible_original he⟩ : {u // u ∈ d.original}) = u := by
          simpa [advance, hb, he] using h
        exact ⟨e, List.mem_cons_self, he, congrArg Subtype.val hx.symm⟩
    · constructor
      · intro _ a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact he
        · exact hn hb a ha
      · simp [advance, hb, he]
  | some u =>
    constructor
    · simp [advance, hb]
    · intro v h
      have hv : u = v := by simpa [advance, hb] using h
      rcases hu u hb with ⟨a, ha, hf, hx⟩
      exact ⟨a, List.mem_cons_of_mem e ha, hf, by simpa [← hv] using hx⟩

theorem restoration_incumbent (u : Point n m) (H : List (Event d))
    (h : ∀ e ∈ H, e.slack ≠ none) : incumbent d u H = u := by
  induction H with
  | nil => rfl
  | cons e H ih =>
    have he := h e List.mem_cons_self
    have ht : ∀ a ∈ H, a.slack ≠ none := fun a ha => h a (List.mem_cons_of_mem e ha)
    cases hslack : e.slack with
    | none => exact (he hslack).elim
    | some rho => simpa [incumbent, hslack] using ih ht

/-- The handoff includes the first feasible event exactly once. No master or
cut anchor is changed; all old events remain behind it in the same history. -/
theorem first_feasible_handoff {s : State d} (hs : Invariant s)
    (hb : s.baseline = none) (e : Event d) (he : e.slack = none) :
    (advance s e).history = e :: s.history ∧
    (advance s e).baseline = some ⟨e.anchor, e.feasible_original he⟩ ∧
    incumbent d e.anchor (advance s e).history = e.anchor ∧
    (advance s e).history.length = s.history.length + 1 := by
  refine ⟨rfl, by simp [advance, hb, he], ?_, by simp [advance]⟩
  simp [advance, incumbent, he, restoration_incumbent e.anchor s.history (hs.1 hb),
    keepBetter]

inductive Action (d : Data n m l r) where
  | infeasible
  | returned (u : Point n m)
  | process (e : Event d)

/-- Exact source decisions, before any finite-return reasoning. An infeasible
answer must come from an empty master. A feasible answer must be the stored
incumbent after a closing fresh bound. Processing uses either the actual
prefix master point or a level-feasible point after an open fresh bound. -/
def Legal (a0 : Point n m) (alpha epsilon : ℝ) (s : State d) : Action d → Prop
  | .infeasible => ¬ (master d a0 s.history).Nonempty
  | .returned v => ∃ u, s.baseline = some u ∧ v = incumbent d u.val s.history ∧
      ∃ p, IsMinimizer (master d a0 s.history) Prod.snd p ∧
        d.f (incumbent d u.val s.history) - p.2 ≤ epsilon
  | .process e =>
      (s.baseline = none ∧ ∃ p, IsMinimizer (master d a0 s.history) Prod.snd p ∧
        p.1.2 = intCast e.target) ∨
      (∃ u, s.baseline = some u ∧ ∃ p,
        IsMinimizer (master d a0 s.history) Prod.snd p ∧
        ¬ (d.f (incumbent d u.val s.history) - p.2 ≤ epsilon) ∧
        ∃ q ∈ Chapter07.Unseeded.level d a0 u.val s.history p.2 alpha,
          q.1.2 = intCast e.target)

structure Decision (d : Data n m l r) (a0 : Point n m) (alpha epsilon : ℝ)
    (s : State d) where
  action : Action d
  legal : Legal a0 alpha epsilon s action

abbrev Selector (d : Data n m l r) (a0 : Point n m) (alpha epsilon : ℝ) :=
  (s : State d) → Decision d a0 alpha epsilon s

/-- Replace one exact source decision, retaining an available selector at
all other states. The dependent result type keeps its actual legality proof. -/
def withDecision {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) (s0 : State d)
    (decision : Decision d a0 alpha epsilon s0) : Selector d a0 alpha epsilon := by
  classical
  exact fun s => if h : s = s0 then h.symm ▸ decision else select s

theorem withDecision_at {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) (s0 : State d)
    (decision : Decision d a0 alpha epsilon s0) :
    withDecision select s0 decision s0 = decision := by
  classical
  simp [withDecision]

theorem withDecision_away {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) (s0 : State d)
    (decision : Decision d a0 alpha epsilon s0) (s : State d) (hne : s ≠ s0) :
    withDecision select s0 decision s = select s := by
  classical
  simp [withDecision, hne]

/-- Default exact selection uses the current master minimizer itself as a
level trial. The optional incumbent is not supplied externally. -/
theorem decision_available (hr : Regularity d) (a0 : Point n m)
    {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (s : State d) :
    Nonempty (Decision d a0 alpha epsilon s) := by
  rcases Chapter07.Unseeded.master_empty_or_attained hr a0 s.history with hi | ⟨p, hp⟩
  · exact ⟨⟨.infeasible, hi⟩⟩
  · cases hb : s.baseline with
    | none =>
      obtain ⟨e, he⟩ := Chapter06.Level.Exec.event_available hr p.1 hp.1.1.1
      exact ⟨⟨.process e, Or.inl ⟨hb, p, hp, he⟩⟩⟩
    | some u =>
      by_cases hc : d.f (incumbent d u.val s.history) - p.2 ≤ epsilon
      · exact ⟨⟨.returned (incumbent d u.val s.history), u, hb, rfl, p, hp, hc⟩⟩
      · obtain ⟨e, he⟩ := Chapter06.Level.Exec.event_available hr p.1 hp.1.1.1
        exact ⟨⟨.process e, Or.inr ⟨u, hb, p, hp, hc, p,
          Chapter07.Unseeded.level_available hr u.property hp ha ha1, he⟩⟩⟩

def exactSelector (hr : Regularity d) (a0 : Point n m)
    {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    Selector d a0 alpha epsilon :=
  fun s => Classical.choice (decision_available hr a0 ha ha1 s)

/-- Additional source certificate for actual ranking minimization. Prefix
processing has no incumbent and uses no auxiliary ranking. Post-handoff events
must come from a physical ranking minimizer of the actual two-anchor level. -/
def RankedLegal (a0 : Point n m) (alpha epsilon : ℝ)
    (ranking : List (Event d) → Point n m → ℝ) (s : State d) : Action d → Prop
  | .process e => s.baseline = none ∨
      ∃ u, s.baseline = some u ∧ ∃ p,
        IsMinimizer (master d a0 s.history) Prod.snd p ∧
        ¬ (d.f (incumbent d u.val s.history) - p.2 ≤ epsilon) ∧
        ∃ q, IsMinimizer (Chapter07.Unseeded.level d a0 u.val s.history p.2 alpha)
          (fun z => ranking s.history z.1) q ∧ q.1.2 = intCast e.target
  | _ => True

structure RankedDecision (d : Data n m l r) (a0 : Point n m) (alpha epsilon : ℝ)
    (ranking : List (Event d) → Point n m → ℝ) (s : State d) where
  toDecision : Decision d a0 alpha epsilon s
  ranked : RankedLegal a0 alpha epsilon ranking s toDecision.action

/-- Continuous physical rankings give actual exact auxiliary selections in
all post-handoff open states. The minimizer certificate is retained in the
resulting type, not discarded when the legal decision is chosen. -/
theorem ranked_decision_available (hr : Regularity d) (a0 : Point n m)
    {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (ranking : List (Event d) → Point n m → ℝ)
    (hc : ∀ H, Continuous (ranking H)) (s : State d) :
    Nonempty (RankedDecision d a0 alpha epsilon ranking s) := by
  rcases Chapter07.Unseeded.master_empty_or_attained hr a0 s.history with hi | ⟨p, hp⟩
  · exact ⟨⟨⟨.infeasible, hi⟩, trivial⟩⟩
  · cases hb : s.baseline with
    | none =>
      obtain ⟨e, he⟩ := Chapter06.Level.Exec.event_available hr p.1 hp.1.1.1
      exact ⟨⟨⟨.process e, Or.inl ⟨hb, p, hp, he⟩⟩, Or.inl hb⟩⟩
    | some u =>
      by_cases hclose : d.f (incumbent d u.val s.history) - p.2 ≤ epsilon
      · exact ⟨⟨⟨.returned (incumbent d u.val s.history), u, hb, rfl, p, hp, hclose⟩,
          trivial⟩⟩
      · obtain ⟨q, hq⟩ := Chapter07.Unseeded.physical_minimum_attained hr u.property hp
          ha ha1 (ranking s.history) (hc s.history)
        obtain ⟨e, he⟩ := Chapter06.Level.Exec.event_available hr q.1 hq.1.1.1.1
        exact ⟨⟨⟨.process e, Or.inr ⟨u, hb, p, hp, hclose, q, hq.1, he⟩⟩,
          Or.inr ⟨u, hb, p, hp, hclose, q, hq, he⟩⟩⟩

def rankedSelector (hr : Regularity d) (a0 : Point n m)
    {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (ranking : List (Event d) → Point n m → ℝ)
    (hc : ∀ H, Continuous (ranking H)) : Selector d a0 alpha epsilon :=
  fun s => (Classical.choice (ranked_decision_available hr a0 ha ha1 ranking hc s)).toDecision

theorem rankedSelector_spec (hr : Regularity d) (a0 : Point n m)
    {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (ranking : List (Event d) → Point n m → ℝ)
    (hc : ∀ H, Continuous (ranking H)) (s : State d) :
    RankedLegal a0 alpha epsilon ranking s
      (rankedSelector (epsilon := epsilon) hr a0 ha ha1 ranking hc s).action :=
  (Classical.choice (ranked_decision_available hr a0 ha ha1 ranking hc s)).ranked

theorem process_fresh (hr : Regularity d) {a0 : Point n m} {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) {s : State d} (hs : Invariant s)
    {e : Event d} (he : Legal a0 alpha epsilon s (.process e)) :
    e.target ∉ s.history.map Event.target := by
  intro hm
  obtain ⟨a, hmem, heq⟩ := List.mem_map.mp hm
  rcases he with ⟨hb, p, hp, hy⟩ | ⟨u, _hb, p, _hp, hopen, q, hq, hy⟩
  · exact Chapter07.Unseeded.master_excludes_restored hr hp.1 hmem (hs.1 hb a hmem)
      (hy.trans (congrArg intCast heq.symm))
  · have hgap : p.2 < d.f (incumbent d u.val s.history) := by
      have h := lt_of_not_ge hopen
      linarith
    exact Chapter07.Unseeded.level_excludes_processed hr hq hgap ha hmem
      (hy.trans (congrArg intCast heq.symm))

theorem process_nodup (hr : Regularity d) {a0 : Point n m} {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) {s : State d} (hs : Invariant s)
    (hn : (s.history.map Event.target).Nodup) {e : Event d}
    (he : Legal a0 alpha epsilon s (.process e)) :
    ((advance s e).history.map Event.target).Nodup :=
  List.nodup_cons.mpr ⟨process_fresh hr ha heps hs he, hn⟩

theorem process_history_lt (hr : Regularity d) {a0 : Point n m} {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) {s : State d} (hs : Invariant s)
    (hn : (s.history.map Event.target).Nodup) {e : Event d}
    (he : Legal a0 alpha epsilon s (.process e)) :
    s.history.length < (targets d hr).card := by
  have h := history_target_bound hr (process_nodup hr ha heps hs hn he)
  simp only [advance_history, List.length_cons] at h
  omega

inductive Outcome (d : Data n m l r) where
  | infeasible
  | returned (u : Point n m)
  | exhausted

structure RunResult (d : Data n m l r) where
  state : State d
  outcome : Outcome d
  processed : ℕ
  queries : ℕ

def countStep (r : RunResult d) : RunResult d :=
  { r with processed := r.processed + 1, queries := r.queries + 1 }

def run {a0 : Point n m} {alpha epsilon : ℝ} (select : Selector d a0 alpha epsilon) :
    ℕ → State d → RunResult d
  | fuel, s => match (select s).action with
    | .infeasible => ⟨s, .infeasible, 0, 1⟩
    | .returned u => ⟨s, .returned u, 0, 1⟩
    | .process e => match fuel with
      | 0 => ⟨s, .exhausted, 0, 1⟩
      | fuel + 1 => countStep (run select fuel (advance s e))

theorem run_infeasible {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) (fuel : ℕ) (s : State d)
    (h : (select s).action = .infeasible) :
    run select fuel s = ⟨s, .infeasible, 0, 1⟩ := by
  rw [run.eq_def]
  simp only [h]

theorem run_returned {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) (fuel : ℕ) (s : State d) (u : Point n m)
    (h : (select s).action = .returned u) :
    run select fuel s = ⟨s, .returned u, 0, 1⟩ := by
  rw [run.eq_def]
  simp only [h]

theorem run_process_zero {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) (s : State d) (e : Event d)
    (h : (select s).action = .process e) :
    run select 0 s = ⟨s, .exhausted, 0, 1⟩ := by
  rw [run.eq_def]
  simp only [h]

theorem run_process_succ {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) (fuel : ℕ) (s : State d) (e : Event d)
    (h : (select s).action = .process e) :
    run select (fuel + 1) s = countStep (run select fuel (advance s e)) := by
  rw [run.eq_def]
  simp only [h]

inductive Trace {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) : State d → State d → Prop
  | refl (s) : Trace select s s
  | step (s t e) (he : (select s).action = .process e)
      (next : Trace select (advance s e) t) : Trace select s t

theorem advance_baseline_some (s : State d) (e : Event d)
    (u : {u : Point n m // u ∈ d.original}) (hb : s.baseline = some u) :
    (advance s e).baseline = some u := by simp [advance, hb]

/-- Installing the first feasible baseline never resets it on a later event.
The changing best point is obtained by replaying the entire retained history. -/
theorem Trace.baseline_retained {a0 : Point n m} {alpha epsilon : ℝ}
    {select : Selector d a0 alpha epsilon} {s t : State d}
    (ht : Trace select s t) (u : {u : Point n m // u ∈ d.original})
    (hb : s.baseline = some u) : t.baseline = some u := by
  induction ht with
  | refl s => exact hb
  | step s t e he ht ih => exact ih (advance_baseline_some s e u hb)

/-- Every original event remains in order as a suffix of every later history.
This includes restoration events before the first feasible incumbent. -/
theorem Trace.retained {a0 : Point n m} {alpha epsilon : ℝ}
    {select : Selector d a0 alpha epsilon} {s t : State d}
    (ht : Trace select s t) : ∃ added, t.history = added ++ s.history := by
  induction ht with
  | refl s => exact ⟨[], rfl⟩
  | step s t e he ht ih =>
    obtain ⟨added, hp⟩ := ih
    exact ⟨added ++ [e], by simpa [advance, List.append_assoc] using hp⟩

theorem Trace.retained_event {a0 : Point n m} {alpha epsilon : ℝ}
    {select : Selector d a0 alpha epsilon} {s t : State d}
    (ht : Trace select s t) {e : Event d} (he : e ∈ s.history) : e ∈ t.history := by
  obtain ⟨added, hp⟩ := ht.retained
  rw [hp]
  exact List.mem_append_right added he

/-- The actual later master contains the original a0 rows and every earlier
source event row; the history theorem is not merely a cardinality claim. -/
theorem Trace.master_rows_retained {a0 : Point n m} {alpha epsilon : ℝ}
    {select : Selector d a0 alpha epsilon} {s t : State d}
    (ht : Trace select s t) {q : Point n m × ℝ}
    (hq : q ∈ master d a0 t.history) :
    selectedRows d a0 0 q.1 ∧ ∀ e ∈ s.history, selectedRows d e.anchor e.rho q.1 :=
  ⟨hq.1.2.1, fun e he => hq.1.2.2 e (ht.retained_event he)⟩

def StoredCorrect (epsilon : ℝ) (s : State d) (v : Point n m) : Prop :=
  (∃ u, s.baseline = some u ∧ v = incumbent d u.val s.history) ∧
  v ∈ d.original ∧ (∃ e ∈ s.history, e.slack = none ∧ v = e.anchor) ∧
  ∀ q ∈ d.original, d.f v ≤ d.f q + epsilon

def Correct (epsilon : ℝ) (s : State d) : Outcome d → Prop
  | .infeasible => ¬ d.original.Nonempty
  | .returned v => StoredCorrect epsilon s v
  | .exhausted => False

theorem closed_correct (hr : Regularity d) {a0 : Point n m} {alpha epsilon : ℝ}
    {s : State d} (hs : Invariant s) {v : Point n m}
    (hv : Legal a0 alpha epsilon s (.returned v)) : StoredCorrect epsilon s v := by
  rcases hv with ⟨u, hb, rfl, p, hp, hc⟩
  refine ⟨⟨u, hb, rfl⟩, incumbent_original u.property s.history, ?_, ?_⟩
  · rcases incumbent_provenance u.val s.history with hx | hx
    · rcases hs.2 u hb with ⟨e, he, hf, hu⟩
      exact ⟨e, he, hf, hx.trans hu⟩
    · exact hx
  · intro q hq
    have hl := master_lower_bound hr hp hq
    linarith

/-- Every query is an actual source master inspection. Fuel exhaustion is a
separate diagnostic and is proved unreachable from the derived finite fuel. -/
theorem run_correct_of_fuel (hr : Regularity d) {a0 : Point n m} {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) (select : Selector d a0 alpha epsilon)
    (fuel : ℕ) (s : State d) (hs : Invariant s)
    (hn : (s.history.map Event.target).Nodup)
    (hfuel : (targets d hr).card ≤ s.history.length + fuel) :
    let result := run select fuel s
    Trace select s result.state ∧ Invariant result.state ∧
      (result.state.history.map Event.target).Nodup ∧
      Correct epsilon result.state result.outcome ∧ result.processed ≤ fuel ∧
      result.state.history.length = s.history.length + result.processed ∧
      result.queries = result.processed + 1 := by
  induction fuel generalizing s with
  | zero =>
    have hl := (select s).legal
    cases he : (select s).action with
    | infeasible =>
      rw [he] at hl
      rw [run.eq_def]
      simp only [he]
      exact ⟨Trace.refl s, hs, hn,
        Chapter07.Unseeded.master_empty_original_empty hr hl, le_rfl, by omega, by trivial⟩
    | returned v =>
      rw [he] at hl
      rw [run.eq_def]
      simp only [he]
      exact ⟨Trace.refl s, hs, hn, closed_correct hr hs hl, le_rfl, by omega, by trivial⟩
    | process e =>
      rw [he] at hl
      have hlt := process_history_lt hr ha heps hs hn hl
      omega
  | succ fuel ih =>
    have hl := (select s).legal
    cases he : (select s).action with
    | infeasible =>
      rw [he] at hl
      rw [run.eq_def]
      simp only [he]
      exact ⟨Trace.refl s, hs, hn,
        Chapter07.Unseeded.master_empty_original_empty hr hl, Nat.zero_le _, by omega, by trivial⟩
    | returned v =>
      rw [he] at hl
      rw [run.eq_def]
      simp only [he]
      exact ⟨Trace.refl s, hs, hn, closed_correct hr hs hl, Nat.zero_le _, by omega, by trivial⟩
    | process e =>
      rw [he] at hl
      have hf : (targets d hr).card ≤ (advance s e).history.length + fuel := by
        simp only [advance_history, List.length_cons]
        omega
      obtain ⟨ht, hi, hn', hc, hp, hlen, hq⟩ :=
        ih (advance s e) (advance_invariant hs e) (process_nodup hr ha heps hs hn hl) hf
      rw [run.eq_def]
      simp only [he]
      refine ⟨Trace.step s _ e he ht, hi, hn', hc, Nat.add_le_add_right hp 1, ?_, ?_⟩
      · simp only [countStep, advance_history, List.length_cons] at hlen ⊢
        omega
      · simp only [countStep]
        omega

def solve (hr : Regularity d) {a0 : Point n m} {alpha epsilon : ℝ}
    (select : Selector d a0 alpha epsilon) : RunResult d :=
  run select (targets d hr).card (initial d)

/-- The fixed a0 parameter occurs in every master in the actual trace. This
finite theorem even allows an arbitrary retained initial tangent anchor; the
source initializer below supplies an actual continuous-relaxation minimum. -/
theorem source_unseeded_return (hr : Regularity d) {a0 : Point n m} {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) (select : Selector d a0 alpha epsilon) :
    let result := solve hr select
    Trace select (initial d) result.state ∧ Invariant result.state ∧
      (result.state.history.map Event.target).Nodup ∧
      Correct epsilon result.state result.outcome ∧
      result.processed ≤ (targets d hr).card ∧
      result.state.history.length = result.processed ∧
      result.queries = result.processed + 1 := by
  simpa only [solve, initial, List.length_nil, zero_add] using
    run_correct_of_fuel hr ha heps select (targets d hr).card (initial d)
      initial_invariant (by simp [initial]) (by simp [initial])

theorem stored_zero_exact {s : State d} {u : Point n m}
    (h : StoredCorrect 0 s u) : IsMinimizer d.original d.f u := by
  refine ⟨h.2.1, ?_⟩
  intro q hq
  simpa only [add_zero] using h.2.2.2 q hq

/-- A separately inspected source initialization: either the continuous
relaxation is actually empty or a0 is an actual minimum of that relaxation. -/
inductive Initialization (d : Data n m l r) where
  | empty (proof : ¬ (Chapter07.Unseeded.relaxation d).Nonempty)
  | attained (a0 : Point n m)
      (proof : IsMinimizer (Chapter07.Unseeded.relaxation d) d.f a0)

theorem initialization_available (hr : Regularity d) : Nonempty (Initialization d) := by
  rcases Chapter07.Unseeded.relaxation_empty_or_attained hr with hi | ⟨a0, ha0⟩
  · exact ⟨.empty hi⟩
  · exact ⟨.attained a0 ha0⟩

structure InitializedResult (d : Data n m l r) where
  result : RunResult d
  initializerInspections : ℕ

/-- The initializer is counted separately. In the empty case no master is
inspected; otherwise the same retained a0 is passed to the entire driver. -/
def initializeRun (hr : Regularity d) {alpha epsilon : ℝ}
    (init : Initialization d) (select : ∀ a0, Selector d a0 alpha epsilon) :
    InitializedResult d :=
  ⟨match init with
    | .empty _ => ⟨initial d, .infeasible, 0, 0⟩
    | .attained a0 _ => solve hr (select a0), 1⟩

def InitializationCounts (init : Initialization d) (result : RunResult d) : Prop :=
  match init with
  | .empty _ => result.processed = 0 ∧ result.queries = 0
  | .attained _ _ => result.queries = result.processed + 1

/-- Source-facing composition: no external feasible seed, retained continuous
minimizer, at most N actual distinct events, correct stored return or certified
global integer infeasibility, and exact separate logical inspection counts. -/
theorem source_initialized_return (hr : Regularity d) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) (init : Initialization d)
    (select : ∀ a0, Selector d a0 alpha epsilon) :
    let execution := initializeRun hr init select
    let result := execution.result
    Invariant result.state ∧ (result.state.history.map Event.target).Nodup ∧
      Correct epsilon result.state result.outcome ∧
      result.processed ≤ (targets d hr).card ∧
      result.state.history.length = result.processed ∧
      InitializationCounts init result ∧ execution.initializerInspections = 1 := by
  cases init with
  | empty hi =>
    exact ⟨initial_invariant, by simp [initializeRun, initial],
      Chapter07.Unseeded.relaxation_empty_original_empty hi, Nat.zero_le _, rfl,
      ⟨rfl, rfl⟩, rfl⟩
  | attained a0 ha0 =>
    obtain ⟨_, hi, hn, hc, hp, hl, hq⟩ := source_unseeded_return hr ha heps (select a0)
    exact ⟨hi, hn, hc, hp, hl, hq, rfl⟩

/-- Exact mathematical subproblem selection and actual initialization exist
under the source regularity assumptions; no progress oracle is postulated. -/
theorem source_total_return (hr : Regularity d) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon) :
    ∃ init : Initialization d, ∃ select : ∀ a0, Selector d a0 alpha epsilon,
      let execution := initializeRun hr init select
      Correct epsilon execution.result.state execution.result.outcome ∧
      execution.result.processed ≤ (targets d hr).card ∧
      InitializationCounts init execution.result ∧ execution.initializerInspections = 1 := by
  let init := Classical.choice (initialization_available hr)
  let select := fun a0 => exactSelector (epsilon := epsilon) hr a0 (le_of_lt ha) ha1
  have h := source_initialized_return hr ha heps init select
  exact ⟨init, select, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- The actual continuous-ranking selector has both its retained minimizing
trial certificate at every state and the initialized finite-return guarantee. -/
theorem source_initialized_ranked_return (hr : Regularity d) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon)
    (ranking : List (Event d) → Point n m → ℝ) (hc : ∀ H, Continuous (ranking H))
    (init : Initialization d) :
    let select := fun a0 => rankedSelector (epsilon := epsilon) hr a0 (le_of_lt ha) ha1 ranking hc
    let execution := initializeRun hr init select
    (∀ a0 s, RankedLegal a0 alpha epsilon ranking s (select a0 s).action) ∧
      Invariant execution.result.state ∧
      (execution.result.state.history.map Event.target).Nodup ∧
      Correct epsilon execution.result.state execution.result.outcome ∧
      execution.result.processed ≤ (targets d hr).card ∧
      execution.result.state.history.length = execution.result.processed ∧
      InitializationCounts init execution.result ∧ execution.initializerInspections = 1 := by
  exact ⟨fun a0 s => rankedSelector_spec hr a0 (le_of_lt ha) ha1 ranking hc s,
    source_initialized_return hr ha heps init _⟩

theorem source_total_ranked_return (hr : Regularity d) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon)
    (ranking : List (Event d) → Point n m → ℝ) (hc : ∀ H, Continuous (ranking H)) :
    ∃ init : Initialization d, ∃ select : ∀ a0, Selector d a0 alpha epsilon,
      (∀ a0 s, RankedLegal a0 alpha epsilon ranking s (select a0 s).action) ∧
      let execution := initializeRun hr init select
      Correct epsilon execution.result.state execution.result.outcome ∧
      execution.result.processed ≤ (targets d hr).card ∧
      InitializationCounts init execution.result ∧ execution.initializerInspections = 1 := by
  let init := Classical.choice (initialization_available hr)
  let select := fun a0 => rankedSelector (epsilon := epsilon) hr a0 (le_of_lt ha) ha1 ranking hc
  have h := source_initialized_ranked_return hr ha ha1 heps ranking hc init
  exact ⟨init, select, h.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- Empty hard domains are an explicit outer boundary, without inventing a
nonempty `Regularity` witness or inspecting a master. -/
theorem hard_empty_return {epsilon : ℝ} (hh : ¬ d.hard.Nonempty) :
    Correct (d := d) epsilon (initial d) .infeasible :=
  Chapter07.Unseeded.hard_empty_original_empty hh

#print axioms Chapter07.UnseededExec.rankedSelector_spec
#print axioms Chapter07.UnseededExec.source_initialized_ranked_return
#print axioms Chapter07.UnseededExec.source_total_ranked_return
#print axioms Chapter07.UnseededExec.withDecision_at
#print axioms Chapter07.UnseededExec.withDecision_away
#print axioms Chapter07.UnseededExec.Trace.master_rows_retained
#print axioms Chapter07.UnseededExec.source_initialized_return
#print axioms Chapter07.UnseededExec.source_total_return

#print axioms Chapter07.UnseededExec.decision_available
#print axioms Chapter07.UnseededExec.ranked_decision_available
#print axioms Chapter07.UnseededExec.process_fresh
#print axioms Chapter07.UnseededExec.first_feasible_handoff
#print axioms Chapter07.UnseededExec.source_unseeded_return

end Chapter07.UnseededExec
