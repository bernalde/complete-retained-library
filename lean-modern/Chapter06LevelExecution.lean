module

public import Chapter06LevelMaster

@[expose] public section

/-!
The fresh-bound guard below is an explicit repair/interpretation of the delayed
printed guard. An exact master is queried first; an auxiliary trial and fiber
event are selected only when its current bound leaves a strictly positive gap.
No answer is returned on artificial fuel exhaustion. The finite-return theorem
proves that exhaustion is unreachable for the derived finite projection fuel.
-/
noncomputable section
open Set Chapter02
namespace Chapter06.Level.Exec
open Chapter06.Level

variable {n m l r : ℕ} {d : Data n m l r}

/-- Mathematical exact selections. The trial may be any level-feasible point;
no auxiliary optimality, convexity, progress or termination premise is stored. -/
structure Selector (d : Data n m l r) (seed : Point n m) (alpha : ℝ) where
  master : (H : List (Event d)) →
    {p // IsMinimizer (Chapter06.Level.master d seed H) Prod.snd p}
  trial : (H : List (Event d)) → (p : Point n m × ℝ) →
    IsMinimizer (Chapter06.Level.master d seed H) Prod.snd p →
    {q // q ∈ levelSet d seed H p.2 alpha}
  event : (q : Point n m) → q ∈ d.mixed →
    {e : Event d // q.2 = intCast e.target}

structure RunResult (d : Data n m l r) where
  history : List (Event d)
  answer : Option (Point n m)
  processed : ℕ
  queries : ℕ

def closedResult (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) : RunResult d :=
  ⟨H, some (incumbent d seed H), 0, 1⟩

def exhaustedResult (H : List (Event d)) : RunResult d := ⟨H, none, 0, 1⟩

def countStep (result : RunResult d) : RunResult d :=
  { result with processed := result.processed + 1, queries := result.queries + 1 }

/-- A finite-fuel implementation with a distinct no-answer exhaustion branch.
Its fresh guard runs before either the level or the fiber-event selection. -/
def run {seed : Point n m} {alpha : ℝ} (select : Selector d seed alpha)
    (epsilon : ℝ) : ℕ → List (Event d) → RunResult d
  | fuel, H =>
    let p := select.master H
    if d.f (incumbent d seed H) - p.val.2 ≤ epsilon then
      closedResult d seed H
    else
      match fuel with
      | 0 => exhaustedResult H
      | fuel + 1 =>
        let q := select.trial H p.val p.property
        let e := select.event q.val.1 q.property.1.1.1
        countStep (run select epsilon fuel (e.val :: H))

/-- Actual histories only grow by the event selected from a level trial after
an open fresh guard. The integer equality is part of `Selector.event`; its
continuous anchor is still the raw actual NLP/restoration minimizer. -/
inductive Trace {seed : Point n m} {alpha : ℝ} (select : Selector d seed alpha)
    (epsilon : ℝ) : List (Event d) → List (Event d) → Prop
  | refl (H) : Trace select epsilon H H
  | step (H K) (ho : ¬ (d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon))
      (next :
        let p := select.master H
        let q := select.trial H p.val p.property
        let e := select.event q.val.1 q.property.1.1.1
        Trace select epsilon (e.val :: H) K) : Trace select epsilon H K

def StoredCorrect (d : Data n m l r) (seed : Point n m) (epsilon : ℝ)
    (H : List (Event d)) (u : Point n m) : Prop :=
  u = incumbent d seed H ∧ u ∈ d.original ∧
    (u = seed ∨ ∃ e ∈ H, e.slack = none ∧ u = e.anchor) ∧
    ∀ q ∈ d.original, d.f u ≤ d.f q + epsilon

theorem fresh_gap {seed : Point n m} {H : List (Event d)} {LB epsilon : ℝ}
    (heps : 0 ≤ epsilon) (ho : ¬ (d.f (incumbent d seed H) - LB ≤ epsilon)) :
    LB < d.f (incumbent d seed H) := by
  have h := lt_of_not_ge ho
  linarith

theorem closed_correct (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (Chapter06.Level.master d seed H) Prod.snd p)
    {epsilon : ℝ} (hc : d.f (incumbent d seed H) - p.2 ≤ epsilon) :
    StoredCorrect d seed epsilon H (incumbent d seed H) := by
  refine ⟨rfl, incumbent_original hs H, incumbent_provenance seed H, ?_⟩
  intro q hq
  have hl := master_lower_bound hr hp hq
  linarith

def nextEvent {seed : Point n m} {alpha : ℝ} (select : Selector d seed alpha)
    (H : List (Event d)) : Event d :=
  let p := select.master H
  let q := select.trial H p.val p.property
  (select.event q.val.1 q.property.1.1.1).val

theorem nextEvent_fresh (hr : Regularity d) {seed : Point n m} {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) (select : Selector d seed alpha)
    (H : List (Event d))
    (ho : ¬ (d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon)) :
    (nextEvent select H).target ∉ H.map Event.target := by
  intro hm
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
  let p := select.master H
  let q := select.trial H p.val p.property
  have hy := (select.event q.val.1 q.property.1.1.1).property
  have hex := level_excludes_processed hr q.property (fresh_gap heps ho) ha he
  apply hex
  exact hy.trans (congrArg intCast heq.symm)

theorem nextEvent_nodup (hr : Regularity d) {seed : Point n m} {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) (select : Selector d seed alpha)
    (H : List (Event d)) (hn : (H.map Event.target).Nodup)
    (ho : ¬ (d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon)) :
    ((nextEvent select H :: H).map Event.target).Nodup := by
  exact List.nodup_cons.mpr ⟨nextEvent_fresh hr ha heps select H ho, hn⟩

theorem open_history_lt (hr : Regularity d) {seed : Point n m} {alpha epsilon : ℝ}
    (ha : 0 < alpha) (heps : 0 ≤ epsilon) (select : Selector d seed alpha)
    (H : List (Event d)) (hn : (H.map Event.target).Nodup)
    (ho : ¬ (d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon)) :
    H.length < (targets d hr).card := by
  have hb := history_target_bound hr (nextEvent_nodup hr ha heps select H hn ho)
  simp only [List.length_cons] at hb
  omega

theorem event_available (hr : Regularity d) (q : Point n m) (hq : q ∈ d.mixed) :
    Nonempty {e : Event d // q.2 = intCast e.target} := by
  obtain ⟨y, hy⟩ := hq.2
  rcases event_exists d hr y ⟨q, hq.1, hy⟩ with ⟨a, ha⟩ | ⟨hi, a, rho, ha⟩
  · exact ⟨⟨⟨y, a, none, ha⟩, hy⟩⟩
  · exact ⟨⟨⟨y, a, some rho, hi, ha⟩, hy⟩⟩

/-- One total mathematical choice uses the exact master minimizer itself as
its level trial. The final theorem permits every `Selector`, not just this one. -/
def exactSelector (hr : Regularity d) {seed : Point n m} (hs : seed ∈ d.original)
    {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) : Selector d seed alpha where
  master H := ⟨Classical.choose (master_attained hr hs H),
    Classical.choose_spec (master_attained hr hs H)⟩
  trial _H p hp := ⟨p, level_available hr hs hp ha ha1⟩
  event q hq := Classical.choice (event_available hr q hq)

theorem selector_exists (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    Nonempty (Selector d seed alpha) := ⟨exactSelector hr hs ha ha1⟩

/-- Exact projection or quadratic minimizers, when supplied, are admissible
solely by membership. Their existence and ranking convexity are not assumed
by the finite-return proof. -/
def withAuxiliary {seed : Point n m} {alpha : ℝ} (select : Selector d seed alpha)
    (ranking : List (Event d) → Point n m × ℝ → ℝ)
    (choose : (H : List (Event d)) → (p : Point n m × ℝ) →
      IsMinimizer (Chapter06.Level.master d seed H) Prod.snd p →
      {q // IsMinimizer (levelSet d seed H p.2 alpha) (ranking H) q}) :
    Selector d seed alpha where
  master := select.master
  trial H p hp := let q := choose H p hp; ⟨q.val, q.property.1⟩
  event := select.event

theorem run_closed {seed : Point n m} {alpha epsilon : ℝ}
    (select : Selector d seed alpha) (fuel : ℕ) (H : List (Event d))
    (hc : d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon) :
    run select epsilon fuel H = closedResult d seed H := by
  rw [run.eq_def]
  dsimp only
  rw [if_pos hc]

theorem run_open_zero {seed : Point n m} {alpha epsilon : ℝ}
    (select : Selector d seed alpha) (H : List (Event d))
    (ho : ¬ (d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon)) :
    run select epsilon 0 H = exhaustedResult H := by
  rw [run.eq_def]
  dsimp only
  rw [if_neg ho]

theorem run_open_succ {seed : Point n m} {alpha epsilon : ℝ}
    (select : Selector d seed alpha) (fuel : ℕ) (H : List (Event d))
    (ho : ¬ (d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon)) :
    run select epsilon (fuel + 1) H =
      countStep (run select epsilon fuel (nextEvent select H :: H)) := by
  rw [run.eq_def]
  dsimp only
  rw [if_neg ho]
  rfl

/-- Strong finite-fuel invariant, including actual event trace and the number
of fresh master queries. The zero-fuel open branch contradicts freshness and
the internally derived finite integer projection. -/
theorem run_correct_of_fuel (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {alpha epsilon : ℝ} (ha : 0 < alpha)
    (heps : 0 ≤ epsilon) (select : Selector d seed alpha)
    (fuel : ℕ) (H : List (Event d)) (hn : (H.map Event.target).Nodup)
    (hfuel : (targets d hr).card ≤ H.length + fuel) :
    let result := run select epsilon fuel H
    Trace select epsilon H result.history ∧
      (result.history.map Event.target).Nodup ∧
      (∃ u, result.answer = some u ∧ StoredCorrect d seed epsilon result.history u) ∧
      result.processed ≤ fuel ∧
      result.history.length = H.length + result.processed ∧
      result.queries = result.processed + 1 := by
  induction fuel generalizing H with
  | zero =>
    have hc : d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon := by
      by_contra ho
      have hlt := open_history_lt hr ha heps select H hn ho
      omega
    rw [run_closed select 0 H hc]
    exact ⟨Trace.refl H, hn,
      ⟨incumbent d seed H, rfl, closed_correct hr hs (select.master H).property hc⟩,
      Nat.le_refl 0, by simp [closedResult], rfl⟩
  | succ fuel ih =>
    by_cases hc : d.f (incumbent d seed H) - (select.master H).val.2 ≤ epsilon
    · rw [run_closed select (fuel + 1) H hc]
      exact ⟨Trace.refl H, hn,
        ⟨incumbent d seed H, rfl, closed_correct hr hs (select.master H).property hc⟩,
        Nat.zero_le _, by simp [closedResult], rfl⟩
    · have hnext := nextEvent_nodup hr ha heps select H hn hc
      have hf : (targets d hr).card ≤ (nextEvent select H :: H).length + fuel := by
        simp only [List.length_cons]
        omega
      obtain ⟨ht, hn', hu, hcount, hlen, hquery⟩ := ih (nextEvent select H :: H) hnext hf
      rw [run_open_succ select fuel H hc]
      refine ⟨Trace.step H _ hc ht, hn', hu, Nat.add_le_add_right hcount 1, ?_, ?_⟩
      · simp only [countStep, List.length_cons] at hlen ⊢
        omega
      · simp only [countStep]
        omega

/-- The repaired seeded driver, with fuel derived from the actual compact
integer projection. The feasible seed is supplied; this is not a global
infeasibility detector or a numerical solver correctness statement. -/
def solve (hr : Regularity d) {seed : Point n m} {alpha : ℝ}
    (select : Selector d seed alpha) (epsilon : ℝ) : RunResult d :=
  run select epsilon (targets d hr).card []

/-- Every admissible level-feasible selector returns a stored feasible point
within epsilon of every feasible objective value. At most `targets.card`
fibers are processed, followed by one closing fresh master query. -/
theorem source_seeded_return (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (_ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon)
    (select : Selector d seed alpha) :
    let result := solve hr select epsilon
    Trace select epsilon [] result.history ∧
      (result.history.map Event.target).Nodup ∧
      (∃ u, result.answer = some u ∧ StoredCorrect d seed epsilon result.history u) ∧
      result.processed ≤ (targets d hr).card ∧
      result.history.length = result.processed ∧
      result.queries = result.processed + 1 := by
  have h := run_correct_of_fuel hr hs ha heps select (targets d hr).card []
    (by simp) (by simp)
  simpa only [solve, List.length_nil, zero_add] using h

theorem stored_zero_exact {seed u : Point n m} {H : List (Event d)}
    (h : StoredCorrect d seed 0 H u) : IsMinimizer d.original d.f u := by
  refine ⟨h.2.1, ?_⟩
  intro q hq
  simpa only [add_zero] using h.2.2.2 q hq

/-- Existence is derived in the same source model, without an oracle progress
premise; epsilon zero specializes the stored guarantee to exact optimality. -/
theorem source_total_return (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon) :
    ∃ select : Selector d seed alpha, ∃ u,
      (solve hr select epsilon).answer = some u ∧
      StoredCorrect d seed epsilon (solve hr select epsilon).history u := by
  let select := exactSelector hr hs (le_of_lt ha) ha1
  exact ⟨select, (source_seeded_return hr hs ha ha1 heps select).2.2.1⟩

/-- Source assumptions contain no supplied integer box or separate affine
nonemptiness premise. The latter is witnessed by the given feasible seed. -/
def sourceRegularity (d : Data n m l r) (seed : Point n m)
    (hs : seed ∈ d.original) (hc : IsCompact d.hard)
    (hfc : ConvexOn ℝ Set.univ d.f) (hf1 : ContDiff ℝ 1 d.f)
    (hgc : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hg1 : ∀ j, ContDiff ℝ 1 (d.g j))
    (hslater : ∀ y, (d.feasibleFiber y).Nonempty →
      ∃ p ∈ d.hardFiber y, ∀ j, d.g j p < 0) : Regularity d where
  hard_compact := hc
  hard_nonempty := ⟨seed, hs.1.1⟩
  objective_convex := hfc
  objective_C1 := hf1
  constraint_convex := hgc
  constraint_C1 := hg1
  fiber_slater := hslater

/-- Source-facing headline for the qualified repaired driver. It derives
regularity nonemptiness, the integer box/projection and total exact selection,
then covers every feasible level selector and actual event selection. No
historical numerical software or the literal delayed guard is certified. -/
theorem source_data_seeded_return (d : Data n m l r) (seed : Point n m)
    (hs : seed ∈ d.original) (hc : IsCompact d.hard)
    (hfc : ConvexOn ℝ Set.univ d.f) (hf1 : ContDiff ℝ 1 d.f)
    (hgc : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hg1 : ∀ j, ContDiff ℝ 1 (d.g j))
    (hslater : ∀ y, (d.feasibleFiber y).Nonempty →
      ∃ p ∈ d.hardFiber y, ∀ j, d.g j p < 0)
    {alpha epsilon : ℝ} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon) :
    let hr := sourceRegularity d seed hs hc hfc hf1 hgc hg1 hslater
    Nonempty (Selector d seed alpha) ∧
    ∀ select : Selector d seed alpha,
      let result := solve hr select epsilon
      Trace select epsilon [] result.history ∧
        (result.history.map Event.target).Nodup ∧
        (∃ u, result.answer = some u ∧ StoredCorrect d seed epsilon result.history u) ∧
        result.processed ≤ (targets d hr).card ∧
        result.history.length = result.processed ∧
        result.queries = result.processed + 1 := by
  let hr := sourceRegularity d seed hs hc hfc hf1 hgc hg1 hslater
  exact ⟨selector_exists hr hs (le_of_lt ha) ha1,
    fun select => source_seeded_return hr hs ha ha1 heps select⟩

end Chapter06.Level.Exec
