module

public import Chapter05QOAModel
public import Chapter03OAExecState

@[expose] public section

/-! Actual source-ordered batches over arbitrary safe-scale exact replies.
The lower bound is assigned before all pool solves, then the gap is inspected.
No freshness, termination or query-existence assumption occurs in a state/step. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter05.QOA.Exec
variable {n p m r : ℕ}
attribute [local instance] Classical.propDecidable

structure State (d : Data n p m r) where
  history : List (Event d)
  incumbent : Option (Point n p)
  lower : ℝ
  primaries : List (IntVector p)

def rows {d : Data n p m r} (seed : Token n p m) (H : List (Event d)) :
    List (Token n p m) := seed :: H.map Event.token

def master (d : Data n p m r) (seed : Token n p m) (H : List (Event d)) :=
  QOA.master d (rows seed H)

def initialState (d : Data n p m r) (seed : Token n p m) : State d :=
  ⟨[],none,d.f seed.anchor,[]⟩

def SeedValid (d : Data n p m r) (seed : Token n p m) : Prop :=
  IsMinimizer d.relaxation d.f seed.anchor ∧ seed.Safe d

def loopOpen (d : Data n p m r) (epsilon : ℝ) (s : State d) : Prop :=
  ∀ u, s.incumbent = some u → epsilon < d.f u - s.lower

structure Batch (d : Data n p m r) (seed : Token n p m) (s : State d) where
  point : Point n p × ℝ
  minimum : IsMinimizer (master d seed s.history) Prod.snd point
  pool : List ((Point n p × ℝ) × Event d)
  includes : point ∈ pool.map Prod.fst
  valid : ∀ v ∈ pool, v.1 ∈ master d seed s.history ∧
    EventValid d v.2 ∧ v.1.1.2 = intCast v.2.target

def Batch.events {d : Data n p m r} {seed : Token n p m} {s : State d}
    (b : Batch d seed s) : List (Event d) := b.pool.map Prod.snd

theorem Batch.events_valid {d : Data n p m r} {seed : Token n p m} {s : State d}
    (b : Batch d seed s) : ∀ e ∈ b.events, EventValid d e := by
  intro e he
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
  exact (b.valid v hv).2.1

theorem Batch.primaryEvent_exists {d : Data n p m r} {seed : Token n p m} {s : State d}
    (b : Batch d seed s) : ∃ e ∈ b.events, b.point.1.2 = intCast e.target := by
  obtain ⟨v,hv,he⟩ := List.mem_map.mp b.includes
  exact ⟨v.2,List.mem_map.mpr ⟨v,hv,rfl⟩,he ▸ (b.valid v hv).2.2⟩

def Batch.primaryEvent {d : Data n p m r} {seed : Token n p m} {s : State d}
    (b : Batch d seed s) : Event d := Classical.choose b.primaryEvent_exists

theorem Batch.primaryEvent_spec {d : Data n p m r} {seed : Token n p m} {s : State d}
    (b : Batch d seed s) : b.primaryEvent ∈ b.events ∧
      b.point.1.2 = intCast b.primaryEvent.target := Classical.choose_spec b.primaryEvent_exists

theorem Batch.pool_height_minimum {d : Data n p m r} {seed : Token n p m} {s : State d}
    (b : Batch d seed s) :
    IsMinimizer {q | q ∈ b.pool.map Prod.fst} Prod.snd b.point := by
  refine ⟨b.includes,?_⟩
  intro q hq
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  exact b.minimum.2 v.1 (b.valid v hv).1

def nextIncumbent {d : Data n p m r} (s : State d) (e : Event d) : Option (Point n p) :=
  if e.restoration = none then Chapter03.OAExec.keepBest d.f s.incumbent e.anchor
  else s.incumbent

def pushEvent {d : Data n p m r} (s : State d) (e : Event d) : State d :=
  ⟨s.history ++ [e],nextIncumbent s e,s.lower,s.primaries⟩

def pushEvents {d : Data n p m r} : State d → List (Event d) → State d
  | s, [] => s
  | s, e :: H => pushEvents (pushEvent s e) H

theorem pushEvents_history {d : Data n p m r} (s : State d) (H : List (Event d)) :
    (pushEvents s H).history = s.history ++ H := by
  induction H generalizing s with
  | nil => simp [pushEvents]
  | cons e H ih => simpa [pushEvents,pushEvent,List.append_assoc] using ih (pushEvent s e)

theorem pushEvents_lower {d : Data n p m r} (s : State d) (H : List (Event d)) :
    (pushEvents s H).lower = s.lower := by
  induction H generalizing s with
  | nil => rfl
  | cons e H ih => exact ih (pushEvent s e)

def advance {d : Data n p m r} {seed : Token n p m} (s : State d)
    (b : Batch d seed s) : State d :=
  let t := pushEvents {s with lower := b.point.2} b.events
  {t with primaries := s.primaries ++ [b.primaryEvent.target]}

@[simp] theorem advance_history {d : Data n p m r} {seed : Token n p m} (s : State d)
    (b : Batch d seed s) : (advance s b).history = s.history ++ b.events :=
  pushEvents_history {s with lower := b.point.2} b.events

@[simp] theorem advance_lower {d : Data n p m r} {seed : Token n p m} (s : State d)
    (b : Batch d seed s) : (advance s b).lower = b.point.2 :=
  pushEvents_lower {s with lower := b.point.2} b.events

@[simp] theorem advance_primaries {d : Data n p m r} {seed : Token n p m} (s : State d)
    (b : Batch d seed s) :
    (advance s b).primaries = s.primaries ++ [b.primaryEvent.target] := rfl

inductive RawStep (d : Data n p m r) (seed : Token n p m) (epsilon : ℝ) :
    State d → State d → Prop
  | step {s : State d} (open_gap : loopOpen d epsilon s) (b : Batch d seed s) :
      RawStep d seed epsilon s (advance s b)

inductive Reachable (d : Data n p m r) (seed : Token n p m) (epsilon : ℝ) : State d → Prop
  | initial : Reachable d seed epsilon (initialState d seed)
  | next {s t : State d} (before : Reachable d seed epsilon s)
      (step : RawStep d seed epsilon s t) : Reachable d seed epsilon t

structure Invariant (d : Data n p m r) (s : State d) : Prop where
  history : ∀ e ∈ s.history, EventValid d e
  lower : IsLowerBound d.original d.f s.lower
  feasible : ∀ u, s.incumbent = some u → u ∈ d.original
  provenance : ∀ u, s.incumbent = some u →
    ∃ e ∈ s.history, e.restoration = none ∧ e.anchor = u
  dominates : ∀ e ∈ s.history, e.restoration = none →
    ∃ u, s.incumbent = some u ∧ d.f u ≤ d.f e.anchor

theorem initial_invariant {d : Data n p m r} (hR : RelaxationRegularity d)
    {seed : Token n p m} (hs : SeedValid d seed) :
    Invariant d (initialState d seed) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [initialState]
  · exact fun z hz => hs.1.2 z (original_subset_relaxation hR hz)
  · simp [initialState]
  · simp [initialState]
  · simp [initialState]

theorem history_safe {d : Data n p m r} {seed : Token n p m}
    (hs : seed.Safe d) {H : List (Event d)} (hh : ∀ e ∈ H, EventValid d e) :
    SafeRows d (rows seed H) := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hs
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp ht
    exact (hh e he).1

theorem pushEvent_invariant {d : Data n p m r} {s : State d} (hi : Invariant d s)
    {e : Event d} (he : EventValid d e) : Invariant d (pushEvent s e) := by
  refine ⟨?_,hi.lower,?_,?_,?_⟩
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hi.history v hv
    · simpa only [List.mem_singleton.mp hv] using he
  · intro u hu
    change nextIncumbent s e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [nextIncumbent,if_pos hn] at hu
      rcases Chapter03.OAExec.keepBest_cases hu with rfl | hu
      · exact event_feasible he hn
      · exact hi.feasible _ hu
    · exact hi.feasible _ (by simpa [nextIncumbent,hn] using hu)
  · intro u hu
    change nextIncumbent s e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [nextIncumbent,if_pos hn] at hu
      rcases Chapter03.OAExec.keepBest_cases hu with rfl | hu
      · exact ⟨e,List.mem_append_right _ (by simp),hn,rfl⟩
      · obtain ⟨v,hv,hnv,ha⟩ := hi.provenance u hu
        exact ⟨v,List.mem_append_left _ hv,hnv,ha⟩
    · obtain ⟨v,hv,hnv,ha⟩ := hi.provenance u (by simpa [nextIncumbent,hn] using hu)
      exact ⟨v,List.mem_append_left _ hv,hnv,ha⟩
  · intro v hv hnv
    change v ∈ s.history ++ [e] at hv
    change ∃ u, nextIncumbent s e = some u ∧ d.f u ≤ d.f v.anchor
    by_cases hn : e.restoration = none
    · obtain ⟨u,hu,hle⟩ := Chapter03.OAExec.keepBest_some d.f s.incumbent e.anchor
      refine ⟨u,by simpa [nextIncumbent,hn] using hu,?_⟩
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨w,hw,hlew⟩ := hi.dominates v hv hnv
        rw [hw] at hu
        exact (Chapter03.OAExec.keepBest_le_old hu).trans hlew
      · simpa only [List.mem_singleton.mp hv] using hle
    · rcases List.mem_append.mp hv with hv | hv
      · simpa [nextIncumbent,hn] using hi.dominates v hv hnv
      · exact False.elim (hn ((List.mem_singleton.mp hv) ▸ hnv))

theorem pushEvents_invariant {d : Data n p m r} (s : State d) (hi : Invariant d s)
    (H : List (Event d)) (hh : ∀ e ∈ H, EventValid d e) :
    Invariant d (pushEvents s H) := by
  induction H generalizing s with
  | nil => exact hi
  | cons e H ih =>
    exact ih (pushEvent s e) (pushEvent_invariant hi (hh e (by simp)))
      (fun e he => hh e (by simp [he]))

theorem advance_invariant {d : Data n p m r} (hr : Regularity d)
    {seed : Token n p m} (hs : seed.Safe d) {s : State d} (hi : Invariant d s)
    (b : Batch d seed s) : Invariant d (advance s b) := by
  have hl : Invariant d {s with lower := b.point.2} :=
    ⟨hi.history,QOA.master_lower_bound hr (history_safe hs hi.history) b.minimum,
      hi.feasible,hi.provenance,hi.dominates⟩
  have hf := pushEvents_invariant _ hl b.events b.events_valid
  exact ⟨hf.history,hf.lower,hf.feasible,hf.provenance,hf.dominates⟩

theorem reachable_invariant {d : Data n p m r} (hr : Regularity d)
    (hR : RelaxationRegularity d) {seed : Token n p m} (hs : SeedValid d seed)
    {epsilon : ℝ} {s : State d} (h : Reachable d seed epsilon s) : Invariant d s := by
  induction h with
  | initial => exact initial_invariant hR hs
  | next _ step ih =>
    cases step with
    | step _ b => exact advance_invariant hr hs.2 ih b

theorem reachable_primary_processed {d : Data n p m r} {seed : Token n p m}
    {epsilon : ℝ} {s : State d} (h : Reachable d seed epsilon s) :
    ∀ y ∈ s.primaries, ∃ e ∈ s.history, e.target = y := by
  induction h with
  | initial => simp [initialState]
  | @next s t _ step ih =>
    cases step with
    | step _ b =>
      intro y hy
      rw [advance_primaries] at hy
      rw [advance_history]
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨e,he,hey⟩ := ih y hy
        exact ⟨e,List.mem_append_left _ he,hey⟩
      · exact ⟨b.primaryEvent,List.mem_append_right _ b.primaryEvent_spec.1,
          (List.mem_singleton.mp hy).symm⟩

theorem reachable_primary_active {d : Data n p m r} (hr : Regularity d)
    (hR : RelaxationRegularity d) {seed : Token n p m} (hs : SeedValid d seed)
    {epsilon : ℝ} {s : State d} (h : Reachable d seed epsilon s) :
    ∀ y ∈ s.primaries, y ∈ d.activeY := by
  intro y hy
  obtain ⟨e,he,rfl⟩ := reachable_primary_processed h y hy
  exact event_active ((reachable_invariant hr hR hs h).history e he)

theorem master_append_subset (d : Data n p m r) (seed : Token n p m)
    (H K : List (Event d)) : master d seed (H ++ K) ⊆ master d seed H := by
  apply QOA.master_antitone d
  intro t ht
  simpa only [rows,List.map_append,List.mem_cons,List.mem_append] using
    (show t = seed ∨ t ∈ H.map Event.token ∨ t ∈ K.map Event.token from
      (List.mem_cons.mp ht).elim Or.inl (fun h => Or.inr (Or.inl h)))

theorem batch_values_monotone {d : Data n p m r} {seed : Token n p m} {s : State d}
    (b : Batch d seed s) (c : Batch d seed (advance s b)) : b.point.2 ≤ c.point.2 := by
  apply b.minimum.2 c.point
  apply master_append_subset d seed s.history b.events
  simpa only [advance_history] using c.minimum.1

end Chapter05.QOA.Exec
