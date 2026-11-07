module

public import Chapter05PSQCMixedModel
public import Chapter05QOAReturn

@[expose] public section

/-! Mixed-history storage reuses the unchanged QOA storage invariant through
an explicit projection. The Batch refers to the concrete mixed master; there
is no coercion to an all-OA Batch or assumed master-support property. -/
noncomputable section
open Set Chapter02 Chapter03.OAKKT
namespace Chapter05.PSQC.Mixed.Exec
variable {p q m l s nw nv : ℕ}
attribute [local instance] Classical.propDecidable

structure State (c : Context p q m l s nw nv) where
  history : List (Event c)
  incumbent : Option (Point (p+q) m)
  lower : ℝ
  primaries : List (IntVector m)

def State.project {c : Context p q m l s nw nv} (a : State c) : QOA.Exec.State c.qd :=
  ⟨a.history.map Event.toQOA, a.incumbent, a.lower, a.primaries⟩

def initialState (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l) : State c :=
  ⟨[], none, c.qd.f seed.anchor, []⟩

def loopOpen (c : Context p q m l s nw nv) (epsilon : ℝ) (a : State c) : Prop :=
  QOA.Exec.loopOpen c.qd epsilon a.project

structure Batch (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (a : State c) where
  point : Point (p+q) m × ℝ
  minimum : IsMinimizer (Mixed.master c seed a.history) Prod.snd point
  pool : List ((Point (p+q) m × ℝ) × Event c)
  includes : point ∈ pool.map Prod.fst
  valid : ∀ v ∈ pool, v.1 ∈ Mixed.master c seed a.history ∧
    EventValid c v.2 ∧ v.1.1.2 = intCast v.2.target

variable {c : Context p q m l s nw nv}

def Batch.events {seed : QOA.Token (p+q) m l} {a : State c}
    (b : Batch c seed a) : List (Event c) := b.pool.map Prod.snd

theorem Batch.events_valid {seed : QOA.Token (p+q) m l} {a : State c}
    (b : Batch c seed a) : HistoryValid c b.events := by
  intro e he
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
  exact (b.valid v hv).2.1

theorem Batch.primaryEvent_exists {seed : QOA.Token (p+q) m l} {a : State c}
    (b : Batch c seed a) : ∃ e ∈ b.events, b.point.1.2 = intCast e.target := by
  obtain ⟨v, hv, he⟩ := List.mem_map.mp b.includes
  exact ⟨v.2, List.mem_map.mpr ⟨v, hv, rfl⟩, he ▸ (b.valid v hv).2.2⟩

def Batch.primaryEvent {seed : QOA.Token (p+q) m l} {a : State c}
    (b : Batch c seed a) : Event c := Classical.choose b.primaryEvent_exists

theorem Batch.primaryEvent_spec {seed : QOA.Token (p+q) m l} {a : State c}
    (b : Batch c seed a) : b.primaryEvent ∈ b.events ∧
      b.point.1.2 = intCast b.primaryEvent.target := Classical.choose_spec b.primaryEvent_exists

theorem Batch.pool_height_minimum {seed : QOA.Token (p+q) m l} {a : State c}
    (b : Batch c seed a) :
    IsMinimizer {z | z ∈ b.pool.map Prod.fst} Prod.snd b.point := by
  refine ⟨b.includes, ?_⟩
  intro z hz
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
  exact b.minimum.2 v.1 (b.valid v hv).1

def pushEvent (a : State c) (e : Event c) : State c :=
  ⟨a.history ++ [e], QOA.Exec.nextIncumbent a.project e.toQOA, a.lower, a.primaries⟩

def pushEvents : State c → List (Event c) → State c
  | a, [] => a
  | a, e :: H => pushEvents (pushEvent a e) H

theorem project_pushEvent (a : State c) (e : Event c) :
    (pushEvent a e).project = QOA.Exec.pushEvent a.project e.toQOA := by
  simp [pushEvent, State.project, QOA.Exec.pushEvent]

theorem project_pushEvents (a : State c) (H : List (Event c)) :
    (pushEvents a H).project = QOA.Exec.pushEvents a.project (H.map Event.toQOA) := by
  induction H generalizing a with
  | nil => rfl
  | cons e H ih =>
    simpa only [pushEvents, List.map_cons, QOA.Exec.pushEvents, project_pushEvent]
      using ih (pushEvent a e)

theorem pushEvents_history (a : State c) (H : List (Event c)) :
    (pushEvents a H).history = a.history ++ H := by
  induction H generalizing a with
  | nil => simp [pushEvents]
  | cons e H ih => simpa [pushEvents, pushEvent, List.append_assoc] using ih (pushEvent a e)

theorem pushEvents_lower (a : State c) (H : List (Event c)) :
    (pushEvents a H).lower = a.lower := by
  induction H generalizing a with
  | nil => rfl
  | cons e H ih => exact ih (pushEvent a e)

def advance {seed : QOA.Token (p+q) m l} (a : State c) (b : Batch c seed a) : State c :=
  let t := pushEvents {a with lower := b.point.2} b.events
  {t with primaries := a.primaries ++ [b.primaryEvent.target]}

@[simp] theorem advance_history {seed : QOA.Token (p+q) m l} (a : State c)
    (b : Batch c seed a) : (advance a b).history = a.history ++ b.events :=
  pushEvents_history {a with lower := b.point.2} b.events

@[simp] theorem advance_lower {seed : QOA.Token (p+q) m l} (a : State c)
    (b : Batch c seed a) : (advance a b).lower = b.point.2 :=
  pushEvents_lower {a with lower := b.point.2} b.events

@[simp] theorem advance_primaries {seed : QOA.Token (p+q) m l} (a : State c)
    (b : Batch c seed a) : (advance a b).primaries = a.primaries ++ [b.primaryEvent.target] := rfl

inductive RawStep (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (epsilon : ℝ) : State c → State c → Prop
  | step {a : State c} (open_gap : loopOpen c epsilon a) (b : Batch c seed a) :
      RawStep c seed epsilon a (advance a b)

inductive Reachable (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (epsilon : ℝ) : State c → Prop
  | initial : Reachable c seed epsilon (initialState c seed)
  | next {a b : State c} (before : Reachable c seed epsilon a)
      (step : RawStep c seed epsilon a b) : Reachable c seed epsilon b

def Invariant (c : Context p q m l s nw nv) (a : State c) : Prop :=
  HistoryValid c a.history ∧ QOA.Exec.Invariant c.qd a.project

theorem initial_invariant {seed : QOA.Token (p+q) m l}
    (hs : QOA.Exec.SeedValid c.qd seed) : Invariant c (initialState c seed) := by
  refine ⟨?_, ?_⟩
  · intro e he
    exact (List.not_mem_nil he).elim
  · exact QOA.Exec.initial_invariant (relaxation_regularity c) hs

theorem pushEvents_invariant (a : State c) (hi : Invariant c a)
    (H : List (Event c)) (hH : HistoryValid c H) : Invariant c (pushEvents a H) := by
  refine ⟨?_, ?_⟩
  · intro e he
    rw [pushEvents_history] at he
    rcases List.mem_append.mp he with he | he
    · exact hi.1 e he
    · exact hH e he
  · rw [project_pushEvents]
    apply QOA.Exec.pushEvents_invariant _ hi.2
    intro e he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    exact event_toQOA_valid (hH v hv)

theorem invariant_source_provenance {a : State c} (hi : Invariant c a)
    {u : Point (p+q) m} (hu : a.incumbent = some u) :
    ∃ e ∈ a.history, e.toQOA.restoration = none ∧ e.anchor = u := by
  obtain ⟨v, hv, hn, ha⟩ := hi.2.provenance u hu
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  exact ⟨e, he, hn, ha⟩

theorem reachable_primary_processed {seed : QOA.Token (p+q) m l} {epsilon : ℝ}
    {a : State c} (h : Reachable c seed epsilon a) :
    ∀ y ∈ a.primaries, ∃ e ∈ a.history, e.target = y := by
  induction h with
  | initial => simp [initialState]
  | @next a t _ step ih =>
    cases step with
    | step _ b =>
      intro y hy
      rw [advance_primaries] at hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨e, he, hey⟩ := ih y hy
        exact ⟨e, by rw [advance_history]; exact List.mem_append_left _ he, hey⟩
      · have hy' : y = b.primaryEvent.target := List.mem_singleton.mp hy
        exact ⟨b.primaryEvent,
          by rw [advance_history]; exact List.mem_append_right _ b.primaryEvent_spec.1,
          hy'.symm⟩

#print axioms project_pushEvents
#print axioms pushEvents_invariant
#print axioms invariant_source_provenance
end Chapter05.PSQC.Mixed.Exec
