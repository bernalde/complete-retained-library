module

public import Chapter02DICOPTModel
public import Chapter02DICOPTNoGood

@[expose] public section

/-! Literal binary no-good state for the qualified VG1990 bound procedure.
Each feasible reply stores actual source KKT/sign-convex data. An infeasible
reply stores exact emptiness. No reply stores optimum, freshness or progress. -/
noncomputable section
open scoped BigOperators
namespace Chapter02.DICOPT
variable {n m e l r : ℕ}

theorem realBinary_binary (b : BVector m) : Binary (realBinary b) := by
  intro i
  cases h : b i <;> simp [realBinary, h]

theorem realBinary_injective : Function.Injective (@realBinary m) := by
  intro b z h
  funext i
  have hi := congrFun h i
  cases hb : b i <;> cases hz : z i <;> simp_all [realBinary]

theorem binary_exists_realBinary {y : RealVector m} (hy : Binary y) :
    ∃ b : BVector m, y = realBinary b := by
  classical
  let b : BVector m := fun i => decide (y i = 1)
  refine ⟨b, ?_⟩
  funext i
  rcases hy i with hi | hi <;> simp [b, realBinary, hi]

theorem binary_mem_yBox (d : Data n m e l r) {y : RealVector m} (hy : Binary y) :
    y ∈ d.yBox := by
  constructor <;> intro i <;> rcases hy i with hi | hi <;> simp [hi]

theorem original_subset_relaxed (d : Data n m e l r) : d.original ⊆ d.relaxed := by
  intro z hz
  exact ⟨hz.1, binary_mem_yBox d hz.2⟩

theorem noGoodRow_realBinary_iff (b z : BVector m) :
    noGoodRow b (realBinary z) ≤ 0 ↔ z ≠ b :=
  binary_no_good_formula_iff b z

/-- An exact fixed-binary reply: its feasible branch is certificate-bearing,
not an oracle claiming that a local nonlinear solve is globally optimal. -/
structure FiberReply (d : Data n m e l r) where
  binary : BVector m
  anchor : Option (Anchor d)
  same_y : ∀ a, anchor = some a → a.y = realBinary binary
  empty : anchor = none → ¬ (d.fiber (realBinary binary)).Nonempty

/-- Every occurrence of an anchor is retained. Equal-valued occurrences are
separate list indices, so they retain separate weights and master slacks. -/
structure State (d : Data n m e l r) where
  initial : Anchor d
  processed : List (FiberReply d)
  incumbent : Option (RealVector n × RealVector m)

def State.history {d : Data n m e l r} (s : State d) : List (Anchor d) :=
  s.initial :: s.processed.filterMap FiberReply.anchor

def State.seen {d : Data n m e l r} (s : State d) : Finset (BVector m) :=
  (s.processed.map FiberReply.binary).toFinset

def State.remaining {d : Data n m e l r} (s : State d) : ℕ :=
  (Finset.univ \ s.seen).card

def State.master {d : Data n m e l r} (s : State d) :=
  masterFeasible d s.history s.seen

def State.value {d : Data n m e l r} (s : State d) :=
  masterObjective d s.history

def pointObjective (d : Data n m e l r) (z : RealVector n × RealVector m) : ℝ :=
  d.objective z.1 z.2

def best (d : Data n m e l r) (old : Option (RealVector n × RealVector m))
    (p : RealVector n × RealVector m) : RealVector n × RealVector m :=
  match old with
  | none => p
  | some u => if pointObjective d p < pointObjective d u then p else u

def append (d : Data n m e l r) (s : State d) (b : FiberReply d) : State d :=
  ⟨s.initial, s.processed ++ [b], match b.anchor with
    | none => s.incumbent
    | some a => some (best d s.incumbent (a.x,a.y))⟩

structure Invariant (d : Data n m e l r) (s : State d) : Prop where
  feasible : ∀ u, s.incumbent = some u → u ∈ d.original
  best : ∀ b ∈ s.processed, ∀ a, b.anchor = some a →
    ∃ u, s.incumbent = some u ∧ pointObjective d u ≤ d.objective a.x a.y

theorem history_nonempty {d : Data n m e l r} (s : State d) : s.history ≠ [] := by
  simp [State.history]

theorem history_append (d : Data n m e l r) (s : State d) (b : FiberReply d) :
    (append d s b).history = s.history ++ b.anchor.toList := by
  simp [State.history, append, List.filterMap_append, List.filterMap_cons]
  cases b.anchor <;> rfl

theorem seen_append (d : Data n m e l r) (s : State d) (b : FiberReply d) :
    (append d s b).seen = insert b.binary s.seen := by
  classical
  ext z
  simp [State.seen, append, or_comm]

theorem best_le_new (d : Data n m e l r) (old : Option (RealVector n × RealVector m))
    (p : RealVector n × RealVector m) :
    pointObjective d (best d old p) ≤ pointObjective d p := by
  cases old with
  | none => exact le_rfl
  | some u =>
    simp only [best]
    split
    · exact le_rfl
    · exact le_of_not_gt ‹¬ pointObjective d p < pointObjective d u›

theorem best_le_old (d : Data n m e l r) (u p : RealVector n × RealVector m) :
    pointObjective d (best d (some u) p) ≤ pointObjective d u := by
  simp only [best]
  split
  · exact le_of_lt ‹pointObjective d p < pointObjective d u›
  · exact le_rfl

theorem best_feasible (d : Data n m e l r) (old : Option (RealVector n × RealVector m))
    (p : RealVector n × RealVector m) (hp : p ∈ d.original)
    (ho : ∀ u, old = some u → u ∈ d.original) : best d old p ∈ d.original := by
  cases old with
  | none => exact hp
  | some u =>
    simp only [best]
    split
    · exact hp
    · exact ho u rfl

theorem reply_anchor_original (d : Data n m e l r) (b : FiberReply d)
    (a : Anchor d) (ha : b.anchor = some a) : (a.x,a.y) ∈ d.original := by
  refine ⟨a.kkt.feasible, ?_⟩
  rw [b.same_y a ha]
  exact realBinary_binary b.binary

theorem append_invariant (d : Data n m e l r) {s : State d}
    (hs : Invariant d s) (b : FiberReply d) : Invariant d (append d s b) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    cases he : b.anchor with
    | none => exact hs.feasible u (by simpa only [append, he] using hu)
    | some a =>
      have hu' : best d s.incumbent (a.x,a.y) = u := by
        simpa only [append, he, Option.some.injEq] using hu
      rw [← hu']
      exact best_feasible d s.incumbent _ (reply_anchor_original d b a he) hs.feasible
  · intro c hc a ha
    simp only [append, List.mem_append, List.mem_singleton] at hc
    cases he : b.anchor with
    | none =>
      rcases hc with hc | rfl
      · simpa only [append, he] using hs.best c hc a ha
      · simp [he] at ha
    | some q =>
      refine ⟨best d s.incumbent (q.x,q.y), by simp [append,he], ?_⟩
      rcases hc with hc | rfl
      · obtain ⟨u,hu,hle⟩ := hs.best c hc a ha
        rw [hu]
        exact (best_le_old d u (q.x,q.y)).trans hle
      · have hqa : q = a := Option.some.inj (he.symm.trans ha)
        subst a
        exact best_le_new d s.incumbent (q.x,q.y)

def initialState {d : Data n m e l r} (a : Anchor d) : State d := ⟨a, [], none⟩

theorem initial_invariant {d : Data n m e l r} (a : Anchor d) :
    Invariant d (initialState a) := by
  constructor <;> simp [initialState]

theorem initial_remaining {d : Data n m e l r} (a : Anchor d) :
    (initialState a).remaining = Fintype.card (BVector m) := by
  simp [State.remaining, State.seen, initialState]

/-- Freshness follows from the actual binary no-good rows in a feasible master. -/
theorem master_fresh (d : Data n m e l r) (s : State d)
    (q : MasterPoint d s.history) (hq : q ∈ s.master)
    (b : BVector m) (hy : q.y = realBinary b) : b ∉ s.seen := by
  intro hb
  have hn := hq.1.2.2 b hb
  rw [hy] at hn
  exact ((noGoodRow_realBinary_iff b b).mp hn) rfl

theorem append_remaining_lt (d : Data n m e l r) (s : State d)
    (q : MasterPoint d s.history) (hq : q ∈ s.master)
    (b : FiberReply d) (hy : q.y = realBinary b.binary) :
    (append d s b).remaining < s.remaining := by
  unfold State.remaining
  rw [seen_append]
  exact binary_remaining_insert_lt s.seen b.binary (master_fresh d s q hq b.binary hy)

end Chapter02.DICOPT
