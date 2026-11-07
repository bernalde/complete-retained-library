module

public import Chapter03OAExecKKT

@[expose] public section

/-! Author-stage execution semantics. Reachability contains only finite raw
source-ordered transitions. It does not assume progress, fresh targets or a
final answer. Master replies include the published unbounded branch; the next
gap inspection occurs only after the selected fixed solve has been appended. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

structure State (d : Data n m l r) where
  history : List (Event d)
  incumbent : Option (Point n m)
  lower : ℝ

def initialState (d : Data n m l r) (seed : Point n m) : State d :=
  ⟨[], none, d.f seed⟩

def SeedValid (d : Data n m l r) (seed : Point n m) : Prop :=
  IsMinimizer d.relaxation d.f seed ∧ seed ∈ d.domain ∧ ¬ integral seed

def loopOpen (d : Data n m l r) (epsilon : ℝ) (s : State d) : Prop :=
  ∀ u, s.incumbent = some u → epsilon < d.f u - s.lower

/-- Finite lower values are retained on a genuinely unbounded reply. -/
structure MasterChoice (d : Data n m l r) (seed : Point n m) (s : State d) where
  point : Point n m × ℝ
  attained : Bool
  valid : if attained then IsMinimizer (master d seed s.history) Prod.snd point
    else point ∈ master d seed s.history ∧
      ¬ BddBelow (Prod.snd '' master d seed s.history)

def MasterChoice.nextLower {d : Data n m l r} {seed : Point n m} {s : State d}
    (q : MasterChoice d seed s) : ℝ := if q.attained then q.point.2 else s.lower

theorem MasterChoice.mem {d : Data n m l r} {seed : Point n m} {s : State d}
    (q : MasterChoice d seed s) : q.point ∈ master d seed s.history := by
  have hv := q.valid
  cases h : q.attained <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hv
  · exact hv.1
  · exact hv.1

def keepBest (f : Point n m → ℝ) (old : Option (Point n m)) (p : Point n m) :
    Option (Point n m) :=
  match old with
  | none => some p
  | some u => if f p < f u then some p else some u

def nextIncumbent {d : Data n m l r} (s : State d) (e : Event d) :
    Option (Point n m) :=
  if e.restoration = none then keepBest d.f s.incumbent e.anchor else s.incumbent

def advance {d : Data n m l r} {seed : Point n m} (s : State d)
    (q : MasterChoice d seed s) (e : Event d) : State d :=
  ⟨s.history ++ [e], nextIncumbent s e, q.nextLower⟩

inductive RawStep (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    State d → State d → Prop
  | step {s : State d} (open_gap : loopOpen d epsilon s)
      (q : MasterChoice d seed s) (e : Event d) (valid : EventValid d e)
      (same_y : q.point.1.2 = intCast e.target) :
      RawStep d seed epsilon s (advance s q e)

/-- Least finite reachable relation, independent of all selector choices. -/
inductive Reachable (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    State d → Prop
  | initial : Reachable d seed epsilon (initialState d seed)
  | next {s t : State d} (before : Reachable d seed epsilon s)
      (step : RawStep d seed epsilon s t) : Reachable d seed epsilon t

inductive Decision (d : Data n m l r) (seed : Point n m) (s : State d)
  | empty (valid : master d seed s.history = ∅)
  | next (q : MasterChoice d seed s) (event : Event d)
      (valid : EventValid d event) (same_y : q.point.1.2 = intCast event.target)

/-- Exact local availability on the same open reachable states and master
choices that the selector can request. No global progress/return input. -/
structure LocalAvailability (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    Prop where
  master_attainment : ∀ s, Reachable d seed epsilon s → loopOpen d epsilon s →
    (master d seed s.history).Nonempty →
    BddBelow (Prod.snd '' master d seed s.history) →
    ∃ z, IsMinimizer (master d seed s.history) Prod.snd z
  fixed_or_restoration : ∀ s, Reachable d seed epsilon s → loopOpen d epsilon s →
    ∀ q : MasterChoice d seed s, ∃ e : Event d,
      EventValid d e ∧ q.point.1.2 = intCast e.target

def Selector (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :=
  ∀ s, Reachable d seed epsilon s → loopOpen d epsilon s → Decision d seed s

theorem selector_inhabited {d : Data n m l r} {seed : Point n m} {epsilon : ℝ}
    (availability : LocalAvailability d seed epsilon) :
    Nonempty (Selector d seed epsilon) := by
  classical
  have hd : ∀ s, Reachable d seed epsilon s → loopOpen d epsilon s →
      Nonempty (Decision d seed s) := by
    intro s hs ho
    by_cases he : (master d seed s.history).Nonempty
    · have hq : Nonempty (MasterChoice d seed s) := by
        by_cases hb : BddBelow (Prod.snd '' master d seed s.history)
        · obtain ⟨z,hz⟩ := availability.master_attainment s hs ho he hb
          exact ⟨⟨z,true,hz⟩⟩
        · obtain ⟨z,hz⟩ := he
          exact ⟨⟨z,false,hz,hb⟩⟩
      obtain ⟨q⟩ := hq
      obtain ⟨e,hv,hy⟩ := availability.fixed_or_restoration s hs ho q
      exact ⟨.next q e hv hy⟩
    · exact ⟨.empty (Set.not_nonempty_iff_eq_empty.mp he)⟩
  exact ⟨fun s hs ho => Classical.choice (hd s hs ho)⟩

structure Invariant (d : Data n m l r) (seed : Point n m) (s : State d) : Prop where
  history : ValidHistory d seed s.history
  lower : IsLowerBound d.original d.f s.lower
  feasible : ∀ u, s.incumbent = some u → u ∈ d.original
  provenance : ∀ u, s.incumbent = some u →
    ∃ e ∈ s.history, e.restoration = none ∧ e.anchor = u
  dominates : ∀ e ∈ s.history, e.restoration = none →
    ∃ u, s.incumbent = some u ∧ d.f u ≤ d.f e.anchor

theorem initial_invariant {d : Data n m l r} {seed : Point n m}
    (h : SeedValid d seed) : Invariant d seed (initialState d seed) := by
  refine ⟨⟨h.2.1, by simp [initialState]⟩,?_,?_,?_,?_⟩
  · exact fun p hp => h.1.2 p (original_subset_relaxation d hp)
  · simp [initialState]
  · simp [initialState]
  · simp [initialState]

theorem keepBest_some (f : Point n m → ℝ) (old : Option (Point n m))
    (p : Point n m) : ∃ u, keepBest f old p = some u ∧ f u ≤ f p := by
  classical
  cases old with
  | none => exact ⟨p,rfl,le_rfl⟩
  | some v =>
    by_cases h : f p < f v
    · exact ⟨p,by simp [keepBest,h],le_rfl⟩
    · exact ⟨v,by simp [keepBest,h],le_of_not_gt h⟩

theorem keepBest_cases {f : Point n m → ℝ} {old : Option (Point n m)}
    {p u : Point n m} (h : keepBest f old p = some u) :
    u = p ∨ old = some u := by
  classical
  cases old with
  | none => exact Or.inl (Option.some.inj h).symm
  | some v =>
    by_cases hv : f p < f v
    · simp only [keepBest,if_pos hv,Option.some.injEq] at h
      exact Or.inl h.symm
    · simpa only [keepBest,if_neg hv] using Or.inr h

theorem keepBest_le_old {f : Point n m → ℝ} {p u v : Point n m}
    (h : keepBest f (some v) p = some u) : f u ≤ f v := by
  classical
  by_cases hv : f p < f v
  · simp only [keepBest,if_pos hv,Option.some.injEq] at h
    exact h ▸ hv.le
  · simp only [keepBest,if_neg hv,Option.some.injEq] at h
    exact h ▸ le_rfl

end Chapter03.OAExec

#print axioms Chapter03.OAExec.selector_inhabited
#print axioms Chapter03.OAExec.initial_invariant
