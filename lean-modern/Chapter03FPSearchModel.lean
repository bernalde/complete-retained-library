module

public import Chapter03FPUnboundedAnalytic

@[expose] public section

/-! First-feasibility search. The actual master contains constraint tangents
and, in enhanced mode only, projection normals. It has no objective epigraph,
incumbent, cutoff, polishing or successful-target exclusion. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch

structure Data (n m l : ℕ) where
  base : Set (Point n m)
  f : Point n m → ℝ
  g : Fin l → Point n m → ℝ
  Df : Point n m → Point n m →L[ℝ] ℝ
  Dg : Fin l → Point n m → Point n m →L[ℝ] ℝ

variable {n m l : ℕ}

def Data.toUnbounded (d : Data n m l) : FPUnbounded.Data n m l :=
  ⟨d.base, d.f, d.g, d.Df, d.Dg, 0⟩

def Data.relaxation (d : Data n m l) : Set (Point n m) :=
  {p | p ∈ d.base ∧ ∀ j, d.g j p ≤ 0}

def Integral (p : Point n m) : Prop := ∃ q : IntVector m, p.2 = intCast q

def Data.original (d : Data n m l) : Set (Point n m) :=
  {p | p ∈ d.relaxation ∧ Integral p}

/-- Analytic assumptions only. The conversion fixes the unused delta to zero. -/
abbrev Analytic (d : Data n m l) : Prop := FPUnbounded.Analytic d.toUnbounded

def tangent (d : Data n m l) (a : Point n m) (j : Fin l) (p : Point n m) : ℝ :=
  d.g j a + d.Dg j a (p-a)

def selectedAt (d : Data n m l) (a : Point n m) (j : Fin l) : Prop :=
  ¬OAKKT.AffineRow (d.g j) ∧ 0 ≤ d.g j a

structure Event (n m : ℕ) where
  target : IntVector m
  projection : Point n m

def Event.normal (e : Event n m) (p : Point n m) : ℝ :=
  @inner ℝ _ _ (Chapter03.yMap n m e.projection - intY e.target)
    (Chapter03.yMap n m p - Chapter03.yMap n m e.projection)

structure State (n m : ℕ) where
  seed : Point n m
  history : List (Event n m)

def initialState (seed : Point n m) : State n m := ⟨seed, []⟩

def State.reference (s : State n m) : Point n m :=
  ((s.history.getLast?).map Event.projection).getD s.seed

def append (s : State n m) (e : Event n m) : State n m :=
  ⟨s.seed, s.history ++ [e]⟩

inductive Mode where
  | basic
  | enhanced
  deriving DecidableEq

/-- Literal selection: all seed rows, later nonlinear rows with g >= 0.
At feasible history anchors the latter are precisely the active nonlinear rows. -/
def Rows (d : Data n m l) (s : State n m) (p : Point n m) : Prop :=
  (∀ j, tangent d s.seed j p ≤ 0) ∧
  ∀ e ∈ s.history, ∀ j, selectedAt d e.projection j → tangent d e.projection j p ≤ 0

def master (d : Data n m l) (mode : Mode) (s : State n m) : Set (Point n m) :=
  {p | p ∈ d.base ∧ Integral p ∧ Rows d s p ∧
    (mode = .enhanced → ∀ e ∈ s.history, 0 ≤ e.normal p)}

def masterCost (s : State n m) (p : Point n m) : ℝ := l1 s.reference p

/-- Only actual projection optimality and the fractional branch are recorded. -/
structure EventValid (d : Data n m l) (e : Event n m) : Prop where
  projection_min : IsMinimizer d.relaxation (distance e.target) e.projection
  fractional : ¬Integral e.projection

structure Valid (d : Data n m l) (s : State n m) : Prop where
  seed : s.seed ∈ d.relaxation
  events : ∀ e ∈ s.history, EventValid d e

/-- The finite set must contain targets of the actual master, not just C. -/
def TargetBound (d : Data n m l) (mode : Mode) (Q : Finset (IntVector m)) : Prop :=
  ∀ s, Valid d s → ∀ p ∈ master d mode s, ∀ q : IntVector m,
    p.2 = intCast q → q ∈ Q

/-- Internal modular premise. Enhanced geometry and the separate basic CQ
bridge must discharge it before any source-facing endpoint is stated. -/
def NormalLaw (d : Data n m l) (mode : Mode) (Q : Finset (IntVector m)) : Prop :=
  ∀ s, Valid d s → (∀ e ∈ s.history, e.target ∈ Q) →
    ∀ p ∈ master d mode s, ∀ e ∈ s.history, 0 ≤ e.normal p

inductive Initialization (d : Data n m l) where
  | empty (isEmpty : ¬d.relaxation.Nonempty)
  | minimum (point : Point n m) (optimal : IsMinimizer d.relaxation d.f point)

/-- Every pair of tied exact master/projection minima is admitted. -/
structure Step (d : Data n m l) (mode : Mode) (s : State n m) where
  point : Point n m
  target : IntVector m
  projection : Point n m
  master_min : IsMinimizer (master d mode s) (masterCost s) point
  target_eq : point.2 = intCast target
  projection_min : IsMinimizer d.relaxation (distance target) projection

def Step.event {d : Data n m l} {mode : Mode} {s : State n m}
    (step : Step d mode s) : Event n m := ⟨step.target, step.projection⟩

inductive Decision (d : Data n m l) (mode : Mode) (s : State n m) where
  | empty (isEmpty : ¬(master d mode s).Nonempty)
  | project (step : Step d mode s)

/-- A feasible seed supplies nonemptiness of the fixed projection domain even
for otherwise unreachable histories. No progress fact is part of this type. -/
def Selector (d : Data n m l) (mode : Mode) :=
  ∀ s : State n m, s.seed ∈ d.relaxation → Decision d mode s

end Chapter03.FPSearch
