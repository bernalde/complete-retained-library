module

public import Chapter03FPBasic
public import Chapter03OAKKTSource

@[expose] public section

/-! Unrestricted integer-domain, disabled-success-exclusion feasibility pump.
The only boundedness assumption concerns the feasible nonlinear relaxation.
No target bounds, supplied local solutions, or progress conclusions are fields. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnbounded

structure Data (n m l : ℕ) where
  base : Set (Point n m)
  f : Point n m → ℝ
  g : Fin l → Point n m → ℝ
  Df : Point n m → Point n m →L[ℝ] ℝ
  Dg : Fin l → Point n m → Point n m →L[ℝ] ℝ
  delta : ℝ

variable {n m l : ℕ}

def Data.nonlinear (d : Data n m l) : Set (Fin l) :=
  {j | ¬Chapter03.OAKKT.AffineRow (d.g j)}

def Data.relaxation (d : Data n m l) : Set (Point n m) :=
  {p | p ∈ d.base ∧ ∀ j, d.g j p ≤ 0}

def Data.original (d : Data n m l) : Set (Point n m) :=
  {p | p ∈ d.relaxation ∧ ∃ y : IntVector m, p.2 = intCast y}

def Data.level (d : Data n m l) (inc : Option (Point n m)) : Option ℝ :=
  inc.map (fun p => cutoffValue d.delta (d.f p))

def Data.region (d : Data n m l) (level : Option ℝ) : Set (Point n m) :=
  {p | p ∈ d.relaxation ∧ Allows level (d.f p)}

def Data.fiber (d : Data n m l) (y : IntVector m) : Set (Point n m) :=
  {p | p ∈ d.relaxation ∧ p.2 = intCast y}

/-- Bounded-feasible-set interpretation of A3, with ambient derivatives on the
original closed convex base. Positivity of delta is reserved for termination. -/
structure Analytic (d : Data n m l) : Prop where
  base_closed : IsClosed d.base
  base_convex : Convex ℝ d.base
  convex_f : ConvexOn ℝ d.base d.f
  convex_g : ∀ j, ConvexOn ℝ d.base (d.g j)
  derivative_f : ∀ p ∈ d.base, HasFDerivAt d.f (d.Df p) p
  derivative_g : ∀ j p, p ∈ d.base → HasFDerivAt (d.g j) (d.Dg j p) p
  bounded_relaxation : Bornology.IsBounded d.relaxation
  delta_nonnegative : 0 ≤ d.delta

def anchors (d : Data n m l) (s : State n m) : List (Anchor n m l) :=
  ⟨s.seed, Set.univ⟩ :: s.history.map (fun e =>
    ⟨e.anchor, {j | j ∈ d.nonlinear ∧ 0 ≤ d.g j e.anchor}⟩)

def family (d : Data n m l) (s : State n m) :
    TangentFamily n m l (anchors d s).length where
  origin i := ((anchors d s).get i).point
  selected i := ((anchors d s).get i).selected
  derivative i j := d.Dg j ((anchors d s).get i).point

/-- Original base and unrestricted integrality, all retained constraint and
objective tangents. There is no artificial integer box. -/
def epigraph (d : Data n m l) (s : State n m) : Set (Point n m × ℝ) :=
  {z | z.1 ∈ d.base ∧ (∃ y : IntVector m, z.1.2 = intCast y) ∧
    (∀ i j, j ∈ (family d s).selected i →
      d.g j ((family d s).origin i) +
        (family d s).derivative i j (z.1 - (family d s).origin i) ≤ 0) ∧
    ∀ i, d.f ((family d s).origin i) +
      d.Df ((family d s).origin i) (z.1 - (family d s).origin i) ≤ z.2}

/-- Success exclusions are disabled. Every failed normal remains in the pump. -/
def master (d : Data n m l) (s : State n m) : Set (Point n m × ℝ) :=
  {z | z ∈ epigraph d s ∧ retainedNormals s z.1 ∧
    Allows (d.level s.incumbent) z.2}

def masterCost (s : State n m) (z : Point n m × ℝ) : ℝ := l1 s.reference z.1

/-- Handoff alone filters normals strictly before the last success. -/
def handoff (d : Data n m l) (s : State n m) : Set (Point n m × ℝ) :=
  {z | z ∈ epigraph d s ∧ handoffNormals s z.1}

/-- Every local best choice is admitted. There is no fixed tie policy. -/
def BestChoice (d : Data n m l) (old : Option (Point n m))
    (polished chosen : Point n m) : Prop :=
  match old with
  | none => chosen = polished
  | some u => (chosen = u ∨ chosen = polished) ∧ d.f chosen = min (d.f u) (d.f polished)

/-- Raw completed-event evidence, containing only actual optimizer outcomes,
branch facts and local selection. It does not assert progress or cut validity. -/
structure EventReply (d : Data n m l) (s : State n m)
    (z : Point n m × ℝ) (e : Event n m) : Prop where
  target_eq : z.1.2 = intCast e.target
  generation_eq : e.generationLevel = d.level s.incumbent
  projection_min : IsMinimizer (d.region (d.level s.incumbent)) (distance e.target) e.projection
  outcome : match e.success with
    | none => distance e.target e.projection ≠ 0
    | some pu => distance e.target e.projection = 0 ∧
        IsMinimizer (d.fiber e.target) d.f pu.1 ∧ BestChoice d s.incumbent pu.1 pu.2

inductive Initialization (d : Data n m l) where
  | empty (isEmpty : ¬d.relaxation.Nonempty)
  | minimum (point : Point n m) (optimal : IsMinimizer d.relaxation d.f point)

inductive MasterChoice (d : Data n m l) (s : State n m) where
  | empty (isEmpty : ¬(master d s).Nonempty)
  | minimum (point : Point n m × ℝ) (optimal : IsMinimizer (master d s) (masterCost s) point)

inductive ProjectionChoice (d : Data n m l) (s : State n m) (y : IntVector m) where
  | empty (isEmpty : ¬(d.region (d.level s.incumbent)).Nonempty)
  | minimum (point : Point n m)
      (optimal : IsMinimizer (d.region (d.level s.incumbent)) (distance y) point)

end Chapter03.FPUnbounded
