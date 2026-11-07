module

public import Chapter03
public import Chapter06

@[expose] public section

/-! Candidate literal feasibility-pump carriers and subproblems. Analytic,
progress and return facts are proved in subsequent modules, not fields here. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02
namespace Chapter03.FP

structure Data (n m l r : ℕ) where
  model : ModelData n m l r
  f : Point n m → ℝ
  Df : Point n m → Point n m →L[ℝ] ℝ
  Dg : Fin l → Point n m → Point n m →L[ℝ] ℝ
  nonlinear : Set (Fin l)
  delta : ℝ

variable {n m l r : ℕ}

def intCast (y : IntVector m) : RealVector m := fun j => (y j : ℝ)
def intY (y : IntVector m) : EuclideanSpace ℝ (Fin m) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm (intCast y)

def Data.base (d : Data n m l r) : Set (Point n m) :=
  {p | p ∈ d.model.linearRegion ∧ ∀ j, d.model.lo j ≤ p.2 j ∧ p.2 j ≤ d.model.hi j}
def Data.relaxation (d : Data n m l r) : Set (Point n m) :=
  d.model.relaxationOn Set.univ
def Data.original (d : Data n m l r) : Set (Point n m) :=
  d.model.feasibleOn Set.univ
def Data.box (d : Data n m l r) : Finset (IntVector m) :=
  (integerBox_finite d.model.lo d.model.hi).toFinset

def cutoffValue (delta U : ℝ) : ℝ := U - delta * max |U| 1

def Allows : Option ℝ → ℝ → Prop
  | none, _ => True
  | some c, v => v ≤ c

def Data.level (d : Data n m l r) (inc : Option (Point n m)) : Option ℝ :=
  inc.map (fun p => cutoffValue d.delta (d.f p))

def Data.region (d : Data n m l r) (level : Option ℝ) : Set (Point n m) :=
  {p | p ∈ d.relaxation ∧ Allows level (d.f p)}

def Data.fiber (d : Data n m l r) (y : IntVector m) : Set (Point n m) :=
  {p | p ∈ d.relaxation ∧ p.2 = intCast y}

def distance (y : IntVector m) (p : Point n m) : ℝ :=
  ‖intY y - Chapter03.yMap n m p‖ ^ 2

def l1 (reference p : Point n m) : ℝ := ∑ j, |p.2 j - reference.2 j|

/-- Sufficient source interpretation: bounded nonlinear feasible relaxation;
ambient derivative extensions at boundary points. No compact master enclosure. -/
structure Analytic (d : Data n m l r) : Prop where
  convex_f : ConvexOn ℝ d.base d.f
  convex_g : ∀ j, ConvexOn ℝ d.base (d.model.g j)
  derivative_f : ∀ p ∈ d.base, HasFDerivAt d.f (d.Df p) p
  derivative_g : ∀ j p, p ∈ d.base → HasFDerivAt (d.model.g j) (d.Dg j p) p
  bounded_relaxation : Bornology.IsBounded d.relaxation
  delta_nonnegative : 0 ≤ d.delta

/-- Only completed bodies occur here. `success = some (p,u)` retains the
actual polished point and the locally chosen incumbent, including either tie. -/
structure Event (n m : ℕ) where
  target : IntVector m
  projection : Point n m
  generationLevel : Option ℝ
  success : Option (Point n m × Point n m)

def Event.anchor (e : Event n m) : Point n m :=
  match e.success with | none => e.projection | some z => z.1

def Event.normal (e : Event n m) (p : Point n m) : ℝ :=
  @inner ℝ _ _ (Chapter03.yMap n m e.projection - intY e.target)
    (Chapter03.yMap n m p - Chapter03.yMap n m e.projection)

structure State (n m : ℕ) where
  seed : Point n m
  history : List (Event n m)
  incumbent : Option (Point n m)
  lastSuccess : Option ℕ

def initialState (seed : Point n m) : State n m := ⟨seed, [], none, none⟩
def State.reference (s : State n m) : Point n m :=
  ((s.history.getLast?).map Event.anchor).getD s.seed

def append (s : State n m) (e : Event n m) : State n m :=
  ⟨s.seed, s.history ++ [e],
    match e.success with | none => s.incumbent | some z => some z.2,
    match e.success with | none => s.lastSuccess | some _ => some s.history.length⟩

structure Anchor (n m l : ℕ) where
  point : Point n m
  selected : Set (Fin l)

def anchors (d : Data n m l r) (s : State n m) : List (Anchor n m l) :=
  ⟨s.seed, Set.univ⟩ :: s.history.map (fun e =>
    ⟨e.anchor, {j | j ∈ d.nonlinear ∧ 0 ≤ d.model.g j e.anchor}⟩)

def family (d : Data n m l r) (s : State n m) :
    TangentFamily n m l (anchors d s).length where
  origin i := ((anchors d s).get i).point
  selected i := ((anchors d s).get i).selected
  derivative i j := d.Dg j ((anchors d s).get i).point

def epigraph (d : Data n m l r) (s : State n m) : Set (Point n m × ℝ) :=
  Chapter06.EpigraphMaster d.model d.f (family d s)
    (fun i => d.Df ((anchors d s).get i).point) Set.univ

def retainedNormals (s : State n m) (p : Point n m) : Prop :=
  ∀ e ∈ s.history, e.success = none → 0 ≤ e.normal p

def noGoods (s : State n m) (p : Point n m) : Prop :=
  ∀ e ∈ s.history, e.success ≠ none → p.2 ≠ intCast e.target

def master (d : Data n m l r) (s : State n m) : Set (Point n m × ℝ) :=
  {z | z ∈ epigraph d s ∧ retainedNormals s z.1 ∧ noGoods s z.1 ∧
    Allows (d.level s.incumbent) z.2}

def masterCost (s : State n m) (z : Point n m × ℝ) : ℝ := l1 s.reference z.1

/-- Strict event indexing: only normals generated before the latest successful
body survive handoff. Before every success, all generated normals survive. -/
def handoffNormals (s : State n m) (p : Point n m) : Prop :=
  ∀ i : Fin s.history.length, (s.history.get i).success = none →
    (∀ k, s.lastSuccess = some k → i.val < k) → 0 ≤ (s.history.get i).normal p

def handoff (d : Data n m l r) (s : State n m) : Set (Point n m × ℝ) :=
  {z | z ∈ epigraph d s ∧ handoffNormals s z.1 ∧ noGoods s z.1}

/-- Every local best choice is admitted. There is no fixed tie policy. -/
def BestChoice (d : Data n m l r) (old : Option (Point n m))
    (polished chosen : Point n m) : Prop :=
  match old with
  | none => chosen = polished
  | some u => (chosen = u ∨ chosen = polished) ∧ d.f chosen = min (d.f u) (d.f polished)

/-- Raw completed-event evidence, containing only actual optimizer outcomes,
branch facts and local selection. It does not assert progress or cut validity. -/
structure EventReply (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) (e : Event n m) : Prop where
  target_eq : z.1.2 = intCast e.target
  generation_eq : e.generationLevel = d.level s.incumbent
  projection_min : IsMinimizer (d.region (d.level s.incumbent)) (distance e.target) e.projection
  outcome : match e.success with
    | none => distance e.target e.projection ≠ 0
    | some pu => distance e.target e.projection = 0 ∧
        IsMinimizer (d.fiber e.target) d.f pu.1 ∧ BestChoice d s.incumbent pu.1 pu.2

inductive Initialization (d : Data n m l r) where
  | empty (isEmpty : ¬d.relaxation.Nonempty)
  | minimum (point : Point n m) (optimal : IsMinimizer d.relaxation d.f point)

inductive MasterChoice (d : Data n m l r) (s : State n m) where
  | empty (isEmpty : ¬(master d s).Nonempty)
  | minimum (point : Point n m × ℝ) (optimal : IsMinimizer (master d s) (masterCost s) point)

inductive ProjectionChoice (d : Data n m l r) (s : State n m) (y : IntVector m) where
  | empty (isEmpty : ¬(d.region (d.level s.incumbent)).Nonempty)
  | minimum (point : Point n m)
      (optimal : IsMinimizer (d.region (d.level s.incumbent)) (distance y) point)

end Chapter03.FP
