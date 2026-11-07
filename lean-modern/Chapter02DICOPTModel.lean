module

public import Chapter02Model
public import Mathlib.Basic.Sign.Basic

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter02.DICOPT

abbrev BVector (m : ℕ) := Fin m → Bool

def realBinary {m : ℕ} (b : BVector m) : RealVector m := fun i => if b i then 1 else 0

def Binary {m : ℕ} (y : RealVector m) : Prop := ∀ i, y i = 0 ∨ y i = 1

def dot {n : ℕ} (a x : RealVector n) : ℝ := ∑ i, a i * x i

structure Data (n m e l r : ℕ) where
  f : RealVector n → ℝ
  h : Fin e → RealVector n → ℝ
  g : Fin l → RealVector n → ℝ
  A : Fin e → RealVector m
  B : Fin l → RealVector m
  C : Fin r → RealVector m
  D : Fin r → RealVector n
  rhs : RealVector r
  xL : RealVector n
  xU : RealVector n
  c : RealVector m

variable {n m e l r : ℕ}

def Data.xBox (d : Data n m e l r) : Set (RealVector n) := Set.Icc d.xL d.xU

def Data.yBox (_d : Data n m e l r) : Set (RealVector m) := Set.Icc 0 1

def Data.objective (d : Data n m e l r) (x : RealVector n) (y : RealVector m) : ℝ :=
  dot d.c y + d.f x

def Data.eqRow (d : Data n m e l r) (i : Fin e) (x : RealVector n) (y : RealVector m) : ℝ :=
  dot (d.A i) y + d.h i x

def Data.ineqRow (d : Data n m e l r) (i : Fin l) (x : RealVector n) (y : RealVector m) : ℝ :=
  dot (d.B i) y + d.g i x

def Data.affineRow (d : Data n m e l r) (i : Fin r) (x : RealVector n) (y : RealVector m) : ℝ :=
  dot (d.C i) y + dot (d.D i) x - d.rhs i

def Data.Hard (d : Data n m e l r) (x : RealVector n) (y : RealVector m) : Prop :=
  x ∈ d.xBox ∧ ∀ i, d.affineRow i x y ≤ 0

def Data.Feasible (d : Data n m e l r) (x : RealVector n) (y : RealVector m) : Prop :=
  d.Hard x y ∧ (∀ i, d.eqRow i x y = 0) ∧ ∀ i, d.ineqRow i x y ≤ 0

def Data.fiber (d : Data n m e l r) (y : RealVector m) : Set (RealVector n) :=
  {x | d.Feasible x y}

def Data.original (d : Data n m e l r) : Set (RealVector n × RealVector m) :=
  {z | d.Feasible z.1 z.2 ∧ Binary z.2}

def Data.relaxed (d : Data n m e l r) : Set (RealVector n × RealVector m) :=
  {z | d.Feasible z.1 z.2 ∧ z.2 ∈ d.yBox}

/-- Actual ambient derivatives; no free linearization coefficients. -/
structure Jet (d : Data n m e l r) (x : RealVector n) where
  Df : RealVector n →L[ℝ] ℝ
  Dh : Fin e → RealVector n →L[ℝ] ℝ
  Dg : Fin l → RealVector n →L[ℝ] ℝ
  fderiv : HasFDerivAt d.f Df x
  hderiv : ∀ i, HasFDerivAt (d.h i) (Dh i) x
  gderiv : ∀ i, HasFDerivAt (d.g i) (Dg i) x

/-- Source epigraph KKT at a fixed REAL parameter, with all box normals. -/
structure FixedKKT (d : Data n m e l r) (x : RealVector n) (y : RealVector m) where
  jet : Jet d x
  alpha : ℝ
  sigma : ℝ
  lambda : RealVector e
  mu : RealVector l
  nu : RealVector r
  xLower : RealVector n
  xUpper : RealVector n
  feasible : d.Feasible x y
  alphaFeasible : d.f x ≤ alpha
  sigmaNonneg : 0 ≤ sigma
  muNonneg : ∀ i, 0 ≤ mu i
  nuNonneg : ∀ i, 0 ≤ nu i
  lowerNonneg : ∀ i, 0 ≤ xLower i
  upperNonneg : ∀ i, 0 ≤ xUpper i
  alphaComp : sigma * (d.f x - alpha) = 0
  ineqComp : ∀ i, mu i * d.ineqRow i x y = 0
  affineComp : ∀ i, nu i * d.affineRow i x y = 0
  lowerComp : ∀ i, xLower i * (d.xL i - x i) = 0
  upperComp : ∀ i, xUpper i * (x i - d.xU i) = 0
  alphaStationarity : 1 - sigma = 0
  stationarity : ∀ v : RealVector n,
    sigma * jet.Df v + (∑ i, lambda i * jet.Dh i v) +
      (∑ i, mu i * jet.Dg i v) + (∑ i, nu i * dot (d.D i) v) +
      (∑ i, (xUpper i - xLower i) * v i) = 0

/-- Full joint relaxed KKT, including BOTH variable-box normal families. -/
structure JointKKT (d : Data n m e l r) (x : RealVector n) (y : RealVector m)
    extends FixedKKT d x y where
  yFeasible : y ∈ d.yBox
  yLower : RealVector m
  yUpper : RealVector m
  yLowerNonneg : ∀ i, 0 ≤ yLower i
  yUpperNonneg : ∀ i, 0 ≤ yUpper i
  yLowerComp : ∀ i, yLower i * (0 - y i) = 0
  yUpperComp : ∀ i, yUpper i * (y i - 1) = 0
  yStationarity : ∀ v : RealVector m,
    dot d.c v + (∑ i, lambda i * dot (d.A i) v) +
      (∑ i, mu i * dot (d.B i) v) + (∑ i, nu i * dot (d.C i) v) +
      (∑ i, (yUpper i - yLower i) * v i) = 0

def signReal (a : ℝ) : ℝ := (SignType.sign a : ℝ)

structure SignedConvex (d : Data n m e l r) {x : RealVector n} {y : RealVector m}
    (k : FixedKKT d x y) : Prop where
  objective : ConvexOn ℝ d.xBox d.f
  inequalities : ∀ i, ConvexOn ℝ d.xBox (d.g i)
  equalities : ∀ i, ConvexOn ℝ d.xBox (fun z => signReal (k.lambda i) * d.h i z)

structure Weights {d : Data n m e l r} {x : RealVector n} {y : RealVector m}
    (k : FixedKKT d x y) where
  obj : ℝ
  eq : RealVector e
  ineq : RealVector l
  obj_gt : |k.sigma| < obj
  eq_gt : ∀ i, |k.lambda i| < eq i
  ineq_gt : ∀ i, |k.mu i| < ineq i

structure Anchor (d : Data n m e l r) where
  x : RealVector n
  y : RealVector m
  kkt : FixedKKT d x y
  convex : SignedConvex d kkt
  weights : Weights kkt

def objTangent (d : Data n m e l r) {x0 : RealVector n} (j : Jet d x0)
    (x : RealVector n) : ℝ := d.f x0 + j.Df (x - x0)

def eqTangent (d : Data n m e l r) {x0 : RealVector n} (j : Jet d x0)
    (lam : RealVector e) (i : Fin e) (x : RealVector n) (y : RealVector m) : ℝ :=
  signReal (lam i) * (dot (d.A i) y + d.h i x0 + j.Dh i (x - x0))

def ineqTangent (d : Data n m e l r) {x0 : RealVector n} (j : Jet d x0)
    (i : Fin l) (x : RealVector n) (y : RealVector m) : ℝ :=
  dot (d.B i) y + d.g i x0 + j.Dg i (x - x0)

def noGoodRow (b : BVector m) (y : RealVector m) : ℝ :=
  (∑ i, if b i then y i else 0) - (∑ i, if b i then 0 else y i) -
    ((∑ i, if b i then (1 : ℝ) else 0) - 1)

/-- Repeated equal-valued anchors have DIFFERENT Fin indices and slack variables. -/
structure MasterPoint (d : Data n m e l r) (H : List (Anchor d)) where
  x : RealVector n
  y : RealVector m
  alpha : ℝ
  s : Fin H.length → ℝ
  p : Fin H.length → RealVector e
  q : Fin H.length → RealVector l

def hardDomain (d : Data n m e l r) (R : Finset (BVector m)) :
    Set (RealVector n × RealVector m) :=
  {z | d.Hard z.1 z.2 ∧ Binary z.2 ∧ ∀ b ∈ R, noGoodRow b z.2 ≤ 0}

def masterFeasible (d : Data n m e l r) (H : List (Anchor d))
    (R : Finset (BVector m)) : Set (MasterPoint d H) := {z |
  (z.x, z.y) ∈ hardDomain d R ∧
  (∀ k, 0 ≤ z.s k) ∧ (∀ k i, 0 ≤ z.p k i) ∧ (∀ k i, 0 ≤ z.q k i) ∧
  (∀ k, objTangent d (H.get k).kkt.jet z.x - z.alpha ≤ z.s k) ∧
  (∀ k i, eqTangent d (H.get k).kkt.jet (H.get k).kkt.lambda i z.x z.y ≤ z.p k i) ∧
  ∀ k i, ineqTangent d (H.get k).kkt.jet i z.x z.y ≤ z.q k i}

def masterObjective (d : Data n m e l r) (H : List (Anchor d))
    (z : MasterPoint d H) : ℝ := dot d.c z.y + z.alpha +
  (∑ k, (H.get k).weights.obj * z.s k) +
  (∑ k, ∑ i, (H.get k).weights.eq i * z.p k i) +
  (∑ k, ∑ i, (H.get k).weights.ineq i * z.q k i)

end Chapter02.DICOPT
