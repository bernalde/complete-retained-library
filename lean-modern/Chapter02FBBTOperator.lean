module

public import Chapter02FBBTBounds
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-! Concrete simultaneous finite affine propagation. All extrema are seeded by
incoming endpoints. Raw endpoints remain defined even after an empty intersection;
public states distinguish canonical empty from every ordered finite tuple. -/
noncomputable section
open Classical
open scoped BigOperators
namespace Chapter02FBBT

abbrev Coordinates (n m : ℕ) := Fin n ⊕ Fin m
abbrev Matrix (n m : ℕ) := Fin m → Fin n → ℝ
abbrev JointBounds (n m : ℕ) := Bounds (Coordinates n m)

def productLo {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  Chapter02.affineProductLo (A i j) (q.1 (.inl j)) (q.2 (.inl j))
def productHi {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  Chapter02.affineProductHi (A i j) (q.1 (.inl j)) (q.2 (.inl j))
def imageLo {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) :=
  ∑ j, productLo A q i j
def imageHi {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) :=
  ∑ j, productHi A q i j
def restLo {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  ∑ k ∈ Finset.univ.erase j, productLo A q i k
def restHi {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  ∑ k ∈ Finset.univ.erase j, productHi A q i k

def inverseLo {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  if A i j = 0 then q.1 (.inl j) else
  if 0 < A i j then (q.1 (.inr i) - restHi A q i j) / A i j
  else (q.2 (.inr i) - restLo A q i j) / A i j
def inverseHi {n m} (A : Matrix n m) (q : JointBounds n m) (i : Fin m) (j : Fin n) :=
  if A i j = 0 then q.2 (.inl j) else
  if 0 < A i j then (q.2 (.inr i) - restLo A q i j) / A i j
  else (q.1 (.inr i) - restHi A q i j) / A i j

def seededMax {m} (seed : ℝ) (v : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨none, Finset.mem_univ _⟩ (fun o : Option (Fin m) => o.elim seed v)
def seededMin {m} (seed : ℝ) (v : Fin m → ℝ) : ℝ :=
  Finset.univ.inf' ⟨none, Finset.mem_univ _⟩ (fun o : Option (Fin m) => o.elim seed v)

def upward {n m} (A : Matrix n m) (q : JointBounds n m) : JointBounds n m :=
  (Sum.elim (fun j => q.1 (.inl j)) (fun i => max (q.1 (.inr i)) (imageLo A q i)),
   Sum.elim (fun j => q.2 (.inl j)) (fun i => min (q.2 (.inr i)) (imageHi A q i)))
def downward {n m} (A : Matrix n m) (q : JointBounds n m) : JointBounds n m :=
  (Sum.elim (fun j => seededMax (q.1 (.inl j)) (fun i => inverseLo A q i j))
      (fun i => q.1 (.inr i)),
   Sum.elim (fun j => seededMin (q.2 (.inl j)) (fun i => inverseHi A q i j))
      (fun i => q.2 (.inr i)))
def rawF {n m} (A : Matrix n m) (q0 q : JointBounds n m) : JointBounds n m :=
  downward A (upward A (clip q q0))
def rawRun {n m} (A : Matrix n m) (q0 : JointBounds n m) (k : ℕ) :=
  (rawF A q0)^[k] q0

def graph {n m} (A : Matrix n m) (x : Fin n → ℝ) : Coordinates n m → ℝ :=
  Sum.elim x (fun i => ∑ j, A i j * x j)

inductive PublicState (ι : Type*) where
  | empty
  | box (q : Bounds ι) (ordered : Ordered q)

def publicOfBounds {ι} (q : Bounds ι) : PublicState ι :=
  if h : Ordered q then .box q h else .empty
def PublicState.members {ι} : PublicState ι → Set (ι → ℝ)
  | .empty => ∅
  | .box q _ => Chapter02FBBT.members q
def publicF {n m} (A : Matrix n m) (q0 : JointBounds n m) :
    PublicState (Coordinates n m) → PublicState (Coordinates n m)
  | .empty => .empty
  | .box q _ => publicOfBounds (rawF A q0 q)
def publicRun {n m} (A : Matrix n m) (q0 : JointBounds n m) (k : ℕ) :=
  (publicF A q0)^[k] (publicOfBounds q0)

/-- Independent endpoint/product assignment for the scalar affine program. -/
structure LPAssignment (n m : ℕ) where
  bounds : JointBounds n m
  zLo : Fin m → Fin n → ℝ
  zHi : Fin m → Fin n → ℝ

/-- Every entry, including zero coefficients, has a fixed product equality.
The constraints below are scalar affine inequalities for fixed real A. -/
def LPFeasible {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (p : LPAssignment n m) : Prop :=
  Ordered p.bounds ∧ Within p.bounds q0 ∧
  (∀ i j, p.zLo i j = productLo A p.bounds i j) ∧
  (∀ i j, p.zHi i j = productHi A p.bounds i j) ∧
  (∀ i, (∑ j, p.zLo i j) ≤ p.bounds.1 (.inr i) ∧
    p.bounds.2 (.inr i) ≤ ∑ j, p.zHi i j) ∧
  (∀ i j, 0 < A i j →
    (p.bounds.1 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zHi i k) / A i j ≤
      p.bounds.1 (.inl j) ∧
    p.bounds.2 (.inl j) ≤
      (p.bounds.2 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zLo i k) / A i j) ∧
  (∀ i j, A i j < 0 →
    (p.bounds.2 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zLo i k) / A i j ≤
      p.bounds.1 (.inl j) ∧
    p.bounds.2 (.inl j) ≤
      (p.bounds.1 (.inr i) - ∑ k ∈ Finset.univ.erase j, p.zHi i k) / A i j)

def canonicalAssignment {n m} (A : Matrix n m) (q : JointBounds n m) : LPAssignment n m :=
  ⟨q, productLo A q, productHi A q⟩
def LPObjective {n m} (p : LPAssignment n m) : ℝ := width p.bounds

end Chapter02FBBT
