module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite nonlinear MkCS exact penalties.
Definitions below preserve the accepted finite model; Statement packages the
proved components. Only Challenge.lean contains the deliberate proof placeholder.
The color product sums over ordered distinct pairs: its coefficient is c2,
so an unordered-pair formulation has coefficient 2*c2.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Chapter09
variable {α : Type*} [DecidableEq α]

def conflicts (E : Finset (α × α)) (S : Finset α) : Finset (α × α) :=
  E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)

def feasible (E : Finset (α × α)) (S : Finset α) : Prop :=
  ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)

def score (E : Finset (α × α)) (w : α × α → ℝ) (S : Finset α) : ℝ :=
  (S.card : ℝ) - ∑ e ∈ conflicts E S, w e

def cover (E : Finset (α × α)) (S : Finset α) : Finset α :=
  (conflicts E S).image Prod.fst

def repair (E : Finset (α × α)) (S : Finset α) : Finset α :=
  S \ cover E S

end Chapter09

namespace Chapter09.Source

abbrev Slot (n k : ℕ) := Fin n × Fin k

structure Graph (n : ℕ) where
  edges : Finset (Fin n × Fin n)
  ordered : ∀ e ∈ edges, e.1 < e.2

def flag {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) (r : Fin k) : ℝ :=
  if (i, r) ∈ S then 1 else 0

def row {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun r => (i, r) ∈ S)

def rowCount {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) : ℕ := (row S i).card

def vertices {n k : ℕ} (S : Finset (Slot n k)) : Finset (Fin n) := S.image Prod.fst

def spatialPairs {n : ℕ} (G : Graph n) (k : ℕ) : Finset (Slot n k × Slot n k) :=
  Finset.univ.filter (fun e => (e.1.1, e.2.1) ∈ G.edges ∧ e.1.2 = e.2.2)

def colorPairs (n k : ℕ) : Finset (Slot n k × Slot n k) :=
  Finset.univ.filter (fun e => e.1.1 = e.2.1 ∧ e.1.2 < e.2.2)

def conflictPairs {n : ℕ} (G : Graph n) (k : ℕ) := spatialPairs G k ∪ colorPairs n k

def Feasible {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) : Prop :=
  Chapter09.feasible (conflictPairs G k) S

@[simp] theorem feasible_empty {n : ℕ} (G : Graph n) (k : ℕ) :
    Feasible G (∅ : Finset (Slot n k)) := by
  intro e _ h
  exact Finset.notMem_empty e.1 h.1

def maxPoint {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ι :=
  Classical.choose (s.exists_max_image f hs)

def maxOn {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ℝ :=
  f (maxPoint s hs f)

def finiteMax {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  maxOn Finset.univ Finset.univ_nonempty f

def feasibleSelections {n : ℕ} (G : Graph n) (k : ℕ) : Finset (Finset (Slot n k)) := by
  classical
  exact Finset.univ.filter (Feasible G)

@[simp] theorem mem_feasibleSelections {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    S ∈ feasibleSelections G k ↔ Feasible G S := by classical simp [feasibleSelections]

theorem feasibleSelections_nonempty {n : ℕ} (G : Graph n) (k : ℕ) :
    (feasibleSelections G k).Nonempty := ⟨∅, by simp⟩

def alpha {n : ℕ} (G : Graph n) (k : ℕ) : ℝ :=
  maxOn (feasibleSelections G k) (feasibleSelections_nonempty G k) (fun S => ((vertices S).card : ℝ))

def Binary {n k : ℕ} (x : Fin n → Fin k → ℝ) : Prop := ∀ i r, x i r = 0 ∨ x i r = 1

def reward {n k : ℕ} (S : Finset (Slot n k)) : ℝ := ∑ i, ∑ r, flag S i r ^ 2

def edgeProducts {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) : ℝ :=
  ∑ e ∈ G.edges, ∑ r, flag S e.1 r * flag S e.2 r

def orderedProducts {n k : ℕ} (S : Finset (Slot n k)) : ℝ :=
  ∑ i, ∑ r, ∑ p, if p ≠ r then flag S i r * flag S i p else 0

def colorProducts {n k : ℕ} (S : Finset (Slot n k)) : ℝ :=
  ∑ i, ∑ r, ∑ p, if r < p then flag S i r * flag S i p else 0

def nScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) : ℝ :=
  reward S - c1 * edgeProducts G S - c2 * orderedProducts S

def arrayNScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (x : Fin n → Fin k → ℝ) : ℝ :=
  (∑ i, ∑ r, x i r ^ 2) - c1 * (∑ e ∈ G.edges, ∑ r, x e.1 r * x e.2 r) -
    c2 * (∑ i, ∑ r, ∑ p, if p ≠ r then x i r * x i p else 0)

def qNonlinear {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) : ℝ :=
  finiteMax (nScore (k := k) G c1 c2)

def isNMax {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) : Prop :=
  ∀ T : Finset (Slot n k), nScore G c1 c2 T ≤ nScore G c1 c2 S

end Chapter09.Source

namespace Chapter09.Source.Controls

def emptyGraph (n : ℕ) : Graph n := ⟨∅,by simp⟩

def twoVertexEdge : Graph 2 :=
  ⟨{(0,1)},by
    intro e he
    have h : e = (0,1) := by simpa using he
    subst e
    decide⟩

end Chapter09.Source.Controls

namespace PalomarMkCS
open Chapter09.Source


/-- Exact maximum over all binary arrays, with no positivity requirement. -/
def BinaryMaximum : Prop :=
  ∀ {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ),
    (∃ x : Fin n → Fin k → ℝ,
      Binary x ∧ arrayNScore G c1 c2 x = qNonlinear G k c1 c2) ∧
    ∀ x : Fin n → Fin k → ℝ,
      Binary x → arrayNScore G c1 c2 x ≤ qNonlinear G k c1 c2

/-- The normalization is part of the statement, not an implicit convention. -/
def OrderedNormalization : Prop :=
  ∀ {n k : ℕ} (S : Finset (Slot n k)), orderedProducts S = 2 * colorProducts S

/-- Weak penalties preserve the value, not feasibility of every optimizer. -/
def WeakValue : Prop :=
  ∀ {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ),
    1 ≤ c1 → 1 ≤ 2*c2 → qNonlinear G k c1 c2 = alpha G k

/-- Auxiliary simultaneous deletion; this does not assert Algorithm12 semantics. -/
def WeakRepair : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (c1 c2 : ℝ),
    1 ≤ c1 → 1 ≤ 2*c2 → ∀ S : Finset (Slot n k), isNMax G c1 c2 S →
      Feasible G (Chapter09.repair (conflictPairs G k) S) ∧
      ((Chapter09.repair (conflictPairs G k) S).card : ℝ) = alpha G k

/-- Strict effective penalties make every global optimizer feasible. -/
def StrictOptimizer : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (c1 c2 : ℝ),
    1 < c1 → 1 < 2*c2 → ∀ S : Finset (Slot n k), isNMax G c1 c2 S →
      Feasible G S ∧ (S.card : ℝ) = alpha G k

/-- With one color the ordered color term vanishes; c2 is any real. -/
def OneColorValue : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ),
    1 ≤ c1 → qNonlinear G 1 c1 c2 = alpha G 1

def OneColorStrict : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ), 1 < c1 →
    ∀ S : Finset (Slot n 1), isNMax G c1 c2 S →
      Feasible G S ∧ (S.card : ℝ) = alpha G 1

def OneColorRepair : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ), 1 ≤ c1 →
    ∀ S : Finset (Slot n 1), isNMax G c1 c2 S →
      Feasible G (Chapter09.repair (conflictPairs G 1) S) ∧
      ((Chapter09.repair (conflictPairs G 1) S).card : ℝ) = alpha G 1

/-- An infeasible global maximum at the unit edge boundary. -/
def UnitEdgeTie : Prop :=
  ∀ c2 : ℝ,
    isNMax Controls.twoVertexEdge 1 c2 (Finset.univ : Finset (Slot 2 1)) ∧
    ¬ Feasible Controls.twoVertexEdge (Finset.univ : Finset (Slot 2 1))

/-- An infeasible global maximum at the ordered color boundary. -/
def HalfColorTie : Prop :=
  isNMax (Controls.emptyGraph 1) 1 (1/2) (Finset.univ : Finset (Slot 1 2)) ∧
  ¬ Feasible (Controls.emptyGraph 1) (Finset.univ : Finset (Slot 1 2))

/-- One coherent entry, rather than ten claimed research contributions. -/
def Statement : Prop :=
  BinaryMaximum ∧ OrderedNormalization ∧ WeakValue ∧ WeakRepair ∧
  StrictOptimizer ∧ OneColorValue ∧ OneColorStrict ∧ OneColorRepair ∧
  UnitEdgeTie ∧ HalfColorTie

theorem solution : Statement := by sorry

end PalomarMkCS
