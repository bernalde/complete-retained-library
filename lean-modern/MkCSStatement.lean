module

public import Chapter09NonlinearControls

/-! Reused S223 ten-component contract over the shared canonical migrated model. -/
@[expose] public section
noncomputable section
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

end PalomarMkCS
