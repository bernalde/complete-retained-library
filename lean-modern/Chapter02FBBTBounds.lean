module

public import Chapter02AffinePropagation

@[expose] public section

/-! Shared finite-endpoint data for the qualified simultaneous FBBT candidate.
No source theorem or acceptance is asserted by these definitions. -/
noncomputable section
open scoped BigOperators
namespace Chapter02FBBT

abbrev Bounds (ι : Type*) := (ι → ℝ) × (ι → ℝ)

def Ordered {ι : Type*} (q : Bounds ι) : Prop := ∀ i, q.1 i ≤ q.2 i

def Within {ι : Type*} (q r : Bounds ι) : Prop :=
  ∀ i, r.1 i ≤ q.1 i ∧ q.2 i ≤ r.2 i

def members {ι : Type*} (q : Bounds ι) : Set (ι → ℝ) :=
  {x | ∀ i, q.1 i ≤ x i ∧ x i ≤ q.2 i}

def width {ι : Type*} [Fintype ι] (q : Bounds ι) : ℝ :=
  ∑ i, (q.2 i - q.1 i)

def clip {ι : Type*} (q r : Bounds ι) : Bounds ι :=
  (fun i => max (q.1 i) (r.1 i), fun i => min (q.2 i) (r.2 i))

end Chapter02FBBT
