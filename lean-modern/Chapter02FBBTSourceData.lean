module

public import Chapter02FBBTBounds
public import Chapter02BBAdapter

@[expose] public section

/-! Finite initial row intervals for the actual retained original-coordinate
source. These helpers neither assume a feasible original point nor identify a
nonempty interval state with graph feasibility. Candidate infrastructure only. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter02FBBT

variable {n l r : ℕ}

def sourceLower (D : BBPolyData n l r) (X : Bounds (Fin n)) (i : Fin r) : ℝ :=
  min (∑ j, affineProductLo (D.coefficient i j) (X.1 j) (X.2 j)) (D.rhs i)

def sourceInitial (D : BBPolyData n l r) (X : Bounds (Fin n)) :
    Bounds (Fin n ⊕ Fin r) :=
  (Sum.elim X.1 (sourceLower D X), Sum.elim X.2 D.rhs)

def sourceGraph (D : BBPolyData n l r) (x : RealVector n) :
    (Fin n ⊕ Fin r) → ℝ :=
  Sum.elim x (fun i => ∑ j, D.coefficient i j * x j)

lemma source_initial_ordered (D : BBPolyData n l r) (X : Bounds (Fin n))
    (hX : Ordered X) : Ordered (sourceInitial D X) := by
  intro i
  cases i with
  | inl j => exact hX j
  | inr i => exact min_le_right _ _

lemma source_graph_mem_iff (D : BBPolyData n l r) (X : Bounds (Fin n))
    (x : RealVector n) :
    sourceGraph D x ∈ members (sourceInitial D X) ↔
      x ∈ members X ∧ x ∈ D.polyhedron := by
  constructor
  · intro h
    exact ⟨fun j => h (Sum.inl j), fun i => (h (Sum.inr i)).2⟩
  · rintro ⟨hx, hD⟩ i
    cases i with
    | inl j => exact hx j
    | inr i =>
      change min (∑ j, affineProductLo (D.coefficient i j) (X.1 j) (X.2 j))
          (D.rhs i) ≤ (∑ j, D.coefficient i j * x j) ∧
        (∑ j, D.coefficient i j * x j) ≤ D.rhs i
      refine ⟨(min_le_left _ _).trans ?_, hD i⟩
      exact Finset.sum_le_sum fun j _ => (affine_product_bounds (hx j)).1

/-- Every retained nonlinear and designated-integrality restriction remains in D.
The finite B lower restrictions add nothing to those affine rows on X. -/
lemma source_feasible_graph_iff (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X : Bounds (Fin n)) (x : RealVector n) :
    x ∈ D.feasible I ∩ members X ↔
      x ∈ D.feasible I ∧ sourceGraph D x ∈ members (sourceInitial D X) := by
  constructor
  · intro h
    exact ⟨h.1, (source_graph_mem_iff D X x).2 ⟨h.2, h.1.1⟩⟩
  · intro h
    exact ⟨h.1, ((source_graph_mem_iff D X x).1 h.2).1⟩

end Chapter02FBBT
