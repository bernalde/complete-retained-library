module

public import Chapter10QUBOAlgebra

@[expose] public section

/-! Ordered coefficient accumulation: repeated monomials add their
coefficients, including overlap between source penalty families. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Algebra

def productMatrix {ι τ : Type*} [DecidableEq ι] [Fintype τ]
    (c : τ → ℝ) (left right : τ → ι) : ι → ι → ℝ :=
  fun i j => ∑ t, if i = left t then if j = right t then c t else 0 else 0

theorem productMatrix_quadratic {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (c : τ → ℝ) (left right : τ → ι) (x : ι → ℝ) :
    quadratic (productMatrix c left right) x = ∑ t, c t * x (left t) * x (right t) := by
  unfold productMatrix
  rw [quadratic_rows]
  apply Finset.sum_congr rfl
  intro t _
  simp [quadratic, ite_mul]

end Chapter10.Algebra

#print axioms Chapter10.Algebra.productMatrix_quadratic
