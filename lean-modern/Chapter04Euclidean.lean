module

public import Chapter02Model
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-! Concrete concatenated Euclidean coordinates for the Chapter4 ball lemma.
The original product/Pi norm on `Chapter02.Point` is unchanged. -/

noncomputable section
open scoped BigOperators
namespace Chapter04.CenterCut

abbrev EuclideanPoint (n m : ℕ) := EuclideanSpace ℝ (Fin n ⊕ Fin m)

/-- Concatenation is a continuous linear equivalence, with the Euclidean norm
only on the target. This is not asserted to be an isometry. -/
def coordinates (n m : ℕ) : Chapter02.Point n m ≃L[ℝ] EuclideanPoint n m :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) ℝ ℝ).symm.toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin n ⊕ Fin m) ℝ).symm

@[simp] theorem coordinates_inl {n m : ℕ} (p : Chapter02.Point n m) (i : Fin n) :
    coordinates n m p (Sum.inl i) = p.1 i := rfl

@[simp] theorem coordinates_inr {n m : ℕ} (p : Chapter02.Point n m) (i : Fin m) :
    coordinates n m p (Sum.inr i) = p.2 i := rfl

@[simp] theorem coordinates_symm_fst {n m : ℕ} (p : EuclideanPoint n m) (i : Fin n) :
    ((coordinates n m).symm p).1 i = p (Sum.inl i) := rfl

@[simp] theorem coordinates_symm_snd {n m : ℕ} (p : EuclideanPoint n m) (i : Fin m) :
    ((coordinates n m).symm p).2 i = p (Sum.inr i) := rfl

theorem inner_coordinates {n m : ℕ} (a q : Chapter02.Point n m) :
    inner ℝ (coordinates n m a) (coordinates n m q) = Chapter02.LinearForm a.1 a.2 q := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, Chapter02.LinearForm, mul_comm]

theorem norm_coordinates_sq {n m : ℕ} (a : Chapter02.Point n m) :
    ‖coordinates n m a‖ ^ 2 = (∑ i, (a.1 i) ^ 2) + ∑ i, (a.2 i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coordinates]
  simp [Chapter02.LinearForm, pow_two]

theorem objective_eq_inner_coordinates {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (q : Chapter02.Point n m) :
    d.objective q = inner ℝ (coordinates n m (d.c1, d.c2)) (coordinates n m q) := by
  rw [inner_coordinates]
  rfl

end Chapter04.CenterCut
