module

public import Chapter02Model
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02DICOPTExamples

abbrev V := RealVector 1
def scalar (a : ℝ) : V := fun _ => a
def coord : V →L[ℝ] ℝ := ContinuousLinearMap.proj 0

@[simp] theorem scalar_apply (a : ℝ) (i : Fin 1) : scalar a i = a := rfl
@[simp] theorem coord_apply (x : V) : coord x = x 0 := rfl
@[simp] theorem scalar_coord (x : V) : scalar (x 0) = x := by
  ext i
  fin_cases i
  rfl

theorem scalar_ext {x y : V} (h : x 0 = y 0) : x = y := by
  rw [← scalar_coord x, ← scalar_coord y, h]

theorem scalar_Icc {a b : ℝ} {x : V} :
    x ∈ Set.Icc (scalar a) (scalar b) ↔ a ≤ x 0 ∧ x 0 ≤ b := by
  constructor
  · intro h
    exact ⟨h.1 0, h.2 0⟩
  · intro h
    constructor <;> intro i <;> fin_cases i
    · exact h.1
    · exact h.2

theorem derivative_coord (x : V) : HasFDerivAt (fun z : V => z 0) coord x :=
  coord.hasFDerivAt

theorem derivative_square (x : V) :
    HasFDerivAt (fun z : V => (z 0)^2) ((2 * x 0) • coord) x := by
  convert (derivative_coord x).mul (derivative_coord x) using 1
  · ext z
    exact pow_two (z 0)
  · ext v
    simp [two_mul, add_mul]

theorem derivative_square_add (x : V) :
    HasFDerivAt (fun z : V => (z 0)^2 + z 0) ((2 * x 0 + 1) • coord) x := by
  convert (derivative_square x).add (derivative_coord x) using 1
  ext v
  simp [add_mul]

theorem derivative_neg_coord (x : V) :
    HasFDerivAt (fun z : V => -(z 0)) (-coord) x :=
  (derivative_coord x).neg

theorem derivative_coord_add (x : V) (c : ℝ) :
    HasFDerivAt (fun z : V => z 0 + c) coord x := by
  simpa using (derivative_coord x).add_const c

theorem convex_square_on {S : Set V} (hS : Convex ℝ S) :
    ConvexOn ℝ S (fun z => (z 0)^2) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0))
  nlinarith [sq_nonneg (x 0), sq_nonneg (y 0)]

theorem convex_affine_on {S : Set V} (hS : Convex ℝ S) (a b : ℝ) :
    ConvexOn ℝ S (fun z => a * z 0 + b) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply le_of_eq
  linear_combination -b * huv

theorem convex_square_add_on {S : Set V} (hS : Convex ℝ S) :
    ConvexOn ℝ S (fun z => (z 0)^2 + z 0) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have hs := (convex_square_on hS).2 hx hy ha hb hab
  have hl := (convex_affine_on hS 1 0).2 hx hy ha hb hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, add_zero] at *
  nlinarith

theorem nonlinear_binary_fiber {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1)
    (hy : y = 0 ∨ y = 1) (heq : x^2 + x - 2*y = 0) :
    (y = 0 ∧ x = 0) ∨ (y = 1 ∧ x = 1) := by
  rcases hy with rfl | rfl
  · left
    exact ⟨rfl, by nlinarith [sq_nonneg x]⟩
  · right
    exact ⟨rfl, by nlinarith [sq_nonneg (x-1)]⟩

theorem nonlinear_relaxed_square (x y : ℝ) (h : x^2+x-2*y=0) :
    -x + (3/4:ℝ)*y + 25/96 = (3/8:ℝ)*(x-5/6)^2 := by
  nlinarith

theorem affine_infeasible_binary {x y : ℝ} (hx : -(1/4:ℝ) ≤ x ∧ x ≤ 1/4)
    (hy : y = 0 ∨ y = 1) : x + 1/2 - y ≠ 0 := by
  rcases hy with rfl | rfl <;> intro h <;> linarith

end Chapter02DICOPTExamples
