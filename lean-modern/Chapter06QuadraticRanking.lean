module

public import Chapter06
public import Chapter05QuadraticAnalytic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! The Chapter6 Q-OA ranking objective, using actual first and second derivatives.
This separate endpoint adds C² to the C¹ hypotheses used for finite progress.
The supplied nonnegative weights need not be KKT multipliers of the seed.
Convexity is a ranking property; no global underestimation claim is made. -/
noncomputable section
open Set
open scoped BigOperators
namespace Chapter06.QuadraticRanking

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {l : ℕ}

def lagrangian (f : E → ℝ) (g : Fin l → E → ℝ) (lam : Fin l → ℝ)
    (x : E) : ℝ := f x + ∑ j, lam j * g j x

/-- The literal linear-plus-quadratic ranking expression in the joint variables.
There is no constant L(a), and these are derivatives of the actual Lagrangian. -/
def ranking (f : E → ℝ) (g : Fin l → E → ℝ) (lam : Fin l → ℝ)
    (a x : E) : ℝ :=
  fderiv ℝ (lagrangian f g lam) a (x-a) +
    fderiv ℝ (fderiv ℝ (lagrangian f g lam)) a (x-a) (x-a) / 2

theorem lagrangian_convex (f : E → ℝ) (g : Fin l → E → ℝ)
    (lam : Fin l → ℝ) (hf : ConvexOn ℝ univ f)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) (hlam : ∀ j, 0 ≤ lam j) :
    ConvexOn ℝ univ (lagrangian f g lam) :=
  Chapter06.weighted_lagrangian_convex univ f g lam hf hg hlam

theorem lagrangian_contDiff (f : E → ℝ) (g : Fin l → E → ℝ)
    (lam : Fin l → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ∀ j, ContDiff ℝ 2 (g j)) :
    ContDiff ℝ 2 (lagrangian f g lam) := by
  exact hf.add (ContDiff.sum fun j _ => contDiff_const.mul (hg j))

theorem ranking_eq_cut_sub (f : E → ℝ) (g : Fin l → E → ℝ)
    (lam : Fin l → ℝ) (a x : E) :
    ranking f g lam a x =
      Chapter05.Quadratic.cut (lagrangian f g lam) a 1 x - lagrangian f g lam a := by
  rw [Chapter05.Quadratic.cut_one]
  unfold ranking Chapter05.Quadratic.tangent Chapter05.Quadratic.curvature
  ring

/-- Convexity of the literal source ranking follows from actual C² convex data.
It is independent of the feasible-selector return theorem. -/
theorem ranking_convex (f : E → ℝ) (g : Fin l → E → ℝ)
    (lam : Fin l → ℝ) (hf : ConvexOn ℝ univ f)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) (hlam : ∀ j, 0 ≤ lam j)
    (hfC2 : ContDiff ℝ 2 f) (hgC2 : ∀ j, ContDiff ℝ 2 (g j)) (a : E) :
    ConvexOn ℝ univ (ranking f g lam a) := by
  have heq : ranking f g lam a = fun x =>
      Chapter05.Quadratic.cut (lagrangian f g lam) a 1 x - lagrangian f g lam a :=
    funext (ranking_eq_cut_sub f g lam a)
  rw [heq]
  have hc := Chapter05.Quadratic.cut_convex
    (lagrangian_convex f g lam hf hg hlam)
    (lagrangian_contDiff f g lam hfC2 hgC2) a (α := 1) (by norm_num)
  exact (hc.add_const (-lagrangian f g lam a)).congr
    (fun _ _ => by simp only [Pi.add_apply, sub_eq_add_neg])

theorem actual_hessian_nonneg (f : E → ℝ) (g : Fin l → E → ℝ)
    (lam : Fin l → ℝ) (hf : ConvexOn ℝ univ f)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) (hlam : ∀ j, 0 ≤ lam j)
    (hfC2 : ContDiff ℝ 2 f) (hgC2 : ∀ j, ContDiff ℝ 2 (g j)) (a h : E) :
    0 ≤ fderiv ℝ (fderiv ℝ (lagrangian f g lam)) a h h :=
  Chapter05.Quadratic.hessian_nonneg (lagrangian_convex f g lam hf hg hlam)
    (lagrangian_contDiff f g lam hfC2 hgC2) a h

@[simp] theorem ranking_at_anchor (f : E → ℝ) (g : Fin l → E → ℝ)
    (lam : Fin l → ℝ) (a : E) : ranking f g lam a a = 0 := by
  simp [ranking]

end Chapter06.QuadraticRanking

#print axioms Chapter06.QuadraticRanking.lagrangian_convex
#print axioms Chapter06.QuadraticRanking.lagrangian_contDiff
#print axioms Chapter06.QuadraticRanking.ranking_eq_cut_sub
#print axioms Chapter06.QuadraticRanking.ranking_convex
#print axioms Chapter06.QuadraticRanking.actual_hessian_nonneg
#print axioms Chapter06.QuadraticRanking.ranking_at_anchor
