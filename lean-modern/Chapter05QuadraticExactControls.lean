module

public import Chapter05QuadraticExactMaster

@[expose] public section

/-! Exact controls: a two-coordinate singular positive-semidefinite quadratic
with a genuine cross term, a nonconstant affine row and an empty-curvature
branch. The singleton master has an exhibited actual minimizer. -/
noncomputable section
open Set
open scoped BigOperators
namespace Chapter05.Quadratic.ExactControls
open Chapter02

def crossForm : QuadraticFormData (RealVector 2) :=
  coordinateQuadratic 0 (fun _ => 0) (fun _ _ => 1)

theorem crossForm_eval (x : RealVector 2) :
    crossForm.eval x = x 0 ^ 2 + 2 * x 0 * x 1 + x 1 ^ 2 := by
  rw [crossForm, coordinateQuadratic_eval]
  simp only [Fin.sum_univ_two, zero_mul, zero_add, add_zero, one_mul]
  ring

theorem crossForm_bilinear (x y : RealVector 2) :
    crossForm.bilinear x y = (x 0 + x 1) * (y 0 + y 1) := by
  change coordinateBilinear (fun (_ _ : Fin 2) => (1 : ℝ)) x y = _
  rw [coordinateBilinear_apply]
  simp only [Fin.sum_univ_two, one_mul]
  ring

theorem crossForm_nonzero_cross :
    crossForm.bilinear ![1,0] ![0,1] = 1 := by
  rw [crossForm_bilinear]
  norm_num

theorem crossForm_singular : crossForm.bilinear ![1,-1] ![1,-1] = 0 := by
  rw [crossForm_bilinear]
  norm_num

theorem crossForm_convex : ConvexOn ℝ univ crossForm.eval := by
  apply crossForm.convex_of_bilinear_nonneg
  intro x
  rw [crossForm_bilinear]
  exact mul_self_nonneg _

theorem crossForm_exact (a x : RealVector 2) :
    cut crossForm.eval a 1 x = x 0 ^ 2 + 2 * x 0 * x 1 + x 1 ^ 2 := by
  rw [crossForm.cut_one_eq, crossForm_eval]

theorem crossForm_safeScale (a : RealVector 2) (B : Set (RealVector 2)) :
    safeScale crossForm.eval a B = 1 :=
  (crossForm.convex_safeScale_bounds crossForm_convex a B).2

def affineForm : QuadraticFormData (RealVector 2) where
  constant := -1
  linear := (ContinuousLinearMap.proj (0 : Fin 2) : RealVector 2 →L[ℝ] ℝ) +
    (ContinuousLinearMap.proj (1 : Fin 2) : RealVector 2 →L[ℝ] ℝ)
  bilinear := 0

theorem affineForm_eval (x : RealVector 2) :
    affineForm.eval x = x 0 + x 1 - 1 := by
  simp [affineForm, QuadraticFormData.eval]
  ring

theorem affine_curvature_zero (a x : RealVector 2) :
    curvature affineForm.eval a x = 0 := by
  rw [affineForm.curvature_eq]
  simp [affineForm]

theorem affine_positive_domain_empty (a : RealVector 2) (B : Set (RealVector 2)) :
    positiveCurvatureDomain affineForm.eval a B = ∅ := by
  ext x
  simp [positiveCurvatureDomain, affine_curvature_zero]

theorem affine_empty_branch_safeScale (a : RealVector 2) (B : Set (RealVector 2)) :
    safeScale affineForm.eval a B = 1 := by
  apply safeScale_of_empty
  rw [affine_positive_domain_empty]
  simp

theorem affine_exact (a x : RealVector 2) :
    cut affineForm.eval a 1 x = x 0 + x 1 - 1 := by
  rw [affineForm.cut_one_eq, affineForm_eval]

def model : MasterData (RealVector 2) Unit Unit where
  f := crossForm.eval
  g := fun _ => affineForm.eval
  anchor := fun _ => ![2,-1]
  objectiveScale := fun _ => 1
  constraintScale := fun _ _ => 1
  base := {x | x 0 ∈ Icc (-2) 2 ∧ x 1 ∈ Icc (-2) 2}

def representations : QuadraticRepresentations model where
  objective := crossForm
  objective_eq := rfl
  constraint := fun _ => affineForm
  constraint_eq := fun _ => rfl

theorem singleton_exact : quadraticMaster model {()} = trueEpigraph model :=
  singleton_master_exact representations () rfl (fun _ => rfl)

theorem original_zero_minimizer :
    IsMinimizer (originalFeasible model) model.f (0 : RealVector 2) := by
  refine ⟨?_,?_⟩
  · constructor
    · norm_num [model]
    · intro j
      change affineForm.eval 0 ≤ 0
      rw [affineForm_eval]
      norm_num
  · intro x hx
    change crossForm.eval 0 ≤ crossForm.eval x
    rw [crossForm_eval, crossForm_eval]
    simp only [Pi.zero_apply, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true,
      zero_pow, zero_mul, zero_add]
    nlinarith [sq_nonneg (x 0 + x 1)]

theorem actual_singleton_minimizer :
    IsMinimizer (quadraticMaster model {()}) Prod.snd ((0 : RealVector 2),0) := by
  have hu : UnitHistory model {()} := by
    intro i hi
    exact ⟨rfl,fun _ => rfl⟩
  have h := original_minimizer_lifts_exact_master representations
    (Finset.singleton_nonempty ()) hu original_zero_minimizer
  simpa [model, crossForm_eval] using h

theorem actual_singleton_recovery :
    (0 : ℝ) = model.f (0 : RealVector 2) ∧
      (0 : RealVector 2) ∈ originalFeasible model ∧
      IsMinimizer (originalFeasible model) model.f (0 : RealVector 2) := by
  exact exact_master_minimizer_recovery representations (Finset.singleton_nonempty ())
    (fun i hi => ⟨rfl,fun _ => rfl⟩) actual_singleton_minimizer

end Chapter05.Quadratic.ExactControls
