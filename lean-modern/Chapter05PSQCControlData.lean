module

public import Chapter02PSCExamples
public import Chapter05QuadraticScale
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! Actual polynomial regularity and Hessians for the existing E/V controls.
These supporting facts do not by themselves certify quadratic PSC validity. -/
noncomputable section
open Chapter02 Chapter02PSCExamples
open Chapter05.Quadratic
namespace Chapter05.PSQC.Control

theorem quadratic_contDiff (A B C : ℝ) : ContDiff ℝ 2 (quadratic A B C) := by
  unfold quadratic
  fun_prop

theorem quadratic_fderiv (A B C : ℝ) (x : RealVector 1) :
    fderiv ℝ (quadratic A B C) x = (2*A*x 0+B) • scalarCoord :=
  (quadratic_derivative A B C x).fderiv

theorem quadratic_hessian (A B C : ℝ) (x h k : RealVector 1) :
    fderiv ℝ (fderiv ℝ (quadratic A B C)) x h k = 2*A*h 0*k 0 := by
  have hf : fderiv ℝ (quadratic A B C) =
      fun x => (2*A*x 0+B) • scalarCoord := funext (quadratic_fderiv A B C)
  rw [hf]
  have hd : HasFDerivAt (fun y : RealVector 1 => 2*A*y 0+B)
      ((2*A) • scalarCoord) x := by
    simpa [scalarCoord] using
      (scalarCoord.hasFDerivAt.const_mul (2*A)).add_const B
  rw [(hd.smul_const scalarCoord).fderiv]
  simp [scalarCoord, mul_assoc]

theorem quadratic_curvature (A B C : ℝ) (a x : RealVector 1) :
    curvature (quadratic A B C) a x = 2*A*(x 0-a 0)^2 := by
  rw [curvature, quadratic_hessian]
  simp only [Pi.sub_apply]
  ring

theorem quadratic_remainder (A B C : ℝ) (a x : RealVector 1) :
    quadratic A B C x - tangent (quadratic A B C) a x = A*(x 0-a 0)^2 := by
  simpa [tangent, quadratic_fderiv] using quadratic_support_identity A B C a x

theorem quadratic_ratio (A B C : ℝ) (a x : RealVector 1)
    (hx : 0 < curvature (quadratic A B C) a x) :
    (quadratic A B C x - tangent (quadratic A B C) a x) /
      curvature (quadratic A B C) a x = 1/2 := by
  apply (div_eq_iff (ne_of_gt hx)).2
  rw [quadratic_remainder, quadratic_curvature]
  ring

theorem quadratic_ratioSet (A B C : ℝ) (a : RealVector 1) (S : Set (RealVector 1))
    (hne : (positiveCurvatureDomain (quadratic A B C) a S).Nonempty) :
    ratioSet (quadratic A B C) a S = {1/2} := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Set.mem_singleton_iff.mpr (quadratic_ratio A B C a x hx.2)
  · intro hr
    rcases hne with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    rw [Set.mem_singleton_iff] at hr
    exact (quadratic_ratio A B C a x hx.2).trans hr.symm

theorem quadratic_safeScale (A B C : ℝ) (a : RealVector 1) (S : Set (RealVector 1))
    (hne : (positiveCurvatureDomain (quadratic A B C) a S).Nonempty) :
    safeScale (quadratic A B C) a S = 1 := by
  rw [safeScale_of_nonempty hne, quadratic_ratioSet A B C a S hne]
  norm_num

theorem e_global_convex : ConvexOn ℝ Set.univ (eModel false).r ∧
    ∀ j, ConvexOn ℝ Set.univ ((eModel false).t j) :=
  ⟨quadratic_convex 1 (-2) 1 (by norm_num), fun _ => quadratic_convex 1 1 0 (by norm_num)⟩

theorem e_global_C2 : ContDiff ℝ 2 (eModel false).r ∧
    ∀ j, ContDiff ℝ 2 ((eModel false).t j) :=
  ⟨quadratic_contDiff 1 (-2) 1, fun _ => quadratic_contDiff 1 1 0⟩

theorem v_global_convex : ConvexOn ℝ Set.univ vModel.r ∧
    ∀ j, ConvexOn ℝ Set.univ (vModel.t j) :=
  ⟨quadratic_convex 1 2 1 (by norm_num), fun _ => quadratic_convex 1 0 0 (by norm_num)⟩

theorem v_global_C2 : ContDiff ℝ 2 vModel.r ∧
    ∀ j, ContDiff ℝ 2 (vModel.t j) :=
  ⟨quadratic_contDiff 1 2 1, fun _ => quadratic_contDiff 1 0 0⟩

end Chapter05.PSQC.Control
