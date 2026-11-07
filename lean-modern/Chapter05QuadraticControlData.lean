module

public import Chapter02
public import Chapter05
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! Actual polynomial derivatives and convexity for the bounded CH05 controls.
These fixtures alone do not certify the scaled-cut or master conclusions. -/
noncomputable section
namespace Chapter05.Quadratic.Control

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_linear_comp (L : E →L[ℝ] ℝ) (p p' : ℝ → ℝ)
    (hp : ∀ z, HasDerivAt p (p' z) z) (x : E) :
    fderiv ℝ (fun y => p (L y)) x = p' (L x) • L :=
  ((hp (L x)).comp_hasFDerivAt x L.hasFDerivAt).fderiv

theorem hessian_linear_comp (L : E →L[ℝ] ℝ) (p p' : ℝ → ℝ)
    (hp : ∀ z, HasDerivAt p (p' z) z) (p'' : ℝ)
    (hp' : HasDerivAt p' p'' 0) (h k : E) :
    fderiv ℝ (fderiv ℝ (fun y => p (L y))) 0 h k = p'' * L h * L k := by
  have hfun : fderiv ℝ (fun y => p (L y)) = fun x => p' (L x) • L :=
    funext (fderiv_linear_comp L p p' hp)
  rw [hfun]
  have h0 : HasDerivAt p' p'' (L 0) := by simpa using hp'
  have hd := ((h0.comp_hasFDerivAt 0 L.hasFDerivAt).smul_const L).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp [mul_assoc]

def sumCoordinates : Chapter02.RealVector 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) +
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)

def rankSquare (x : Chapter02.RealVector 2) : ℝ := (x 0 + x 1)^2
def rankBox : Set (Chapter02.RealVector 2) := {x | ∀ i, -1 ≤ x i ∧ x i ≤ 1}
def nullDirection : Chapter02.RealVector 2 := ![1, -1]
def positiveDirection : Chapter02.RealVector 2 := ![1, 0]
def scalarBox : Set ℝ := Set.Icc (-1) 1
def fourth (x : ℝ) : ℝ := x^4

theorem square_deriv (z : ℝ) : HasDerivAt (fun z : ℝ => z^2) (2*z) z := by
  simpa using hasDerivAt_pow 2 z

theorem square_deriv2 : HasDerivAt (fun z : ℝ => 2*z) 2 0 := by
  simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2

theorem quartic_deriv (z : ℝ) : HasDerivAt Chapter05.quartic (2*z+4*z^3) z := by
  unfold Chapter05.quartic
  simpa using (hasDerivAt_pow 2 z).fun_add (hasDerivAt_pow 4 z)

theorem quartic_deriv2 : HasDerivAt (fun z : ℝ => 2*z+4*z^3) 2 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).fun_add
    ((hasDerivAt_pow 3 (0 : ℝ)).const_mul 4)

theorem fourth_deriv (z : ℝ) : HasDerivAt fourth (4*z^3) z := by
  unfold fourth
  simpa using hasDerivAt_pow 4 z

theorem fourth_deriv2 : HasDerivAt (fun z : ℝ => 4*z^3) 0 0 := by
  simpa using (hasDerivAt_pow 3 (0 : ℝ)).const_mul 4

theorem rankSquare_contDiff : ContDiff ℝ 2 rankSquare := by
  unfold rankSquare
  exact ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 2)).add
    (contDiff_apply ℝ (fun _ => ℝ) (1 : Fin 2))).pow 2

theorem rankSquare_convex : ConvexOn ℝ Set.univ rankSquare := by
  unfold rankSquare
  have h : ConvexOn ℝ Set.univ (fun z : ℝ => z^2) :=
    (by norm_num : Even (2 : ℕ)).convexOn_pow
  simpa [sumCoordinates, Function.comp_def] using
    h.comp_linearMap sumCoordinates.toLinearMap

theorem quartic_contDiff : ContDiff ℝ 2 Chapter05.quartic :=
  (contDiff_id.pow 2).add (contDiff_id.pow 4)

theorem quartic_convex : ConvexOn ℝ Set.univ Chapter05.quartic :=
  ((by norm_num : Even (2 : ℕ)).convexOn_pow (𝕜 := ℝ)).add
    ((show Even (4 : ℕ) from ⟨2, rfl⟩).convexOn_pow (𝕜 := ℝ))

theorem fourth_contDiff : ContDiff ℝ 2 fourth := contDiff_id.pow 4

theorem fourth_convex : ConvexOn ℝ Set.univ fourth :=
  (show Even (4 : ℕ) from ⟨2, rfl⟩).convexOn_pow

theorem rankSquare_fderiv_zero : fderiv ℝ rankSquare 0 = 0 := by
  unfold rankSquare
  simpa [sumCoordinates] using
    fderiv_linear_comp sumCoordinates (fun z => z^2) (fun z => 2*z) square_deriv 0

theorem rankSquare_hessian (h k : Chapter02.RealVector 2) :
    fderiv ℝ (fderiv ℝ rankSquare) 0 h k = 2*(h 0+h 1)*(k 0+k 1) := by
  unfold rankSquare
  simpa [sumCoordinates] using hessian_linear_comp sumCoordinates
    (fun z => z^2) (fun z => 2*z) square_deriv 2 square_deriv2 h k

theorem quartic_fderiv_zero : fderiv ℝ Chapter05.quartic 0 = 0 := by
  simpa using fderiv_linear_comp (ContinuousLinearMap.id ℝ ℝ) Chapter05.quartic
    (fun z => 2*z+4*z^3) quartic_deriv 0

theorem quartic_hessian (h k : ℝ) :
    fderiv ℝ (fderiv ℝ Chapter05.quartic) 0 h k = 2*h*k := by
  simpa using hessian_linear_comp (ContinuousLinearMap.id ℝ ℝ) Chapter05.quartic
    (fun z => 2*z+4*z^3) quartic_deriv 2 quartic_deriv2 h k

theorem fourth_fderiv_zero : fderiv ℝ fourth 0 = 0 := by
  simpa using fderiv_linear_comp (ContinuousLinearMap.id ℝ ℝ) fourth
    (fun z => 4*z^3) fourth_deriv 0

theorem fourth_hessian (h k : ℝ) : fderiv ℝ (fderiv ℝ fourth) 0 h k = 0 := by
  simpa using hessian_linear_comp (ContinuousLinearMap.id ℝ ℝ) fourth
    (fun z => 4*z^3) fourth_deriv 0 fourth_deriv2 h k

/-- The explicit ratio range is identified with the actual analytic ratio set
in the final control module, after the analytic and scale imports are released. -/
def quarticRatios : Set ℝ :=
  (fun x : ℝ => (1+x^2)/2) '' {x ∈ scalarBox | x ≠ 0}

theorem quarticRatios_nonempty : quarticRatios.Nonempty := by
  refine ⟨1, 1, ?_, ?_⟩ <;> norm_num [scalarBox]

theorem quarticRatios_gt_half {r : ℝ} (hr : r ∈ quarticRatios) : 1/2 < r := by
  rcases hr with ⟨x, hx, rfl⟩
  nlinarith [sq_pos_of_ne_zero hx.2]

theorem quarticRatios_inf : sInf quarticRatios = 1/2 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt quarticRatios_nonempty
  · exact fun r hr => le_of_lt (quarticRatios_gt_half hr)
  · intro w hw
    let x : ℝ := min (1/2) (w-1/2)
    have hx0 : 0 < x := lt_min (by norm_num) (by linarith)
    have hx1 : x ≤ 1/2 := min_le_left _ _
    have hxw : x ≤ w-1/2 := min_le_right _ _
    refine ⟨(1+x^2)/2, ⟨x, ⟨?_, ne_of_gt hx0⟩, rfl⟩, ?_⟩
    · change -1 ≤ x ∧ x ≤ 1
      constructor <;> linarith
    · have hxx : x^2 ≤ x/2 := by nlinarith
      nlinarith

theorem quarticRatios_inf_not_mem : sInf quarticRatios ∉ quarticRatios := by
  rw [quarticRatios_inf]
  intro h
  exact (lt_irrefl (1/2 : ℝ)) (quarticRatios_gt_half h)

end Chapter05.Quadratic.Control
