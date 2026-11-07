module

public import Chapter05PSQCControlData
public import Chapter05PSQCRows
public import Chapter05PSQCGeometry
public import Chapter05PSQCSource

@[expose] public section

/-! The two accepted E/V models applied to actual quadratic PSC rows.
The explicit KKT-entry formulas remain separate from source-selected multipliers.
Only original feasible points are asserted to satisfy the objective bounds. -/
noncomputable section
open Chapter02 Chapter02PSCExamples
open Chapter05.Quadratic
open scoped BigOperators
namespace Chapter05.PSQC.Control

theorem e_lagrangian : lagrangian (eModel false) (eAnchor false) = quadratic 3 0 1 := by
  funext v
  simp [lagrangian, eModel, eAnchor, anchor0, skeleton, PSCData.objective,
    PSCData.nonlinear, quadratic, lin, scalarCoord, scalar]
  ring

theorem v_lagrangian : lagrangian vModel vAnchor = quadratic 2 2 1 := by
  funext v
  simp [lagrangian, vModel, vAnchor, anchor0, skeleton, PSCData.objective,
    PSCData.nonlinear, quadratic, lin, scalarCoord, scalar]
  ring

theorem e_hessian (h k : RealVector 1) :
    fderiv ℝ (fderiv ℝ (lagrangian (eModel false) (eAnchor false)))
      (eAnchor false).v h k = 6*h 0*k 0 := by
  rw [e_lagrangian, quadratic_hessian]
  ring

theorem v_hessian (h k : RealVector 1) :
    fderiv ℝ (fderiv ℝ (lagrangian vModel vAnchor)) vAnchor.v h k = 4*h 0*k 0 := by
  rw [v_lagrangian, quadratic_hessian]
  ring

theorem e_curvature (v : RealVector 1) :
    curvature (lagrangian (eModel false) (eAnchor false)) (eAnchor false).v v = 6*(v 0)^2 := by
  rw [e_lagrangian, quadratic_curvature]
  norm_num [eAnchor, anchor0, scalar]

theorem v_curvature (v : RealVector 1) :
    curvature (lagrangian vModel vAnchor) vAnchor.v v = 4*(v 0)^2 := by
  rw [v_lagrangian, quadratic_curvature]
  norm_num [vAnchor, anchor0, scalar]

theorem e_remainder (v : RealVector 1) :
    remainder (eModel false) (eAnchor false) v = 3*(v 0)^2 := by
  unfold remainder
  rw [e_lagrangian]
  simpa [tangent, sub_add_eq_sub_sub, eAnchor, anchor0, scalar]
    using quadratic_remainder 3 0 1 (eAnchor false).v v

theorem v_remainder (v : RealVector 1) : remainder vModel vAnchor v = 2*(v 0)^2 := by
  unfold remainder
  rw [v_lagrangian]
  simpa [tangent, sub_add_eq_sub_sub, vAnchor, anchor0, scalar]
    using quadratic_remainder 2 2 1 vAnchor.v v

theorem e_positive_domain :
    (positiveCurvatureDomain (lagrangian (eModel false) (eAnchor false))
      (eAnchor false).v (eModel false).V).Nonempty := by
  refine ⟨scalar 1, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [eModel, skeleton, intervalRow, intervalBound, lin, scalarCoord, scalar]
  · norm_num [e_curvature, scalar]

theorem v_positive_domain :
    (positiveCurvatureDomain (lagrangian vModel vAnchor) vAnchor.v vModel.V).Nonempty := by
  refine ⟨scalar 1, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [vModel, skeleton, intervalRow, intervalBound, lin, scalarCoord, scalar]
  · norm_num [v_curvature, scalar]

theorem e_ratioSet : ratioSet (lagrangian (eModel false) (eAnchor false))
    (eAnchor false).v (eModel false).V = {1/2} := by
  rw [e_lagrangian]
  exact quadratic_ratioSet 3 0 1 _ _ (by simpa [e_lagrangian] using e_positive_domain)

theorem v_ratioSet : ratioSet (lagrangian vModel vAnchor) vAnchor.v vModel.V = {1/2} := by
  rw [v_lagrangian]
  exact quadratic_ratioSet 2 2 1 _ _ (by simpa [v_lagrangian] using v_positive_domain)

theorem e_safeScale : safeScale (lagrangian (eModel false) (eAnchor false))
    (eAnchor false).v (eModel false).V = 1 := by
  rw [safeScale_of_nonempty e_positive_domain, e_ratioSet]
  norm_num

theorem v_safeScale : safeScale (lagrangian vModel vAnchor) vAnchor.v vModel.V = 1 := by
  rw [safeScale_of_nonempty v_positive_domain, v_ratioSet]
  norm_num

theorem e_row (w : RealVector 0) (v y : RealVector 1) :
    psqcRow (eModel false) (eAnchor false) 1 w v y = 1-2*y 0+3*(v 0)^2 := by
  rw [psqcRow, e_psc_row, e_curvature]
  ring

theorem v_row (w v : RealVector 1) (y : RealVector 0) :
    psqcRow vModel vAnchor 1 w v y = 1-w 0+2*(v 0)^2 := by
  rw [psqcRow, v_psc_row, v_curvature]
  ring

theorem v_fullCut (w v : RealVector 1) (y : RealVector 0) :
    fullCut vModel vAnchor 1 w v y = 1+2*(v 0)^2 := by
  rw [fullCut, v_row]
  simp [vModel, skeleton, lin, scalarCoord]
  ring

theorem e_row_bounds (w : RealVector 0) (v y : RealVector 1)
    (hf : (eModel false).feasible w v y) :
    1-2*y 0 ≤ psqcRow (eModel false) (eAnchor false) 1 w v y ∧
      psqcRow (eModel false) (eAnchor false) 1 w v y ≤ (eModel false).r v := by
  simpa only [e_psc_row] using row_bounds (eModel false) (eAnchor false) (e_kkt false)
    e_global_convex.1 e_global_convex.2 e_global_C2.1 e_global_C2.2
    (α := 1) (by norm_num) (by rw [e_safeScale]) w v y hf

theorem v_row_bounds (w v : RealVector 1) (y : RealVector 0)
    (hf : vModel.feasible w v y) :
    1-w 0 ≤ psqcRow vModel vAnchor 1 w v y ∧
      psqcRow vModel vAnchor 1 w v y ≤ vModel.r v := by
  simpa only [v_psc_row] using row_bounds vModel vAnchor v_kkt
    v_global_convex.1 v_global_convex.2 v_global_C2.1 v_global_C2.2
    (α := 1) (by norm_num) (by rw [v_safeScale]) w v y hf

theorem e_fullCut_bound (w : RealVector 0) (v y : RealVector 1)
    (hf : (eModel false).feasible w v y) :
    fullCut (eModel false) (eAnchor false) 1 w v y ≤ (eModel false).objective w v y :=
  fullCut_le (eModel false) (eAnchor false) (e_kkt false)
    e_global_convex.1 e_global_convex.2 e_global_C2.1 e_global_C2.2
    (α := 1) (by norm_num) (by rw [e_safeScale]) w v y hf

theorem v_fullCut_bound (w v : RealVector 1) (y : RealVector 0)
    (hf : vModel.feasible w v y) : 1+2*(v 0)^2 ≤ vModel.objective w v y := by
  simpa only [v_fullCut] using fullCut_le vModel vAnchor v_kkt
    v_global_convex.1 v_global_convex.2 v_global_C2.1 v_global_C2.2
    (α := 1) (by norm_num) (by rw [v_safeScale]) w v y hf

theorem v_normal (h : RealVector 1) : vAnchor.normalV h = -2*h 0 := by
  have hh : h = h 0 • scalar 1 := by
    ext i
    fin_cases i
    simp [scalar]
  calc
    _ = vAnchor.normalV (h 0 • scalar 1) := congrArg vAnchor.normalV hh
    _ = h 0 * (-2) := by simp only [map_smul, v_nonzero_domain_normal, smul_eq_mul]
    _ = -2*h 0 := mul_comm _ _

theorem v_retained_normal_identity (w v : RealVector 1) (y : RealVector 0) :
    vModel.r v - pscRow vModel vAnchor w v y =
      2*(v 0)^2 - ((v 0)^2-w 0) + 2*v 0 := by
  have hi := retained_normal_identity vModel vAnchor v_kkt w v y
  rw [v_remainder, v_normal] at hi
  have hs : (∑ j, vAnchor.lambda j * vModel.nonlinear j w v y) = (v 0)^2-w 0 := by
    simp [vAnchor, anchor0, vModel, skeleton, PSCData.nonlinear, quadratic, lin, scalarCoord]
    ring
  rw [hs] at hi
  simpa only [show vAnchor.v = 0 from rfl, sub_zero, neg_mul, sub_neg_eq_add] using hi

theorem e_tightness :
    fullCut (eModel false) (eAnchor false) 1 (eAnchor false).w (eAnchor false).v
      (eAnchor false).y = (eModel false).objective (eAnchor false).w
        (eAnchor false).v (eAnchor false).y :=
  fullCut_at_anchor _ _ (e_kkt false) 1

theorem v_tightness : fullCut vModel vAnchor 1 vAnchor.w vAnchor.v vAnchor.y =
    vModel.objective vAnchor.w vAnchor.v vAnchor.y :=
  fullCut_at_anchor _ _ v_kkt 1

theorem e_geometry :
    Continuous (fun z : PSCCoordinates 0 1 1 =>
      psqcRow (eModel false) (eAnchor false) 1 z.1.1 z.1.2 z.2) ∧
    ConvexOn ℝ Set.univ (fun z : PSCCoordinates 0 1 1 =>
      psqcRow (eModel false) (eAnchor false) 1 z.1.1 z.1.2 z.2) ∧
    ConvexOn ℝ Set.univ (fun z : PSCCoordinates 0 1 1 =>
      fullCut (eModel false) (eAnchor false) 1 z.1.1 z.1.2 z.2) := by
  have hc := lagrangian_convex (eModel false) (eAnchor false) (e_kkt false)
    e_global_convex.1 e_global_convex.2
  have hd := lagrangian_contDiff (eModel false) (eAnchor false) e_global_C2.1 e_global_C2.2
  exact ⟨row_continuous _ _ _, row_convex _ _ hc hd (by norm_num),
    fullCut_convex _ _ hc hd (by norm_num)⟩

theorem v_geometry :
    Continuous (fun z : PSCCoordinates 1 1 0 => psqcRow vModel vAnchor 1 z.1.1 z.1.2 z.2) ∧
    ConvexOn ℝ Set.univ (fun z : PSCCoordinates 1 1 0 => psqcRow vModel vAnchor 1 z.1.1 z.1.2 z.2) ∧
    ConvexOn ℝ Set.univ (fun z : PSCCoordinates 1 1 0 => fullCut vModel vAnchor 1 z.1.1 z.1.2 z.2) := by
  have hc := lagrangian_convex vModel vAnchor v_kkt v_global_convex.1 v_global_convex.2
  have hd := lagrangian_contDiff vModel vAnchor v_global_C2.1 v_global_C2.2
  exact ⟨row_continuous _ _ _, row_convex _ _ hc hd (by norm_num),
    fullCut_convex _ _ hc hd (by norm_num)⟩

/-- The source object supplies actual first derivatives, a proved fixed-fiber
minimum and same-fiber Slater. It supplies no multiplier vector. -/
def eSourceAnchor : PSCSourceAnchor (eModel false) where
  w := (eAnchor false).w
  v := (eAnchor false).v
  y := (eAnchor false).y
  Dr := (eAnchor false).Dr
  Dt := (eAnchor false).Dt
  y_mem := (e_kkt false).y_mem
  derivative_r := (e_kkt false).derivative_r
  derivative_t := (e_kkt false).derivative_t
  minimum := (e_full_model false).2.2
  slater := e_slater false

/-- The selected entry and its own actual scale are used together. This does
not identify its multipliers with the explicit E KKT entry above. -/
theorem e_source_safe_row :
    let e := sourceEntry (eModel false) e_global_convex.1 e_global_convex.2 eSourceAnchor
    let α := safeScale (lagrangian (eModel false) e.data) e.data.v (eModel false).V
    pscSourceMatches eSourceAnchor e ∧ (0 ≤ α ∧ α ≤ 1) ∧
      ∀ w v y, (eModel false).feasible w v y →
        pscRow (eModel false) e.data w v y ≤ psqcRow (eModel false) e.data α w v y ∧
        psqcRow (eModel false) e.data α w v y ≤ (eModel false).r v ∧
        fullCut (eModel false) e.data α w v y ≤ (eModel false).objective w v y :=
  source_safe_row (eModel false) e_global_convex.1 e_global_convex.2
    e_global_C2.1 e_global_C2.2 eSourceAnchor

end Chapter05.PSQC.Control
