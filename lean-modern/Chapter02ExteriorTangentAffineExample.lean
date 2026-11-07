module

public import Chapter02ExteriorTangentSource
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

@[expose] public section

/-! Exact source-model control: the strict reference and boundary cut origin
belong to X but violate L. This is permitted by the published X-only hypothesis.
All data are rational, all nonlinear derivatives are actual derivatives, and
the uniform separation is obtained from the source adapter. No procedure for
finding a reference or segment root is claimed. -/

noncomputable section
open Chapter02
namespace Chapter02ExteriorTangentAffineExample

def point (x y : ℝ) : Point 2 0 := (![x,y], fun i => Fin.elim0 i)
def coordX : Point 2 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.fst ℝ (RealVector 2) (RealVector 0))
def coordY : Point 2 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 1).comp
    (ContinuousLinearMap.fst ℝ (RealVector 2) (RealVector 0))
def model : ModelData 2 0 1 1 where
  g := fun _ p => (p.1 0)^2 + (p.1 1)^2 - 1
  A := ![![0,-1]]
  B := fun _ i => Fin.elim0 i
  rhs := ![-(9/10)]
  c1 := ![0,0]
  c2 := fun i => Fin.elim0 i
  lo := fun i => Fin.elim0 i
  hi := fun i => Fin.elim0 i
def domain : Set (Point 2 0) := Set.Icc (point 0 0) (point (6/5) (8/5))
def trials : Set (Point 2 0) := domain ∩ model.linearRegion
def derivative (_ : Fin 1) (p : Point 2 0) : Point 2 0 →L[ℝ] ℝ :=
  (2*p.1 0) • coordX + (2*p.1 1) • coordY
def cuts : TangentFamily 2 0 1 1 :=
  exteriorTangentFamily (point 0 0) (point (6/5) (8/5)) (1/2) 0 derivative

theorem affine_linear_region (p : Point 2 0) :
    p ∈ model.linearRegion ↔ (9/10 : ℝ) ≤ p.1 1 := by
  simp [ModelData.linearRegion, model, LinearForm, Fin.sum_univ_succ,
    Fin.forall_fin_one]

theorem affine_geometry : IsCompact domain ∧ Convex ℝ domain ∧
    IsCompact trials ∧ trials ⊆ domain := by
  have hclosed : IsClosed model.linearRegion := by
    have heq : model.linearRegion = {p : Point 2 0 | (9/10 : ℝ) ≤ p.1 1} := by
      ext p
      exact affine_linear_region p
    rw [heq]
    exact isClosed_le continuous_const (by fun_prop)
  refine ⟨isCompact_Icc, ?_, isCompact_Icc.inter_right hclosed, Set.inter_subset_left⟩
  have hi : ∀ p : Point 2 0, p ∈ domain ↔
      0 ≤ p.1 0 ∧ p.1 0 ≤ 6/5 ∧ 0 ≤ p.1 1 ∧ p.1 1 ≤ 8/5 := by
    intro p
    simp [domain, point, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_succ]
    tauto
  intro p hp q hq a b ha hb hab
  apply (hi _).mpr
  obtain ⟨hp0,hp1,hp2,hp3⟩ := (hi _).mp hp
  obtain ⟨hq0,hq1,hq2,hq3⟩ := (hi _).mp hq
  simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0), ?_,
    add_nonneg (mul_nonneg ha hp2) (mul_nonneg hb hq2), ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hp1 ha, mul_le_mul_of_nonneg_left hq1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hp3 ha, mul_le_mul_of_nonneg_left hq3 hb]

theorem affine_convex (j : Fin 1) : ConvexOn ℝ domain (model.g j) := by
  refine ⟨affine_geometry.2.1, ?_⟩
  intro p hp q hq a b ha hb hab
  have hb' : b = 1-a := by linarith
  subst b
  have hx := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.1 0-q.1 0))
  have hy := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.1 1-q.1 1))
  simp only [model, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  nlinarith

theorem affine_actual_derivative (j : Fin 1) (p : Point 2 0) :
    HasFDerivAt (model.g j) (derivative j p) p := by
  have hx := (hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p coordX.hasFDerivAt
  have hy := (hasDerivAt_pow 2 (p.1 1)).comp_hasFDerivAt p coordY.hasFDerivAt
  convert (hx.add hy).sub_const (1 : ℝ) using 1 <;>
    norm_num [model, derivative, coordX, coordY, Function.comp_def]

theorem affine_reference_control :
    point 0 0 ∈ domain ∧ point 0 0 ∉ model.linearRegion ∧
    (∀ j, model.g j (point 0 0) < 0) ∧
    AffineMap.lineMap (point 0 0) (point (6/5) (8/5)) (1/2 : ℝ) = point (3/5) (4/5) ∧
    point (3/5) (4/5) ∈ domain ∧ point (3/5) (4/5) ∉ model.linearRegion ∧
    model.g 0 (point (3/5) (4/5)) = 0 ∧ model.g 0 (point (6/5) (8/5)) = 3 ∧
    (point (6/5) (8/5), (1/2 : ℝ)) ∈ exteriorData trials model.g (point 0 0) 1 0 := by
  have hline : AffineMap.lineMap (point 0 0) (point (6/5) (8/5)) (1/2 : ℝ) =
      point (3/5) (4/5) := by
    ext i <;> fin_cases i <;>
      norm_num [AffineMap.lineMap_apply_module, point]
  refine ⟨?_, ?_, ?_, hline, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [domain, point, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_succ]
  · rw [affine_linear_region]; norm_num [point]
  · intro j; norm_num [model, point]
  · norm_num [domain, point, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_succ]
  · rw [affine_linear_region]; norm_num [point]
  · norm_num [model, point]
  · norm_num [model, point]
  · refine ⟨⟨?_, ?_⟩, by norm_num, ⟨0, by norm_num [model, point]⟩, ?_, ?_⟩
    · norm_num [domain, point, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_succ]
    · rw [affine_linear_region]; norm_num [point]
    · intro j; fin_cases j; exact le_rfl
    · rw [hline]; norm_num [model, point]

theorem affine_complete_tangent :
    (∀ p : Point 2 0, exteriorTangent model.g derivative 0 (point (3/5) (4/5)) p =
      (6/5 : ℝ)*p.1 0 + (8/5 : ℝ)*p.1 1 - 2) ∧
    exteriorTangent model.g derivative 0 (point (3/5) (4/5)) (point (6/5) (8/5)) = 2 ∧
    exteriorTangent model.g derivative 0 (point (3/5) (4/5)) (point 0 1) = -(2/5 : ℝ) := by
  have ht : ∀ p : Point 2 0, exteriorTangent model.g derivative 0 (point (3/5) (4/5)) p =
      (6/5 : ℝ)*p.1 0 + (8/5 : ℝ)*p.1 1 - 2 := by
    intro p
    norm_num [exteriorTangent, model, derivative, coordX, coordY, point,
      Matrix.vecHead, Matrix.vecTail]
    ring
  refine ⟨ht, ?_, ?_⟩ <;> rw [ht] <;> norm_num [point]

theorem affine_feasible_witness : point 0 1 ∈ model.feasibleOn domain := by
  apply (source_feasible_iff _ _ _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [domain, point, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_succ]
  · intro j; norm_num [model, point]
  · change point 0 1 ∈ model.linearRegion
    rw [affine_linear_region]; norm_num [point]
  · refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · funext i; exact Fin.elim0 i

theorem affine_source_control :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ j p, p ∈ domain → ‖derivative j p‖ ≤ M) ∧
      ∃ delta > 0,
        model.feasibleOn domain ⊆ model.masterOn cuts domain ∧
        point (6/5) (8/5) ∉ cuts.cutRegion model ∧
        (∀ w ∈ cuts.cutRegion model, delta ≤ dist (point (6/5) (8/5)) w) ∧
        point 0 1 ∈ model.masterOn cuts domain := by
  have hc : ∀ j, ContinuousOn (derivative j) domain := by
    intro j
    unfold derivative
    fun_prop
  obtain ⟨M, hM, hbound, delta, hdelta, hall⟩ := source_exterior_compact_cut
    model domain trials derivative affine_geometry.1 affine_geometry.2.1
    affine_geometry.2.2.1 affine_geometry.2.2.2 affine_convex
    (fun j p _ => (affine_actual_derivative j p).hasFDerivWithinAt) hc
    (point 0 0) affine_reference_control.1 affine_reference_control.2.2.1 1 (by norm_num)
  have hcut := hall 0 (point (6/5) (8/5)) (1/2)
    affine_reference_control.2.2.2.2.2.2.2.2
  exact ⟨M, hM, hbound, delta, hdelta, hcut.1, hcut.2.1, hcut.2.2,
    hcut.1 affine_feasible_witness⟩

end Chapter02ExteriorTangentAffineExample

#print axioms Chapter02ExteriorTangentAffineExample.affine_linear_region
#print axioms Chapter02ExteriorTangentAffineExample.affine_geometry
#print axioms Chapter02ExteriorTangentAffineExample.affine_convex
#print axioms Chapter02ExteriorTangentAffineExample.affine_actual_derivative
#print axioms Chapter02ExteriorTangentAffineExample.affine_reference_control
#print axioms Chapter02ExteriorTangentAffineExample.affine_complete_tangent
#print axioms Chapter02ExteriorTangentAffineExample.affine_feasible_witness
#print axioms Chapter02ExteriorTangentAffineExample.affine_source_control
