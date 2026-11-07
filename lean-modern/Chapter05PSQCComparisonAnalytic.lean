module

public import Chapter05PSQCSource
public import Chapter05QuadraticMaster
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-! Actual second derivatives for the separable PSC subclass. Ordinary
Fréchet Hessians are used, with fixed anchor w/y only in the Lagrangian.
The joint Taylor bridge retains free candidate coordinates. -/
noncomputable section
open Set Chapter02
open scoped BigOperators
namespace Chapter05.PSQC.Comparison
open Quadratic

section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem curvature_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (a x : E) :
    curvature (fun z => f z + g z) a x = curvature f a x + curvature g a x := by
  have hdf := hf.differentiable (by norm_num)
  have hdg := hg.differentiable (by norm_num)
  have hDf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hDg := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (fun z => f z + g z) =
      fun z => fderiv ℝ f z + fderiv ℝ g z := funext fun z => fderiv_fun_add (hdf z) (hdg z)
  simp only [curvature, he, fderiv_fun_add (hDf a) (hDg a), ContinuousLinearMap.add_apply]

theorem cut_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (a x : E) (c : ℝ) :
    cut (fun z => f z + g z) a c x = cut f a c x + cut g a c x := by
  rw [cut, curvature_add hf hg]
  simp only [tangent, fderiv_fun_add (hf.differentiable (by norm_num) a)
    (hg.differentiable (by norm_num) a), ContinuousLinearMap.add_apply, cut]
  ring

theorem curvature_smul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (a x : E) :
    curvature (fun z => c * f z) a x = c * curvature f a x := by
  have he : fderiv ℝ (fun z => c * f z) = fun z => c • fderiv ℝ f z := by
    funext z
    simpa only [smul_eq_mul] using fderiv_fun_const_smul (hf.differentiable (by norm_num) z) c
  rw [curvature, he]
  rw [fderiv_fun_const_smul ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) a)]
  simp [curvature]

theorem cut_smul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (a x : E) (b : ℝ) :
    cut (fun z => c * f z) a b x = c * cut f a b x := by
  rw [cut, curvature_smul hf]
  simp only [tangent, fderiv_const_mul (hf.differentiable (by norm_num) a),
    ContinuousLinearMap.smul_apply, smul_eq_mul, cut]
  ring

theorem curvature_affine (L : E →L[ℝ] ℝ) (c : ℝ) (a x : E) :
    curvature (fun z => L z + c) a x = 0 := by
  have he : fderiv ℝ (fun z => L z + c) = fun _ => L := by
    funext z
    exact (L.hasFDerivAt.add_const c).fderiv
  simp [curvature, he]

theorem cut_affine (L : E →L[ℝ] ℝ) (c : ℝ) (a x : E) (b : ℝ) :
    cut (fun z => L z + c) a b x = L x + c := by
  rw [cut, curvature_affine]
  simp [tangent, (L.hasFDerivAt.add_const c).fderiv, map_sub]
  ring

theorem cut_sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ S, ContDiff ℝ 2 (f i)) (a x : E) (b : ℝ) :
    cut (fun z => ∑ i ∈ S, f i z) a b x = ∑ i ∈ S, cut (f i) a b x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cut, tangent, curvature]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [cut_add (hf i (Finset.mem_insert_self i S))
      (ContDiff.sum fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem curvature_sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ S, ContDiff ℝ 2 (f i)) (a x : E) :
    curvature (fun z => ∑ i ∈ S, f i z) a x = ∑ i ∈ S, curvature (f i) a x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [curvature]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [curvature_add (hf i (Finset.mem_insert_self i S))
      (ContDiff.sum fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem curvature_comp_linear {f : F → ℝ} (hf : ContDiff ℝ 2 f)
    (P : E →L[ℝ] F) (a x : E) :
    curvature (fun z => f (P z)) a x = curvature f (P a) (P x) := by
  have he : fderiv ℝ (fun z => f (P z)) = fun z => (fderiv ℝ f (P z)).comp P := by
    funext z
    exact ((hf.differentiable (by norm_num) (P z)).hasFDerivAt.comp z P.hasFDerivAt).fderiv
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) (P a)).hasFDerivAt.comp a P.hasFDerivAt
  have hconst : HasFDerivAt (fun _ : E => P) (0 : E →L[ℝ] E →L[ℝ] F) a :=
    hasFDerivAt_const P a
  have hcomp := hd.clm_comp hconst
  dsimp only [Function.comp_def] at hcomp
  rw [curvature, he, hcomp.fderiv]
  simp [curvature, map_sub]

theorem cut_comp_linear {f : F → ℝ} (hf : ContDiff ℝ 2 f)
    (P : E →L[ℝ] F) (a x : E) (b : ℝ) :
    cut (fun z => f (P z)) a b x = cut f (P a) b (P x) := by
  rw [cut, curvature_comp_linear hf]
  have he : fderiv ℝ (fun z => f (P z)) a = (fderiv ℝ f (P a)).comp P :=
    ((hf.differentiable (by norm_num) (P a)).hasFDerivAt.comp a P.hasFDerivAt).fderiv
  rw [tangent, he]
  simp [cut, tangent, map_sub]
end Calculus

variable {p q m l s nw nv : ℕ}

def jointW : PSCCoordinates p q m →L[ℝ] RealVector p :=
  (ContinuousLinearMap.fst ℝ (RealVector p) (RealVector q)).comp
    (ContinuousLinearMap.fst ℝ (RealVector p × RealVector q) (RealVector m))
def jointV : PSCCoordinates p q m →L[ℝ] RealVector q :=
  (ContinuousLinearMap.snd ℝ (RealVector p) (RealVector q)).comp
    (ContinuousLinearMap.fst ℝ (RealVector p × RealVector q) (RealVector m))
def jointY : PSCCoordinates p q m →L[ℝ] RealVector m :=
  ContinuousLinearMap.snd ℝ (RealVector p × RealVector q) (RealVector m)
def jointAnchor {d : PSCData p q m l s nw nv} (e : PSCAnchor d) : PSCCoordinates p q m :=
  ((e.w,e.v),e.y)
def jointObjective (d : PSCData p q m l s nw nv) (z : PSCCoordinates p q m) : ℝ :=
  d.objective z.1.1 z.1.2 z.2
def jointConstraint (d : PSCData p q m l s nw nv) (j : Fin l)
    (z : PSCCoordinates p q m) : ℝ := d.nonlinear j z.1.1 z.1.2 z.2

theorem joint_objective_cut (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (hr : ContDiff ℝ 2 d.r) (z : PSCCoordinates p q m) (b : ℝ) :
    cut (jointObjective d) (jointAnchor e) b z =
      d.a z.1.1 + d.c z.2 + cut d.r e.v b z.1.2 := by
  let L : PSCCoordinates p q m →L[ℝ] ℝ := d.a.comp jointW + d.c.comp jointY
  have he : jointObjective d = fun z => (L z + 0) + d.r (jointV z) := by
    funext z
    change d.a z.1.1 + d.r z.1.2 + d.c z.2 =
      (d.a z.1.1 + d.c z.2 + 0) + d.r z.1.2
    ring
  have hrv : ContDiff ℝ 2 (fun z : PSCCoordinates p q m => d.r (jointV z)) :=
    hr.comp jointV.contDiff
  rw [he, cut_add (L.contDiff.add (contDiff_const (c := (0 : ℝ)))) hrv,
    cut_affine, cut_comp_linear hr]
  simp [L,jointW,jointY,jointV,jointAnchor]

theorem joint_constraint_cut (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (ht : ∀ j, ContDiff ℝ 2 (d.t j)) (j : Fin l) (z : PSCCoordinates p q m) (b : ℝ) :
    cut (jointConstraint d j) (jointAnchor e) b z =
      d.C j z.2 + d.D j z.1.1 + cut (d.t j) e.v b z.1.2 := by
  let L : PSCCoordinates p q m →L[ℝ] ℝ := (d.C j).comp jointY + (d.D j).comp jointW
  have he : jointConstraint d j = fun z => (L z + 0) + d.t j (jointV z) := by
    funext z
    simp [jointConstraint,PSCData.nonlinear,L,jointW,jointY,jointV]
  have htv : ContDiff ℝ 2 (fun z : PSCCoordinates p q m => d.t j (jointV z)) :=
    (ht j).comp jointV.contDiff
  rw [he, cut_add (L.contDiff.add (contDiff_const (c := (0 : ℝ)))) htv,
    cut_affine, cut_comp_linear (ht j)]
  simp [L,jointW,jointY,jointV,jointAnchor]

def lagrangianLinear (d : PSCData p q m l s nw nv) (e : PSCAnchor d) :
    RealVector q →L[ℝ] ℝ := ∑ i, e.mu i • d.G i
def lagrangianConstant (d : PSCData p q m l s nw nv) (e : PSCAnchor d) : ℝ :=
  d.a e.w + d.c e.y + (∑ j, e.lambda j * (d.C j e.y + d.D j e.w)) +
    ∑ i, e.mu i * (d.E i e.y + d.F i e.w - d.b i)

theorem lagrangian_split (d : PSCData p q m l s nw nv) (e : PSCAnchor d) :
    lagrangian d e = fun v =>
      ((lagrangianLinear d e v + lagrangianConstant d e) + d.r v) +
        ∑ j, e.lambda j * d.t j v := by
  funext v
  simp only [lagrangian, lagrangianLinear, lagrangianConstant, PSCData.objective,
    PSCData.nonlinear, PSCData.coupling, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem lagrangian_curvature (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j)) (v : RealVector q) :
    curvature (lagrangian d e) e.v v =
      curvature d.r e.v v + ∑ j, e.lambda j * curvature (d.t j) e.v v := by
  rw [lagrangian_split]
  rw [curvature_add (((lagrangianLinear d e).contDiff.add contDiff_const).add hr)
    (ContDiff.sum fun j _ => contDiff_const.mul (ht j))]
  rw [curvature_add ((lagrangianLinear d e).contDiff.add contDiff_const) hr,
    curvature_affine, zero_add, curvature_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact curvature_smul (ht j) _ _ _
  · intro j _
    exact contDiff_const.mul (ht j)

theorem lagrangian_cut (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j)) (v : RealVector q) (b : ℝ) :
    cut (lagrangian d e) e.v b v =
      lagrangianLinear d e v + lagrangianConstant d e + cut d.r e.v b v +
        ∑ j, e.lambda j * cut (d.t j) e.v b v := by
  rw [lagrangian_split]
  rw [cut_add (((lagrangianLinear d e).contDiff.add contDiff_const).add hr)
    (ContDiff.sum fun j _ => contDiff_const.mul (ht j))]
  rw [cut_add ((lagrangianLinear d e).contDiff.add contDiff_const) hr,
    cut_affine, cut_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact cut_smul (ht j) _ _ _ _
  · intro j _
    exact contDiff_const.mul (ht j)

theorem lagrangian_remainder (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j)) (v : RealVector q) :
    remainder d e v = d.r v - tangent d.r e.v v +
      ∑ j, e.lambda j * (d.t j v - tangent (d.t j) e.v v) := by
  have h := lagrangian_cut d e hr ht v 0
  simp only [cut_zero] at h
  have he : remainder d e v = lagrangian d e v - tangent (lagrangian d e) e.v v := by
    unfold remainder tangent
    ring
  rw [he]
  rw [h, lagrangian_split]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Every component is valid on the same literal V. -/
theorem unit_lagrangian_underestimation (d : PSCData p q m l s nw nv)
    (e : PSCEntry d) (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (hru : ∀ v ∈ d.V, cut d.r e.data.v 1 v ≤ d.r v)
    (htu : ∀ j v, v ∈ d.V → cut (d.t j) e.data.v 1 v ≤ d.t j v) :
    ∀ v ∈ d.V, cut (lagrangian d e.data) e.data.v 1 v ≤ lagrangian d e.data v := by
  intro v hv
  rw [lagrangian_cut d e.data hr ht, lagrangian_split]
  exact add_le_add (add_le_add le_rfl (hru v hv))
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (htu j v hv) (e.kkt.lambda_nonneg j))

end Chapter05.PSQC.Comparison
