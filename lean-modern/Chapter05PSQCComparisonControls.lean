module

public import Chapter05PSQCComparisonMaster
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! Exact nonlinear KKT control: r(v)=(v-2)^2, t(v)=v^2-1,
V=[-2,2], anchor v=1 and lambda=1. Trivial w/y factors remain in the
literal model. These finite controls assert no numerical or execution result.
Polynomial proof patterns are adapted from accepted Chapter02PSCExamples and
Chapter05PSQCControlData; these new functions are separate definitions. -/
noncomputable section
open Set Chapter02
open scoped BigOperators
namespace Chapter05.PSQC.Comparison.Control
open Quadratic

def scalar (v : ℝ) : RealVector 1 := fun _ => v
def coord : RealVector 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
def poly (A B C : ℝ) (v : RealVector 1) : ℝ := A*(v 0)^2+B*v 0+C

theorem poly_derivative (A B C : ℝ) (x : RealVector 1) :
    HasFDerivAt (poly A B C) ((2*A*x 0+B) • coord) x := by
  have h := ((((hasDerivAt_pow 2 (x 0)).comp_hasFDerivAt x
    coord.hasFDerivAt).const_mul A).fun_add
    (coord.hasFDerivAt.const_mul B)).add_const C
  have he : A • (((2 : ℝ) * x 0 ^ (2-1)) • coord) + B • coord =
      (2*A*x 0+B) • coord := by
    ext z
    simp [smul_eq_mul] <;> ring
  unfold poly
  simpa [coord, Function.comp_def] using h.congr_fderiv he
theorem poly_C2 (A B C : ℝ) : ContDiff ℝ 2 (poly A B C) := by
  unfold poly
  fun_prop
theorem poly_convex (A B C : ℝ) (hA : 0 ≤ A) : ConvexOn ℝ univ (poly A B C) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ s t hs ht hst
  have hn := mul_nonneg (mul_nonneg (mul_nonneg hA hs) ht) (sq_nonneg (x 0-z 0))
  have ht' : t = 1-s := by linarith
  simp only [poly, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ht'] at hn ⊢
  nlinarith
theorem poly_curvature (A B C : ℝ) (a v : RealVector 1) :
    curvature (poly A B C) a v = 2*A*(v 0-a 0)^2 := by
  have he : fderiv ℝ (poly A B C) = fun x => (2*A*x 0+B) • coord :=
    funext fun x => (poly_derivative A B C x).fderiv
  have hd : HasFDerivAt (fun x : RealVector 1 => 2*A*x 0+B)
      ((2*A) • coord) a := by
    simpa [coord] using (coord.hasFDerivAt.const_mul (2*A)).add_const B
  rw [curvature, he, (hd.smul_const coord).fderiv]
  simp [coord]
  ring
theorem poly_cut_one (A B C : ℝ) (a v : RealVector 1) :
    cut (poly A B C) a 1 v = poly A B C v := by
  rw [cut, poly_curvature]
  simp [tangent, (poly_derivative A B C a).fderiv, coord, poly]
  ring

def model : PSCData 0 1 0 1 0 0 2 where
  a := 0
  c := 0
  r := poly 1 (-4) 4
  C := fun _ => 0
  D := fun _ => 0
  t := fun _ => poly 1 0 (-1)
  E := fun _ => 0
  F := fun _ => 0
  G := fun _ => 0
  b := fun _ => 0
  Wrow := fun _ => 0
  Wbound := fun _ => 0
  Vrow := fun i => if i = 0 then -coord else coord
  Vbound := fun _ => 2
  Y := univ
def anchor : PSCAnchor model where
  w := 0
  v := scalar 1
  y := 0
  Dr := (-2 : ℝ) • coord
  Dt := fun _ => (2 : ℝ) • coord
  lambda := fun _ => 1
  mu := fun _ => 0
  nuW := fun _ => 0
  nuV := fun _ => 0

theorem model_V (v : RealVector 1) : v ∈ model.V ↔ -2 ≤ v 0 ∧ v 0 ≤ 2 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    norm_num [model,coord] at h0 h1
    exact ⟨by linarith,h1⟩
  · rintro ⟨hl,hu⟩ i
    fin_cases i <;> norm_num [model,coord] <;> linarith

theorem anchor_kkt : PSCKKT model anchor := by
  constructor
  · intro i; exact Fin.elim0 i
  · exact (model_V _).mpr (by norm_num [anchor,scalar])
  · trivial
  · intro j; norm_num [model,anchor,PSCData.nonlinear,poly,scalar]
  · intro i; exact Fin.elim0 i
  · change HasFDerivAt (poly 1 (-4) 4) ((-2 : ℝ) • coord) (scalar 1)
    have h := poly_derivative 1 (-4) 4 (scalar 1)
    rw [show 2*(1 : ℝ)*(scalar 1) 0 + (-4) = -2 by norm_num [scalar]] at h
    exact h
  · intro j
    change HasFDerivAt (poly 1 0 (-1)) ((2 : ℝ) • coord) (scalar 1)
    simpa [scalar] using poly_derivative 1 0 (-1) (scalar 1)
  · intro j; norm_num [anchor]
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; norm_num [anchor]
  · intro j; norm_num [model,anchor,PSCData.nonlinear,poly,scalar]
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; simp [anchor]
  · intro dw; simp [model,anchor,PSCAnchor.normalW]
  · intro dv; simp [model,anchor,PSCAnchor.normalV,coord]

def entry : PSCEntry model := ⟨anchor,anchor_kkt⟩
theorem model_regular : ContDiff ℝ 2 model.r ∧ ∀ j, ContDiff ℝ 2 (model.t j) :=
  ⟨poly_C2 1 (-4) 4,fun _ => poly_C2 1 0 (-1)⟩
theorem model_convex : ConvexOn ℝ univ model.r ∧ ∀ j, ConvexOn ℝ univ (model.t j) :=
  ⟨poly_convex 1 (-4) 4 (by norm_num),fun _ => poly_convex 1 0 (-1) (by norm_num)⟩
theorem positive_multiplier : 0 < entry.data.lambda 0 := by norm_num [entry,anchor]
theorem positive_curvature : 0 < curvature (lagrangian model entry.data) entry.data.v (scalar 0) := by
  rw [lagrangian_curvature model entry.data model_regular.1 model_regular.2]
  norm_num [model,entry,anchor,poly_curvature,scalar]
theorem actual_psqc_row (v : RealVector 1) :
    fullCut model entry.data 1 0 v 0 = 1+2*(v 0-1)^2 := by
  rw [fullCut,psqcRow,lagrangian_curvature model entry.data model_regular.1 model_regular.2]
  norm_num [model,entry,anchor,pscRow,PSCData.nonlinear,poly,poly_curvature,scalar]
  ring
theorem actual_oa_rows (v : RealVector 1) :
    objectiveRow model entry.data 1 0 v 0 = (v 0-2)^2 ∧
      constraintRow model entry.data (fun _ => 1) 0 0 v 0 = (v 0)^2-1 := by
  constructor <;> simp [objectiveRow,constraintRow,model,entry,anchor,poly_cut_one,poly] <;> ring
theorem control_comparison (v : RealVector 1) (eta : ℝ) (hv : v ∈ model.V)
    (ho : (v 0-2)^2 ≤ eta) (hg : (v 0)^2-1 ≤ 0) :
    1+2*(v 0-1)^2 ≤ eta := by
  have hobj : objectiveRow model entry.data 1 0 v 0 ≤ eta := by rw [(actual_oa_rows v).1]; exact ho
  have hcon : ∀ j, constraintRow model entry.data (fun _ => 1) j 0 v 0 ≤ 0 := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hj,(actual_oa_rows v).2]
    exact hg
  have hc := common_scale_row model entry model_convex.1 model_convex.2
    model_regular.1 model_regular.2 1 0 v 0 eta hv hobj hcon
  have he := actual_psqc_row v
  simp only [fullCut,model,ContinuousLinearMap.zero_apply,zero_add,sub_zero] at he hc
  linarith

theorem unit_component_scales :
    safeScale model.r entry.data.v model.V = 1 ∧
      (∀ j, safeScale (model.t j) entry.data.v model.V = 1) ∧
      safeScale (lagrangian model entry.data) entry.data.v model.V = 1 := by
  have hr : ∀ v ∈ model.V, cut model.r entry.data.v 1 v ≤ model.r v := by
    intro v _; exact le_of_eq (poly_cut_one 1 (-4) 4 _ _)
  have ht : ∀ j v, v ∈ model.V → cut (model.t j) entry.data.v 1 v ≤ model.t j v := by
    intro j v _; exact le_of_eq (poly_cut_one 1 0 (-1) _ _)
  exact ⟨unit_underestimation_safeScale_eq_one hr,
    fun j => unit_underestimation_safeScale_eq_one (ht j),
    unit_lagrangian_safeScale model entry model_regular.1 model_regular.2 hr ht⟩

def history : List (Occurrence model) := [⟨entry,1,fun _ => 1,1⟩]
theorem history_compatible : Compatible history := by
  intro o ho
  simp only [history,List.mem_cons,List.not_mem_nil,or_false] at ho
  subst o
  exact ⟨le_rfl,fun _ => le_rfl⟩

theorem history_valid : ValidScales model history := by
  have hf : safeScale (jointObjective model) (jointAnchor entry.data) (pscRetainedBase model) = 1 := by
    apply unit_underestimation_safeScale_eq_one
    intro z _
    rw [joint_objective_cut model entry.data model_regular.1]
    change 0 + 0 + cut (poly 1 (-4) 4) entry.data.v 1 z.1.2 ≤ 0 + poly 1 (-4) 4 z.1.2 + 0
    rw [poly_cut_one]
    simp
  have hg : ∀ j, safeScale (jointConstraint model j) (jointAnchor entry.data)
      (pscRetainedBase model) = 1 := by
    intro j
    apply unit_underestimation_safeScale_eq_one
    intro z _
    rw [joint_constraint_cut model entry.data model_regular.2]
    change 0 + 0 + cut (poly 1 0 (-1)) entry.data.v 1 z.1.2 ≤ 0 + 0 + poly 1 0 (-1) z.1.2
    rw [poly_cut_one]
  constructor
  · intro i _
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (0 ≤ (1 : ℝ) ∧ 1 ≤ safeScale (jointObjective model) (jointAnchor entry.data)
      (pscRetainedBase model)) ∧ ∀ j, 0 ≤ (1 : ℝ) ∧ 1 ≤ safeScale
        (jointConstraint model j) (jointAnchor entry.data) (pscRetainedBase model)
    simp [hf,hg]
  · intro ea hea
    simp only [pscProjection,history,List.map_cons,List.map_nil,List.mem_cons,
      List.not_mem_nil,or_false] at hea
    subst ea
    exact ⟨by norm_num,le_of_eq unit_component_scales.2.2.symm⟩

theorem retained_anchor_nonempty : model.feasible 0 (scalar 1) 0 := anchor_kkt.feasible

def strictWitness : PSCCoordinates 0 1 0 × ℝ := (((0,scalar 2),0),3)
theorem strict_control :
    epigraphToPSC model strictWitness ∈ psqcMaster model (pscProjection history) ∧
      strictWitness ∉ quadraticMaster (jointMasterData model history) Finset.univ := by
  constructor
  · refine ⟨(epigraph_psc_base model strictWitness).mpr ?_, ?_⟩
    · refine ⟨?_,(model_V _).mpr (by norm_num [strictWitness,scalar]),by trivial,?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
    · intro ea hea
      simp only [pscProjection,history,List.map_cons,List.map_nil,List.mem_cons,
        List.not_mem_nil,or_false] at hea
      subst ea
      have he := actual_psqc_row (scalar 2)
      norm_num [fullCut,model,scalar] at he
      simpa [epigraphToPSC,strictWitness,model] using le_of_eq he
  · intro h
    let i : Fin history.length := ⟨0,by simp [history]⟩
    have hj := h.2.2 i (Finset.mem_univ i) 0
    change cut (jointConstraint model 0) (jointAnchor entry.data) 1 strictWitness.1 ≤ 0 at hj
    rw [joint_constraint_cut model entry.data model_regular.2] at hj
    change 0+0+cut (poly 1 0 (-1)) entry.data.v 1 (scalar 2) ≤ 0 at hj
    rw [poly_cut_one] at hj
    norm_num [poly,scalar] at hj

end Chapter05.PSQC.Comparison.Control
