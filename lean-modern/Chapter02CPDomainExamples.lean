module

public import Chapter02CPDomain
public import Chapter02CPDomainSource
public import Chapter02Model
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Concrete domain-relative derivative controls. Arbitrary normal components
are permitted within a lower-dimensional set; boundedness belongs to a fixed
continuous choice, never to all such derivatives. Candidate, not accepted. -/
noncomputable section
open Chapter02
namespace Chapter02CPDomainExamples

abbrev Plane := ℝ × ℝ
def normal (a : ℝ) : Plane →L[ℝ] ℝ :=
  a • ContinuousLinearMap.snd ℝ ℝ ℝ
def segment : Set Plane := Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)

theorem empty_domain_control (g : ℝ → ℝ) (D : ℝ → ℝ →L[ℝ] ℝ) :
    (∀ z, HasFDerivWithinAt g (D z) ∅ z) ∧
    (∀ z ∈ (∅ : Set ℝ), ∀ x ∈ (∅ : Set ℝ), g z + D z (x-z) ≤ g x) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ (∅ : Set ℝ), ‖D z‖ ≤ M) := by
  refine ⟨fun z => .empty, ?_, ?_⟩
  · intro z hz; simp at hz
  · exact cp_continuous_field_bounded isCompact_empty (by intro z hz; simp at hz)

theorem singleton_control (a c : ℝ) :
    HasFDerivWithinAt (fun _ : ℝ => c) (0 : ℝ →L[ℝ] ℝ) {a} a ∧
    c + (0 : ℝ →L[ℝ] ℝ) (a-a) ≤ c ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ ({a} : Set ℝ), ‖(0 : ℝ →L[ℝ] ℝ)‖ ≤ M) := by
  have hd := hasFDerivWithinAt_singleton (𝕜 := ℝ) (fun _ : ℝ => c) a
  refine ⟨hd, cp_tangent_underestimator_within (convexOn_const c (convex_singleton a))
    (by simp) (by simp) hd, ?_⟩
  exact cp_continuous_field_bounded isCompact_singleton continuousOn_const

theorem empty_row_control :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (_j : Fin 0) (z : ℝ), z ∈ Set.Icc (0 : ℝ) 1 →
      ‖(0 : ℝ →L[ℝ] ℝ)‖ ≤ M := by
  exact cp_finite_continuous_fields_bounded (J := Fin 0)
    (D := fun _ _ => (0 : ℝ →L[ℝ] ℝ)) isCompact_Icc (fun _ => continuousOn_const)

theorem segment_compact_convex : IsCompact segment ∧ Convex ℝ segment := by
  exact ⟨isCompact_Icc.prod isCompact_singleton, (convex_Icc 0 1).prod (convex_singleton 0)⟩

theorem segment_arbitrary_normal_derivative (a : ℝ) (z : Plane) (hz : z ∈ segment) :
    HasFDerivWithinAt (fun _ : Plane => (0 : ℝ)) (normal a) segment z := by
  apply (normal a).hasFDerivAt.hasFDerivWithinAt.congr' _ hz
  intro x hx
  have hx2 : x.2 = 0 := hx.2
  simp [normal, hx2]

theorem segment_support_and_fixed_bound (a : ℝ) :
    (∀ z ∈ segment, ∀ x ∈ segment, (normal a) (x-z) ≤ 0) ∧
    ContinuousOn (fun _ : Plane => normal a) segment ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ segment, ‖normal a‖ ≤ M) := by
  refine ⟨?_, continuousOn_const,
    cp_continuous_field_bounded segment_compact_convex.1 continuousOn_const⟩
  intro z hz x hx
  simpa using cp_tangent_underestimator_within
    (convexOn_const (0 : ℝ) segment_compact_convex.2) hz hx
    (segment_arbitrary_normal_derivative a z hz)

def unboundedField (z : Plane) : Plane →L[ℝ] ℝ := normal z.1⁻¹

theorem unbounded_selection_derivative (z : Plane) (hz : z ∈ segment) :
    HasFDerivWithinAt (fun _ : Plane => (0 : ℝ)) (unboundedField z) segment z :=
  segment_arbitrary_normal_derivative _ z hz

theorem unbounded_selection_control :
    (∀ M : ℝ, 0 ≤ M → ∃ z ∈ segment, M < ‖unboundedField z‖) ∧
    ¬ ContinuousOn unboundedField segment := by
  have hu : ∀ M : ℝ, 0 ≤ M → ∃ z ∈ segment, M < ‖unboundedField z‖ := by
    intro M hM
    have hp : 0 < M+1 := by linarith
    refine ⟨((M+1)⁻¹, 0), ⟨?_, by simp⟩, ?_⟩
    · exact ⟨le_of_lt (inv_pos.mpr hp), (inv_le_one₀ hp).mpr (by linarith)⟩
    · have hn := (normal (M+1)).le_opNorm ((0:ℝ),1)
      change ‖(M+1)*1‖ ≤ ‖normal (M+1)‖ * ‖((0:ℝ),1)‖ at hn
      norm_num [Prod.norm_def, abs_of_pos hp] at hn
      change M < ‖normal (((M+1)⁻¹)⁻¹)‖
      rw [inv_inv]
      linarith
  refine ⟨hu, ?_⟩
  intro hc
  obtain ⟨M,hM,hbound⟩ := cp_continuous_field_bounded segment_compact_convex.1 hc
  obtain ⟨z,hz,hzM⟩ := hu M hM
  exact (not_lt_of_ge (hbound z hz)) hzM

def localGlobal (x : ℝ) : ℝ := x^2 - 1/4 - 4 * (max (x-1) 0)^3
def scalarDerivative (x : ℝ) : ℝ →L[ℝ] ℝ :=
  (2*x) • ContinuousLinearMap.id ℝ ℝ

theorem localGlobal_restriction (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    localGlobal x = x^2 - 1/4 := by
  have h : x-1 ≤ 0 := by linarith [hx.2]
  simp [localGlobal, max_eq_right h]

theorem localGlobal_within_derivative (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivWithinAt localGlobal (scalarDerivative x) (Set.Icc (0 : ℝ) 1) x := by
  have hd := ((hasDerivAt_pow 2 x).sub_const (1/4 : ℝ)).hasFDerivAt
  have hd' : HasFDerivWithinAt (fun t : ℝ => t^2-1/4) (scalarDerivative x)
      (Set.Icc (0 : ℝ) 1) x := by
    convert hd.hasFDerivWithinAt using 1
    ext
    simp [scalarDerivative]
  exact hd'.congr' (fun t ht => localGlobal_restriction t ht) hx

theorem localGlobal_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) localGlobal := by
  have hc : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun x : ℝ => x^2-1/4) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
    simp only [smul_eq_mul]
    nlinarith
  exact hc.congr (fun x hx => (localGlobal_restriction x hx).symm)

theorem localGlobal_cut_control :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, localGlobal x ≤ 0 →
      localGlobal 1 + scalarDerivative 1 (x-1) ≤ 0) ∧
    ((0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ localGlobal 0 ≤ 0) ∧
    localGlobal 2 = -(1/4 : ℝ) ∧
    localGlobal 1 + scalarDerivative 1 (2-1) = (11/4 : ℝ) := by
  refine ⟨?_, by norm_num [localGlobal], by norm_num [localGlobal], ?_⟩
  · intro x hx hf
    exact cp_tangent_cut_valid_within localGlobal_convex (by norm_num) hx
      (localGlobal_within_derivative 1 (by norm_num)) hf
  · norm_num [localGlobal, scalarDerivative]

theorem localGlobal_model_control :
    IsMinimizer {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ localGlobal x ≤ 0} id 0 ∧
    (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → localGlobal x ≤ 0 →
      localGlobal 1 + scalarDerivative 1 (x-1) ≤ 0) ∧
    localGlobal 2 ≤ 0 ∧ ¬ (localGlobal 1 + scalarDerivative 1 (2-1) ≤ 0) := by
  refine ⟨⟨localGlobal_cut_control.2.1, fun x hx => hx.1.1⟩,
    localGlobal_cut_control.1, ?_, ?_⟩
  · rw [localGlobal_cut_control.2.2.1]; norm_num
  · rw [localGlobal_cut_control.2.2.2]; norm_num

def mixedPoint (x y : ℝ) : Point 1 1 := (fun _ => x, fun _ => y)
def mixedX : Point 1 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector 1))
def mixedY : Point 1 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ (RealVector 1) (RealVector 1))
def mixedDomain : Set (Point 1 1) := Set.Icc (mixedPoint 0 0) (mixedPoint 1 1)
def mixedModel : ModelData 1 1 1 4 where
  g := fun _ p => (p.1 0)^2 + (p.2 0-1/2)^2 - 1/4
  A := ![![1], ![-1], ![0], ![0]]
  B := ![![0], ![0], ![1], ![-1]]
  rhs := ![1,0,1,0]
  c1 := ![1]
  c2 := ![1]
  lo := ![0]
  hi := ![1]
def mixedDerivative (_ : Fin 1) (p : Point 1 1) : Point 1 1 →L[ℝ] ℝ :=
  (2*p.1 0) • mixedX + (2*(p.2 0-1/2)) • mixedY
def mixedCuts : TangentFamily 1 1 1 1 :=
  cpDomainTangentFamily (fun _ => mixedPoint 1 (1/2)) (fun _ => Set.univ) mixedDerivative

theorem mixed_domain_geometry : IsCompact mixedDomain ∧ Convex ℝ mixedDomain ∧
    (∀ p, p ∈ mixedDomain ↔ 0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1) := by
  have hi : ∀ p, p ∈ mixedDomain ↔
      0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
    intro p
    simp [mixedDomain, mixedPoint, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_one]
    tauto
  refine ⟨isCompact_Icc, ?_, hi⟩
  intro p hp q hq a b ha hb hab
  apply (hi _).mpr
  obtain ⟨hp0,hp1,hp2,hp3⟩ := (hi _).mp hp
  obtain ⟨hq0,hq1,hq2,hq3⟩ := (hi _).mp hq
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · exact add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hp1 ha, mul_le_mul_of_nonneg_left hq1 hb]
  constructor
  · exact add_nonneg (mul_nonneg ha hp2) (mul_nonneg hb hq2)
  · nlinarith [mul_le_mul_of_nonneg_left hp3 ha, mul_le_mul_of_nonneg_left hq3 hb]

theorem mixed_convex (j : Fin 1) : ConvexOn ℝ mixedDomain (mixedModel.g j) := by
  refine ⟨mixed_domain_geometry.2.1, ?_⟩
  intro p hp q hq a b ha hb hab
  have hb' : b = 1-a := by linarith
  subst b
  have hx := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.1 0-q.1 0))
  have hy := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.2 0-q.2 0))
  simp only [mixedModel, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

theorem mixed_actual_derivative (j : Fin 1) (p : Point 1 1) :
    HasFDerivAt (mixedModel.g j) (mixedDerivative j p) p := by
  have hx := (hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p mixedX.hasFDerivAt
  have hy := (hasDerivAt_pow 2 (p.2 0-1/2)).comp_hasFDerivAt p
    (mixedY.hasFDerivAt.sub_const (1/2 : ℝ))
  convert (hx.add hy).sub_const (1/4 : ℝ) using 1 <;>
    norm_num [mixedModel, mixedDerivative, mixedX, mixedY, Function.comp_def]

theorem mixed_source_compact_control :
    (∀ j, ContinuousOn (mixedModel.g j) mixedDomain) ∧
    ∃ M : ℝ, 0 ≤ M ∧ (∀ j p, p ∈ mixedDomain → ‖mixedDerivative j p‖ ≤ M) ∧
      mixedModel.feasibleOn mixedDomain ⊆ mixedModel.masterOn mixedCuts mixedDomain := by
  have hc : ∀ j, ContinuousOn (mixedDerivative j) mixedDomain := by
    intro j
    unfold mixedDerivative
    fun_prop
  obtain ⟨hg,M,hM,hbound,houter⟩ := source_cp_compact_domain mixedModel mixedDomain
    mixedDerivative mixed_domain_geometry.1 mixed_convex
    (fun j p _ => (mixed_actual_derivative j p).hasFDerivWithinAt) hc
  refine ⟨hg,M,hM,hbound, houter 1 (fun _ => mixedPoint 1 (1/2)) (fun _ => Set.univ) ?_⟩
  intro i
  exact (mixed_domain_geometry.2.2 _).mpr (by norm_num [mixedPoint])

theorem mixed_feasible_endpoints :
    mixedPoint 0 0 ∈ mixedModel.feasibleOn mixedDomain ∧
    mixedPoint 0 1 ∈ mixedModel.feasibleOn mixedDomain ∧
    mixedModel.objective (mixedPoint 0 0) = 0 ∧
    mixedModel.objective (mixedPoint 0 1) = 1 := by
  have hf : ∀ y : ℤ, 0 ≤ y → y ≤ 1 →
      mixedPoint 0 y ∈ mixedModel.feasibleOn mixedDomain := by
    intro y hy0 hy1
    have hy : y=0 ∨ y=1 := by omega
    apply (source_feasible_iff _ _ _).mpr
    refine ⟨(mixed_domain_geometry.2.2 _).mpr ?_, ?_, ?_, ?_⟩
    · norm_num [mixedPoint]; exact ⟨by exact_mod_cast hy0, by exact_mod_cast hy1⟩
    · intro j; rcases hy with rfl|rfl <;> norm_num [mixedModel, mixedPoint]
    · intro j
      rcases hy with rfl|rfl <;> fin_cases j <;>
        norm_num [mixedModel, mixedPoint, LinearForm, Fin.sum_univ_succ]
    · refine ⟨fun _ => y, ?_, rfl⟩
      intro i; simpa [mixedModel] using And.intro (show (0:ℝ) ≤ y by exact_mod_cast hy0)
        (show (y:ℝ) ≤ 1 by exact_mod_cast hy1)
  refine ⟨by simpa using hf 0 (by norm_num) (by norm_num),
    by simpa using hf 1 (by norm_num) (by norm_num), ?_, ?_⟩ <;>
    norm_num [ModelData.objective, mixedModel, mixedPoint, LinearForm, Fin.sum_univ_succ]

theorem mixed_fractional_origin_control :
    mixedPoint 1 (1/2) ∈ mixedDomain ∧
    mixedPoint 1 (1/2) ∉ IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi ∧
    mixedPoint 0 0 ∈ mixedModel.masterOn mixedCuts mixedDomain ∧
    mixedPoint 0 1 ∈ mixedModel.masterOn mixedCuts mixedDomain := by
  have ho := mixed_source_compact_control.2.choose_spec.2.2
  refine ⟨(mixed_domain_geometry.2.2 _).mpr (by norm_num [mixedPoint]), ?_,
    ho mixed_feasible_endpoints.1, ho mixed_feasible_endpoints.2.1⟩
  rintro ⟨y, hy, hp⟩
  have heq : (y 0 : ℝ) = 1/2 := by simpa [mixedPoint] using (congrFun hp 0).symm
  have h0 : (0:ℤ) < y 0 := by exact_mod_cast (show (0:ℝ) < y 0 by linarith)
  have h1 : y 0 < (1:ℤ) := by exact_mod_cast (show (y 0:ℝ) < 1 by linarith)
  omega

theorem mixed_minimum_and_cut_exclusion :
    IsMinimizer (mixedModel.feasibleOn mixedDomain) mixedModel.objective (mixedPoint 0 0) ∧
    mixedPoint 1 (1/2) ∉ mixedCuts.cutRegion mixedModel := by
  constructor
  · refine ⟨mixed_feasible_endpoints.1, ?_⟩
    intro p hp
    have hk := (mixed_domain_geometry.2.2 _).mp ((source_feasible_iff _ _ _).mp hp).1
    rw [mixed_feasible_endpoints.2.2.1]
    change 0 ≤ mixedModel.objective p
    simpa [ModelData.objective, mixedModel, LinearForm, Fin.sum_univ_succ] using
      add_nonneg hk.1 hk.2.2.1
  · intro hp
    have hc := hp (0 : Fin 1) (0 : Fin 1) (by simp [mixedCuts, cpDomainTangentFamily])
    norm_num [mixedCuts, cpDomainTangentFamily, mixedModel, mixedPoint] at hc

theorem mixed_base_nonconvex :
    ¬ Convex ℝ (mixedModel.linearRegion ∩ IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi) := by
  intro hc
  have ha : mixedPoint 0 0 ∈ mixedModel.linearRegion ∩
      IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi :=
    ⟨mixed_feasible_endpoints.1.1.2, mixed_feasible_endpoints.1.2⟩
  have hb : mixedPoint 0 1 ∈ mixedModel.linearRegion ∩
      IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi :=
    ⟨mixed_feasible_endpoints.2.1.1.2, mixed_feasible_endpoints.2.1.2⟩
  have hm := hc ha hb (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
  obtain ⟨y,hy,heq⟩ := hm.2
  have hyhalf : (y 0 : ℝ) = 1/2 := by
    have h := (congrFun heq 0).symm
    norm_num [mixedPoint] at h
    exact h
  have h0 : (0:ℤ) < y 0 := by exact_mod_cast (show (0:ℝ) < y 0 by linarith)
  have h1 : y 0 < (1:ℤ) := by exact_mod_cast (show (y 0:ℝ) < 1 by linarith)
  omega

end Chapter02CPDomainExamples

#print axioms Chapter02CPDomainExamples.empty_domain_control
#print axioms Chapter02CPDomainExamples.singleton_control
#print axioms Chapter02CPDomainExamples.empty_row_control
#print axioms Chapter02CPDomainExamples.segment_compact_convex
#print axioms Chapter02CPDomainExamples.segment_arbitrary_normal_derivative
#print axioms Chapter02CPDomainExamples.segment_support_and_fixed_bound
#print axioms Chapter02CPDomainExamples.unbounded_selection_derivative
#print axioms Chapter02CPDomainExamples.unbounded_selection_control
#print axioms Chapter02CPDomainExamples.localGlobal_restriction
#print axioms Chapter02CPDomainExamples.localGlobal_within_derivative
#print axioms Chapter02CPDomainExamples.localGlobal_convex
#print axioms Chapter02CPDomainExamples.localGlobal_cut_control
#print axioms Chapter02CPDomainExamples.localGlobal_model_control
#print axioms Chapter02CPDomainExamples.mixed_domain_geometry
#print axioms Chapter02CPDomainExamples.mixed_convex
#print axioms Chapter02CPDomainExamples.mixed_actual_derivative
#print axioms Chapter02CPDomainExamples.mixed_source_compact_control
#print axioms Chapter02CPDomainExamples.mixed_feasible_endpoints
#print axioms Chapter02CPDomainExamples.mixed_fractional_origin_control
#print axioms Chapter02CPDomainExamples.mixed_minimum_and_cut_exclusion
#print axioms Chapter02CPDomainExamples.mixed_base_nonconvex
