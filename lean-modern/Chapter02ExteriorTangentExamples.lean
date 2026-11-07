module

public import Chapter02ExteriorTangent
public import Chapter02CPDomainExamples

@[expose] public section

/-! Exact controls for the bounded exterior-tangent contract. No numerical
producer or procedure is asserted. All fields below are actual derivatives. -/
noncomputable section
open Chapter02
namespace Chapter02ExteriorTangentExamples

def scalarK : Set ℝ := Set.Icc 0 2
def scalarG (_ : Fin 1) (x : ℝ) : ℝ := x-1
def scalarD (_ : Fin 1) (_ : ℝ) : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

theorem scalar_analytic_premises : IsCompact scalarK ∧ Convex ℝ scalarK ∧
    (∀ j, ConvexOn ℝ scalarK (scalarG j)) ∧
    (∀ j x, HasFDerivAt (scalarG j) (scalarD j x) x) ∧
    (∀ j, ContinuousOn (scalarD j) scalarK) ∧
    (∀ j, scalarG j 0 < 0) := by
  refine ⟨isCompact_Icc, convex_Icc _ _, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [scalarG]
    nlinarith
  · intro j x
    exact (hasFDerivAt_id x).sub_const 1
  · intro j
    exact continuous_const.continuousOn
  · intro j
    norm_num [scalarG]

theorem scalar_admissible_iff (q t : ℝ) :
    (q,t) ∈ exteriorData ({2} : Set ℝ) scalarG 0 1 (0 : Fin 1) ↔
      q=2 ∧ t ∈ Set.Icc (1/2 : ℝ) 1 := by
  simp only [exteriorData, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_Icc,
    scalarG, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, sub_zero, add_zero, smul_eq_mul, mul_zero, zero_add]
  constructor
  · rintro ⟨rfl,ht,hv,hm,hz⟩
    exact ⟨rfl, by constructor <;> linarith [ht.1,ht.2]⟩
  · rintro ⟨rfl,ht⟩
    refine ⟨rfl, ⟨by linarith [ht.1],ht.2⟩, ⟨0,by norm_num⟩,
      fun _ => le_refl _, ?_⟩
    linarith [ht.1]

theorem scalar_complete_tangent (t w : ℝ) :
    exteriorTangent scalarG scalarD (0 : Fin 1) (AffineMap.lineMap 0 2 t) w = w-1 ∧
    exteriorNormalizedMargin scalarG scalarD 0 (0 : Fin 1) (2,t) = 1/2 := by
  constructor
  · simp [exteriorTangent, scalarG, scalarD]
  · norm_num [exteriorNormalizedMargin, exteriorTangent, scalarG, scalarD]

theorem scalar_endpoint_and_intercept_control :
    (2,0) ∉ exteriorData ({2} : Set ℝ) scalarG 0 1 (0 : Fin 1) ∧
    (2,1) ∈ exteriorData ({2} : Set ℝ) scalarG 0 1 (0 : Fin 1) ∧
    exteriorTangent scalarG scalarD (0 : Fin 1) 2 2 = 1 ∧
    scalarD (0 : Fin 1) 2 (2-2) = 0 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, exteriorTangent scalarG scalarD (0 : Fin 1) 2 x ≤ 0) := by
  refine ⟨by rw [scalar_admissible_iff]; norm_num,
    by rw [scalar_admissible_iff]; norm_num, ?_, ?_, ?_⟩
  · norm_num [exteriorTangent, scalarG, scalarD]
  · simp
  · intro x hx
    simpa [exteriorTangent, scalarG, scalarD] using sub_nonpos.mpr hx.2

theorem scalar_uniform_and_outside_control :
    ∃ delta > 0,
      (∀ j q t, (q,t) ∈ exteriorData ({2} : Set ℝ) scalarG 0 1 j →
        ∀ w, exteriorTangent scalarG scalarD j (AffineMap.lineMap 0 q t) w ≤ 0 →
          delta ≤ dist q w) ∧
      (-1 : ℝ) ∉ scalarK ∧
      exteriorTangent scalarG scalarD (0 : Fin 1) 2 (-1) ≤ 0 ∧ delta ≤ 3 := by
  obtain ⟨delta,hd,hsep⟩ := exterior_uniform_separation
    (isCompact_singleton : IsCompact ({2} : Set ℝ)) scalar_analytic_premises.2.1
    (show ({2} : Set ℝ) ⊆ scalarK by intro x hx; have hx2 : x=2 := hx; subst x; norm_num [scalarK])
    scalar_analytic_premises.2.2.1
    (fun j x _ => (scalar_analytic_premises.2.2.2.1 j x).hasFDerivWithinAt)
    scalar_analytic_premises.2.2.2.2.1 (show (0:ℝ) ∈ scalarK by norm_num [scalarK])
    scalar_analytic_premises.2.2.2.2.2 (show (0:ℝ)<1 by norm_num)
  refine ⟨delta,hd,hsep,by norm_num [scalarK],by norm_num [exteriorTangent,scalarG,scalarD], ?_⟩
  have h := hsep 0 2 1 scalar_endpoint_and_intercept_control.2.1 (-1)
    (by norm_num [exteriorTangent,scalarG,scalarD])
  norm_num [Real.dist_eq] at h; exact h

def twoG (j : Fin 2) (x : ℝ) : ℝ := if j=0 then x-1 else x-2
def twoD (_ : Fin 2) (_ : ℝ) : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

theorem nonmaximal_zero_row_control :
    (∀ j, ConvexOn ℝ scalarK (twoG j)) ∧
    (∀ j x, HasFDerivAt (twoG j) (twoD j x) x) ∧
    (∀ j, twoG j 0 < 0) ∧
    (2,1) ∈ exteriorData ({2} : Set ℝ) twoG 0 1 (0 : Fin 2) ∧
    (2,1) ∉ exteriorData ({2} : Set ℝ) twoG 0 1 (1 : Fin 2) ∧
    twoG 1 2 = 0 ∧ exteriorTangent twoG twoD 1 2 2 = 0 := by
  have hc (b : ℝ) : ConvexOn ℝ scalarK (fun x : ℝ => x-b) := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a c ha hc hac
    dsimp; nlinarith [congrArg (fun z : ℝ => z*b) hac]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro j; fin_cases j
    · change ConvexOn ℝ scalarK (fun x : ℝ => x - 1)
      exact hc 1
    · change ConvexOn ℝ scalarK (fun x : ℝ => x - 2)
      exact hc 2
  · intro j x
    fin_cases j
    · change HasFDerivAt (fun u : ℝ => u-1) (ContinuousLinearMap.id ℝ ℝ) x
      exact (hasFDerivAt_id x).sub_const 1
    · change HasFDerivAt (fun u : ℝ => u-2) (ContinuousLinearMap.id ℝ ℝ) x
      exact (hasFDerivAt_id x).sub_const 2
  · intro j; fin_cases j <;> norm_num [twoG]
  · refine ⟨by simp, by norm_num, ⟨0,by norm_num [twoG]⟩, ?_, by norm_num [twoG]⟩
    intro j; fin_cases j <;> norm_num [twoG]
  · intro h
    have hh := h.2.2.2.1 (0 : Fin 2)
    norm_num [twoG] at hh
  · norm_num [twoG]
  · norm_num [exteriorTangent,twoG,twoD]

theorem zero_threshold_control :
    (1,1) ∈ exteriorData ({1} : Set ℝ) scalarG 0 0 (0 : Fin 1) ∧
    exteriorTangent scalarG scalarD (0 : Fin 1) 1 1 = 0 := by
  constructor
  · refine ⟨by simp,by norm_num,⟨0,by norm_num [scalarG]⟩,?_,by norm_num [scalarG]⟩
    intro j; simp [scalarG]
  · norm_num [exteriorTangent,scalarG,scalarD]

theorem empty_and_nonviolating_data_control :
    exteriorData (∅ : Set ℝ) scalarG 0 1 (0 : Fin 1) = ∅ ∧
    exteriorData ({0} : Set ℝ) scalarG 0 1 (0 : Fin 1) = ∅ ∧
    ∃ delta > 0, ∀ B ∈ ({(∅ : Set ℝ), {0}} : Set (Set ℝ)), ∀ j,
      ∀ p ∈ exteriorData B scalarG 0 1 j,
        delta ≤ exteriorNormalizedMargin scalarG scalarD 0 j p := by
  have he : ∀ j, exteriorData (∅ : Set ℝ) scalarG 0 1 j = ∅ := by
    intro j; ext p; simp [exteriorData]
  have hz : ∀ j, exteriorData ({0} : Set ℝ) scalarG 0 1 j = ∅ := by
    intro j; apply Set.eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp,ht,⟨k,hk⟩,hm,hg⟩
    have hp0 : p.1=0 := hp
    norm_num [scalarG,hp0] at hk
  refine ⟨he 0,hz 0,1,by norm_num,?_⟩
  intro B hB j p hp
  rcases hB with hB|hB
  · have hb : B=∅ := hB; subst B; rw [he] at hp; exact hp.elim
  · have hb : B={0} := hB; subst B; rw [hz] at hp; exact hp.elim

def emptyG (j : Fin 0) : ℝ → ℝ := Fin.elim0 j
def emptyD (j : Fin 0) : ℝ → ℝ →L[ℝ] ℝ := Fin.elim0 j

theorem empty_rows_uniform_control :
    ∃ delta > 0, ∀ j, ∀ p ∈ exteriorData ({2} : Set ℝ) emptyG 0 1 j,
      delta ≤ exteriorNormalizedMargin emptyG emptyD 0 j p := by
  exact exterior_uniform_normalized_margin isCompact_singleton (convex_Icc _ _)
    (show ({2} : Set ℝ) ⊆ scalarK by intro x hx; have hx2 : x=2 := hx; subst x; norm_num [scalarK])
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (show (0:ℝ) ∈ scalarK by norm_num [scalarK]) (fun j => Fin.elim0 j) (by norm_num)

open Chapter02CPDomainExamples

def mixedBase : Set (Point 1 1) :=
  mixedModel.linearRegion ∩ IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi
def mixedA : Point 1 1 := mixedPoint 0 (1/2)
def mixedQ : Point 1 1 := mixedPoint 1 1
def mixedZ : Point 1 1 := mixedPoint (1/2) (3/4)
def exteriorMixedCuts : TangentFamily 1 1 1 1 :=
  cpDomainTangentFamily (fun _ => mixedZ) (fun _ => Set.univ) mixedDerivative

theorem mixed_linear_region_identity : mixedModel.linearRegion = mixedDomain := by
  ext p
  rw [mixed_domain_geometry.2.2]
  constructor
  · intro hp
    have h0:=hp ⟨0,by decide⟩; have h1:=hp ⟨1,by decide⟩
    have h2:=hp ⟨2,by decide⟩; have h3:=hp ⟨3,by decide⟩
    norm_num [mixedModel,LinearForm,Fin.sum_univ_succ] at h0 h1 h2 h3
    exact ⟨by linarith,h0,by linarith,h2⟩
  · rintro ⟨h0,h1,h2,h3⟩ j
    fin_cases j <;> norm_num [mixedModel,LinearForm,Fin.sum_univ_succ] <;> linarith

theorem mixed_base_compact : IsCompact mixedBase ∧ mixedBase ⊆ mixedDomain ∧
    mixedQ ∈ mixedBase := by
  have heq : mixedBase = mixedDomain ∩ {p | p.2 0 = 0 ∨ p.2 0 = 1} := by
    ext p
    change (p∈mixedModel.linearRegion ∧ p∈IntegerCylinder mixedModel.lo mixedModel.hi) ↔ _
    rw [mixed_linear_region_identity]
    constructor
    · rintro ⟨hp,⟨y,hy,he⟩⟩
      have hb := hy 0
      norm_num [mixedModel] at hb
      have hy0 : (0:ℤ)≤y 0 := by exact_mod_cast hb.1
      have hy1 : y 0≤(1:ℤ) := by exact_mod_cast hb.2
      have hor : y 0=0 ∨ y 0=1 := by omega
      refine ⟨hp,?_⟩
      rcases hor with h|h
      · left; simpa [h] using congrFun he 0
      · right; simpa [h] using congrFun he 0
    · rintro ⟨hp,hy⟩
      refine ⟨hp,?_⟩
      rcases hy with hy|hy
      · refine ⟨fun _ => 0,by intro i; norm_num [mixedModel],?_⟩
        ext i; fin_cases i; simpa using hy
      · refine ⟨fun _ => 1,by intro i; norm_num [mixedModel],?_⟩
        ext i; fin_cases i; simpa using hy
  have hc : IsClosed {p : Point 1 1 | p.2 0 = 0 ∨ p.2 0 = 1} :=
    (isClosed_eq (by fun_prop) continuous_const).union (isClosed_eq (by fun_prop) continuous_const)
  refine ⟨?_,?_,?_⟩
  · rw [heq]; exact mixed_domain_geometry.1.inter_right hc
  · rw [heq]; exact Set.inter_subset_left
  · rw [heq]
    exact ⟨(mixed_domain_geometry.2.2 _).mpr (by norm_num [mixedQ,mixedPoint]), by simp [mixedQ,mixedPoint]⟩

theorem mixed_actual_admissibility :
    AffineMap.lineMap mixedA mixedQ (1/2 : ℝ) = mixedZ ∧
    mixedA ∈ mixedDomain ∧
    (∀ j, mixedModel.g j mixedA < 0) ∧
    (∀ j, ContinuousOn (mixedDerivative j) mixedDomain) ∧
    (mixedQ,1/2) ∈ exteriorData mixedBase mixedModel.g mixedA 1 (0 : Fin 1) := by
  have hline : AffineMap.lineMap mixedA mixedQ (1/2 : ℝ)=mixedZ := by
    ext i <;> norm_num [AffineMap.lineMap_apply,mixedA,mixedQ,mixedZ,mixedPoint]
  refine ⟨hline,(mixed_domain_geometry.2.2 _).mpr (by norm_num [mixedA,mixedPoint]),
    ?_,?_,?_⟩
  · intro j; norm_num [mixedModel,mixedA,mixedPoint]
  · intro j; unfold mixedDerivative; fun_prop
  · refine ⟨mixed_base_compact.2.2,by norm_num,⟨0,by norm_num [mixedModel,mixedQ,mixedPoint]⟩,?_,?_⟩
    · intro j; simp [mixedModel]
    · rw [hline]; norm_num [mixedModel,mixedZ,mixedPoint]

theorem mixed_complete_tangent_values :
    mixedModel.g 0 mixedA = -1/4 ∧ mixedModel.g 0 mixedQ = 1 ∧
    mixedModel.g 0 mixedZ = 1/16 ∧
    exteriorTangent mixedModel.g mixedDerivative 0 mixedZ mixedQ = 11/16 ∧
    exteriorTangent mixedModel.g mixedDerivative 0 mixedZ (mixedPoint 0 0) = -13/16 ∧
    exteriorTangent mixedModel.g mixedDerivative 0 mixedZ (mixedPoint 0 1) = -5/16 := by
  norm_num [exteriorTangent,mixedModel,mixedA,mixedQ,mixedZ,mixedPoint,
    mixedDerivative,mixedX,mixedY]

theorem mixed_fractional_and_cut_region_control :
    mixedZ ∉ IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi ∧
    mixedModel.feasibleOn mixedDomain ⊆ exteriorMixedCuts.cutRegion mixedModel ∧
    mixedQ ∉ exteriorMixedCuts.cutRegion mixedModel ∧
    IsMinimizer (mixedModel.feasibleOn mixedDomain) mixedModel.objective (mixedPoint 0 0) ∧
    mixedPoint 0 0 ∈ exteriorMixedCuts.cutRegion mixedModel ∧
    mixedPoint 0 1 ∈ exteriorMixedCuts.cutRegion mixedModel := by
  have hp := exterior_pointwise mixed_domain_geometry.2.1 mixed_base_compact.2.1
    mixed_actual_admissibility.2.1 mixed_convex
    (fun j p _ => (mixed_actual_derivative j p).hasFDerivWithinAt)
    mixed_actual_admissibility.2.2.1 (show (0:ℝ)<1 by norm_num)
    mixed_actual_admissibility.2.2.2.2
  rw [mixed_actual_admissibility.1] at hp
  have ho : mixedModel.feasibleOn mixedDomain ⊆ exteriorMixedCuts.cutRegion mixedModel := by
    intro p hf i j hj
    fin_cases i; fin_cases j
    have hg := hp.2.2.2.1 p hf.1.1.1
    exact hg.trans (hf.1.1.2 0)
  refine ⟨?_,ho,?_,mixed_minimum_and_cut_exclusion.1,
    ho mixed_feasible_endpoints.1,ho mixed_feasible_endpoints.2.1⟩
  · rintro ⟨y,hy,he⟩
    have hyq : (y 0:ℝ)=3/4 := by simpa [mixedZ,mixedPoint] using (congrFun he 0).symm
    have h0 : (0:ℤ)<y 0 := by exact_mod_cast (show (0:ℝ)<y 0 by linarith)
    have h1 : y 0<(1:ℤ) := by exact_mod_cast (show (y 0:ℝ)<1 by linarith)
    omega
  · intro hq
    have hh := hq 0 0 (by simp [exteriorMixedCuts,cpDomainTangentFamily])
    change exteriorTangent mixedModel.g mixedDerivative 0 mixedZ mixedQ ≤ 0 at hh
    rw [mixed_complete_tangent_values.2.2.2.1] at hh
    norm_num at hh

theorem mixed_uniform_separation_control :
    ∃ delta > 0, ∀ j q t, (q,t) ∈ exteriorData mixedBase mixedModel.g mixedA 1 j →
      ∀ w, exteriorTangent mixedModel.g mixedDerivative j (AffineMap.lineMap mixedA q t) w ≤ 0 →
        delta ≤ dist q w := by
  exact exterior_uniform_separation mixed_base_compact.1 mixed_domain_geometry.2.1
    mixed_base_compact.2.1 mixed_convex
    (fun j p _ => (mixed_actual_derivative j p).hasFDerivWithinAt)
    mixed_actual_admissibility.2.2.2.1 mixed_actual_admissibility.2.1
    mixed_actual_admissibility.2.2.1 (by norm_num)

end Chapter02ExteriorTangentExamples

#print axioms Chapter02ExteriorTangentExamples.scalar_analytic_premises
#print axioms Chapter02ExteriorTangentExamples.scalar_admissible_iff
#print axioms Chapter02ExteriorTangentExamples.scalar_complete_tangent
#print axioms Chapter02ExteriorTangentExamples.scalar_endpoint_and_intercept_control
#print axioms Chapter02ExteriorTangentExamples.scalar_uniform_and_outside_control
#print axioms Chapter02ExteriorTangentExamples.nonmaximal_zero_row_control
#print axioms Chapter02ExteriorTangentExamples.zero_threshold_control
#print axioms Chapter02ExteriorTangentExamples.empty_and_nonviolating_data_control
#print axioms Chapter02ExteriorTangentExamples.empty_rows_uniform_control
#print axioms Chapter02ExteriorTangentExamples.mixed_linear_region_identity
#print axioms Chapter02ExteriorTangentExamples.mixed_base_compact
#print axioms Chapter02ExteriorTangentExamples.mixed_actual_admissibility
#print axioms Chapter02ExteriorTangentExamples.mixed_complete_tangent_values
#print axioms Chapter02ExteriorTangentExamples.mixed_fractional_and_cut_region_control
#print axioms Chapter02ExteriorTangentExamples.mixed_uniform_separation_control
