module

public import Chapter02Clarke
public import Chapter02ClarkeESHSource
public import Chapter02ConvexSubgradientSource
public import Mathlib

@[expose] public section

/-! Complete nonsmooth mixed-model control. Supporting declarations are uncounted.
The quotient uses actual moving bases and positive time; no selected-normal oracle. -/
noncomputable section
open Set Filter Chapter02
open scoped Topology BigOperators
namespace Chapter02ClarkeESHExamples
abbrev P := Point 1 1
def point (x y : ℝ) : P := (fun _ => x, fun _ => y)
def coordX : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector 1))
def coordY : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ (RealVector 1) (RealVector 1))
def h (x : ℝ) : ℝ := x + x^3 + max 0 x
def g (p : P) : ℝ := h (coordX p)
def polyQ (x t v : ℝ) : ℝ := v * (1 + 3*x^2 + 3*x*t*v + t^2*v^2)

lemma coordX_point (x y : ℝ) : coordX (point x y) = x := rfl
lemma coordY_point (x y : ℝ) : coordY (point x y) = y := rfl
lemma point_decompose (p : P) : p = coordX p • point 1 0 + coordY p • point 0 1 := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> simp [point, coordX, coordY]

lemma h_strictMono : StrictMono h := by
  intro x y hxy
  have hc : x^3 < y^3 := (show Odd (3:ℕ) by decide).strictMono_pow hxy
  have hm : max (0:ℝ) x ≤ max 0 y := max_le_max_left 0 hxy.le
  unfold h
  linarith

lemma h_zero : h 0 = 0 := by norm_num [h]
lemma h_nonpos (x : ℝ) : h x ≤ 0 ↔ x ≤ 0 := by
  simpa only [h_zero] using (show h x ≤ h 0 ↔ x ≤ 0 from h_strictMono.le_iff_le)
lemma h_neg (x : ℝ) : h x < 0 ↔ x < 0 := by
  simpa only [h_zero] using (show h x < h 0 ↔ x < 0 from h_strictMono.lt_iff_lt)
lemma h_eq_zero (x : ℝ) : h x = 0 ↔ x = 0 := by
  simpa only [h_zero] using (show h x = h 0 ↔ x = 0 from h_strictMono.injective.eq_iff)

lemma g_locallyLipschitz : LocallyLipschitz g := by
  have hp : LocallyLipschitz (fun p : P => coordX p + (coordX p)^3) := by
    apply ContDiff.locallyLipschitz (𝕂 := ℝ)
    exact coordX.contDiff.add (coordX.contDiff.pow 3)
  have hr : LocallyLipschitz (fun p : P => max 0 (coordX p)) :=
    coordX.lipschitz.locallyLipschitz.const_max 0
  have ha : LocallyLipschitz (fun z : ℝ × ℝ => z.1 + z.2) := by
    apply ContDiff.locallyLipschitz (𝕂 := ℝ)
    fun_prop
  exact ha.comp (hp.prodMk hr)

lemma polynomial_quotient (x t v : ℝ) (ht : t ≠ 0) :
    ((x+t*v)+(x+t*v)^3-(x+x^3))/t = polyQ x t v := by
  apply (div_eq_iff ht).2
  unfold polyQ
  ring

lemma relu_quotient_upper (x t v : ℝ) (ht : 0 < t) :
    (max 0 (x+t*v)-max 0 x)/t ≤ max 0 v := by
  apply (div_le_iff₀ ht).2
  have h0 := le_max_left (0:ℝ) x
  have hx := le_max_right (0:ℝ) x
  have hv0 := le_max_left (0:ℝ) v
  have hv := le_max_right (0:ℝ) v
  have hm : max 0 (x+t*v) ≤ max 0 x + max 0 v * t := by
    apply max_le
    · nlinarith
    · nlinarith
  linarith

lemma actual_quotient (v : P) (p : P × ℝ) (ht : p.2 ≠ 0) :
    clarkeQuotient g v p = polyQ (coordX p.1) p.2 (coordX v) +
      (max 0 (coordX p.1+p.2*coordX v)-max 0 (coordX p.1))/p.2 := by
  simp only [clarkeQuotient,g,h,map_add,map_smul,smul_eq_mul]
  rw [← polynomial_quotient _ _ _ ht, ← add_div]
  congr 1
  ring

lemma polyQ_tendsto (x v : P) :
    Tendsto (fun p : P × ℝ => polyQ (coordX p.1) p.2 (coordX v))
      (clarkeFilter x) (𝓝 ((1+3*(coordX x)^2)*coordX v)) := by
  have hb := coordX.continuous.tendsto x |>.comp (clarke_base_tendsto x)
  have ht := clarke_time_tendsto x
  have hc : Continuous (fun p : ℝ × ℝ => polyQ p.1 p.2 (coordX v)) := by
    unfold polyQ; fun_prop
  have he : (1+3*(coordX x)^2)*coordX v = polyQ (coordX x) 0 (coordX v) := by
    unfold polyQ
    ring
  rw [he]
  simpa only [Function.comp_def] using hc.continuousAt.tendsto.comp (hb.prodMk_nhds ht)

lemma directional_negative (x v : P) (hx : coordX x < 0) :
    clarkeDirectional g x v = (((1+3*(coordX x)^2)*coordX v : ℝ) : EReal) := by
  apply clarkeDirectional_of_tendsto
  apply (polyQ_tendsto x v).congr'
  have hb := (coordX.continuous.tendsto x).comp (clarke_base_tendsto x)
  have hs := (coordX.continuous.tendsto x).comp (clarke_shift_tendsto x v)
  filter_upwards [clarke_time_pos x, hb.eventually (gt_mem_nhds hx),
    hs.eventually (gt_mem_nhds hx)] with p ht hb hs
  rw [actual_quotient v p ht.ne']
  have hs' : coordX p.1 + p.2 * coordX v < 0 := by simpa using hs
  change coordX p.1 < 0 at hb
  rw [max_eq_left hb.le,max_eq_left hs'.le]
  simp

lemma directional_positive (x v : P) (hx : 0 < coordX x) :
    clarkeDirectional g x v = (((2+3*(coordX x)^2)*coordX v : ℝ) : EReal) := by
  apply clarkeDirectional_of_tendsto
  have hp := (polyQ_tendsto x v).add_const (coordX v)
  have he : (1+3*(coordX x)^2)*coordX v + coordX v =
      (2+3*(coordX x)^2)*coordX v := by ring
  rw [he] at hp
  apply hp.congr'
  have hb := (coordX.continuous.tendsto x).comp (clarke_base_tendsto x)
  have hs := (coordX.continuous.tendsto x).comp (clarke_shift_tendsto x v)
  filter_upwards [clarke_time_pos x, hb.eventually (lt_mem_nhds hx),
    hs.eventually (lt_mem_nhds hx)] with p ht hb hs
  rw [actual_quotient v p ht.ne']
  have hs' : 0 < coordX p.1 + p.2 * coordX v := by simpa using hs
  change 0 < coordX p.1 at hb
  rw [max_eq_right hb.le,max_eq_right hs'.le]
  congr 1
  field_simp [ht.ne']
  ring

lemma fixed_base_limit_lower {f : P → ℝ} {x v : P} {a : ℝ}
    (hlim : Tendsto (fun t : ℝ => clarkeQuotient f v (x,t))
      (𝓝[>] (0:ℝ)) (𝓝 a)) : (a : EReal) ≤ clarkeDirectional f x v := by
  unfold clarkeDirectional
  have hp : Tendsto (fun t : ℝ => (x,t)) (𝓝[>] (0:ℝ)) (clarkeFilter x) :=
    tendsto_const_nhds.prodMk tendsto_id
  have hcoe := continuous_coe_real_ereal.continuousAt.tendsto.comp hlim
  rw [← hcoe.limsup_eq]
  simpa only [← limsup_comp, Function.comp_def] using
    (limsup_le_limsup_of_le hp (u := fun p => (clarkeQuotient f v p : EReal)))

lemma directional_zero (x v : P) (hx : coordX x = 0) :
    clarkeDirectional g x v = ((max (coordX v) (2*coordX v) : ℝ) : EReal) := by
  have hm : coordX v + max 0 (coordX v) = max (coordX v) (2*coordX v) := by
    by_cases hv : 0 ≤ coordX v
    · rw [max_eq_right hv,max_eq_right (by linarith)]; ring
    · rw [max_eq_left (le_of_not_ge hv),max_eq_left (by linarith)]; ring
  apply le_antisymm
  · have hu : ∀ᶠ p in clarkeFilter x, (clarkeQuotient g v p : EReal) ≤
        ((polyQ (coordX p.1) p.2 (coordX v) + max 0 (coordX v) : ℝ) : EReal) := by
      filter_upwards [clarke_time_pos x] with p ht
      apply EReal.coe_le_coe_iff.mpr
      rw [actual_quotient v p ht.ne']
      exact add_le_add_right (relu_quotient_upper _ _ _ ht) _
    have ht := (polyQ_tendsto x v).add_const (max 0 (coordX v))
    have he : (1+3*(coordX x)^2)*coordX v+max 0 (coordX v) =
        max (coordX v) (2*coordX v) := by simpa [hx] using hm
    rw [he] at ht
    exact (limsup_le_limsup hu).trans_eq
      (continuous_coe_real_ereal.continuousAt.tendsto.comp ht).limsup_eq
  · apply fixed_base_limit_lower
    have hc : Continuous (fun t : ℝ => polyQ 0 t (coordX v)+max 0 (coordX v)) := by
      unfold polyQ; fun_prop
    have ht : Tendsto (fun t : ℝ => polyQ 0 t (coordX v)+max 0 (coordX v))
        (𝓝[>] (0:ℝ)) (𝓝 (polyQ 0 0 (coordX v)+max 0 (coordX v))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have he : polyQ 0 0 (coordX v)+max 0 (coordX v) =
        max (coordX v) (2*coordX v) := by simpa [polyQ] using hm
    rw [he] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [actual_quotient v (x,t) ht.ne',hx]
    simp only [zero_add,max_self,sub_zero]
    have hmax : max 0 (t*coordX v) = t*max 0 (coordX v) := by
      rw [mul_max_of_nonneg _ _ ht.le,mul_zero]
    rw [hmax,mul_div_cancel_left₀ _ ht.ne']

lemma g_weak : ClarkeQuasiconvex g := by
  refine ⟨g_locallyLipschitz, ?_⟩
  intro x y hxy
  have hd : coordX (y-x) ≤ 0 := by
    rw [map_sub]
    exact sub_nonpos.mpr (h_strictMono.le_iff_le.mp hxy)
  rcases lt_trichotomy (coordX x) 0 with hx | hx | hx
  · rw [directional_negative x (y-x) hx]
    exact EReal.coe_le_coe_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hd)
  · rw [directional_zero x (y-x) hx]
    exact EReal.coe_le_coe_iff.mpr (max_le hd (by linarith))
  · rw [directional_positive x (y-x) hx]
    exact EReal.coe_le_coe_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hd)

lemma g_strict : ClarkePseudoconvex g := by
  refine ⟨g_locallyLipschitz, ?_⟩
  intro x y hxy
  have hd : coordX (y-x) < 0 := by
    rw [map_sub]
    exact sub_neg.mpr (h_strictMono.lt_iff_lt.mp hxy)
  rcases lt_trichotomy (coordX x) 0 with hx | hx | hx
  · rw [directional_negative x (y-x) hx]
    exact EReal.coe_lt_coe_iff.mpr (mul_neg_of_pos_of_neg (by positivity) hd)
  · rw [directional_zero x (y-x) hx]
    exact EReal.coe_lt_coe_iff.mpr (max_lt hd (by linarith))
  · rw [directional_positive x (y-x) hx]
    exact EReal.coe_lt_coe_iff.mpr (mul_neg_of_pos_of_neg (by positivity) hd)

lemma normal_interval (x : P) (hx : coordX x = 0) :
    clarkeSubdifferential g x = {D | ∃ θ : ℝ, 1 ≤ θ ∧ θ ≤ 2 ∧ D = θ • coordX} := by
  ext D
  constructor
  · intro hD
    have bound (v : P) : D v ≤ max (coordX v) (2*coordX v) := by
      have hb := hD v
      rw [directional_zero x v hx] at hb
      exact EReal.coe_le_coe_iff.mp hb
    have dy0 : D (point 0 1) = 0 := by
      have ha := bound (point 0 1)
      have hb := bound (-(point 0 1))
      simp only [map_neg,coordX_point] at ha hb
      norm_num at ha hb
      linarith
    refine ⟨D (point 1 0), ?_, ?_, ?_⟩
    · have hb := bound (-(point 1 0))
      simp only [map_neg,coordX_point] at hb
      norm_num at hb
      linarith
    · have hb := bound (point 1 0)
      norm_num [coordX_point] at hb
      exact hb
    · apply ContinuousLinearMap.ext
      intro v
      have he := congrArg D (point_decompose v)
      simpa [map_add,map_smul,dy0,mul_comm] using he
  · rintro ⟨θ,hl,hu,rfl⟩ v
    rw [directional_zero x v hx]
    apply EReal.coe_le_coe_iff.mpr
    change θ*coordX v ≤ max (coordX v) (2*coordX v)
    by_cases hv : 0 ≤ coordX v
    · exact (mul_le_mul_of_nonneg_right hu hv).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hl (le_of_not_ge hv)).trans (by simp)

lemma boundary_normals (x : P) (hx : g x = 0) :
    (clarkeSubdifferential g x).Nonempty ∧ 0 ∉ clarkeSubdifferential g x := by
  have hz : coordX x = 0 := (h_eq_zero _).mp hx
  rw [normal_interval x hz]
  constructor
  · exact ⟨coordX,1,by norm_num,by norm_num,by simp⟩
  · rintro ⟨θ,hθ,_,he⟩
    have hp := congrArg (fun D : P →L[ℝ] ℝ => D (point 1 0)) he
    simp [coordX_point] at hp
    linarith

lemma g_nondifferentiable (y : ℝ) : ¬ DifferentiableAt ℝ g (point 0 y) := by
  intro hd
  have hc : DifferentiableAt ℝ (fun t : ℝ => point t y) 0 := by
    unfold point; fun_prop
  have hh : DifferentiableAt ℝ h 0 := by
    simpa only [Function.comp_def,g,coordX_point] using hd.comp 0 hc
  have habs : (fun t : ℝ => 2*h t - 3*t - 2*t^3) = abs := by
    ext t
    unfold h
    by_cases ht : 0 ≤ t
    · rw [max_eq_right ht,abs_of_nonneg ht]; ring
    · rw [max_eq_left (le_of_not_ge ht),abs_of_neg (lt_of_not_ge ht)]; ring
  apply not_differentiableAt_abs_zero
  rw [← habs]
  exact ((hh.const_mul 2).sub (differentiableAt_id.const_mul 3)).sub
    ((differentiableAt_id.pow 3).const_mul 2)

lemma g_nonconvex : ¬ ConvexOn ℝ Set.univ g := by
  intro hc
  have hb := hc.2 (Set.mem_univ (point (-1) 0)) (Set.mem_univ (point 0 0))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  norm_num [g,h,coordX,point] at hb

def model : ModelData 1 1 1 4 where
  g := fun _ => g
  A := ![fun _ => -1, fun _ => 1, fun _ => 0, fun _ => 0]
  B := ![fun _ => 0, fun _ => 0, fun _ => -1, fun _ => 1]
  rhs := ![1,1,0,1]
  c1 := fun _ => -1
  c2 := fun _ => 1
  lo := fun _ => 0
  hi := fun _ => 1

def mixedRow (_ : Fin 1) (x : RealVector 1) (_ : IntVector 1) := h (x 0)
def sourceSet := sourceMixedFeasible model mixedRow Set.univ
def baseSet : Set P := {p | -1 ≤ coordX p ∧ coordX p ≤ 1 ∧ (coordY p = 0 ∨ coordY p = 1)}
def feasibleSet : Set P := {p | -1 ≤ coordX p ∧ coordX p ≤ 0 ∧ (coordY p = 0 ∨ coordY p = 1)}
def initializer := point (-1) (1/2)
def trial0 := point 1 0
def root0 := point 0 (1/4)
def trial1 := point 0 0

lemma coordinates_ext {p q : P} (hx : coordX p = coordX q) (hy : coordY p = coordY q) : p = q := by
  apply Prod.ext <;> ext i <;> fin_cases i
  · exact hx
  · exact hy

lemma linear_mem (p : P) : p ∈ model.linearRegion ↔
    -1 ≤ coordX p ∧ coordX p ≤ 1 ∧ 0 ≤ coordY p ∧ coordY p ≤ 1 := by
  simp [ModelData.linearRegion,LinearForm,model,Fin.sum_univ_one,
    Fin.forall_fin_succ,coordX,coordY]
  intro _ _ _
  constructor <;> intro hh <;> linarith

lemma linear_interval : model.linearRegion = Set.Icc (point (-1) 0) (point 1 1) := by
  ext p
  rw [linear_mem]
  simp only [Set.mem_Icc,Prod.le_def,Pi.le_def,Fin.forall_fin_one,point]
  change (-1 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1) ↔ _
  tauto

lemma linear_compact : IsCompact model.linearRegion := by
  rw [linear_interval]
  exact isCompact_Icc

lemma integer_iff (p : P) : p ∈ IntegerCylinder (n := 1) model.lo model.hi ↔
    coordY p = 0 ∨ coordY p = 1 := by
  constructor
  · rintro ⟨y,hy,hp⟩
    have hb := hy 0
    change (0:ℝ) ≤ (y 0:ℝ) ∧ (y 0:ℝ) ≤ 1 at hb
    have hb' : (0:ℤ) ≤ y 0 ∧ y 0 ≤ 1 := by exact_mod_cast hb
    have he : y 0 = 0 ∨ y 0 = 1 := by omega
    have hp' : coordY p = (y 0:ℝ) := congrFun hp 0
    rcases he with he | he <;> simp [hp',he]
  · intro hp
    rcases hp with hp | hp
    · refine ⟨fun _ => (0:ℤ),?_,?_⟩
      · intro i; norm_num [model]
      · ext i; fin_cases i; simpa [coordY] using hp
    · refine ⟨fun _ => (1:ℤ),?_,?_⟩
      · intro i; norm_num [model]
      · ext i; fin_cases i; simpa [coordY] using hp

lemma base_identity : model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi = baseSet := by
  ext p
  simp only [Set.mem_inter_iff,linear_mem,integer_iff,baseSet,Set.mem_setOf_eq]
  constructor
  · exact fun hp => ⟨hp.1.1,hp.1.2.1,hp.2⟩
  · rintro ⟨hl,hu,hy⟩
    refine ⟨⟨hl,hu,?_,?_⟩,hy⟩ <;> rcases hy with hy | hy <;> rw [hy] <;> norm_num

lemma objective (p : P) : model.objective p = -coordX p + coordY p := by
  simp [ModelData.objective,LinearForm,model,Fin.sum_univ_one,coordX,coordY]

lemma feasible_identity : model.feasibleOn Set.univ = feasibleSet := by
  ext p
  rw [source_feasible_iff]
  change (p ∈ Set.univ ∧ (∀ j : Fin 1, g p ≤ 0) ∧ p ∈ model.linearRegion ∧
    p ∈ IntegerCylinder (n := 1) model.lo model.hi) ↔ _
  simp only [Set.mem_univ,Fin.forall_fin_one,true_and,linear_mem,integer_iff,
    feasibleSet,Set.mem_setOf_eq,g,h_nonpos]
  constructor
  · exact fun hp => ⟨hp.2.1.1,hp.1,hp.2.2⟩
  · rintro ⟨hl,hu,hy⟩
    refine ⟨hu,⟨hl,by linarith,?_,?_⟩,hy⟩ <;>
      rcases hy with hy | hy <;> rw [hy] <;> norm_num

lemma source_identity : sourceSet = model.feasibleOn Set.univ := by
  ext p
  rw [source_feasible_iff]
  simp only [sourceSet,sourceMixedFeasible,Set.mem_setOf_eq,Set.mem_univ,true_and]
  constructor
  · rintro ⟨hL,y,hy,he,hg⟩
    exact ⟨hg,hL,y,hy,he⟩
  · rintro ⟨hg,hL,y,hy,he⟩
    exact ⟨hL,y,hy,he,hg⟩

lemma source_bounds (p : P) (hp : p ∈ model.linearRegion) (i : Fin 1) :
    model.lo i ≤ p.2 i ∧ p.2 i ≤ model.hi i := by
  fin_cases i
  exact ⟨((linear_mem p).mp hp).2.2.1,((linear_mem p).mp hp).2.2.2⟩

lemma initializer_facts : initializer ∈ model.linearRegion ∧ g initializer < 0 ∧
    initializer ∉ IntegerCylinder (n := 1) model.lo model.hi := by
  rw [linear_mem,integer_iff]
  norm_num [initializer,point,coordX,coordY,g,h]

lemma feasible_nonempty : (model.feasibleOn Set.univ).Nonempty := by
  rw [feasible_identity]
  exact ⟨trial1,by norm_num [feasibleSet,trial1,point,coordX,coordY]⟩

lemma base_unique_minimum : IsMinimizer baseSet model.objective trial0 ∧
    ∀ p, IsMinimizer baseSet model.objective p → p = trial0 := by
  have h0 : IsMinimizer baseSet model.objective trial0 := by
    refine ⟨by norm_num [baseSet,trial0,point,coordX,coordY],?_⟩
    intro p hp
    rw [objective,objective]
    rcases hp with ⟨hl,hu,hy⟩
    change -(1:ℝ)+0 ≤ -coordX p+coordY p
    rcases hy with hy | hy <;> rw [hy] <;> linarith
  refine ⟨h0,?_⟩
  intro p hp
  have ho := hp.2 trial0 h0.1
  rw [objective,objective] at ho
  rcases hp.1 with ⟨hl,hu,hy⟩
  change -coordX p+coordY p ≤ -(1:ℝ)+0 at ho
  apply coordinates_ext
  · change coordX p = 1
    rcases hy with hy | hy <;> rw [hy] at ho <;> linarith
  · change coordY p = 0
    rcases hy with hy | hy
    · exact hy
    · rw [hy] at ho; linarith

lemma feasible_unique_minimum : IsMinimizer feasibleSet model.objective trial1 ∧
    ∀ p, IsMinimizer feasibleSet model.objective p → p = trial1 := by
  have h0 : IsMinimizer feasibleSet model.objective trial1 := by
    refine ⟨by norm_num [feasibleSet,trial1,point,coordX,coordY],?_⟩
    intro p hp
    rw [objective,objective]
    rcases hp with ⟨hl,hu,hy⟩
    change -(0:ℝ)+0 ≤ -coordX p+coordY p
    rcases hy with hy | hy <;> rw [hy] <;> linarith
  refine ⟨h0,?_⟩
  intro p hp
  have ho := hp.2 trial1 h0.1
  rw [objective,objective] at ho
  rcases hp.1 with ⟨hl,hu,hy⟩
  change -coordX p+coordY p ≤ -(0:ℝ)+0 at ho
  apply coordinates_ext
  · change coordX p = 0
    rcases hy with hy | hy <;> rw [hy] at ho <;> linarith
  · change coordY p = 0
    rcases hy with hy | hy
    · exact hy
    · rw [hy] at ho; linarith

lemma root_exact : AffineMap.lineMap initializer trial0 (1/2:ℝ) = root0 ∧
    g root0 = 0 := by
  constructor
  · apply coordinates_ext <;> norm_num [AffineMap.lineMap_apply,initializer,trial0,root0,point,coordX,coordY]
  · norm_num [g,h,root0,point,coordX]

lemma every_normal_same_cut (D : P →L[ℝ] ℝ) (hD : D ∈ clarkeSubdifferential g root0) :
    {p | D (p-root0) ≤ 0} = {p | coordX p ≤ 0} := by
  rw [normal_interval root0 (by rfl)] at hD
  obtain ⟨θ,hθ,_,rfl⟩ := hD
  ext p
  change θ*coordX (p-root0) ≤ 0 ↔ coordX p ≤ 0
  simp only [map_sub,show coordX root0 = 0 from rfl,sub_zero]
  constructor
  · intro hh
    by_contra hn
    have := mul_pos (by linarith : 0 < θ) (lt_of_not_ge hn)
    linarith
  · intro hh
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hh

lemma second_master_identity (D : P →L[ℝ] ℝ) (hD : D ∈ clarkeSubdifferential g root0) :
    {p ∈ baseSet | D (p-root0) ≤ 0} = feasibleSet := by
  have hc := every_normal_same_cut D hD
  ext p
  have he : D (p-root0) ≤ 0 ↔ coordX p ≤ 0 := Set.ext_iff.mp hc p
  simp only [Set.mem_setOf_eq,baseSet,feasibleSet,he]
  constructor
  · exact fun hp => ⟨hp.1.1,hp.2,hp.1.2.2⟩
  · exact fun hp => ⟨⟨hp.1,by linarith [hp.2.1],hp.2.2⟩,hp.2.1⟩

lemma base_compact : IsCompact baseSet := by
  have hY : IsClosed {p : P | coordY p = 0 ∨ coordY p = 1} :=
    (isClosed_eq coordY.continuous continuous_const).union
      (isClosed_eq coordY.continuous continuous_const)
  have he : baseSet = model.linearRegion ∩ {p : P | coordY p = 0 ∨ coordY p = 1} := by
    rw [← base_identity]
    ext p
    simp [integer_iff]
  rw [he]
  exact linear_compact.inter_right hY

lemma base_subset_linear : baseSet ⊆ model.linearRegion := by
  rw [← base_identity]
  exact Set.inter_subset_left

lemma root_unique (t : ℝ) (ht : g (AffineMap.lineMap initializer trial0 t) = 0) :
    t = 1/2 := by
  have hx := (h_eq_zero _).mp ht
  norm_num [AffineMap.lineMap_apply,initializer,trial0,point,coordX] at hx
  linarith

lemma extension_agreement : ∀ j x y,
    model.g j (x,fun i => (y i:ℝ)) = mixedRow j x y := by
  intros; rfl

def originalFeasible : Set P := {p | p ∈ model.linearRegion ∧
  ∃ y : IntVector 1, p.2 = (fun i => (y i:ℝ)) ∧ ∀ j, mixedRow j p.1 y ≤ 0}

lemma original_source_identity : originalFeasible = sourceSet := by
  ext p
  constructor
  · rintro ⟨hL,y,he,hg⟩
    refine ⟨Set.mem_univ p,hL,y,?_,he,hg⟩
    intro i
    have hb := source_bounds p hL i
    simpa only [he] using hb
  · rintro ⟨_,hL,y,_,he,hg⟩
    exact ⟨hL,y,he,hg⟩

lemma objective_values : model.objective trial0 = -1 ∧ model.objective trial1 = 0 := by
  norm_num [objective,trial0,trial1,coordX,coordY,point]

-- The following application is compiled only against released source API bytes.
def firstBatch (D : P →L[ℝ] ℝ) : ClarkeESHBatch P (Fin 1) :=
  ⟨trial0,1/2,0,D⟩

lemma first_batch_origin (D : P →L[ℝ] ℝ) : (firstBatch D).origin initializer = root0 :=
  root_exact.1

lemma empty_master : clarkeESHMaster baseSet initializer ([] : List (ClarkeESHBatch P (Fin 1))) = baseSet := by
  ext p
  simp [clarkeESHMaster]

lemma batch_master (D : P →L[ℝ] ℝ) (hD : D ∈ clarkeSubdifferential g root0) :
    clarkeESHMaster baseSet initializer [firstBatch D] = feasibleSet := by
  rw [← second_master_identity D hD]
  ext p
  simp only [clarkeESHMaster,Set.mem_setOf_eq,List.mem_singleton,forall_eq]
  rw [first_batch_origin]
  rfl

lemma first_step (D : P →L[ℝ] ℝ) (hD : D ∈ clarkeSubdifferential g root0) :
    ClarkeESHStep baseSet model.objective model.g initializer [] (firstBatch D) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [empty_master]
    exact base_unique_minimum.1
  · exact ⟨0,by norm_num [firstBatch,model,g,h,trial0,point,coordX]⟩
  · norm_num [firstBatch]
  · intro j
    simpa only [first_batch_origin,model,root_exact.2] using (le_refl (0:ℝ))
  · simpa only [first_batch_origin,model] using root_exact.2
  · change D ∈ clarkeSubdifferential g ((firstBatch D).origin initializer)
    rw [first_batch_origin]
    exact hD
  · intro he
    exact (boundary_normals root0 root_exact.2).2 (he ▸ hD)

lemma after_one_stop (D : P →L[ℝ] ℝ) (hD : D ∈ clarkeSubdifferential g root0) :
    ClarkeESHStop baseSet model.objective model.g initializer [firstBatch D] (some trial1) := by
  change IsMinimizer (clarkeESHMaster baseSet initializer [firstBatch D]) model.objective trial1 ∧ _
  rw [batch_master D hD]
  exact ⟨feasible_unique_minimum.1,by intro j; norm_num [model,g,h,trial1,point,coordX]⟩

lemma selector_exists : Nonempty (ClarkeESHSelector baseSet model.objective model.g initializer) := by
  apply clarke_esh_selector_exists base_compact base_subset_linear (source_linearRegion_convex model)
    (linearForm_continuous model.c1 model.c2) (fun _ => g_locallyLipschitz.continuous)
    initializer_facts.1 (fun _ => initializer_facts.2.1)
  intro z _ _ j hj
  exact boundary_normals z hj

lemma initial_step_exact (b : ClarkeESHBatch P (Fin 1))
    (hb : ClarkeESHStep baseSet model.objective model.g initializer [] b) :
    b.trial = trial0 ∧ b.parameter = 1/2 ∧ b.origin initializer = root0 ∧
      b.normal ∈ clarkeSubdifferential g root0 ∧
      clarkeESHMaster baseSet initializer [b] = feasibleSet := by
  have hm := hb.1
  rw [empty_master] at hm
  have hq := base_unique_minimum.2 b.trial hm
  have ht : b.parameter = 1/2 := by
    apply root_unique
    simpa only [ClarkeESHBatch.origin,hq,model] using hb.2.2.2.2.1
  have hz : b.origin initializer = root0 := by
    simpa only [ClarkeESHBatch.origin,hq,ht] using root_exact.1
  have hn : b.normal ∈ clarkeSubdifferential g root0 := by
    simpa only [model,hz] using hb.2.2.2.2.2.1
  refine ⟨hq,ht,hz,hn,?_⟩
  rw [← second_master_identity b.normal hn]
  ext p
  simp [clarkeESHMaster,hz]

lemma initial_stop_impossible (out : Option P) :
    ¬ ClarkeESHStop baseSet model.objective model.g initializer [] out := by
  intro hs
  cases out with
  | none =>
    change clarkeESHMaster baseSet initializer [] = ∅ at hs
    rw [empty_master] at hs
    have hp := base_unique_minimum.1.1
    rw [hs] at hp
    exact hp.elim
  | some q =>
    change IsMinimizer (clarkeESHMaster baseSet initializer []) model.objective q ∧ _ at hs
    rw [empty_master] at hs
    have he := base_unique_minimum.2 q hs.1
    have hg := hs.2 0
    norm_num [he,model,g,h,trial0,point,coordX] at hg

lemma final_decision (H : List (ClarkeESHBatch P (Fin 1)))
    (hm : clarkeESHMaster baseSet initializer H = feasibleSet)
    (c : Option P ⊕ ClarkeESHBatch P (Fin 1))
    (hc : ClarkeESHDecisionLegal baseSet model.objective model.g initializer H c) :
    c = .inl (some trial1) := by
  cases c with
  | inl out =>
    cases out with
    | none =>
      change clarkeESHMaster baseSet initializer H = ∅ at hc
      have hp := feasible_unique_minimum.1.1
      rw [← hm,hc] at hp
      exact hp.elim
    | some q =>
      change IsMinimizer (clarkeESHMaster baseSet initializer H) model.objective q ∧ _ at hc
      rw [hm] at hc
      rw [feasible_unique_minimum.2 q hc.1]
  | inr b =>
    change ClarkeESHStep baseSet model.objective model.g initializer H b at hc
    have hmin := hc.1
    rw [hm] at hmin
    have he := feasible_unique_minimum.2 b.trial hmin
    obtain ⟨j,hj⟩ := hc.2.1
    norm_num [he,model,g,h,trial1,point,coordX] at hj

lemma all_selectors_stop_two
    (choose : ClarkeESHSelector baseSet model.objective model.g initializer) :
    ∃ b : ClarkeESHBatch P (Fin 1),
      b.trial = trial0 ∧ b.parameter = 1/2 ∧ b.origin initializer = root0 ∧
      b.normal ∈ clarkeSubdifferential g root0 ∧
      clarkeESHMaster baseSet initializer [b] = feasibleSet ∧
      clarkeESHRun baseSet model.objective model.g initializer choose 1 = .active [b] ∧
      clarkeESHRun baseSet model.objective model.g initializer choose 2 = .stopped [b] (some trial1) := by
  have hc := (choose []).property
  cases he : (choose []).val with
  | inl out =>
    simp only [he,ClarkeESHDecisionLegal] at hc
    exact (initial_stop_impossible out hc).elim
  | inr b =>
    simp only [he,ClarkeESHDecisionLegal] at hc
    obtain ⟨hq,ht,hz,hn,hm⟩ := initial_step_exact b hc
    have hnext := final_decision [b] hm (choose [b]).val (choose [b]).property
    refine ⟨b,hq,ht,hz,hn,hm,?_,?_⟩
    · simp [clarkeESHRun,he]
    · simp [clarkeESHRun,he,hnext]

lemma original_optimum : IsMinimizer originalFeasible model.objective trial1 := by
  rw [original_source_identity,source_identity,feasible_identity]
  exact feasible_unique_minimum.1

lemma source_procedure_instantiated :
    clarkeESHOriginalFeasible model mixedRow = feasibleSet ∧
    Nonempty (ClarkeESHSelector (cpBase model) model.objective model.g initializer) ∧
    ∀ choose : ClarkeESHSelector (cpBase model) model.objective model.g initializer,
      ClarkeESHSourceDichotomy model mixedRow initializer choose := by
  have hn : ClarkeESHNormals model.linearRegion model.g := by
    intro z _ _ j hj
    exact boundary_normals z hj
  obtain ⟨_,ho,hs,_,_,_,hchoose,hall⟩ := source_clarke_esh_zero_procedure model mixedRow
    initializer extension_agreement linear_compact source_bounds (fun _ => g_weak)
    initializer_facts.1 (fun _ => initializer_facts.2.1) feasible_nonempty hn
  refine ⟨?_,hchoose,hall⟩
  exact ho.trans (hs.trans feasible_identity)

/-- Full actual nonsmooth control, including original source transport, every
allowed root normal, complete master minima and the real recursively generated
procedure. Every legal selector stops after two decisions; no infinite example
is asserted. This is the only counted endpoint of the module. -/
theorem nonsmooth_mixed_model_control :
    LocallyLipschitz g ∧ ClarkeQuasiconvex g ∧ ClarkePseudoconvex g ∧
    (∀ x v, coordX x < 0 → clarkeDirectional g x v =
      (((1+3*(coordX x)^2)*coordX v : ℝ) : EReal)) ∧
    (∀ x v, coordX x = 0 → clarkeDirectional g x v =
      ((max (coordX v) (2*coordX v) : ℝ) : EReal)) ∧
    (∀ x v, 0 < coordX x → clarkeDirectional g x v =
      (((2+3*(coordX x)^2)*coordX v : ℝ) : EReal)) ∧
    (∀ x, coordX x = 0 → clarkeSubdifferential g x =
      {D | ∃ θ : ℝ, 1 ≤ θ ∧ θ ≤ 2 ∧ D = θ • coordX}) ∧
    (∀ x, g x = 0 → (clarkeSubdifferential g x).Nonempty ∧ 0 ∉ clarkeSubdifferential g x) ∧
    (∀ y, ¬ DifferentiableAt ℝ g (point 0 y)) ∧ ¬ ConvexOn ℝ Set.univ g ∧
    model.linearRegion = Set.Icc (point (-1) 0) (point 1 1) ∧ IsCompact model.linearRegion ∧
    cpBase model = baseSet ∧
    originalFeasible = sourceSet ∧ sourceSet = model.feasibleOn Set.univ ∧
    model.feasibleOn Set.univ = feasibleSet ∧
    (∀ j x y, model.g j (x,fun i => (y i:ℝ)) = mixedRow j x y) ∧
    (∀ p ∈ model.linearRegion, ∀ i, model.lo i ≤ p.2 i ∧ p.2 i ≤ model.hi i) ∧
    initializer ∈ model.linearRegion ∧ g initializer < 0 ∧
    initializer ∉ IntegerCylinder (n := 1) model.lo model.hi ∧
    (model.feasibleOn Set.univ).Nonempty ∧
    model.objective trial0 = -1 ∧ model.objective trial1 = 0 ∧
    clarkeESHMaster baseSet initializer ([] : List (ClarkeESHBatch P (Fin 1))) = baseSet ∧
    IsMinimizer baseSet model.objective trial0 ∧
    (∀ p, IsMinimizer baseSet model.objective p → p = trial0) ∧
    IsMinimizer feasibleSet model.objective trial1 ∧
    (∀ p, IsMinimizer feasibleSet model.objective p → p = trial1) ∧
    IsMinimizer originalFeasible model.objective trial1 ∧
    AffineMap.lineMap initializer trial0 (1/2:ℝ) = root0 ∧ g root0 = 0 ∧
    (∀ D ∈ clarkeSubdifferential g root0,
      {p | D (p-root0) ≤ 0} = {p | coordX p ≤ 0} ∧
      clarkeESHMaster baseSet initializer [firstBatch D] = feasibleSet ∧
      ClarkeESHStep baseSet model.objective model.g initializer [] (firstBatch D) ∧
      ClarkeESHStop baseSet model.objective model.g initializer [firstBatch D] (some trial1)) ∧
    clarkeESHOriginalFeasible model mixedRow = feasibleSet ∧
    Nonempty (ClarkeESHSelector (cpBase model) model.objective model.g initializer) ∧
    (∀ choose : ClarkeESHSelector (cpBase model) model.objective model.g initializer,
      ClarkeESHSourceDichotomy model mixedRow initializer choose) ∧
    Nonempty (ClarkeESHSelector baseSet model.objective model.g initializer) ∧
    ∀ choose : ClarkeESHSelector baseSet model.objective model.g initializer,
      ∃ b : ClarkeESHBatch P (Fin 1),
        b.trial = trial0 ∧ b.parameter = 1/2 ∧ b.origin initializer = root0 ∧
        b.normal ∈ clarkeSubdifferential g root0 ∧
        clarkeESHMaster baseSet initializer [b] = feasibleSet ∧
        clarkeESHRun baseSet model.objective model.g initializer choose 1 = .active [b] ∧
        clarkeESHRun baseSet model.objective model.g initializer choose 2 = .stopped [b] (some trial1) := by
  exact ⟨g_locallyLipschitz,g_weak,g_strict,directional_negative,directional_zero,
    directional_positive,normal_interval,boundary_normals,g_nondifferentiable,g_nonconvex,
    linear_interval,linear_compact,base_identity,original_source_identity,source_identity,feasible_identity,
    extension_agreement,source_bounds,initializer_facts.1,initializer_facts.2.1,
    initializer_facts.2.2,feasible_nonempty,objective_values.1,objective_values.2,
    empty_master,base_unique_minimum.1,base_unique_minimum.2,
    feasible_unique_minimum.1,feasible_unique_minimum.2,original_optimum,
    root_exact.1,root_exact.2,
    (fun D hD => ⟨every_normal_same_cut D hD,batch_master D hD,first_step D hD,after_one_stop D hD⟩),
    source_procedure_instantiated.1,source_procedure_instantiated.2.1,
    source_procedure_instantiated.2.2,selector_exists,all_selectors_stop_two⟩

end Chapter02ClarkeESHExamples
#print axioms Chapter02ClarkeESHExamples.nonsmooth_mixed_model_control
