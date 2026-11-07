module

public import Mathlib

@[expose] public section

/-! Actual moving-base Clarke quotient and finite local Lipschitz bounds.
All declarations in this module are uncounted supporting obligations. -/

open Set Filter
open scoped Topology NNReal

namespace Chapter02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Independent nearby bases and strictly positive times approaching zero. -/
def clarkeFilter (x : E) : Filter (E × ℝ) :=
  (𝓝 x) ×ˢ (𝓝[>] (0 : ℝ))

/-- The real quotient is evaluated only at eventually strictly positive times. -/
noncomputable def clarkeQuotient (f : E → ℝ) (v : E) (p : E × ℝ) : ℝ :=
  (f (p.1 + p.2 • v) - f p.1) / p.2

/-- The extended-real limsup, without a totalized real supremum. -/
noncomputable def clarkeDirectional (f : E → ℝ) (x v : E) : EReal :=
  Filter.limsup (fun p => (clarkeQuotient f v p : EReal)) (clarkeFilter x)

/-- Actual all-direction domination by the quotient limsup. -/
def clarkeSubdifferential (f : E → ℝ) (x : E) : Set (E →L[ℝ] ℝ) :=
  {D | ∀ v, (D v : EReal) ≤ clarkeDirectional f x v}

/-- The source's all-ambient weak generalized-convexity law. -/
def ClarkeQuasiconvex (f : E → ℝ) : Prop :=
  LocallyLipschitz f ∧ ∀ x y, f y ≤ f x → clarkeDirectional f x (y - x) ≤ 0

/-- The separate strict law; no implication to the weak law is assumed. -/
def ClarkePseudoconvex (f : E → ℝ) : Prop :=
  LocallyLipschitz f ∧ ∀ x y, f y < f x → clarkeDirectional f x (y - x) < 0

instance clarkeFilter_neBot (x : E) : (clarkeFilter x).NeBot := by
  unfold clarkeFilter
  exact Filter.NeBot.prod (inferInstance : (𝓝 x).NeBot) (nhdsGT_neBot (0 : ℝ))

omit [NormedSpace ℝ E] in
theorem clarke_time_pos (x : E) : ∀ᶠ p in clarkeFilter x, 0 < p.2 := by
  exact tendsto_snd.eventually self_mem_nhdsWithin

omit [NormedSpace ℝ E] in
theorem clarke_base_tendsto (x : E) :
    Tendsto (fun p : E × ℝ => p.1) (clarkeFilter x) (𝓝 x) :=
  tendsto_fst

omit [NormedSpace ℝ E] in
theorem clarke_time_tendsto (x : E) :
    Tendsto (fun p : E × ℝ => p.2) (clarkeFilter x) (𝓝 (0 : ℝ)) :=
  tendsto_snd.mono_right nhdsWithin_le_nhds

theorem clarke_shift_tendsto (x v : E) :
    Tendsto (fun p : E × ℝ => p.1 + p.2 • v) (clarkeFilter x) (𝓝 x) := by
  simpa using (clarke_base_tendsto x).add ((clarke_time_tendsto x).smul tendsto_const_nhds)

/-- One neighborhood Lipschitz constant bounds all directional quotients eventually.
The neighborhood may depend on the direction, but the constant does not. -/
theorem clarke_quotient_local_bound {f : E → ℝ} {x : E} {K : ℝ≥0} {s : Set E}
    (hs : s ∈ 𝓝 x) (hf : LipschitzOnWith K f s) (v : E) :
    ∀ᶠ p in clarkeFilter x, |clarkeQuotient f v p| ≤ (K : ℝ) * ‖v‖ := by
  filter_upwards [clarke_time_pos x, (clarke_base_tendsto x).eventually hs,
    (clarke_shift_tendsto x v).eventually hs] with p hp hy hz
  have h := hf.dist_le_mul (p.1 + p.2 • v) hz p.1 hy
  rw [Real.dist_eq, dist_eq_norm] at h
  have hsub : p.1 + p.2 • v - p.1 = p.2 • v := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hp] at h
  rw [clarkeQuotient, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  nlinarith

theorem clarke_locallyLipschitz_quotient_bound {f : E → ℝ}
    (hf : LocallyLipschitz f) (x : E) :
    ∃ K : ℝ≥0, ∀ v, ∀ᶠ p in clarkeFilter x,
      |clarkeQuotient f v p| ≤ (K : ℝ) * ‖v‖ := by
  obtain ⟨K, s, hs, hK⟩ := hf x
  exact ⟨K, fun v => clarke_quotient_local_bound hs hK v⟩

/-- Finite lower and upper bounds are proved in EReal before any real conversion. -/
theorem clarke_directional_bounds {f : E → ℝ} {x v : E} {K : ℝ≥0}
    (h : ∀ᶠ p in clarkeFilter x, |clarkeQuotient f v p| ≤ (K : ℝ) * ‖v‖) :
    ((-(K : ℝ) * ‖v‖ : ℝ) : EReal) ≤ clarkeDirectional f x v ∧
      clarkeDirectional f x v ≤ (((K : ℝ) * ‖v‖ : ℝ) : EReal) := by
  have hlo : ∀ᶠ p in clarkeFilter x,
      ((-(K : ℝ) * ‖v‖ : ℝ) : EReal) ≤ (clarkeQuotient f v p : EReal) := by
    filter_upwards [h] with p hp
    exact EReal.coe_le_coe_iff.mpr (by nlinarith [abs_le.mp hp])
  have hhi : ∀ᶠ p in clarkeFilter x,
      (clarkeQuotient f v p : EReal) ≤ (((K : ℝ) * ‖v‖ : ℝ) : EReal) := by
    filter_upwards [h] with p hp
    exact EReal.coe_le_coe_iff.mpr (le_trans (le_abs_self _) hp)
  exact ⟨le_limsup_of_frequently_le hlo.frequently, limsup_le_of_le (by isBoundedDefault) hhi⟩

theorem clarke_directional_finite {f : E → ℝ} (hf : LocallyLipschitz f) (x v : E) :
    clarkeDirectional f x v ≠ ⊤ ∧ clarkeDirectional f x v ≠ ⊥ := by
  obtain ⟨K, hK⟩ := clarke_locallyLipschitz_quotient_bound hf x
  obtain ⟨hlo, hhi⟩ := clarke_directional_bounds (hK v)
  exact ⟨ne_of_lt (hhi.trans_lt (EReal.coe_lt_top _)),
    ne_of_gt ((EReal.bot_lt_coe _).trans_le hlo)⟩

/-- Conversion is explicitly guarded by actual local Lipschitzness. -/
noncomputable def clarkeDirectionalReal (f : E → ℝ) (_hf : LocallyLipschitz f)
    (x v : E) : ℝ := (clarkeDirectional f x v).toReal

theorem clarkeDirectionalReal_coe {f : E → ℝ} (hf : LocallyLipschitz f) (x v : E) :
    (clarkeDirectionalReal f hf x v : EReal) = clarkeDirectional f x v :=
  EReal.coe_toReal (clarke_directional_finite hf x v).1
    (clarke_directional_finite hf x v).2

theorem clarke_normal_le_zero {f : E → ℝ} {x y : E} {D : E →L[ℝ] ℝ}
    (h : ClarkeQuasiconvex f) (hD : D ∈ clarkeSubdifferential f x) (hxy : f y ≤ f x) :
    D (y - x) ≤ 0 := by
  have hb : (D (y - x) : EReal) ≤ 0 := (hD (y - x)).trans (h.2 x y hxy)
  exact EReal.coe_le_coe_iff.mp (by simpa using hb)

theorem clarke_normal_lt_zero {f : E → ℝ} {x y : E} {D : E →L[ℝ] ℝ}
    (h : ClarkePseudoconvex f) (hD : D ∈ clarkeSubdifferential f x) (hxy : f y < f x) :
    D (y - x) < 0 := by
  have hb : (D (y - x) : EReal) < 0 := (hD (y - x)).trans_lt (h.2 x y hxy)
  exact EReal.coe_lt_coe_iff.mp (by simpa using hb)

/-- A genuine quotient limit computes the defined Clarke limsup. -/
theorem clarkeDirectional_of_tendsto {f : E → ℝ} {x v : E} {a : ℝ}
    (h : Tendsto (clarkeQuotient f v) (clarkeFilter x) (𝓝 a)) :
    clarkeDirectional f x v = (a : EReal) :=
  (continuous_coe_real_ereal.continuousAt.tendsto.comp h).limsup_eq

end Chapter02

