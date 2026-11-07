/-
Compatibility definitions copied from Mathlib: Copyright (c) 2019 Sébastien Gouëzel,
released under Apache 2.0 as described in the upstream LICENSE.
The new proofs are local toolchain-migration glue, not additional thesis claims.
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Seq
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

open Filter Set
open scoped Topology

namespace MigrationCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact body of the positive tangent-cone definition at the frozen4.19 baseline. -/
def legacyPosTangentConeAt (s : Set E) (x : E) : Set E :=
  { y : E | ∃ (c : ℕ → ℝ) (d : ℕ → E), (∀ᶠ n in atTop, x + d n ∈ s) ∧
    Tendsto c atTop atTop ∧ Tendsto (fun n => c n • d n) atTop (𝓝 y) }

/-- Exact body of the general tangent-cone definition at the frozen4.19 baseline,
instantiated under its actually reached real normed-space hypotheses. -/
def legacyRealTangentConeAt (s : Set E) (x : E) : Set E :=
  { y : E | ∃ (c : ℕ → ℝ) (d : ℕ → E),
    (∀ᶠ n in atTop, x + d n ∈ s) ∧
    Tendsto (fun n => ‖c n‖) atTop atTop ∧
    Tendsto (fun n => c n • d n) atTop (𝓝 y) }

/-- The official modern theorem explicitly characterizes the old general definition. -/
theorem legacyRealTangentConeAt_eq (s : Set E) (x : E) :
    legacyRealTangentConeAt s x = tangentConeAt ℝ s x := by
  ext y
  rw [mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop]
  constructor
  · rintro ⟨c, d, hds, hc, hcd⟩
    exact ⟨c, d, hc, hds, hcd⟩
  · rintro ⟨c, d, hc, hds, hcd⟩
    exact ⟨c, d, hds, hc, hcd⟩

/-- Positive scaling-to-infinity and the modern NNReal filter cone agree for arbitrary
sets/basepoints in a real normed space; no closedness/convexity/completeness is added. -/
theorem legacyPosTangentConeAt_eq (s : Set E) (x : E) :
    legacyPosTangentConeAt s x = posTangentConeAt s x := by
  ext y
  constructor
  · rintro ⟨c, d, hds, hc, hcd⟩
    have hcn : Tendsto (fun n => ‖c n‖) atTop atTop := by
      simpa only [Real.norm_eq_abs, Function.comp_def] using tendsto_abs_atTop_atTop.comp hc
    have hd0 : Tendsto d atTop (𝓝 0) := tangentConeAt.lim_zero atTop hcn hcd
    refine mem_tangentConeAt_of_seq atTop (fun n => (c n).toNNReal) d hd0 hds ?_
    apply hcd.congr'
    filter_upwards [hc.eventually_ge_atTop 0] with n hn
    simp only [NNReal.smul_def, Real.coe_toNNReal _ hn]
  · intro hy
    rcases eq_or_ne y 0 with rfl | hy0
    · have hx : x ∈ closure s := zero_mem_tangentConeAt_iff.mp hy
      have hg : (0 : E) ∈ tangentConeAt ℝ s x := zero_mem_tangentConeAt_iff.mpr hx
      obtain ⟨c, d, hc, hds, hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hg
      refine ⟨fun n => ‖c n‖, d, hds, hc, ?_⟩
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [norm_smul, norm_norm, norm_zero] using hcd.norm
    · obtain ⟨c, d, hd0, hds, hcd⟩ := mem_tangentConeAt_iff_exists_seq.mp hy
      have hcdR : Tendsto (fun n => (c n : ℝ) • d n) atTop (𝓝 y) := by
        simpa only [NNReal.smul_def] using hcd
      have hcNorm : Tendsto (fun n => ‖(c n : ℝ)‖) atTop atTop := by
        have hd0' : ∀ᶠ n in atTop, d n ≠ 0 :=
          hcdR.eventually_ne hy0 |>.mono fun _ => right_ne_zero_of_smul
        have hdnorm := hd0.norm
        have hcdnorm := hcdR.norm
        simp only [norm_smul, norm_zero, ← div_inv_eq_mul] at hdnorm hcdnorm
        refine .num ?_ (norm_pos_iff.mpr hy0) hcdnorm
        rw [← inv_nhdsGT_zero (𝕜 := ℝ), ← Filter.comap_inv, Filter.tendsto_comap_iff]
        simpa [Function.comp_def, tendsto_nhdsWithin_iff, hdnorm] using hd0'
      have hcR : Tendsto (fun n => (c n : ℝ)) atTop atTop := by
        convert hcNorm using 1
        funext n
        exact (Real.norm_of_nonneg (c n).coe_nonneg).symm
      exact ⟨(fun n => (c n : ℝ)), d, hds, hcR, hcdR⟩

end MigrationCone

#print axioms MigrationCone.legacyRealTangentConeAt_eq
#print axioms MigrationCone.legacyPosTangentConeAt_eq
