module

public import Chapter02FBBTOperator
public import Chapter02FBBTPreservation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Actual simultaneous two-row recurrence, kept distinct from the source's
sequential exponents. Candidate controls; generic theorem application follows. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02FBBT
namespace Chapter02FBBTControls

private lemma seededMax_two (s : ℝ) (v : Fin 2 → ℝ) :
    seededMax s v = max s (max (v 0) (v 1)) := by
  have h : (Finset.univ : Finset (Option (Fin 2))) = {none, some 0, some 1} := by decide
  simp [seededMax, h, Finset.sup'_insert, Finset.sup'_singleton]

private lemma seededMin_two (s : ℝ) (v : Fin 2 → ℝ) :
    seededMin s v = min s (min (v 0) (v 1)) := by
  have h : (Finset.univ : Finset (Option (Fin 2))) = {none, some 0, some 1} := by decide
  simp [seededMin, h, Finset.inf'_insert, Finset.inf'_singleton]

def contractionMatrix (a : ℝ) : Chapter02FBBT.Matrix 2 2 := ![![a,-1],![1,-a]]

def contractionBox (t : ℝ) : JointBounds 2 2 :=
  (Sum.elim (fun _ => 0) (fun _ => 0), Sum.elim (fun _ => t) (fun _ => 0))

lemma contraction_box_ordered {t : ℝ} (ht : 0 ≤ t) : Ordered (contractionBox t) := by
  intro i
  cases i with
  | inl j => exact ht
  | inr j => exact le_rfl

lemma contraction_upward (a t : ℝ) (ha : 1 < a) (ht : 0 ≤ t) :
    upward (contractionMatrix a) (contractionBox t) = contractionBox t := by
  have hapos : 0 < a := lt_trans zero_lt_one ha
  have haneg : ¬ 0 ≤ -a := by linarith
  have hat : 0 ≤ a*t := mul_nonneg hapos.le ht
  apply Prod.ext <;> funext i <;> cases i with
  | inl j => rfl
  | inr i =>
    fin_cases i <;>
      simp [upward, imageLo, imageHi, productLo, productHi,
        contractionMatrix, contractionBox, affineProductLo, affineProductHi,
        Fin.sum_univ_succ, hapos.le, haneg, ht, hat, show ¬ (1 : ℝ) ≤ 0 by norm_num]

lemma contraction_downward (a t : ℝ) (ha : 1 < a) (ht : 0 ≤ t) :
    downward (contractionMatrix a) (contractionBox t) = contractionBox (t/a) := by
  have hapos : 0 < a := lt_trans zero_lt_one ha
  have hane : a ≠ 0 := ne_of_gt hapos
  have haneg : ¬ 0 ≤ -a := by linarith
  have hant : ¬ 0 < -a := by linarith
  have hta : t/a ≤ t := div_le_self ht ha.le
  have htat : t ≤ a*t := by nlinarith
  have htaa : t/a ≤ a*t := hta.trans htat
  apply Prod.ext <;> funext i <;> cases i with
  | inr i => rfl
  | inl j =>
    fin_cases j <;>
      simp [downward, inverseLo, inverseHi, restLo, restHi, productLo, productHi,
        contractionMatrix, contractionBox, affineProductLo, affineProductHi,
        seededMax_two, seededMin_two, Fin.sum_univ_succ, Finset.univ_fin2,
        hapos, hapos.le, hane, haneg, hant, min_eq_right hta,
        min_eq_left htaa, min_eq_right htaa, show ¬ (1 : ℝ) ≤ 0 by norm_num,
        show ¬ (1 : ℝ) < 0 by norm_num]

lemma contraction_clip (t : ℝ) (ht1 : t ≤ 1) :
    clip (contractionBox t) (contractionBox 1) = contractionBox t := by
  apply Prod.ext <;> funext i <;> cases i with
  | inl j => simp [clip, contractionBox, min_eq_left ht1]
  | inr j => simp [clip, contractionBox]

lemma contraction_raw_step (a t : ℝ) (ha : 1 < a) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    rawF (contractionMatrix a) (contractionBox 1) (contractionBox t) =
      contractionBox (t/a) := by
  rw [rawF, contraction_clip t ht1, contraction_upward a t ha ht,
    contraction_downward a t ha ht]

lemma contraction_raw_run (a : ℝ) (ha : 1 < a) (k : ℕ) :
    rawRun (contractionMatrix a) (contractionBox 1) k = contractionBox ((a⁻¹)^k) := by
  have hp : 0 < a⁻¹ := inv_pos.mpr (lt_trans zero_lt_one ha)
  have hle : a⁻¹ ≤ 1 := (inv_le_one₀ (lt_trans zero_lt_one ha)).mpr ha.le
  induction k with
  | zero => simp [rawRun]
  | succ k ih =>
    simp only [rawRun, Function.iterate_succ_apply']
    change rawF (contractionMatrix a) (contractionBox 1)
      (rawRun (contractionMatrix a) (contractionBox 1) k) = _
    rw [ih, contraction_raw_step a ((a⁻¹)^k) ha (pow_nonneg hp.le k)
      (pow_le_one₀ hp.le hle)]
    simp [pow_succ, div_eq_mul_inv]

lemma contraction_every_public_nonempty (a : ℝ) (ha : 1 < a) :
    ∀ k, (publicRun (contractionMatrix a) (contractionBox 1) k).members.Nonempty := by
  apply (public_run_nonempty_iff _ _).2
  intro k
  rw [contraction_raw_run a ha k]
  exact contraction_box_ordered (pow_nonneg (inv_nonneg.mpr (by linarith)) k)

lemma contraction_finite_positive_width (a : ℝ) (ha : 1 < a) (k : ℕ) :
    0 < width (rawRun (contractionMatrix a) (contractionBox 1) k) := by
  rw [contraction_raw_run a ha k]
  have hp : 0 < (a⁻¹)^k := pow_pos (inv_pos.mpr (by linarith)) k
  simp [width, contractionBox, Fintype.sum_sum_type, Fin.sum_univ_succ]
  exact pow_pos (by linarith : 0 < a) k

lemma contraction_raw_tends_zero (a : ℝ) (ha : 1 < a) :
    Filter.Tendsto (rawRun (contractionMatrix a) (contractionBox 1))
      Filter.atTop (nhds (contractionBox 0)) := by
  have hp : 0 ≤ a⁻¹ := inv_nonneg.mpr (by linarith)
  have hlt : a⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < a)).mpr ha
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hp hlt
  have h : Continuous (contractionBox : ℝ → JointBounds 2 2) := by
    apply Continuous.prodMk
    · exact continuous_const
    · apply continuous_pi
      intro i
      cases i with
      | inl j => exact continuous_id
      | inr j => exact continuous_const
  have he : rawRun (contractionMatrix a) (contractionBox 1) =
      fun k => contractionBox ((a⁻¹)^k) := funext (contraction_raw_run a ha)
  rw [he]
  exact h.continuousAt.tendsto.comp ht

end Chapter02FBBTControls
