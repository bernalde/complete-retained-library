module

public import Chapter02Clarke
public import Chapter02ESHAnalysis
public import Chapter02ECPAnalysis

@[expose] public section

/-! Actual Clarke zero-level ESH geometry. Supporting declarations are uncounted.
The weak all-ambient law and nonzero actual normals are explicit hypotheses.
No continuity of selected normals or assumed progress margin is used. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Chapter02
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem clarke_strict_ball [Fintype J] [Nonempty J] {g : J → E → ℝ}
    (hg : ∀ j, Continuous (g j)) {a : E} (ha : ∀ j, g j a < 0) :
    ∃ r > 0, ∀ p, ‖p - a‖ ≤ r → ∀ j, g j p < 0 := by
  have hFa : eshMaximum g a < 0 := by
    obtain ⟨j, hj⟩ := eshMaximum_attained g a
    rw [hj]
    exact ha j
  have hn : {p | eshMaximum g p < 0} ∈ 𝓝 a :=
    (eshMaximum_continuous hg).continuousAt.preimage_mem_nhds (Iio_mem_nhds hFa)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r / 2, by positivity, ?_⟩
  intro p hp j
  have hFp := hb (show p ∈ Metric.ball a r by
    simp only [Metric.mem_ball, dist_eq_norm]
    linarith)
  have hj := (eshMaximum_le_iff g p (eshMaximum g p)).mp le_rfl j
  exact hj.trans_lt hFp

/-- A continuous linear functional bounded on a ball has the corresponding
operator-norm bound. No attainment of its operator norm is assumed. -/
theorem clarke_ball_opNorm {D : E →L[ℝ] ℝ} {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hball : ∀ v, ‖v‖ ≤ r → D v ≤ b) : r * ‖D‖ ≤ b := by
  have hnorm : ‖D‖ ≤ b / r := by
    apply D.opNorm_le_bound (div_nonneg hb hr.le)
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hc : 0 < r / ‖v‖ := div_pos hr hvp
    have hw : ‖(r / ‖v‖) • v‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt hvp))
    have hp := hball ((r / ‖v‖) • v) hw
    have hn := hball (-((r / ‖v‖) • v)) (by simpa using hw)
    simp only [map_smul, smul_eq_mul, map_neg] at hp hn
    have hab : (r / ‖v‖) * |D v| ≤ b := by
      rw [← abs_of_pos hc, ← abs_mul]
      exact abs_le.mpr ⟨by linarith, hp⟩
    rw [Real.norm_eq_abs]
    have hab := (le_div_iff₀ hc).mpr (show |D v| * (r / ‖v‖) ≤ b by nlinarith [hab])
    have hid : b / (r / ‖v‖) = b / r * ‖v‖ := by field_simp
    exact hid ▸ hab
  exact (mul_le_mul_of_nonneg_left hnorm hr.le).trans_eq (by field_simp)

theorem clarke_inward_margin {g : E → ℝ} (hg : ClarkeQuasiconvex g)
    {a z : E} {r : ℝ} (hr : 0 < r)
    (hball : ∀ p, ‖p - a‖ ≤ r → g p < 0) (hz : g z = 0)
    {D : E →L[ℝ] ℝ} (hD : D ∈ clarkeSubdifferential g z) :
    D (a - z) ≤ -r * ‖D‖ := by
  have hbase : D (a - z) ≤ 0 :=
    clarke_normal_le_zero hg hD (by rw [hz]; exact (hball a (by simp; positivity)).le)
  have hn := clarke_ball_opNorm (D := D) hr (neg_nonneg.mpr hbase) (by
    intro v hv
    have h := clarke_normal_le_zero hg hD
      (show g (a + v) ≤ g z by rw [hz]; exact (hball (a + v) (by simpa using hv)).le)
    have hid : D (a + v - z) = D (a - z) + D v := by
      rw [← map_add]; congr 1; abel
    rw [hid] at h
    linarith)
  linarith

/-- Compact root data uniformly stay away from the trial endpoint, including
the vacuous case of empty positive-threshold root sets. -/
theorem clarke_root_parameter_margin [Fintype J] [Nonempty J]
    {B : Set E} (hB : IsCompact B) {g : J → E → ℝ}
    (hg : ∀ j, Continuous (g j)) {a : E} (ha : ∀ j, g j a < 0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ d > 0, ∀ j, ∀ p ∈ eshRootData B g a eps j, d ≤ 1 - p.2 := by
  classical
  have hrow : ∀ j, ∃ d > 0, ∀ p ∈ eshRootData B g a eps j, d ≤ 1 - p.2 := by
    intro j
    exact (esh_rootData_isCompact hB hg a eps j).exists_forall_le'
      (continuous_const.sub continuous_snd).continuousOn
      (fun p hp => sub_pos.mpr (esh_rootData_parameter_interior ha heps hp).2)
  choose d hd hb using hrow
  refine ⟨Finset.univ.inf' Finset.univ_nonempty d, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun j _ => hd j)
  · intro j p hp
    exact (Finset.inf'_le d (Finset.mem_univ j)).trans (hb j p hp)

/-- Uniform separation for every exact root, active row and nonzero actual
Clarke normal. Its normalization cancels; no bounded normal selection is needed. -/
theorem clarke_esh_uniform_separation [Fintype J] [Nonempty J]
    {B : Set E} (hB : IsCompact B) {g : J → E → ℝ}
    (hg : ∀ j, Continuous (g j)) (hweak : ∀ j, ClarkeQuasiconvex (g j))
    {a : E} (ha : ∀ j, g j a < 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ q ∈ B, (∃ k, eps ≤ g k q) →
      ∀ t ∈ Icc (0 : ℝ) 1, (∀ k, g k (AffineMap.lineMap a q t) ≤ 0) →
      ∀ j, g j (AffineMap.lineMap a q t) = 0 →
      ∀ D ∈ clarkeSubdifferential (g j) (AffineMap.lineMap a q t), D ≠ 0 →
      ∀ w, D (w - AffineMap.lineMap a q t) ≤ 0 → delta ≤ dist q w := by
  obtain ⟨r, hr, hball⟩ := clarke_strict_ball hg ha
  obtain ⟨d, hd, hparam⟩ := clarke_root_parameter_margin hB hg ha heps
  refine ⟨r * d, mul_pos hr hd, ?_⟩
  intro q hq hv t ht hf j hj D hD hDn w hw
  have hroot : (q, t) ∈ eshRootData B g a eps j := ⟨hq, ht, hv, hf, hj⟩
  have hti := esh_rootData_parameter_interior ha heps hroot
  have htpos : 0 < t := hti.1
  have htlt : t < 1 := hti.2
  have hdt := hparam j (q, t) hroot
  let z := AffineMap.lineMap a q t
  have hin := clarke_inward_margin (hweak j) hr (fun p hp => hball p hp j) hj hD
  have hid : t * D (q - z) = -(1 - t) * D (a - z) := by
    dsimp [z]
    simp only [AffineMap.lineMap_apply_module, map_sub, map_add, map_smul, smul_eq_mul]
    ring
  change D (a - z) ≤ -r * ‖D‖ at hin
  have hn : 0 < ‖D‖ := norm_pos_iff.mpr hDn
  have hlow : r * d * ‖D‖ ≤ D (q - z) := by
    have hm := mul_le_mul_of_nonneg_left hin (sub_nonneg.mpr ht.2)
    have hpos : 0 < D (q - z) := by
      have htp : 0 < t * D (q - z) := by nlinarith [mul_pos (sub_pos.mpr htlt) (mul_pos hr hn)]
      exact pos_of_mul_pos_right htp htpos.le
    have h1 : r * (1 - t) * ‖D‖ ≤ D (q - z) := by
      nlinarith
    nlinarith [mul_nonneg (mul_nonneg hr.le (sub_nonneg.mpr hdt)) (norm_nonneg D)]
  have hcut : D (q - z) ≤ D (q - w) := by
    have heq : D (q - z) = D (q - w) + D (w - z) := by
      rw [← map_add]; congr 1; abel
    rw [heq]
    exact add_le_of_nonpos_right hw
  have hop := (le_abs_self (D (q - w))).trans (D.le_opNorm (q - w))
  rw [dist_eq_norm]
  nlinarith

end Chapter02

