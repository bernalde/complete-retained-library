module

public import Chapter02ESH
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Uniform ESH separation derived from compact exact-root data and C1 rows.
The global-domain assumptions are an explicit sufficient source interpretation.
The theorem quantifies over every exact root and every active row; neither
progress nor a positive separation margin is an input. Empty row families are
allowed at the statement level. No numerical root-search claim is made. -/

noncomputable section
namespace Chapter02

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The entire admissible exact-root data set for one active row. -/
def eshRootData (B : Set E) (g : J → E → ℝ) (a : E) (eps : ℝ) (j : J) :
    Set (E × ℝ) :=
  {p | p.1 ∈ B ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    (∃ k, eps ≤ g k p.1) ∧
    (∀ k, g k (AffineMap.lineMap a p.1 p.2) ≤ 0) ∧
    g j (AffineMap.lineMap a p.1 p.2) = 0}

theorem esh_lineMap_data_continuous (a : E) :
    Continuous (fun p : E × ℝ => AffineMap.lineMap a p.1 p.2) := by
  simp only [AffineMap.lineMap_apply_module]
  exact ((continuous_const.sub continuous_snd).smul continuous_const).add
    (continuous_snd.smul continuous_fst)

theorem esh_rootData_isCompact [Fintype J] {B : Set E} (hB : IsCompact B)
    {g : J → E → ℝ} (hg : ∀ j, Continuous (g j)) (a : E) (eps : ℝ) (j : J) :
    IsCompact (eshRootData B g a eps j) := by
  have hz := esh_lineMap_data_continuous a
  have hv : IsClosed {p : E × ℝ | ∃ k, eps ≤ g k p.1} := by
    simpa only [Set.setOf_exists, Function.comp_apply] using isClosed_iUnion_of_finite
      (fun k => isClosed_le continuous_const ((hg k).comp continuous_fst))
  have hf : IsClosed {p : E × ℝ | ∀ k, g k (AffineMap.lineMap a p.1 p.2) ≤ 0} := by
    simpa only [Set.setOf_forall, Function.comp_apply] using isClosed_iInter
      (fun k => isClosed_le ((hg k).comp hz) continuous_const)
  have ha : IsClosed {p : E × ℝ | g j (AffineMap.lineMap a p.1 p.2) = 0} :=
    isClosed_eq ((hg j).comp hz) continuous_const
  convert (hB.prod (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))).inter_right
    (hv.inter (hf.inter ha)) using 1
  ext p
  simp only [eshRootData, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, and_assoc]

/-- The compact closed parameter interval loses both endpoints under the
strict-start and positive-threshold hypotheses. -/
theorem esh_rootData_parameter_interior {B : Set E} {g : J → E → ℝ}
    {a : E} {eps : ℝ} {j : J} {p : E × ℝ}
    (ha : ∀ k, g k a < 0) (heps : 0 < eps) (hp : p ∈ eshRootData B g a eps j) :
    p.2 ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hq, ht, hv, hf, hj⟩ := hp
  refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
  · intro hzero
    have : g j a = 0 := by simpa [← hzero] using hj
    exact (ne_of_lt (ha j)) this
  · intro hone
    obtain ⟨k, hk⟩ := hv
    have hfk : g k p.1 ≤ 0 := by simpa [hone] using hf k
    linarith

/-- Canonical normalized separation of an exact-root active tangent. -/
def eshNormalizedMargin (g : J → E → ℝ) (a : E) (j : J) (p : E × ℝ) : ℝ :=
  let z := AffineMap.lineMap a p.1 p.2
  (g j z + fderiv ℝ (g j) z (p.1 - z)) / (1 + ‖fderiv ℝ (g j) z‖)

theorem esh_normalizedMargin_continuous {g : J → E → ℝ}
    (hC1 : ∀ j, ContDiff ℝ 1 (g j)) (a : E) (j : J) :
    Continuous (eshNormalizedMargin g a j) := by
  have hz := esh_lineMap_data_continuous a
  have hd := (hC1 j).continuous_fderiv (by norm_num)
  have he := ((hC1 j).continuous_fderiv_apply (by norm_num)).comp
    (hz.prodMk (continuous_fst.sub hz))
  exact (((hC1 j).continuous.comp hz).add he).div
    (continuous_const.add ((hd.comp hz).norm)) (fun p => by positivity)

theorem esh_normalizedMargin_pos {B : Set E} {g : J → E → ℝ}
    {a : E} {eps : ℝ} {j : J} {p : E × ℝ}
    (hconv : ∀ k, ConvexOn ℝ Set.univ (g k))
    (hdiff : ∀ k, Differentiable ℝ (g k))
    (ha : ∀ k, g k a < 0) (heps : 0 < eps)
    (hp : p ∈ eshRootData B g a eps j) :
    0 < eshNormalizedMargin g a j p := by
  have ht := esh_rootData_parameter_interior ha heps hp
  have hs := (esh_active_cut_separates (hconv j)
    (hdiff j _).hasFDerivAt (ha j) ht hp.2.2.2.2).2.2
  exact div_pos hs (by positivity)

/-- A strictly positive common margin is derived on all compact root data.
This includes empty admissible-data sets and empty row families. -/
theorem esh_uniform_normalized_margin [Fintype J] {B : Set E} (hB : IsCompact B)
    {g : J → E → ℝ} (hconv : ∀ j, ConvexOn ℝ Set.univ (g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (g j)) {a : E} (ha : ∀ j, g j a < 0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ j, ∀ p ∈ eshRootData B g a eps j,
      delta ≤ eshNormalizedMargin g a j p := by
  classical
  have hrow : ∀ j, ∃ d > 0, ∀ p ∈ eshRootData B g a eps j,
      d ≤ eshNormalizedMargin g a j p := by
    intro j
    exact (esh_rootData_isCompact hB (fun j => (hC1 j).continuous) a eps j).exists_forall_le'
      (esh_normalizedMargin_continuous hC1 a j).continuousOn
      (fun p hp => esh_normalizedMargin_pos hconv
        (fun j => (hC1 j).differentiable (by norm_num)) ha heps hp)
  choose d hd hbound using hrow
  cases isEmpty_or_nonempty J with
  | inl hJ => exact ⟨1, by norm_num, fun j => isEmptyElim j⟩
  | inr hJ =>
    refine ⟨Finset.univ.inf' Finset.univ_nonempty d, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff _).mpr (fun j _ => hd j)
    · intro j p hp
      exact (Finset.inf'_le d (Finset.mem_univ j)).trans (hbound j p hp)

/-- Every admissible exact root and active row separates every point obeying
its tangent from its positively violated trial by one derived positive bound. -/
theorem esh_uniform_separation [Fintype J] {B : Set E} (hB : IsCompact B)
    {g : J → E → ℝ} (hconv : ∀ j, ConvexOn ℝ Set.univ (g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (g j)) {a : E} (ha : ∀ j, g j a < 0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ q ∈ B, (∃ k, eps ≤ g k q) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∀ k, g k (AffineMap.lineMap a q t) ≤ 0) →
      ∀ j, g j (AffineMap.lineMap a q t) = 0 →
      ∀ w, g j (AffineMap.lineMap a q t) +
        fderiv ℝ (g j) (AffineMap.lineMap a q t) (w - AffineMap.lineMap a q t) ≤ 0 →
        delta ≤ dist q w := by
  obtain ⟨delta, hdelta, hb⟩ := esh_uniform_normalized_margin hB hconv hC1 ha heps
  refine ⟨delta, hdelta, ?_⟩
  intro q hq hv t ht hf j hj w hw
  let z := AffineMap.lineMap a q t
  let D := fderiv ℝ (g j) z
  have hb' := hb j (q, t) ⟨hq, ht, hv, hf, hj⟩
  have hden : 0 < 1 + ‖D‖ := by positivity
  have hcut : g j z + D (q - z) ≤ D (q - w) := by
    have hid : D (q - z) = D (q - w) + D (w - z) := by
      rw [← map_add]
      congr 1
      abel
    change g j z + D (w - z) ≤ 0 at hw
    rw [hid]
    linarith
  have hop : D (q - w) ≤ ‖D‖ * ‖q - w‖ :=
    (le_abs_self _).trans (D.le_opNorm (q - w))
  have hmargin : eshNormalizedMargin g a j (q, t) ≤ dist q w := by
    change (g j z + D (q - z)) / (1 + ‖D‖) ≤ dist q w
    apply (div_le_iff₀ hden).mpr
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (q - w)]
  exact hb'.trans hmargin

/-- Literal row shift used in ESH2016 Remark1. -/
def eshShiftRows (g : J → E → ℝ) (eta : ℝ) : J → E → ℝ := fun j x => g j x - eta

theorem esh_shift_convex {g : J → E → ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (g j)) (eta : ℝ) :
    ∀ j, ConvexOn ℝ Set.univ (eshShiftRows g eta j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (hconv j).2 hx hy ha hb hab
  simp only [eshShiftRows, smul_eq_mul] at *
  nlinarith [congrArg (fun t : ℝ => t * eta) hab]

theorem esh_shift_contDiff {g : J → E → ℝ}
    (hC1 : ∀ j, ContDiff ℝ 1 (g j)) (eta : ℝ) :
    ∀ j, ContDiff ℝ 1 (eshShiftRows g eta j) := by
  intro j
  exact (hC1 j).sub contDiff_const

theorem esh_shift_fderiv (g : J → E → ℝ) (eta : ℝ) (j : J) (x : E) :
    fderiv ℝ (eshShiftRows g eta j) x = fderiv ℝ (g j) x := by
  exact fderiv_sub_const eta

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem esh_shift_strict_start {g : J → E → ℝ} {a : E} {eta : ℝ}
    (ha : ∀ j, g j a ≤ 0) (heta : 0 < eta) :
    ∀ j, eshShiftRows g eta j a < 0 := by
  intro j
  dsimp [eshShiftRows]
  linarith [ha j]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem esh_shift_preserves_feasible {g : J → E → ℝ} {x : E} {eta : ℝ}
    (hx : ∀ j, g j x ≤ 0) (heta : 0 ≤ eta) :
    ∀ j, eshShiftRows g eta j x ≤ 0 := by
  intro j
  dsimp [eshShiftRows]
  linarith [hx j]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem esh_shift_tolerance_transfer {g : J → E → ℝ} {q : E} {eta : ℝ}
    (hq : ∀ j, eshShiftRows g eta j q ≤ eta) :
    ∀ j, g j q ≤ 2 * eta := by
  intro j
  have hj := hq j
  dsimp [eshShiftRows] at hj
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem esh_shift_half_tolerance_transfer {g : J → E → ℝ} {q : E} {eps : ℝ}
    (hq : ∀ j, eshShiftRows g (eps / 2) j q ≤ eps / 2) :
    ∀ j, g j q ≤ eps := by
  intro j
  have hj := esh_shift_tolerance_transfer hq j
  linarith

end Chapter02

#print axioms Chapter02.esh_lineMap_data_continuous
#print axioms Chapter02.esh_rootData_isCompact
#print axioms Chapter02.esh_rootData_parameter_interior
#print axioms Chapter02.esh_normalizedMargin_continuous
#print axioms Chapter02.esh_normalizedMargin_pos
#print axioms Chapter02.esh_uniform_normalized_margin
#print axioms Chapter02.esh_uniform_separation
#print axioms Chapter02.esh_shift_convex
#print axioms Chapter02.esh_shift_contDiff
#print axioms Chapter02.esh_shift_fderiv
#print axioms Chapter02.esh_shift_strict_start
#print axioms Chapter02.esh_shift_preserves_feasible
#print axioms Chapter02.esh_shift_tolerance_transfer
#print axioms Chapter02.esh_shift_half_tolerance_transfer
