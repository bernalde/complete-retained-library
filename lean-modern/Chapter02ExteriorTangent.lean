module

public import Chapter02CPDomain
public import Chapter02ESHAnalysis
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Tactic

@[expose] public section

/-! Exact-valued complete exterior tangents on a declared continuous domain.
Actual within derivatives derive support; compact admissible pairs derive a
positive normalized margin. B is compact but need not be convex. The generic
proof needs convex K containing B and a, not compact K or global continuity.
Neither root generation nor any algorithm/solver/convergence result is asserted. -/

noncomputable section
namespace Chapter02

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Complete affine tangent evaluated using the specified derivative field. -/
def exteriorTangent (g : J → E → ℝ) (D : J → E → E →L[ℝ] ℝ)
    (j : J) (z x : E) : ℝ := g j z + D j z (x - z)

/-- Admissible exterior-origin data for one selected maximal row. No maximum
of an empty row family is evaluated. The trial endpoint t=1 remains allowed. -/
def exteriorData (B : Set E) (g : J → E → ℝ) (a : E) (eps : ℝ) (j : J) :
    Set (E × ℝ) :=
  {p | p.1 ∈ B ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    (∃ k, eps ≤ g k p.1) ∧
    (∀ k, g k (AffineMap.lineMap a p.1 p.2) ≤ g j (AffineMap.lineMap a p.1 p.2)) ∧
    0 ≤ g j (AffineMap.lineMap a p.1 p.2)}

def exteriorNormalizedMargin (g : J → E → ℝ) (D : J → E → E →L[ℝ] ℝ)
    (a : E) (j : J) (p : E × ℝ) : ℝ :=
  let z := AffineMap.lineMap a p.1 p.2
  exteriorTangent g D j z p.1 / (1 + ‖D j z‖)

/-- A quantitative lower bound for the full tangent at the trial, derived from
within-domain support at the reference; it also holds at t=1. -/
theorem exterior_tangent_lower_bound {K : Set E} {g : E → ℝ}
    {a q : E} {t : ℝ} {D : E →L[ℝ] ℝ}
    (hconv : ConvexOn ℝ K g) (haK : a ∈ K) (hqK : q ∈ K)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hd : HasFDerivWithinAt g D K (AffineMap.lineMap a q t)) :
    (g (AffineMap.lineMap a q t) - (1-t)*g a) / t ≤
      g (AffineMap.lineMap a q t) + D (q - AffineMap.lineMap a q t) := by
  let z := AffineMap.lineMap a q t
  have hz : z ∈ K := hconv.1.lineMap_mem haK hqK ⟨ht.1.le, ht.2⟩
  have hs := cp_tangent_underestimator_within hconv hz haK hd
  have hleft : a-z = t • (a-q) := AffineMap.left_vsub_lineMap a q t
  have hright : q-z = (1-t) • (q-a) := AffineMap.right_vsub_lineMap a q t
  have hneg : D (a-q) = -D (q-a) := by rw [← map_neg, neg_sub]
  rw [hleft, map_smul, smul_eq_mul, hneg] at hs
  change (g z - (1-t)*g a)/t ≤ g z + D (q-z)
  rw [hright, map_smul, smul_eq_mul]
  apply (div_le_iff₀ ht.1).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
    (show 0 ≤ g a - g z + t * D (q-a) by linarith)]

/-- Every admissible selected row has a nonzero actual derivative, supports its
row on K, and strictly excludes the trial. t=0 is impossible; t=1 is allowed. -/
theorem exterior_pointwise {K B : Set E} {g : J → E → ℝ}
    {D : J → E → E →L[ℝ] ℝ} {a : E} {eps : ℝ} {j : J} {p : E × ℝ}
    (hK : Convex ℝ K) (hBK : B ⊆ K) (haK : a ∈ K)
    (hconv : ∀ k, ConvexOn ℝ K (g k))
    (hd : ∀ k z, z ∈ K → HasFDerivWithinAt (g k) (D k z) K z)
    (ha : ∀ k, g k a < 0) (heps : 0 < eps)
    (hp : p ∈ exteriorData B g a eps j) :
    AffineMap.lineMap a p.1 p.2 ∈ K ∧ p.2 ∈ Set.Ioc (0 : ℝ) 1 ∧
      D j (AffineMap.lineMap a p.1 p.2) ≠ 0 ∧
      (∀ x ∈ K, exteriorTangent g D j (AffineMap.lineMap a p.1 p.2) x ≤ g j x) ∧
      0 < exteriorTangent g D j (AffineMap.lineMap a p.1 p.2) p.1 := by
  obtain ⟨hq, ht, hv, hmax, hn⟩ := hp
  let z := AffineMap.lineMap a p.1 p.2
  have hz : z ∈ K := hK.lineMap_mem haK (hBK hq) ht
  have ht0 : 0 < p.2 := lt_of_le_of_ne ht.1 (by
    intro hzero
    have hn' : 0 ≤ g j a := by simpa [← hzero] using hn
    linarith [ha j])
  have hsupport : ∀ x ∈ K, exteriorTangent g D j z x ≤ g j x :=
    fun x hx => cp_tangent_underestimator_within (hconv j) hz hx (hd j z hz)
  have hne : D j z ≠ 0 := by
    intro hzero
    have hs := hsupport a haK
    simp only [exteriorTangent, hzero, ContinuousLinearMap.zero_apply, add_zero] at hs
    change 0 ≤ g j z at hn
    linarith [ha j]
  refine ⟨hz, ⟨ht0, ht.2⟩, hne, hsupport, ?_⟩
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · have hb := exterior_tangent_lower_bound (hconv j) haK (hBK hq)
      ⟨ht0, ht.2⟩ (hd j z hz)
    have hnum : 0 < g j z - (1-p.2)*g j a := by
      have hm := mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (ha j)
      change 0 ≤ g j z at hn
      linarith
    exact (div_pos hnum ht0).trans_le hb
  · obtain ⟨k, hk⟩ := hv
    have hj : eps ≤ g j p.1 := hk.trans (by simpa [heq] using hmax k)
    simpa [exteriorTangent, z, heq] using heps.trans_le hj

/-- Compactness uses scalar continuity only on the continuous comparison domain.
Every closed comparison is restricted to the compact parameter set B×[0,1]. -/
theorem exterior_data_isCompact [Fintype J] {K B : Set E}
    (hB : IsCompact B) (hK : Convex ℝ K) (hBK : B ⊆ K)
    {g : J → E → ℝ} (hg : ∀ j, ContinuousOn (g j) K)
    {a : E} (haK : a ∈ K) (eps : ℝ) (j : J) :
    IsCompact (exteriorData B g a eps j) := by
  let S : Set (E × ℝ) := B ×ˢ Set.Icc (0 : ℝ) 1
  let z : E × ℝ → E := fun p => AffineMap.lineMap a p.1 p.2
  have hS : IsCompact S := hB.prod isCompact_Icc
  have hqmap : Set.MapsTo (fun p : E × ℝ => p.1) S K := fun _ hp => hBK hp.1
  have hzmap : Set.MapsTo z S K := fun _ hp => hK.lineMap_mem haK (hBK hp.1) hp.2
  have hq : ∀ k, ContinuousOn (fun p : E × ℝ => g k p.1) S :=
    fun k => (hg k).comp continuous_fst.continuousOn hqmap
  have hz : ∀ k, ContinuousOn (fun p : E × ℝ => g k (z p)) S :=
    fun k => (hg k).comp (esh_lineMap_data_continuous a).continuousOn hzmap
  have hv : IsClosed {p : E × ℝ | p ∈ S ∧ ∃ k, eps ≤ g k p.1} := by
    have hc := isClosed_iUnion_of_finite (fun k =>
      hS.isClosed.isClosed_le (continuousOn_const (c := eps)) (hq k))
    convert hc using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hp, k, hk⟩; exact ⟨k, hp, hk⟩
    · rintro ⟨k, hp, hk⟩; exact ⟨hp, k, hk⟩
  have hm : IsClosed {p : E × ℝ | ∀ k, p ∈ S ∧ g k (z p) ≤ g j (z p)} := by
    simpa only [Set.setOf_forall] using isClosed_iInter
      (fun k => hS.isClosed.isClosed_le (hz k) (hz j))
  have hn : IsClosed {p : E × ℝ | p ∈ S ∧ 0 ≤ g j (z p)} :=
    hS.isClosed.isClosed_le continuousOn_const (hz j)
  apply hS.of_isClosed_subset
  · convert hv.inter (hm.inter hn) using 1
    ext p
    change (p.1 ∈ B ∧ p.2 ∈ Set.Icc (0:ℝ) 1 ∧ (∃ k, eps ≤ g k p.1) ∧
      (∀ k, g k (z p) ≤ g j (z p)) ∧ 0 ≤ g j (z p)) ↔
      (p ∈ S ∧ ∃ k, eps ≤ g k p.1) ∧
        (∀ k, p ∈ S ∧ g k (z p) ≤ g j (z p)) ∧ (p ∈ S ∧ 0 ≤ g j (z p))
    constructor
    · rintro ⟨hb, ht, hv, hm, hn⟩
      exact ⟨⟨⟨hb, ht⟩, hv⟩, (fun k => ⟨⟨hb, ht⟩, hm k⟩), ⟨⟨hb, ht⟩, hn⟩⟩
    · rintro ⟨⟨hs, hv⟩, hm, ⟨_, hn⟩⟩
      exact ⟨hs.1, hs.2, hv, (fun k => (hm k).2), hn⟩
  · intro p hp
    exact ⟨hp.1, hp.2.1⟩

/-- The margin is continuous relative to B×[0,1], using the specified chosen
field only on K. No canonical derivative or ambient C1 extension is used. -/
theorem exterior_margin_continuousOn {K B : Set E} (hK : Convex ℝ K) (hBK : B ⊆ K)
    {g : J → E → ℝ} {D : J → E → E →L[ℝ] ℝ}
    (hg : ∀ j, ContinuousOn (g j) K) (hD : ∀ j, ContinuousOn (D j) K)
    {a : E} (haK : a ∈ K) (j : J) :
    ContinuousOn (exteriorNormalizedMargin g D a j) (B ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (E × ℝ) := B ×ˢ Set.Icc (0 : ℝ) 1
  let z : E × ℝ → E := fun p => AffineMap.lineMap a p.1 p.2
  have hz : ContinuousOn z S := (esh_lineMap_data_continuous a).continuousOn
  have hzmap : Set.MapsTo z S K := fun _ hp => hK.lineMap_mem haK (hBK hp.1) hp.2
  have hd := (hD j).comp hz hzmap
  have he := hd.clm_apply (continuous_fst.continuousOn.sub hz)
  exact (((hg j).comp hz hzmap).add he).div
    (continuousOn_const.add hd.norm) (fun p hp => by positivity)

/-- A common strictly positive margin is derived for every selected row and
admissible pair, including empty row families and empty admissible sets. -/
theorem exterior_uniform_normalized_margin [Fintype J] {K B : Set E}
    (hB : IsCompact B) (hK : Convex ℝ K) (hBK : B ⊆ K)
    {g : J → E → ℝ} {D : J → E → E →L[ℝ] ℝ}
    (hconv : ∀ j, ConvexOn ℝ K (g j))
    (hd : ∀ j z, z ∈ K → HasFDerivWithinAt (g j) (D j z) K z)
    (hD : ∀ j, ContinuousOn (D j) K) {a : E} (haK : a ∈ K)
    (ha : ∀ j, g j a < 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ j, ∀ p ∈ exteriorData B g a eps j,
      delta ≤ exteriorNormalizedMargin g D a j p := by
  classical
  have hg : ∀ j, ContinuousOn (g j) K := fun j =>
    cp_continuousOn_of_derivative_within (hd j)
  have hrow : ∀ j, ∃ d > 0, ∀ p ∈ exteriorData B g a eps j,
      d ≤ exteriorNormalizedMargin g D a j p := by
    intro j
    apply (exterior_data_isCompact hB hK hBK hg haK eps j).exists_forall_le'
    · exact (exterior_margin_continuousOn hK hBK hg hD haK j).mono
        (fun _ hp => ⟨hp.1, hp.2.1⟩)
    · intro p hp
      have hs := (exterior_pointwise hK hBK haK hconv hd ha heps hp).2.2.2.2
      exact div_pos hs (by positivity)
  choose d hdpos hbound using hrow
  cases isEmpty_or_nonempty J with
  | inl hJ => exact ⟨1, by norm_num, fun j => isEmptyElim j⟩
  | inr hJ =>
    refine ⟨Finset.univ.inf' Finset.univ_nonempty d, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff _).mpr (fun j _ => hdpos j)
    · intro j p hp
      exact (Finset.inf'_le d (Finset.mem_univ j)).trans (hbound j p hp)

/-- Every point satisfying the same complete tangent lies at a uniformly
positive distance from its trial. The compared point w is arbitrary ambient E;
only original-feasible containment separately needs w in the domain K. -/
theorem exterior_uniform_separation [Fintype J] {K B : Set E}
    (hB : IsCompact B) (hK : Convex ℝ K) (hBK : B ⊆ K)
    {g : J → E → ℝ} {D : J → E → E →L[ℝ] ℝ}
    (hconv : ∀ j, ConvexOn ℝ K (g j))
    (hd : ∀ j z, z ∈ K → HasFDerivWithinAt (g j) (D j z) K z)
    (hD : ∀ j, ContinuousOn (D j) K) {a : E} (haK : a ∈ K)
    (ha : ∀ j, g j a < 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ j q t, (q,t) ∈ exteriorData B g a eps j →
      ∀ w, exteriorTangent g D j (AffineMap.lineMap a q t) w ≤ 0 →
        delta ≤ dist q w := by
  obtain ⟨delta, hdelta, hb⟩ :=
    exterior_uniform_normalized_margin hB hK hBK hconv hd hD haK ha heps
  refine ⟨delta, hdelta, ?_⟩
  intro j q t hp w hw
  let z := AffineMap.lineMap a q t
  let A := D j z
  have hden : 0 < 1 + ‖A‖ := by positivity
  have hcut : g j z + A (q-z) ≤ A (q-w) := by
    have hid : A (q-z) = A (q-w) + A (w-z) := by
      rw [← map_add]
      congr 1
      abel
    change g j z + A (w-z) ≤ 0 at hw
    rw [hid]
    linarith
  have hop : A (q-w) ≤ ‖A‖ * ‖q-w‖ :=
    (le_abs_self _).trans (A.le_opNorm (q-w))
  have hmargin : exteriorNormalizedMargin g D a j (q,t) ≤ dist q w := by
    change (g j z + A (q-z)) / (1 + ‖A‖) ≤ dist q w
    apply (div_le_iff₀ hden).mpr
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (q-w)]
  exact (hb j (q,t) hp).trans hmargin

end Chapter02

#print axioms Chapter02.exterior_tangent_lower_bound
#print axioms Chapter02.exterior_pointwise
#print axioms Chapter02.exterior_data_isCompact
#print axioms Chapter02.exterior_margin_continuousOn
#print axioms Chapter02.exterior_uniform_normalized_margin
#print axioms Chapter02.exterior_uniform_separation
