module

public import Chapter02Model
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Module

@[expose] public section

/-! Finite real integer-coordinate bounds are essential. The source compact
mixed affine base yields compact continuous affine relaxation when the former
is nonempty. A normalized unbounded sequence constructs the contradictory ray;
there is no recession or attainment oracle. Empty mixed bases remain allowed. -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace Chapter02

/-- An unbounded closed convex set in a proper real normed space contains a
unit-speed ray from each of its points. -/
theorem bb_unbounded_closed_convex_ray {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {C : Set E} (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (hunbounded : ¬ Bornology.IsBounded C)
    {p : E} (hp : p ∈ C) :
    ∃ v : E, ‖v‖ = 1 ∧ ∀ t : ℝ, 0 ≤ t → p + t • v ∈ C := by
  have hex (k : ℕ) : ∃ z ∈ C, (k : ℝ) + 1 < ‖z - p‖ := by
    by_contra h
    push_neg at h
    apply hunbounded
    exact (Metric.isBounded_iff_subset_closedBall p).2 ⟨(k : ℝ) + 1,
      fun z hz => by simpa only [mem_closedBall, dist_eq_norm] using h z hz⟩
  choose z hz hlarge using hex
  let r : ℕ → ℝ := fun k => ‖z k - p‖
  have hrpos (k : ℕ) : 0 < r k := by
    dsimp [r]
    exact lt_trans (by positivity) (hlarge k)
  have hr : Tendsto r atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp [r]; linarith [hlarge k])
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)
  let u : ℕ → E := fun k => (r k)⁻¹ • (z k - p)
  have hu (k : ℕ) : u k ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (by
      intro h
      have := hrpos k
      simp [r, h] at this)
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hu
  refine ⟨v, mem_sphere_zero_iff_norm.mp hv, ?_⟩
  intro t ht
  apply hclosed.mem_of_tendsto (tendsto_const_nhds.add (tendsto_const_nhds.smul hlim))
  filter_upwards [(hr.comp hφ.tendsto_atTop).eventually_ge_atTop t] with k hk
  have ha : 0 ≤ t / r (φ k) := div_nonneg ht (hrpos _).le
  have hb : t / r (φ k) ≤ 1 := (div_le_one (hrpos _)).2 hk
  have hcombo := hconv hp (hz (φ k)) (sub_nonneg.mpr hb) ha (by ring)
  have heq : (1 - t / r (φ k)) • p + (t / r (φ k)) • z (φ k) =
      p + t • u (φ k) := by
    dsimp [u]
    rw [smul_smul]
    simp only [div_eq_mul_inv]
    module
  simpa only [Function.comp_apply, heq] using hcombo

/-- A ray staying between two finite real bounds has zero direction. -/
theorem bb_bounded_scalar_ray_direction {a b p v : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → a ≤ p + t * v ∧ p + t * v ≤ b) : v = 0 := by
  have hp := h 0 le_rfl
  simp only [zero_mul, add_zero] at hp
  apply le_antisymm
  · by_contra hn
    have hv : 0 < v := lt_of_not_ge hn
    have ht : 0 ≤ (b - p + 1) / v := div_nonneg (by linarith [hp.2]) hv.le
    have hh := (h _ ht).2
    rw [div_mul_cancel₀ _ hv.ne'] at hh
    linarith
  · by_contra hn
    have hv : 0 < -v := by linarith
    have ht : 0 ≤ (p - a + 1) / (-v) := div_nonneg (by linarith [hp.1]) hv.le
    have hh := (h _ ht).1
    have heq : (p - a + 1) / (-v) * v = -(p - a + 1) := by
      have := div_mul_cancel₀ (p - a + 1) hv.ne'
      nlinarith
    rw [heq] at hh
    linarith

/-- The compact mixed set supplies a point on the ray; finite real y-bounds
force the ray to preserve that point's exact integer vector. -/
theorem bb_closed_convex_box_compact {n m : ℕ} {C : Set (Point n m)}
    (a b : RealVector m) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    (hbounds : ∀ p ∈ C, ∀ i, a i ≤ p.2 i ∧ p.2 i ≤ b i)
    (hM : IsCompact (C ∩ IntegerCylinder (n := n) a b))
    (hne : (C ∩ IntegerCylinder (n := n) a b).Nonempty) : IsCompact C := by
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨hclosed, ?_⟩
  by_contra hunbounded
  obtain ⟨p, hpC, hpY⟩ := hne
  obtain ⟨v, hv, hray⟩ := bb_unbounded_closed_convex_ray hclosed hconv hunbounded hpC
  have hvY : v.2 = 0 := by
    funext i
    apply bb_bounded_scalar_ray_direction (a := a i) (b := b i) (p := p.2 i)
    intro t ht
    exact hbounds _ (hray t ht) i
  have hmem (t : ℝ) (ht : 0 ≤ t) : p + t • v ∈ C ∩ IntegerCylinder a b := by
    refine ⟨hray t ht, ?_⟩
    rcases hpY with ⟨y, hy, hpy⟩
    exact ⟨y, hy, by simpa [hvY] using hpy⟩
  obtain ⟨K, hK⟩ := hM.isBounded.exists_norm_le
  let t : ℝ := max 0 (K + ‖p‖) + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hn : t ≤ K + ‖p‖ := by
    calc
      t = ‖t • v‖ := by simp [norm_smul, Real.norm_of_nonneg ht, hv]
      _ = ‖(p + t • v) - p‖ := by congr 1; abel
      _ ≤ ‖p + t • v‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ K + ‖p‖ := add_le_add (hK _ (hmem t ht)) le_rfl
  have := le_max_right 0 (K + ‖p‖)
  dsimp [t] at hn
  linarith

/-- The literal affine continuous node box; bounds are finite real vectors. -/
def bbAffineRelaxation {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) : Set (Point n m) :=
  ContinuousRelaxation Set.univ d.linearRegion a b

/-- The affine mixed node base, before imposing the nonlinear rows. -/
def bbMixedBase {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) : Set (Point n m) :=
  d.linearRegion ∩ IntegerCylinder (n := n) a b

/-- The actual continuous nonlinear node relaxation. -/
def bbNodeRelaxation {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) : Set (Point n m) :=
  ContinuousRelaxation d.nonlinearRegion d.linearRegion a b

theorem bb_linearRegion_closed {n m l r : ℕ} (d : ModelData n m l r) :
    IsClosed d.linearRegion := by
  have heq : d.linearRegion = ⋂ j, {p | LinearForm (d.A j) (d.B j) p ≤ d.rhs j} := by
    ext p
    simp [ModelData.linearRegion]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le (linearForm_continuous _ _) continuous_const

theorem bb_real_box_closed {n m : ℕ} (a b : RealVector m) :
    IsClosed {p : Point n m | ∀ i, a i ≤ p.2 i ∧ p.2 i ≤ b i} := by
  have heq : {p : Point n m | ∀ i, a i ≤ p.2 i ∧ p.2 i ≤ b i} =
      ⋂ i, {p : Point n m | a i ≤ p.2 i ∧ p.2 i ≤ b i} := by
    ext p
    simp
  rw [heq]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)).inter
      (isClosed_le ((continuous_apply i).comp continuous_snd) continuous_const)

theorem bb_affine_relaxation_closed {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) : IsClosed (bbAffineRelaxation d a b) := by
  have heq : bbAffineRelaxation d a b =
      d.linearRegion ∩ {p : Point n m | ∀ i, a i ≤ p.2 i ∧ p.2 i ≤ b i} := by
    ext p
    simp [bbAffineRelaxation, ContinuousRelaxation]
  rw [heq]
  exact (bb_linearRegion_closed d).inter (bb_real_box_closed a b)

theorem bb_affine_mixed_eq {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) :
    bbAffineRelaxation d a b ∩ IntegerCylinder (n := n) a b = bbMixedBase d a b := by
  ext p
  constructor
  · rintro ⟨hp, hy⟩
    exact ⟨hp.2.1, hy⟩
  · rintro ⟨hp, hy⟩
    refine ⟨⟨Set.mem_univ _, hp, ?_⟩, hy⟩
    rcases hy with ⟨y, hy, hpy⟩
    simpa only [IntegerBox, Set.mem_setOf_eq, hpy] using hy

/-- Source mixed compactness, together with an actual point of that mixed base,
derives continuous compactness; it is not supplied as an additional premise. -/
theorem bb_affine_relaxation_compact {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) (hM : IsCompact (bbMixedBase d a b))
    (hne : (bbMixedBase d a b).Nonempty) : IsCompact (bbAffineRelaxation d a b) := by
  apply bb_closed_convex_box_compact a b (bb_affine_relaxation_closed d a b)
    (continuousRelaxation_convex a b convex_univ (source_linearRegion_convex d))
    (fun p hp => hp.2.2)
  · simpa only [bb_affine_mixed_eq] using hM
  · simpa only [bb_affine_mixed_eq] using hne

/-- Descendant mixed compactness follows from actual refinement of the root
real bounds. The raw process need not carry compactness as an invariant field. -/
theorem bb_mixed_base_compact_of_refines {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (ha : ∀ i, d.lo i ≤ a i) (hb : ∀ i, b i ≤ d.hi i) :
    IsCompact (bbMixedBase d a b) := by
  have heq : bbMixedBase d a b = bbMixedBase d d.lo d.hi ∩
      {p : Point n m | ∀ i, a i ≤ p.2 i ∧ p.2 i ≤ b i} := by
    ext p
    constructor
    · rintro ⟨hp, y, hy, hpy⟩
      refine ⟨⟨hp, y, ?_, hpy⟩, ?_⟩
      · exact fun i => ⟨(ha i).trans (hy i).1, (hy i).2.trans (hb i)⟩
      · simpa only [IntegerBox, Set.mem_setOf_eq, hpy] using hy
    · rintro ⟨⟨hp, y, _, hpy⟩, hbounds⟩
      exact ⟨hp, y, by simpa only [IntegerBox, Set.mem_setOf_eq, hpy] using hbounds, hpy⟩
  rw [heq]
  exact hbase.inter_right (bb_real_box_closed a b)

theorem bb_nonlinearRegion_closed {n m l r : ℕ} (d : ModelData n m l r)
    (hg : ∀ j, Continuous (d.g j)) : IsClosed d.nonlinearRegion := by
  have heq : d.nonlinearRegion = ⋂ j, {p | d.g j p ≤ 0} := by
    ext p
    simp [ModelData.nonlinearRegion]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le (hg j) continuous_const

theorem bb_node_relaxation_subset_affine {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) : bbNodeRelaxation d a b ⊆ bbAffineRelaxation d a b :=
  fun _ hp => ⟨Set.mem_univ _, hp.2⟩

/-- Nonlinear continuity suffices; convexity and C1 are not needed for this
exact attainment argument. The thesis wrapper may retain their source scope. -/
theorem bb_node_relaxation_compact {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) (hM : IsCompact (bbMixedBase d a b))
    (hne : (bbMixedBase d a b).Nonempty) (hg : ∀ j, Continuous (d.g j)) :
    IsCompact (bbNodeRelaxation d a b) := by
  have heq : bbNodeRelaxation d a b = d.nonlinearRegion ∩ bbAffineRelaxation d a b := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, Set.mem_univ _, hp.2⟩
    · rintro ⟨hn, _, hl, hb⟩
      exact ⟨hn, hl, hb⟩
  rw [heq]
  exact (bb_affine_relaxation_compact d a b hM hne).inter_left
    (bb_nonlinearRegion_closed d hg)

theorem bb_node_minimum_attained {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) (f : Point n m → ℝ)
    (hM : IsCompact (bbMixedBase d a b)) (hne : (bbMixedBase d a b).Nonempty)
    (hg : ∀ j, Continuous (d.g j)) (hf : ContinuousOn f (bbAffineRelaxation d a b))
    (hR : (bbNodeRelaxation d a b).Nonempty) :
    ∃ p, IsMinimizer (bbNodeRelaxation d a b) f p :=
  compact_feasible_attainment (bb_node_relaxation_compact d a b hM hne hg) hR
    (hf.mono (bb_node_relaxation_subset_affine d a b))

/-- The source linear objective is a specialization of the general continuous
objective endpoint, not an epigraph conversion of nonlinear objectives. -/
theorem bb_node_linear_minimum_attained {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) (hM : IsCompact (bbMixedBase d a b))
    (hne : (bbMixedBase d a b).Nonempty) (hg : ∀ j, Continuous (d.g j))
    (hR : (bbNodeRelaxation d a b).Nonempty) :
    ∃ p, IsMinimizer (bbNodeRelaxation d a b) d.objective p :=
  bb_node_minimum_attained d a b d.objective hM hne hg
    (linearForm_continuous d.c1 d.c2).continuousOn hR

/-- The nonlinear relaxation must be nonempty. An empty nonlinear region alone
does not imply that the affine mixed base is empty. -/
theorem bb_node_no_minimum_implies_mixed_base_empty {n m l r : ℕ}
    (d : ModelData n m l r) (a b : RealVector m) (f : Point n m → ℝ)
    (hM : IsCompact (bbMixedBase d a b)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d a b))
    (hR : (bbNodeRelaxation d a b).Nonempty)
    (hbad : ¬ ∃ p, IsMinimizer (bbNodeRelaxation d a b) f p) :
    bbMixedBase d a b = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hbad (bb_node_minimum_attained d a b f hM ⟨p, hp⟩ hg hf hR)

/-- A genuinely unbounded-below relaxation has a point below every real value.
This status is distinct from numerical failure or a local NLP point. -/
theorem bb_node_unbounded_implies_mixed_base_empty {n m l r : ℕ}
    (d : ModelData n m l r) (a b : RealVector m) (f : Point n m → ℝ)
    (hM : IsCompact (bbMixedBase d a b)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d a b))
    (hbad : ∀ B : ℝ, ∃ p ∈ bbNodeRelaxation d a b, f p < B) :
    bbMixedBase d a b = ∅ := by
  have hR : (bbNodeRelaxation d a b).Nonempty := by
    obtain ⟨p, hp, _⟩ := hbad 0
    exact ⟨p, hp⟩
  apply bb_node_no_minimum_implies_mixed_base_empty d a b f hM hg hf hR
  rintro ⟨p, hp, hmin⟩
  obtain ⟨q, hq, hqv⟩ := hbad (f p)
  exact (not_lt_of_ge (hmin q hq)) hqv

/-- Finiteness of the infimum distinguishes this status from unboundedness.
The no-minimum routing proof itself needs only nonemptiness and nonattainment. -/
theorem bb_node_finite_unattained_implies_mixed_base_empty {n m l r : ℕ}
    (d : ModelData n m l r) (a b : RealVector m) (f : Point n m → ℝ)
    (hM : IsCompact (bbMixedBase d a b)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d a b))
    (hR : (bbNodeRelaxation d a b).Nonempty)
    (_hbelow : BddBelow (f '' bbNodeRelaxation d a b))
    (hbad : ¬ ∃ p, IsMinimizer (bbNodeRelaxation d a b) f p) :
    bbMixedBase d a b = ∅ :=
  bb_node_no_minimum_implies_mixed_base_empty d a b f hM hg hf hR hbad

/-- Equivalent exact finite-unattained status with an explicit infimum value. -/
theorem bb_node_unattained_infimum_implies_mixed_base_empty {n m l r : ℕ}
    (d : ModelData n m l r) (a b : RealVector m) (f : Point n m → ℝ)
    (hM : IsCompact (bbMixedBase d a b)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d a b))
    (hR : (bbNodeRelaxation d a b).Nonempty) (v : ℝ)
    (hinf : IsGLB (f '' bbNodeRelaxation d a b) v)
    (hbad : ∀ p ∈ bbNodeRelaxation d a b, f p ≠ v) : bbMixedBase d a b = ∅ := by
  apply bb_node_no_minimum_implies_mixed_base_empty d a b f hM hg hf hR
  rintro ⟨p, hp, hmin⟩
  apply hbad p hp
  apply le_antisymm
  · apply hinf.2
    rintro _ ⟨q, hq, rfl⟩
    exact hmin q hq
  · exact hinf.1 ⟨p, hp, rfl⟩

theorem bb_mixed_feasible_empty_of_base_empty {n m l r : ℕ} (d : ModelData n m l r)
    (a b : RealVector m) (hM : bbMixedBase d a b = ∅) :
    MixedFeasible d.nonlinearRegion d.linearRegion a b = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨⟨_, hp⟩, hy⟩
  have hm : p ∈ bbMixedBase d a b := ⟨hp, hy⟩
  simp only [hM, Set.mem_empty_iff_false] at hm

end Chapter02

#print axioms Chapter02.bb_unbounded_closed_convex_ray
#print axioms Chapter02.bb_bounded_scalar_ray_direction
#print axioms Chapter02.bb_closed_convex_box_compact
#print axioms Chapter02.bb_linearRegion_closed
#print axioms Chapter02.bb_real_box_closed
#print axioms Chapter02.bb_affine_relaxation_closed
#print axioms Chapter02.bb_affine_mixed_eq
#print axioms Chapter02.bb_affine_relaxation_compact
#print axioms Chapter02.bb_mixed_base_compact_of_refines
#print axioms Chapter02.bb_nonlinearRegion_closed
#print axioms Chapter02.bb_node_relaxation_subset_affine
#print axioms Chapter02.bb_node_relaxation_compact
#print axioms Chapter02.bb_node_minimum_attained
#print axioms Chapter02.bb_node_linear_minimum_attained
#print axioms Chapter02.bb_node_no_minimum_implies_mixed_base_empty
#print axioms Chapter02.bb_node_unbounded_implies_mixed_base_empty
#print axioms Chapter02.bb_node_finite_unattained_implies_mixed_base_empty
#print axioms Chapter02.bb_node_unattained_infimum_implies_mixed_base_empty
#print axioms Chapter02.bb_mixed_feasible_empty_of_base_empty
