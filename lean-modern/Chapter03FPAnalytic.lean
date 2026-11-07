module

public import Chapter03FPModel
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section

/-! Candidate analytic attainment for the literal source pump. Compactness is
derived for the nonlinear relaxation; the linear master is never assumed compact.
All results are supporting declarations, not independent accepted endpoints. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02
namespace Chapter03.FP
variable {n m l r : ℕ}

theorem base_closed (d : Data n m l r) : IsClosed d.base := by
  have hL : IsClosed d.model.linearRegion := by
    have he : d.model.linearRegion = ⋂ j, {p | LinearForm (d.model.A j) (d.model.B j) p ≤ d.model.rhs j} := by
      ext p; simp [ModelData.linearRegion]
    rw [he]
    exact isClosed_iInter fun j => isClosed_le (linearForm_continuous _ _) continuous_const
  have hB : IsClosed {p : Point n m | ∀ j, d.model.lo j ≤ p.2 j ∧ p.2 j ≤ d.model.hi j} := by
    have he : {p : Point n m | ∀ j, d.model.lo j ≤ p.2 j ∧ p.2 j ≤ d.model.hi j} =
        ⋂ j, {p | d.model.lo j ≤ p.2 j} ∩ {p | p.2 j ≤ d.model.hi j} := by
      ext p; simp
    rw [he]
    exact isClosed_iInter fun j => (isClosed_le continuous_const
      ((continuous_apply j).comp continuous_snd)).inter
      (isClosed_le ((continuous_apply j).comp continuous_snd) continuous_const)
  exact hL.inter hB

theorem base_convex (d : Data n m l r) : Convex ℝ d.base := by
  have he : d.base = ContinuousRelaxation Set.univ d.model.linearRegion d.model.lo d.model.hi := by
    ext p; simp [Data.base, ContinuousRelaxation]
  rw [he]
  exact continuousRelaxation_convex _ _ convex_univ (source_linearRegion_convex d.model)

theorem relaxation_mem_iff (d : Data n m l r) (p : Point n m) :
    p ∈ d.relaxation ↔ p ∈ d.base ∧ ∀ j, d.model.g j p ≤ 0 := by
  simp [Data.relaxation, Data.base, ModelData.relaxationOn, ContinuousRelaxation,
    ModelData.nonlinearRegion, and_assoc, and_left_comm, and_comm]

theorem relaxation_subset_base (d : Data n m l r) : d.relaxation ⊆ d.base :=
  fun p hp => ((relaxation_mem_iff d p).mp hp).1

theorem continuousOn_f (d : Data n m l r) (h : Analytic d) : ContinuousOn d.f d.base :=
  fun p hp => (h.derivative_f p hp).continuousAt.continuousWithinAt

theorem continuousOn_g (d : Data n m l r) (h : Analytic d) (j : Fin l) :
    ContinuousOn (d.model.g j) d.base :=
  fun p hp => (h.derivative_g j p hp).continuousAt.continuousWithinAt

theorem relaxation_closed (d : Data n m l r) (h : Analytic d) : IsClosed d.relaxation := by
  have he : d.relaxation = d.base ∩ ⋂ j, {p ∈ d.base | d.model.g j p ≤ 0} := by
    ext p; simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, relaxation_mem_iff]
    constructor
    · rintro ⟨hb, hg⟩; exact ⟨hb, fun j => ⟨hb, hg j⟩⟩
    · rintro ⟨hb, hg⟩; exact ⟨hb, fun j => (hg j).2⟩
  rw [he]
  exact (base_closed d).inter (isClosed_iInter fun j =>
    (base_closed d).isClosed_le (continuousOn_g d h j) continuousOn_const)

theorem relaxation_compact (d : Data n m l r) (h : Analytic d) : IsCompact d.relaxation :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨relaxation_closed d h, h.bounded_relaxation⟩

theorem relaxation_convex (d : Data n m l r) (h : Analytic d) : Convex ℝ d.relaxation := by
  have he : d.relaxation = d.base ∩ d.model.nonlinearRegion := by
    ext p; exact relaxation_mem_iff d p
  rw [he]
  exact source_nonlinearRegion_convex_on d.model d.base (base_convex d) h.convex_g

theorem region_compact (d : Data n m l r) (h : Analytic d) (level : Option ℝ) :
    IsCompact (d.region level) := by
  cases level with
  | none => simpa [Data.region, Allows] using relaxation_compact d h
  | some c =>
    have hc : IsClosed (d.region (some c)) :=
      (relaxation_closed d h).isClosed_le
        ((continuousOn_f d h).mono (relaxation_subset_base d)) continuousOn_const
    exact (relaxation_compact d h).of_isClosed_subset hc (fun _ hp => hp.1)

theorem region_convex (d : Data n m l r) (h : Analytic d) (level : Option ℝ) :
    Convex ℝ (d.region level) := by
  cases level with
  | none => simpa [Data.region, Allows] using relaxation_convex d h
  | some c =>
    exact (h.convex_f.subset (relaxation_subset_base d) (relaxation_convex d h)).convex_le c

theorem fiber_compact (d : Data n m l r) (h : Analytic d) (y : IntVector m) :
    IsCompact (d.fiber y) :=
  (relaxation_compact d h).inter_right (isClosed_eq continuous_snd continuous_const)

theorem fiber_convex (d : Data n m l r) (h : Analytic d) (y : IntVector m) :
    Convex ℝ (d.fiber y) := by
  intro p hp q hq a b ha hb hab
  refine ⟨relaxation_convex d h hp.1 hq.1 ha hb hab, ?_⟩
  change a • p.2 + b • q.2 = intCast y
  rw [hp.2, hq.2, ← add_smul, hab, one_smul]

theorem relaxation_attained (d : Data n m l r) (h : Analytic d)
    (hne : d.relaxation.Nonempty) : ∃ p, IsMinimizer d.relaxation d.f p :=
  compact_feasible_attainment (relaxation_compact d h) hne
    ((continuousOn_f d h).mono (relaxation_subset_base d))

theorem region_objective_attained (d : Data n m l r) (h : Analytic d) (level : Option ℝ)
    (hne : (d.region level).Nonempty) : ∃ p, IsMinimizer (d.region level) d.f p :=
  compact_feasible_attainment (region_compact d h level) hne
    ((continuousOn_f d h).mono (fun _ hp => relaxation_subset_base d hp.1))

theorem distance_continuous (y : IntVector m) : Continuous (distance (n := n) y) := by
  have hy : Continuous (Chapter03.yMap n m) := (Chapter03.yMap n m).continuous_of_finiteDimensional
  exact (continuous_const.sub hy).norm.pow 2

theorem projection_attained (d : Data n m l r) (h : Analytic d) (level : Option ℝ)
    (y : IntVector m) (hne : (d.region level).Nonempty) :
    ∃ p, IsMinimizer (d.region level) (distance y) p :=
  compact_feasible_attainment (region_compact d h level) hne (distance_continuous y).continuousOn

theorem fiber_attained (d : Data n m l r) (h : Analytic d) (y : IntVector m)
    (hne : (d.fiber y).Nonempty) : ∃ p, IsMinimizer (d.fiber y) d.f p :=
  compact_feasible_attainment (fiber_compact d h y) hne
    ((continuousOn_f d h).mono (fun _ hp => relaxation_subset_base d hp.1))

theorem fiber_projection_attained (d : Data n m l r) (h : Analytic d)
    (y target : IntVector m) (hne : (d.fiber y).Nonempty) :
    ∃ p, IsMinimizer (d.fiber y) (distance target) p :=
  compact_feasible_attainment (fiber_compact d h y) hne
    (distance_continuous target).continuousOn

theorem projection_normal (d : Data n m l r) (h : Analytic d)
    (level : Option ℝ) (y : IntVector m) {p : Point n m}
    (hp : IsMinimizer (d.region level) (distance y) p)
    {q : Point n m} (hq : q ∈ d.region level) :
    0 ≤ @inner ℝ _ _ (Chapter03.yMap n m p - intY y)
      (Chapter03.yMap n m q - Chapter03.yMap n m p) := by
  have hm : Chapter03.ProjectionMin (Chapter03.yMap n m '' d.region level)
      (intY y) (Chapter03.yMap n m p) := by
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    rintro v ⟨w, hw, rfl⟩
    exact hp.2 w hw
  exact Chapter03.projection_cut_valid
    ((region_convex d h level).linear_image (Chapter03.yMap n m)) hm _ ⟨q, hq, rfl⟩

/-- The selected integer values are those admitting a full master witness.
No closedness, boundedness or optimizer premise is imposed on their fibers. -/
theorem finite_integer_value_attained (lo hi : RealVector m)
    (S : Set (Point n m × ℝ)) (reference : Point n m)
    (hInt : ∀ z ∈ S, ∃ y ∈ IntegerBox lo hi, z.1.2 = intCast y)
    (hne : S.Nonempty) : ∃ z, IsMinimizer S (fun w => l1 reference w.1) z := by
  let T : Set (IntVector m) := {y | y ∈ IntegerBox lo hi ∧ ∃ z ∈ S, z.1.2 = intCast y}
  have hf : T.Finite := (integerBox_finite lo hi).subset (fun _ hy => hy.1)
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨y₀, hy₀, he₀⟩ := hInt z₀ hz₀
  have ht : T.Nonempty := ⟨y₀, hy₀, z₀, hz₀, he₀⟩
  obtain ⟨y, hy, hm⟩ := Set.exists_min_image T (fun y => ∑ j, |intCast y j - reference.2 j|) hf ht
  obtain ⟨z, hz, he⟩ := hy.2
  refine ⟨z, hz, ?_⟩
  intro w hw
  obtain ⟨v, hv, hev⟩ := hInt w hw
  have hh := hm v ⟨hv, w, hw, hev⟩
  simpa only [l1, he, hev] using hh

theorem master_integer (d : Data n m l r) (s : State n m)
    {z : Point n m × ℝ} (hz : z ∈ master d s) :
    ∃ y ∈ IntegerBox d.model.lo d.model.hi, z.1.2 = intCast y :=
  hz.1.1.2

theorem master_attained (d : Data n m l r) (s : State n m)
    (hne : (master d s).Nonempty) : ∃ z, IsMinimizer (master d s) (masterCost s) z :=
  finite_integer_value_attained d.model.lo d.model.hi (master d s) s.reference
    (fun _ hz => master_integer d s hz) hne

theorem initialization_nonempty (d : Data n m l r) (h : Analytic d) : Nonempty (Initialization d) := by
  classical
  by_cases he : d.relaxation.Nonempty
  · obtain ⟨p, hp⟩ := relaxation_attained d h he
    exact ⟨Initialization.minimum p hp⟩
  · exact ⟨Initialization.empty he⟩

theorem masterChoice_nonempty (d : Data n m l r) (s : State n m) : Nonempty (MasterChoice d s) := by
  classical
  by_cases he : (master d s).Nonempty
  · obtain ⟨p, hp⟩ := master_attained d s he
    exact ⟨MasterChoice.minimum p hp⟩
  · exact ⟨MasterChoice.empty he⟩

theorem projectionChoice_nonempty (d : Data n m l r) (h : Analytic d)
    (s : State n m) (y : IntVector m) : Nonempty (ProjectionChoice d s y) := by
  classical
  by_cases he : (d.region (d.level s.incumbent)).Nonempty
  · obtain ⟨p, hp⟩ := projection_attained d h _ y he
    exact ⟨ProjectionChoice.minimum p hp⟩
  · exact ⟨ProjectionChoice.empty he⟩

theorem distance_zero_iff (y : IntVector m) (p : Point n m) :
    distance y p = 0 ↔ p.2 = intCast y := by
  rw [distance, Chapter03.projection_zero_iff]
  change (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm (intCast y) =
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm p.2 ↔ p.2 = intCast y
  rw [(WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.injective.eq_iff]
  exact eq_comm

theorem projection_zero_fiber (d : Data n m l r) (level : Option ℝ) (y : IntVector m)
    {p : Point n m} (hp : IsMinimizer (d.region level) (distance y) p)
    (hz : distance y p = 0) : p ∈ d.fiber y :=
  ⟨hp.1.1, (distance_zero_iff y p).mp hz⟩

theorem fiber_original (d : Data n m l r) (y : IntVector m)
    {p : Point n m} (hp : p ∈ d.fiber y) : p ∈ d.original :=
  Chapter03.source_projection_zero_feasible d.model Set.univ hp.1 y hp.2

theorem polished_in_region (d : Data n m l r) (level : Option ℝ) (y : IntVector m)
    {projection polished : Point n m}
    (hp : IsMinimizer (d.region level) (distance y) projection)
    (hz : distance y projection = 0)
    (hpol : IsMinimizer (d.fiber y) d.f polished) :
    polished ∈ d.region level ∧ d.f polished ≤ d.f projection := by
  have hle := hpol.2 projection (projection_zero_fiber d level y hp hz)
  refine ⟨⟨hpol.1.1, ?_⟩, hle⟩
  cases level with
  | none => trivial
  | some c => exact hle.trans hp.1.2

end Chapter03.FP
