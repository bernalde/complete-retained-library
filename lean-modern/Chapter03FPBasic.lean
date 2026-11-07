module

public import Chapter03FPAnalytic

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02
namespace Chapter03.FP
variable {n m l r : ℕ}

theorem yMap_eq_intY_iff (p : Point n m) (y : IntVector m) :
    Chapter03.yMap n m p = intY y ↔ p.2 = intCast y := by
  change (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm p.2 =
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm (intCast y) ↔ _
  exact (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.injective.eq_iff

theorem intCast_injective : Function.Injective (intCast (m := m)) := by
  intro y z h
  funext j
  exact Int.cast_injective (congrFun h j)

theorem relaxation_mem (d : Data n m l r) (p : Point n m) :
    p ∈ d.relaxation ↔ p ∈ d.base ∧ ∀ j, d.model.g j p ≤ 0 := by
  simp only [Data.relaxation, Data.base, ModelData.relaxationOn,
    ContinuousRelaxation, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_univ,
    true_and, ModelData.nonlinearRegion]
  tauto

theorem original_subset_relaxation (d : Data n m l r) : d.original ⊆ d.relaxation :=
  source_mixed_subset_relaxation d.model Set.univ

theorem fiber_subset_original (d : Data n m l r) (y : IntVector m) :
    d.fiber y ⊆ d.original := by
  intro p hp
  exact source_projection_zero_feasible d.model Set.univ hp.1 y hp.2

theorem master_box_integer (d : Data n m l r) (s : State n m)
    {z : Point n m × ℝ} (hz : z ∈ master d s) :
    ∃ y ∈ d.box, z.1.2 = intCast y := by
  rcases hz.1.1.2 with ⟨y,hy,he⟩
  exact ⟨y,by simpa [Data.box] using hy,he⟩

theorem master_base (d : Data n m l r) (s : State n m)
    {z : Point n m × ℝ} (hz : z ∈ master d s) : z.1 ∈ d.base := by
  rcases hz.1.1 with ⟨⟨_,hl⟩,y,hy,he⟩
  exact ⟨hl,by simpa [IntegerBox,he] using hy⟩

theorem cutoff_le (delta U : ℝ) (hd : 0 ≤ delta) : cutoffValue delta U ≤ U := by
  have h := mul_nonneg hd (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right |U| 1))
  unfold cutoffValue
  linarith

theorem best_le_new (d : Data n m l r) {old : Option (Point n m)}
    {p q : Point n m} (h : BestChoice d old p q) : d.f q ≤ d.f p := by
  cases old with
  | none => change q = p at h; simp [h]
  | some u => exact h.2.trans_le (min_le_right _ _)

theorem best_le_old (d : Data n m l r) {u p q : Point n m}
    (h : BestChoice d (some u) p q) : d.f q ≤ d.f u :=
  h.2.trans_le (min_le_left _ _)

theorem best_feasible (d : Data n m l r) {old : Option (Point n m)}
    {p q : Point n m} (h : BestChoice d old p q) (hp : p ∈ d.original)
    (ho : ∀ u, old = some u → u ∈ d.original) : q ∈ d.original := by
  cases old with
  | none => change q = p at h; simpa [h] using hp
  | some u =>
    rcases h.1 with hq | hq
    · rw [hq]; exact ho u rfl
    · rw [hq]; exact hp

theorem best_exists (d : Data n m l r) (old : Option (Point n m)) (p : Point n m) :
    ∃ q, BestChoice d old p q := by
  cases old with
  | none => exact ⟨p,rfl⟩
  | some u =>
    by_cases h : d.f u ≤ d.f p
    · exact ⟨u,Or.inl rfl,(min_eq_left h).symm⟩
    · exact ⟨p,Or.inr rfl,(min_eq_right (le_of_not_ge h)).symm⟩

theorem reply_projection_fiber (d : Data n m l r) {s : State n m}
    {z : Point n m × ℝ} {e : Event n m} (h : EventReply d s z e)
    {pu : Point n m × Point n m} (he : e.success = some pu) :
    e.projection ∈ d.fiber e.target := by
  have ho := h.outcome
  rw [he] at ho
  exact ⟨h.projection_min.1.1,(distance_zero_iff _ _).mp ho.1⟩

theorem reply_success_le_level (d : Data n m l r) {s : State n m}
    {z : Point n m × ℝ} {e : Event n m} (h : EventReply d s z e)
    {pu : Point n m × Point n m} (he : e.success = some pu) :
    d.f pu.2 ≤ d.f pu.1 ∧ d.f pu.1 ≤ d.f e.projection ∧
    Allows (d.level s.incumbent) (d.f pu.2) := by
  have ho := h.outcome
  rw [he] at ho
  have h1 := best_le_new d ho.2.2
  have h2 := ho.2.1.2 e.projection (reply_projection_fiber d h he)
  refine ⟨h1,h2,?_⟩
  have hp := h.projection_min.1.2
  cases hl : d.level s.incumbent with
  | none => trivial
  | some c => rw [hl] at hp; exact h1.trans (h2.trans hp)

theorem append_region_subset (d : Data n m l r) (hd : 0 ≤ d.delta)
    {s : State n m} {z : Point n m × ℝ} {e : Event n m}
    (h : EventReply d s z e) :
    d.region (d.level (append s e).incumbent) ⊆ d.region (d.level s.incumbent) := by
  cases he : e.success with
  | none => simp [append,he]
  | some pu =>
    intro p hp
    refine ⟨hp.1,?_⟩
    have hl := (reply_success_le_level d h he).2.2
    have hv : d.f p ≤ cutoffValue d.delta (d.f pu.2) := by
      simpa [append,he,Data.level,Allows] using hp.2
    have hle := hv.trans (cutoff_le _ _ hd)
    cases hc : d.level s.incumbent with
    | none => trivial
    | some c => rw [hc] at hl; exact hle.trans hl

theorem success_sublevel_subset_old_region (d : Data n m l r)
    {s : State n m} {z : Point n m × ℝ} {e : Event n m}
    (h : EventReply d s z e) {pu : Point n m × Point n m}
    (he : e.success = some pu) {p : Point n m}
    (hp : p ∈ d.relaxation) (hle : d.f p ≤ d.f pu.2) :
    p ∈ d.region (d.level s.incumbent) := by
  refine ⟨hp,?_⟩
  have hl := (reply_success_le_level d h he).2.2
  cases hc : d.level s.incumbent with
  | none => trivial
  | some c => rw [hc] at hl; exact hle.trans hl

end Chapter03.FP
