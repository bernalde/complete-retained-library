module

public import Chapter05PSQCMixedModel
public import Chapter05QOAFiber

@[expose] public section

/-! Geometry of the literal mixed PSC master. The permanent seed and
restoration events supply individual OA constraint rows; feasible source
events supply only their full PSC objective rows. The total height is lifted
to the PSC alpha coordinate, with beta equal to height minus the affine offset.
These author results are subject to independent frozen review. -/
noncomputable section
open Set Chapter02 Chapter03.OAKKT Chapter05.Quadratic
open scoped BigOperators

namespace Chapter05.PSQC.Mixed
variable {p q m l s nw nv : ℕ}

/-- Frozen full rows are continuous in the actual flattened coordinates. -/
theorem fullCut_flat_continuous (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (scale : ℝ) :
    Continuous (fun z : Point (p+q) m =>
      fullCut d e scale (weightedX z.1) (weightedV z.1) z.2) := by
  have hw : Continuous (fun z : Point (p+q) m =>
      (weightedX (n := p) (s := q)) z.1) :=
    (weightedX (n := p) (s := q)).continuous.comp continuous_fst
  have hv : Continuous (fun z : Point (p+q) m =>
      (weightedV (n := p) (s := q)) z.1) :=
    (weightedV (n := p) (s := q)).continuous.comp continuous_fst
  have hcoords : Continuous (fun z : Point (p+q) m =>
      (((weightedX z.1, weightedV z.1), z.2) : PSCCoordinates p q m)) :=
    (hw.prodMk hv).prodMk continuous_snd
  have hrow := (row_continuous d e scale).comp hcoords
  change Continuous (fun z : Point (p+q) m =>
    d.a (weightedX z.1) + d.c z.2 +
      psqcRow d e scale (weightedX z.1) (weightedV z.1) z.2)
  exact ((d.a.continuous.comp hw).add (d.c.continuous.comp continuous_snd)).add
    hrow

/-- A single retained full row supports its actual anchor value throughout
the same hard fiber. Nonlinear feasibility at the queried point is not needed. -/
theorem fullCut_same_fiber_support (d : PSCData p q m l s nw nv)
    (e : PSCEntry d) (hr : ConvexOn ℝ univ d.r)
    (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    {scale : ℝ} (hscale : 0 ≤ scale)
    {w : RealVector p} {v : RealVector q} {y : RealVector m} {height : ℝ}
    (hb : d.base w v y) (hy : y = e.data.y)
    (hrow : fullCut d e.data scale w v y ≤ height) :
    d.objective e.data.w e.data.v e.data.y ≤ height := by
  let z : PSCPoint p q m := ⟨w, v, y, height - d.a w - d.c y, height⟩
  have hz : pscPointBase d z := by
    refine ⟨hb, ?_⟩
    dsimp [z]
    ring
  have hlinear := row_le_psqcRow d e.data e.kkt hr ht hr2 ht2 hscale w v y
  have hbeta : pscRow d e.data z.w z.v z.y ≤ z.beta := by
    dsimp [z]
    dsimp only [fullCut] at hrow
    linarith
  have hgbd := psc_row_implies_gbd d e.data e.kkt z hz hbeta
  change pscGBDRow d e.data y ≤ height at hgbd
  rw [hy, psc_gbd_at_anchor] at hgbd
  exact hgbd

/-- The restoration contradiction uses only the individual constraint rows.
No restoration objective row or equality to an all-OA master is needed. -/
theorem restoration_constraintBase_excludes {d : QOA.Data (p+q) m l s}
    (hr : QOA.Regularity d) {e : QOA.Event d} (he : QOA.EventValid d e)
    {slack : RealVector l} (hs : e.restoration = some slack)
    {T : List (QOA.Token (p+q) m l)} (het : e.token ∈ T) :
    ¬ ∃ z ∈ QOA.constraintBase (QOA.masterData d) T,
      z.2 = intCast e.target := by
  have hm := he.2
  rw [hs] at hm
  have hempty : ¬ ∃ x ∈ d.hardFiber e.target,
      ∀ j, d.g j (x, intCast e.target) ≤ 0 := by
    simpa only [QOA.Data.feasibleFiber, QOA.Data.soft,
      Set.nonempty_def, Set.mem_setOf_eq] using hm.1
  have hex := QOA.restoration_fiber_quadratic_excludes (d.hardFiber e.target) d.g
    (intCast e.target) e.x e.constraintScale
    (QOA.hardFiber_convex hr.X_convex e.target)
    hr.constraint_convex hr.constraint_C2
    (QOA.event_restoration_positive_minimum he hs) hempty
    (fun j => (he.1.2 j).1)
  rintro ⟨z, hz, hy⟩
  have hp : z = (z.1, intCast e.target) := Prod.ext rfl hy
  apply hex
  refine ⟨z.1, QOA.base_hard hz.1 hy, fun j => ?_⟩
  have hrow := hz.2 e.token het j
  change cut (d.g j) (e.x, intCast e.target) (e.constraintScale j) z ≤ 0 at hrow
  rw [hp] at hrow
  exact hrow

/-- Every original feasible epigraph point satisfies precisely the retained
seed, restoration constraints and source-selected full PSC rows. -/
theorem original_lift (c : Context p q m l s nw nv)
    (seed : QOA.Token (p+q) m l) (hs : seed.Safe c.qd)
    (H : List (Event c)) (hH : HistoryValid c H) :
    EpigraphLift c.qd.original c.qd.f ⊆ master c seed H := by
  rintro z ⟨hz, hheight⟩
  have hr := qoa_regularity c
  refine (master_mem_iff c seed H z).mpr ⟨hz.1, ?_, ?_, ?_, ?_⟩
  · exact (cut_le_of_safeScale hr.objective_convex hr.objective_C2
      seed.anchor c.qd.base hs.1.2 z.1 hz.1).trans hheight
  · intro j
    exact (cut_le_of_safeScale (hr.constraint_convex j) (hr.constraint_C2 j)
      seed.anchor c.qd.base (hs.2 j).2 z.1 hz.1).trans (hz.2 j)
  · intro e he j
    have hevalid : QOA.EventValid c.qd e.event := hH (.restoration e) he
    exact (cut_le_of_safeScale (hr.constraint_convex j) (hr.constraint_C2 j)
      e.event.anchor c.qd.base (hevalid.1.2 j).2 z.1 hz.1).trans (hz.2 j)
  · intro e he
    have hevalid : e.Valid := hH (.feasible e) he
    have hrow := fullCut_le c.data e.entry.data e.entry.kkt c.r_convex c.t_convex
      c.r_C2 c.t_C2 hevalid.1 hevalid.2
      (weightedX z.1.1) (weightedV z.1.1) z.1.2 ((original_iff c z.1).mp hz)
    exact hrow.trans hheight

theorem master_lower_bound (c : Context p q m l s nw nv)
    (seed : QOA.Token (p+q) m l) (hs : seed.Safe c.qd)
    (H : List (Event c)) (hH : HistoryValid c H) {z : Point (p+q) m × ℝ}
    (hz : IsMinimizer (master c seed H) Prod.snd z) :
    IsLowerBound c.qd.original c.qd.f z.2 := by
  intro x hx
  exact hz.2 (x, c.qd.f x) (original_lift c seed hs H hH ⟨hx, le_rfl⟩)

theorem original_empty_of_master_empty (c : Context p q m l s nw nv)
    (seed : QOA.Token (p+q) m l) (hs : seed.Safe c.qd)
    (H : List (Event c)) (hH : HistoryValid c H)
    (he : ¬ (master c seed H).Nonempty) : ¬ c.qd.original.Nonempty := by
  rintro ⟨x, hx⟩
  exact he ⟨(x, c.qd.f x), original_lift c seed hs H hH ⟨hx, le_rfl⟩⟩

theorem master_append_subset (c : Context p q m l s nw nv)
    (seed : QOA.Token (p+q) m l) (H K : List (Event c)) :
    master c seed (H ++ K) ⊆ master c seed H := by
  intro z hz
  obtain ⟨hb, hs, hg, hr, hf⟩ := (master_mem_iff c seed (H ++ K) z).mp hz
  exact (master_mem_iff c seed H z).mpr ⟨hb, hs, hg,
    fun e he => hr e (List.mem_append.mpr (Or.inl he)),
    fun e he => hf e (List.mem_append.mpr (Or.inl he))⟩

theorem attained_append_mono (c : Context p q m l s nw nv)
    (seed : QOA.Token (p+q) m l) (H K : List (Event c))
    {z z' : Point (p+q) m × ℝ}
    (hz : IsMinimizer (master c seed H) Prod.snd z)
    (hz' : IsMinimizer (master c seed (H ++ K)) Prod.snd z') : z.2 ≤ z'.2 :=
  hz.2 z' (master_append_subset c seed H K hz'.1)

theorem objectiveRows_continuous (c : Context p q m l s nw nv)
    (seed : QOA.Token (p+q) m l) (H : List (Event c))
    (row : Point (p+q) m → ℝ) (hrow : row ∈ objectiveRows c seed H) :
    Continuous row := by
  rcases List.mem_cons.mp hrow with hs | hH
  · subst row
    exact QOA.cut_continuous _ _ _
  · obtain ⟨e, _, he⟩ := List.mem_flatMap.mp hH
    cases e with
    | feasible e =>
      simp only [Event.objectiveRows, List.mem_singleton] at he
      subst row
      exact fullCut_flat_continuous c.data e.entry.data e.scale
    | restoration e => simp only [Event.objectiveRows, List.not_mem_nil] at he

/-- The seed makes the finite continuous objective envelope nonempty. Only
the retained variable base is compact; the total height remains unbounded. -/
theorem master_minimum_exists (c : Context p q m l s nw nv)
    (seed : QOA.Token (p+q) m l) (H : List (Event c))
    (hne : (master c seed H).Nonempty) :
    ∃ z, IsMinimizer (master c seed H) Prod.snd z := by
  have hrows : objectiveRows c seed H ≠ [] := List.cons_ne_nil _ _
  have hbase : (QOA.constraintBase (QOA.masterData c.qd)
      (constraintTokens seed H)).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z.1, hz.1⟩
  obtain ⟨z, hz⟩ := psc_envelope_epigraph_attainment
    (QOA.constraintBase (QOA.masterData c.qd) (constraintTokens seed H))
    (fun row => row) (objectiveRows c seed H) (fun _ => 0) hrows
    (QOA.constraintBase_compact _ _ (QOA.base_compact (qoa_regularity c).X_compact))
    hbase continuousOn_const
    (fun row hrow => (objectiveRows_continuous c seed H row hrow).continuousOn)
  refine ⟨z, ?_⟩
  have hoff : pscEnvelopeObjective (fun _ : Point (p+q) m => (0 : ℝ)) = Prod.snd := by
    funext x
    simp only [pscEnvelopeObjective, zero_add]
  rw [hoff] at hz
  exact hz

theorem feasible_event_master_lower (c : Context p q m l s nw nv)
    {e : FeasibleEvent c} (he : e.Valid)
    {seed : QOA.Token (p+q) m l} {H : List (Event c)}
    (heH : Event.feasible e ∈ H) {z : Point (p+q) m × ℝ}
    (hz : z ∈ master c seed H) (hy : z.1.2 = intCast e.target) :
    c.qd.f e.toQOA.anchor ≤ z.2 := by
  have hm : pscSourceMatches e.source e.entry :=
    source_entry_matches c.data c.r_convex c.t_convex e.source
  have hz' := (master_mem_iff c seed H z).mp hz
  have hentryY : e.entry.data.y = intCast e.target := hm.2.2.1.trans e.source_y
  have hbound := fullCut_same_fiber_support c.data e.entry c.r_convex c.t_convex
    c.r_C2 c.t_C2 he.1 ((base_iff c z.1).mp hz'.1)
    (hy.trans hentryY.symm) (hz'.2.2.2.2 e heH)
  have hvalue : c.qd.f e.toQOA.anchor =
      c.data.objective e.entry.data.w e.entry.data.v e.entry.data.y := by
    simp only [FeasibleEvent.toQOA, QOA.Event.anchor, objective_eq,
      weightedX_insert, weightedV_insert, hm.1, hm.2.1, hm.2.2.1, e.source_y]
  rw [hvalue]
  exact hbound

theorem restoration_event_master_excludes (c : Context p q m l s nw nv)
    {e : RestorationEvent c} (he : QOA.EventValid c.qd e.event)
    {seed : QOA.Token (p+q) m l} {H : List (Event c)}
    (heH : Event.restoration e ∈ H) :
    ¬ ∃ z ∈ master c seed H, z.1.2 = intCast e.event.target := by
  have het : e.event.token ∈ constraintTokens seed H := by
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    exact ⟨Event.restoration e, heH, List.mem_singleton_self _⟩
  have hex := restoration_constraintBase_excludes (qoa_regularity c) he e.restoration_eq het
  rintro ⟨z, hz, hy⟩
  exact hex ⟨z.1, hz.1, hy⟩

/-- The geometric input to finite progress. Other retained events need not
be valid for this one processed-fiber support/exclusion conclusion. -/
theorem event_master_same_fiber (c : Context p q m l s nw nv)
    {e : Event c} (he : EventValid c e)
    {seed : QOA.Token (p+q) m l} {H : List (Event c)} (heH : e ∈ H)
    {z : Point (p+q) m × ℝ} (hz : z ∈ master c seed H)
    (hy : z.1.2 = intCast e.target) :
    e.toQOA.restoration = none ∧ c.qd.f e.anchor ≤ z.2 := by
  cases e with
  | feasible a => exact ⟨rfl, feasible_event_master_lower c he heH hz hy⟩
  | restoration a =>
    exact (restoration_event_master_excludes c he heH ⟨z, hz, hy⟩).elim

#print axioms original_lift
#print axioms master_lower_bound
#print axioms original_empty_of_master_empty
#print axioms attained_append_mono
#print axioms master_minimum_exists
#print axioms feasible_event_master_lower
#print axioms restoration_event_master_excludes
#print axioms event_master_same_fiber

end Chapter05.PSQC.Mixed
