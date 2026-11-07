module

public import Chapter05PSQCRows
public import Chapter05PSQCGeometry
public import Chapter02PSCAttainment

@[expose] public section

/-! Finite matched quadratic PSC histories on the literal retained base.
These are static row/master and attained-value statements, not an algorithm
or a correctness claim for arbitrary nonlinear models. Empty histories retain
their literal meaning; the attainment consumer explicitly excludes them. -/
noncomputable section
open Set Chapter02
namespace Chapter05.PSQC

variable {p q m l s nw nv : ℕ}

def matchedHistory {d : PSCData p q m l s nw nv}
    (H : List (PSCEntry d × ℝ)) : List (PSCEntry d) := H.map Prod.fst

def scalesValid (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d × ℝ)) : Prop :=
  ∀ ea ∈ H, 0 ≤ ea.2 ∧
    ea.2 ≤ Quadratic.safeScale (lagrangian d ea.1.data) ea.1.data.v d.V

def psqcMaster (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d × ℝ)) : Set (PSCPoint p q m) :=
  {z | pscPointBase d z ∧
    ∀ ea ∈ H, psqcRow d ea.1.data ea.2 z.w z.v z.y ≤ z.beta}

def retainedRow (d : PSCData p q m l s nw nv) (ea : PSCEntry d × ℝ)
    (z : PSCCoordinates p q m) : ℝ :=
  psqcRow d ea.1.data ea.2 z.1.1 z.1.2 z.2

theorem original_mem_master (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (PSCEntry d × ℝ)) (hH : scalesValid d H)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) :
    pscOriginalPoint d w v y ∈ psqcMaster d H := by
  refine ⟨⟨hf.1, ?_⟩, ?_⟩
  · dsimp [pscOriginalPoint, PSCData.objective]
    ring
  · intro ea hea
    exact (row_bounds d ea.1.data ea.1.kkt hr ht hC2 ht2
      (hH ea hea).1 (hH ea hea).2 w v y hf).2

theorem master_subset_linear (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (PSCEntry d × ℝ)) (hH : scalesValid d H) :
    psqcMaster d H ⊆ pscMaster d (matchedHistory H) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro e he
  obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp he
  exact (row_le_psqcRow d ea.1.data ea.1.kkt hr ht hC2 ht2
    (hH ea hea).1 z.w z.v z.y).trans (hz.2 ea hea)

theorem projected_master_subset_gbd (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (PSCEntry d × ℝ)) (hH : scalesValid d H) :
    pscProject (psqcMaster d H) ⊆ pscGBDMaster d (matchedHistory H) :=
  (psc_project_mono (master_subset_linear d hr ht hC2 ht2 H hH)).trans
    (psc_projected_subset_gbd d (matchedHistory H))

theorem attained_original_bound (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (PSCEntry d × ℝ)) (hH : scalesValid d H)
    (z : PSCPoint p q m) (hz : IsMinimizer (psqcMaster d H) PSCPoint.alpha z)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) : z.alpha ≤ d.objective w v y :=
  hz.2 (pscOriginalPoint d w v y) (original_mem_master d hr ht hC2 ht2 H hH w v y hf)

theorem attained_value_order (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (PSCEntry d × ℝ)) (hH : scalesValid d H)
    (gb : RealVector m × ℝ) (ps qs : PSCPoint p q m)
    (hg : IsMinimizer (pscGBDMaster d (matchedHistory H)) Prod.snd gb)
    (hp : IsMinimizer (pscMaster d (matchedHistory H)) PSCPoint.alpha ps)
    (hq : IsMinimizer (psqcMaster d H) PSCPoint.alpha qs) :
    gb.2 ≤ ps.alpha ∧ ps.alpha ≤ qs.alpha :=
  ⟨hg.2 (ps.y, ps.alpha)
      (psc_projected_subset_gbd d _ ⟨ps, hp.1, rfl, rfl⟩),
   hp.2 qs (master_subset_linear d hr ht hC2 ht2 H hH hq.1)⟩

theorem master_append_subset (d : PSCData p q m l s nw nv)
    (H K : List (PSCEntry d × ℝ)) : psqcMaster d (H ++ K) ⊆ psqcMaster d H := by
  intro z hz
  exact ⟨hz.1, fun ea hea => hz.2 ea (List.mem_append.mpr (Or.inl hea))⟩

theorem attained_append_mono (d : PSCData p q m l s nw nv)
    (H K : List (PSCEntry d × ℝ)) (z z' : PSCPoint p q m)
    (hz : IsMinimizer (psqcMaster d H) PSCPoint.alpha z)
    (hz' : IsMinimizer (psqcMaster d (H ++ K)) PSCPoint.alpha z') :
    z.alpha ≤ z'.alpha := hz.2 z' (master_append_subset d H K hz'.1)

theorem retained_row_continuous (d : PSCData p q m l s nw nv)
    (ea : PSCEntry d × ℝ) : Continuous (retainedRow d ea) :=
  row_continuous d ea.1.data ea.2

theorem master_lift_iff (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d × ℝ)) (z : PSCCoordinates p q m × ℝ) :
    pscGraphLift d z ∈ psqcMaster d H ↔
      z ∈ pscEnvelopeEpigraph (pscRetainedBase d) (retainedRow d) H := by
  simp [pscGraphLift, psqcMaster, pscPointBase, pscRetainedOffset,
    pscEnvelopeEpigraph, pscRetainedBase, pscEnvelopeRows, retainedRow]

theorem master_flatten_mem (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d × ℝ)) (z : PSCPoint p q m) (hz : z ∈ psqcMaster d H) :
    pscGraphFlatten z ∈ pscEnvelopeEpigraph (pscRetainedBase d) (retainedRow d) H :=
  ⟨hz.1.1, hz.2⟩

theorem alpha_lift (d : PSCData p q m l s nw nv) (z : PSCCoordinates p q m × ℝ) :
    (pscGraphLift d z).alpha = pscEnvelopeObjective (pscRetainedOffset d) z := rfl

theorem master_minimum_of_envelope (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d × ℝ)) {z : PSCCoordinates p q m × ℝ}
    (hz : IsMinimizer (pscEnvelopeEpigraph (pscRetainedBase d) (retainedRow d) H)
      (pscEnvelopeObjective (pscRetainedOffset d)) z) :
    IsMinimizer (psqcMaster d H) PSCPoint.alpha (pscGraphLift d z) := by
  refine ⟨(master_lift_iff d H z).mpr hz.1, ?_⟩
  intro w hw
  have h := hz.2 (pscGraphFlatten w) (master_flatten_mem d H w hw)
  change pscRetainedOffset d z.1 + z.2 ≤ w.alpha
  rw [hw.1.2]
  exact h

/-- Attainment uses continuity of the frozen rows, not their validity.
The source-facing consumer additionally supplies certified scales and the
ambient convex C2 assumptions for original-model lower bounds. -/
theorem master_attainment (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d × ℝ)) (hne : H ≠ [])
    (hcompact : IsCompact (pscRetainedBase d)) :
    ∃ z, IsMinimizer (psqcMaster d H) PSCPoint.alpha z := by
  have hm : matchedHistory H ≠ [] := by
    cases H with
    | nil => exact (hne rfl).elim
    | cons ea H => simp [matchedHistory]
  obtain ⟨z, hz⟩ := psc_envelope_epigraph_attainment (pscRetainedBase d)
    (retainedRow d) H (pscRetainedOffset d) hne hcompact
    (psc_retained_base_nonempty d (matchedHistory H) hm)
    (psc_retained_offset_continuous d).continuousOn
    (fun ea _ => (retained_row_continuous d ea).continuousOn)
  exact ⟨_, master_minimum_of_envelope d H hz⟩

#print axioms original_mem_master
#print axioms master_subset_linear
#print axioms projected_master_subset_gbd
#print axioms attained_original_bound
#print axioms attained_value_order
#print axioms attained_append_mono
#print axioms master_attainment

end Chapter05.PSQC
