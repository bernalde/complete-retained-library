module

public import Chapter02PSCOrder
public import Chapter02PSCEnvelope

@[expose] public section

/-! Attainment for the actual QG-(5)/Grossmann-PL separable PSC masters,
with one matched feasible-anchor history and the qualified domain encoding.
The retained coordinate base includes Y. Only that base, and separately Y for
cut-only GBD, is assumed compact; the free-height epigraph is not compactified.
OA keeps its own closed constraint tangents. These are existence/minimum
statements, not numerical solver or iteration guarantees. -/

noncomputable section
open scoped BigOperators
namespace Chapter02
variable {p q m l s nw nv : ℕ}

abbrev PSCCoordinates (p q m : ℕ) := (RealVector p × RealVector q) × RealVector m

def pscRetainedBase (d : PSCData p q m l s nw nv) : Set (PSCCoordinates p q m) :=
  {z | d.base z.1.1 z.1.2 z.2}

def pscRetainedOffset (d : PSCData p q m l s nw nv) (z : PSCCoordinates p q m) : ℝ :=
  d.a z.1.1 + d.c z.2

def pscRetainedRow (d : PSCData p q m l s nw nv) (e : PSCEntry d)
    (z : PSCCoordinates p q m) : ℝ := pscRow d e.data z.1.1 z.1.2 z.2

def pscRetainedObjectiveTangent (d : PSCData p q m l s nw nv) (e : PSCEntry d)
    (z : PSCCoordinates p q m) : ℝ := pscObjectiveTangent d e.data z.1.2

def pscRetainedConstraintTangent (d : PSCData p q m l s nw nv) (e : PSCEntry d)
    (j : Fin l) (z : PSCCoordinates p q m) : ℝ :=
  pscConstraintTangent d e.data j z.1.1 z.1.2 z.2

def pscOARetainedBase (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    Set (PSCCoordinates p q m) :=
  {z | z ∈ pscRetainedBase d ∧ ∀ e ∈ H, ∀ j, pscRetainedConstraintTangent d e j z ≤ 0}

def pscGraphLift (d : PSCData p q m l s nw nv)
    (z : PSCCoordinates p q m × ℝ) : PSCPoint p q m :=
  ⟨z.1.1.1, z.1.1.2, z.1.2, z.2, pscRetainedOffset d z.1 + z.2⟩

def pscGraphFlatten (z : PSCPoint p q m) : PSCCoordinates p q m × ℝ :=
  (((z.w, z.v), z.y), z.beta)

@[simp] theorem psc_graph_flatten_lift (d : PSCData p q m l s nw nv)
    (z : PSCCoordinates p q m × ℝ) : pscGraphFlatten (pscGraphLift d z) = z := by
  rcases z with ⟨⟨⟨w,v⟩,y⟩,beta⟩
  rfl

theorem psc_graph_lift_flatten (d : PSCData p q m l s nw nv) (z : PSCPoint p q m)
    (hz : z.alpha = d.a z.w + d.c z.y + z.beta) :
    pscGraphLift d (pscGraphFlatten z) = z := by
  cases z
  simp only [pscGraphFlatten, pscGraphLift, pscRetainedOffset] at *
  congr
  exact hz.symm

theorem psc_master_lift_iff (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (z : PSCCoordinates p q m × ℝ) :
    pscGraphLift d z ∈ pscMaster d H ↔
      z ∈ pscEnvelopeEpigraph (pscRetainedBase d) (pscRetainedRow d) H := by
  simp [pscGraphLift, pscMaster, pscPointBase, pscRetainedOffset,
    pscEnvelopeEpigraph, pscRetainedBase, pscEnvelopeRows, pscRetainedRow]

theorem psc_master_flatten_mem (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (z : PSCPoint p q m) (hz : z ∈ pscMaster d H) :
    pscGraphFlatten z ∈ pscEnvelopeEpigraph (pscRetainedBase d) (pscRetainedRow d) H :=
  ⟨hz.1.1, hz.2⟩

theorem psc_oa_lift_iff (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (z : PSCCoordinates p q m × ℝ) :
    pscGraphLift d z ∈ pscOAMaster d H ↔
      z ∈ pscEnvelopeEpigraph (pscOARetainedBase d H) (pscRetainedObjectiveTangent d) H := by
  constructor
  · intro hz
    exact ⟨⟨hz.1.1, fun e he => (hz.2 e he).2⟩, fun e he => (hz.2 e he).1⟩
  · rintro ⟨⟨hb, hc⟩, ho⟩
    exact ⟨⟨hb, rfl⟩, fun e he => ⟨ho e he, hc e he⟩⟩

theorem psc_oa_flatten_mem (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (z : PSCPoint p q m) (hz : z ∈ pscOAMaster d H) :
    pscGraphFlatten z ∈
      pscEnvelopeEpigraph (pscOARetainedBase d H) (pscRetainedObjectiveTangent d) H :=
  ⟨⟨hz.1.1, fun e he => (hz.2 e he).2⟩, fun e he => (hz.2 e he).1⟩

theorem psc_retained_offset_continuous (d : PSCData p q m l s nw nv) :
    Continuous (pscRetainedOffset d) := by
  exact (d.a.continuous.comp (continuous_fst.comp continuous_fst)).add
    (d.c.continuous.comp continuous_snd)

theorem psc_retained_row_continuous (d : PSCData p q m l s nw nv) (e : PSCEntry d) :
    Continuous (pscRetainedRow d e) := by
  unfold pscRetainedRow pscRow PSCData.nonlinear
  apply Continuous.sub
  · apply continuous_const.add
    apply continuous_finset_sum
    intro j _
    apply continuous_const.mul
    exact (((d.C j).continuous.comp continuous_snd).add
      ((d.D j).continuous.comp (continuous_fst.comp continuous_fst))).add continuous_const
  · apply continuous_finset_sum
    intro i _
    exact continuous_const.mul ((d.G i).continuous.comp
      ((continuous_snd.comp continuous_fst).sub continuous_const))

theorem psc_retained_objective_tangent_continuous (d : PSCData p q m l s nw nv)
    (e : PSCEntry d) : Continuous (pscRetainedObjectiveTangent d e) := by
  exact continuous_const.add (e.data.Dr.continuous.comp
    ((continuous_snd.comp continuous_fst).sub continuous_const))

theorem psc_retained_constraint_tangent_continuous (d : PSCData p q m l s nw nv)
    (e : PSCEntry d) (j : Fin l) : Continuous (pscRetainedConstraintTangent d e j) := by
  exact ((((d.C j).continuous.comp continuous_snd).add
    ((d.D j).continuous.comp (continuous_fst.comp continuous_fst))).add continuous_const).add
      ((e.data.Dt j).continuous.comp
        ((continuous_snd.comp continuous_fst).sub continuous_const))

theorem psc_gbd_row_continuous (d : PSCData p q m l s nw nv) (e : PSCEntry d) :
    Continuous (pscGBDRow d e.data) := by
  unfold pscGBDRow
  apply Continuous.add
  · apply Continuous.add
    · exact continuous_const.add (d.c.continuous.comp (continuous_id.sub continuous_const))
    · apply continuous_finset_sum
      intro j _
      exact continuous_const.mul ((d.C j).continuous.comp (continuous_id.sub continuous_const))
  · apply continuous_finset_sum
    intro i _
    exact continuous_const.mul ((d.E i).continuous.comp (continuous_id.sub continuous_const))

theorem psc_oa_retained_base_compact (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hbase : IsCompact (pscRetainedBase d)) :
    IsCompact (pscOARetainedBase d H) := by
  have he : pscOARetainedBase d H = pscRetainedBase d ∩
      ⋂ e, ⋂ (_ : e ∈ H), ⋂ j, {z | pscRetainedConstraintTangent d e j z ≤ 0} := by
    ext z
    simp [pscOARetainedBase]
  rw [he]
  exact hbase.inter_right (isClosed_iInter fun e => isClosed_iInter fun _ =>
    isClosed_iInter fun j => isClosed_le
      (psc_retained_constraint_tangent_continuous d e j) continuous_const)

theorem psc_entry_mem_retained_base (d : PSCData p q m l s nw nv) (e : PSCEntry d) :
    ((e.data.w,e.data.v),e.data.y) ∈ pscRetainedBase d := e.kkt.feasible.1

theorem psc_retained_base_nonempty (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (hH : H ≠ []) : (pscRetainedBase d).Nonempty := by
  cases H with
  | nil => exact (hH rfl).elim
  | cons e H => exact ⟨_, psc_entry_mem_retained_base d e⟩

theorem psc_Y_nonempty (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (hH : H ≠ []) : d.Y.Nonempty := by
  cases H with
  | nil => exact (hH rfl).elim
  | cons e H => exact ⟨e.data.y, e.kkt.y_mem⟩

theorem psc_master_minimum_of_envelope (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) {z : PSCCoordinates p q m × ℝ}
    (hz : IsMinimizer (pscEnvelopeEpigraph (pscRetainedBase d) (pscRetainedRow d) H)
      (pscEnvelopeObjective (pscRetainedOffset d)) z) :
    IsMinimizer (pscMaster d H) PSCPoint.alpha (pscGraphLift d z) := by
  refine ⟨(psc_master_lift_iff d H z).mpr hz.1, ?_⟩
  intro w hw
  have h := hz.2 (pscGraphFlatten w) (psc_master_flatten_mem d H w hw)
  change pscRetainedOffset d z.1 + z.2 ≤ w.alpha
  rw [hw.1.2]
  exact h

theorem psc_oa_minimum_of_envelope (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) {z : PSCCoordinates p q m × ℝ}
    (hz : IsMinimizer (pscEnvelopeEpigraph (pscOARetainedBase d H)
      (pscRetainedObjectiveTangent d) H) (pscEnvelopeObjective (pscRetainedOffset d)) z) :
    IsMinimizer (pscOAMaster d H) PSCPoint.alpha (pscGraphLift d z) := by
  refine ⟨(psc_oa_lift_iff d H z).mpr hz.1, ?_⟩
  intro w hw
  have h := hz.2 (pscGraphFlatten w) (psc_oa_flatten_mem d H w hw)
  change pscRetainedOffset d z.1 + z.2 ≤ w.alpha
  rw [hw.1.2]
  exact h

/-- Every nonempty feasible-anchor history supplies a nonempty retained base. -/
theorem psc_master_attainment (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (hH : H ≠ []) (hbase : IsCompact (pscRetainedBase d)) :
    ∃ z, IsMinimizer (pscMaster d H) PSCPoint.alpha z := by
  obtain ⟨z, hz⟩ := psc_envelope_epigraph_attainment (pscRetainedBase d)
    (pscRetainedRow d) H (pscRetainedOffset d) hH hbase
    (psc_retained_base_nonempty d H hH) (psc_retained_offset_continuous d).continuousOn
    (fun e _ => (psc_retained_row_continuous d e).continuousOn)
  exact ⟨_, psc_master_minimum_of_envelope d H hz⟩

theorem psc_oa_attainment_of_nonempty (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hH : H ≠ []) (hbase : IsCompact (pscRetainedBase d))
    (hne : (pscOARetainedBase d H).Nonempty) :
    ∃ z, IsMinimizer (pscOAMaster d H) PSCPoint.alpha z := by
  obtain ⟨z, hz⟩ := psc_envelope_epigraph_attainment (pscOARetainedBase d H)
    (pscRetainedObjectiveTangent d) H (pscRetainedOffset d) hH
    (psc_oa_retained_base_compact d H hbase) hne
    (psc_retained_offset_continuous d).continuousOn
    (fun e _ => (psc_retained_objective_tangent_continuous d e).continuousOn)
  exact ⟨_, psc_oa_minimum_of_envelope d H hz⟩

theorem psc_oa_retained_base_of_feasible (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) : ((w,v),y) ∈ pscOARetainedBase d H := by
  have ho := psc_original_mem_oa d H hr ht w v y hf
  exact (psc_oa_flatten_mem d H _ ho).1

theorem psc_oa_retained_base_nonempty (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hH : H ≠ []) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j)) : (pscOARetainedBase d H).Nonempty := by
  cases H with
  | nil => exact (hH rfl).elim
  | cons e H =>
    exact ⟨_, psc_oa_retained_base_of_feasible d (e :: H) hr ht
      e.data.w e.data.v e.data.y e.kkt.feasible⟩

/-- The actual feasible head anchor supplies OA nonemptiness, using relative
convexity and the true derivatives stored by every matched entry. -/
theorem psc_oa_attainment (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hH : H ≠ []) (hbase : IsCompact (pscRetainedBase d))
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j)) :
    ∃ z, IsMinimizer (pscOAMaster d H) PSCPoint.alpha z :=
  psc_oa_attainment_of_nonempty d H hH hbase
    (psc_oa_retained_base_nonempty d H hH hr ht)

/-- Cut-only GBD requires compact Y separately; retained-base compactness alone
does not establish it. -/
theorem psc_gbd_attainment (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (hH : H ≠ []) (hY : IsCompact d.Y) :
    ∃ z, IsMinimizer (pscGBDMaster d H) Prod.snd z := by
  obtain ⟨z, hz⟩ := psc_envelope_epigraph_attainment d.Y
    (fun e : PSCEntry d => pscGBDRow d e.data) H (fun _ => 0) hH hY
    (psc_Y_nonempty d H hH) continuousOn_const
    (fun e _ => (psc_gbd_row_continuous d e).continuousOn)
  refine ⟨z, hz.1, ?_⟩
  intro w hw
  have h := hz.2 w hw
  change 0 + z.2 ≤ 0 + w.2 at h
  simpa only [zero_add] using h

theorem psc_three_masters_attained_order (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hH : H ≠ []) (hbase : IsCompact (pscRetainedBase d))
    (hY : IsCompact d.Y) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j)) :
    ∃ oa ps gb,
      IsMinimizer (pscOAMaster d H) PSCPoint.alpha oa ∧
      IsMinimizer (pscMaster d H) PSCPoint.alpha ps ∧
      IsMinimizer (pscGBDMaster d H) Prod.snd gb ∧
      gb.2 ≤ ps.alpha ∧ ps.alpha ≤ oa.alpha := by
  obtain ⟨oa, ho⟩ := psc_oa_attainment d H hH hbase hr ht
  obtain ⟨ps, hp⟩ := psc_master_attainment d H hH hbase
  obtain ⟨gb, hg⟩ := psc_gbd_attainment d H hH hY
  exact ⟨oa, ps, gb, ho, hp, hg, psc_attained_value_order d H oa ps gb ho hp hg⟩

theorem psc_empty_master_unbounded (d : PSCData p q m l s nw nv)
    (hne : (pscRetainedBase d).Nonempty) :
    ∀ B : ℝ, ∃ z ∈ pscMaster d [], z.alpha < B := by
  intro B
  obtain ⟨z, hz, hlt⟩ := psc_empty_envelope_unbounded (pscRetainedBase d)
    (pscRetainedRow d) (pscRetainedOffset d) hne B
  exact ⟨pscGraphLift d z, (psc_master_lift_iff d [] z).mpr hz, hlt⟩

theorem psc_empty_oa_unbounded (d : PSCData p q m l s nw nv)
    (hne : (pscRetainedBase d).Nonempty) :
    ∀ B : ℝ, ∃ z ∈ pscOAMaster d [], z.alpha < B := by
  intro B
  obtain ⟨z, hz, hlt⟩ := psc_empty_master_unbounded d hne B
  exact ⟨z, ⟨hz.1, by simp⟩, hlt⟩

theorem psc_empty_gbd_unbounded (d : PSCData p q m l s nw nv) (hne : d.Y.Nonempty) :
    ∀ B : ℝ, ∃ z ∈ pscGBDMaster d [], z.2 < B := by
  simpa [pscGBDMaster, pscEnvelopeEpigraph, pscEnvelopeRows, pscEnvelopeObjective] using
    psc_empty_envelope_unbounded d.Y (fun e : PSCEntry d => pscGBDRow d e.data)
      (fun _ => 0) hne

end Chapter02

#print axioms Chapter02.psc_graph_flatten_lift
#print axioms Chapter02.psc_graph_lift_flatten
#print axioms Chapter02.psc_master_lift_iff
#print axioms Chapter02.psc_master_flatten_mem
#print axioms Chapter02.psc_oa_lift_iff
#print axioms Chapter02.psc_oa_flatten_mem
#print axioms Chapter02.psc_retained_offset_continuous
#print axioms Chapter02.psc_retained_row_continuous
#print axioms Chapter02.psc_retained_objective_tangent_continuous
#print axioms Chapter02.psc_retained_constraint_tangent_continuous
#print axioms Chapter02.psc_gbd_row_continuous
#print axioms Chapter02.psc_oa_retained_base_compact
#print axioms Chapter02.psc_entry_mem_retained_base
#print axioms Chapter02.psc_retained_base_nonempty
#print axioms Chapter02.psc_Y_nonempty
#print axioms Chapter02.psc_master_minimum_of_envelope
#print axioms Chapter02.psc_oa_minimum_of_envelope
#print axioms Chapter02.psc_master_attainment
#print axioms Chapter02.psc_oa_attainment_of_nonempty
#print axioms Chapter02.psc_oa_retained_base_of_feasible
#print axioms Chapter02.psc_oa_retained_base_nonempty
#print axioms Chapter02.psc_oa_attainment
#print axioms Chapter02.psc_gbd_attainment
#print axioms Chapter02.psc_three_masters_attained_order
#print axioms Chapter02.psc_empty_master_unbounded
#print axioms Chapter02.psc_empty_oa_unbounded
#print axioms Chapter02.psc_empty_gbd_unbounded
