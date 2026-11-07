module

public import Chapter02
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-! Generic finite-envelope attainment infrastructure for the qualified
QG-(5)/Grossmann-PL separable PSC subclass and matched feasible-anchor histories.
This module makes no PSC cut-validity claim: arbitrary continuous rows are not
assumed to be tangents of one function. Compactness is imposed on the retained
coordinate domain, never on the free-height epigraph. Fiber-Slater and domain
normals belong to the separate source-facing qualified completion. No numerical
solver or totalized empty/unbounded infimum is used. -/

noncomputable section
namespace Chapter02

section Envelopes
variable {E I : Type*}

def pscEnvelopeRows (row : I → E → ℝ) (H : List I) (z : E) (beta : ℝ) : Prop :=
  ∀ i ∈ H, row i z ≤ beta

def pscEnvelopeTail (row : I → E → ℝ) : List I → (E → ℝ) → E → ℝ
  | [], floor => floor
  | i :: H, floor => fun z => max (row i z) (pscEnvelopeTail row H floor z)

def pscEnvelope (row : I → E → ℝ) (first : I) (tail : List I) : E → ℝ :=
  pscEnvelopeTail row tail (row first)

def pscEnvelopeEpigraph (C : Set E) (row : I → E → ℝ) (H : List I) : Set (E × ℝ) :=
  {p | p.1 ∈ C ∧ pscEnvelopeRows row H p.1 p.2}

def pscEnvelopeObjective (offset : E → ℝ) (p : E × ℝ) : ℝ := offset p.1 + p.2

def pscFlooredEnvelopeEpigraph (C : Set E) (row : I → E → ℝ) (H : List I)
    (floor : E → ℝ) : Set (E × ℝ) :=
  {p | p.1 ∈ C ∧ floor p.1 ≤ p.2 ∧ pscEnvelopeRows row H p.1 p.2}

theorem psc_envelope_rows_nil (row : I → E → ℝ) (z : E) (beta : ℝ) :
    pscEnvelopeRows row [] z beta := by simp [pscEnvelopeRows]

theorem psc_envelope_rows_cons (row : I → E → ℝ) (i : I) (H : List I)
    (z : E) (beta : ℝ) :
    pscEnvelopeRows row (i :: H) z beta ↔ row i z ≤ beta ∧ pscEnvelopeRows row H z beta := by
  simp [pscEnvelopeRows]

theorem psc_envelope_rows_append (row : I → E → ℝ) (H K : List I) (z : E) (beta : ℝ) :
    pscEnvelopeRows row (H ++ K) z beta ↔
      pscEnvelopeRows row H z beta ∧ pscEnvelopeRows row K z beta := by
  simp [pscEnvelopeRows, or_imp, forall_and]

theorem psc_envelope_tail_le_iff (row : I → E → ℝ) (H : List I) (floor : E → ℝ)
    (z : E) (beta : ℝ) :
    pscEnvelopeTail row H floor z ≤ beta ↔
      floor z ≤ beta ∧ pscEnvelopeRows row H z beta := by
  induction H with
  | nil => simp [pscEnvelopeTail, pscEnvelopeRows]
  | cons i H ih =>
    simp only [pscEnvelopeTail, max_le_iff, ih, psc_envelope_rows_cons]
    tauto

theorem psc_envelope_le_iff (row : I → E → ℝ) (i : I) (H : List I) (z : E) (beta : ℝ) :
    pscEnvelope row i H z ≤ beta ↔ pscEnvelopeRows row (i :: H) z beta := by
  rw [pscEnvelope, psc_envelope_tail_le_iff, psc_envelope_rows_cons]

theorem psc_envelope_epigraph_iff (C : Set E) (row : I → E → ℝ) (i : I)
    (H : List I) (p : E × ℝ) :
    p ∈ pscEnvelopeEpigraph C row (i :: H) ↔
      p.1 ∈ C ∧ pscEnvelope row i H p.1 ≤ p.2 := by
  simp only [pscEnvelopeEpigraph, Set.mem_setOf_eq, psc_envelope_le_iff]

theorem psc_envelope_epigraph_projection (C : Set E) (row : I → E → ℝ)
    (i : I) (H : List I) (z : E) :
    (∃ beta, (z, beta) ∈ pscEnvelopeEpigraph C row (i :: H)) ↔ z ∈ C := by
  constructor
  · rintro ⟨beta, hp⟩
    exact hp.1
  · intro hz
    exact ⟨pscEnvelope row i H z,
      (psc_envelope_epigraph_iff C row i H _).mpr ⟨hz, le_rfl⟩⟩

theorem psc_envelope_minimum_transfer (C : Set E) (row : I → E → ℝ)
    (i : I) (H : List I) (offset : E → ℝ) {z : E}
    (hz : IsMinimizer C (fun x => offset x + pscEnvelope row i H x) z) :
    IsMinimizer (pscEnvelopeEpigraph C row (i :: H)) (pscEnvelopeObjective offset)
      (z, pscEnvelope row i H z) := by
  refine ⟨(psc_envelope_epigraph_iff C row i H _).mpr ⟨hz.1, le_rfl⟩, ?_⟩
  intro p hp
  have h := (psc_envelope_epigraph_iff C row i H p).mp hp
  exact (hz.2 p.1 h.1).trans (add_le_add_right h.2 _)

theorem psc_envelope_minimizer_height (C : Set E) (row : I → E → ℝ)
    (i : I) (H : List I) (offset : E → ℝ) {p : E × ℝ}
    (hp : IsMinimizer (pscEnvelopeEpigraph C row (i :: H)) (pscEnvelopeObjective offset) p) :
    p.2 = pscEnvelope row i H p.1 := by
  have hm := (psc_envelope_epigraph_iff C row i H p).mp hp.1
  have hv := hp.2 (p.1, pscEnvelope row i H p.1)
    ((psc_envelope_epigraph_iff C row i H _).mpr ⟨hm.1, le_rfl⟩)
  dsimp [pscEnvelopeObjective] at hv
  linarith [hm.2]

theorem psc_envelope_minimizer_iff (C : Set E) (row : I → E → ℝ)
    (i : I) (H : List I) (offset : E → ℝ) (p : E × ℝ) :
    IsMinimizer (pscEnvelopeEpigraph C row (i :: H)) (pscEnvelopeObjective offset) p ↔
      IsMinimizer C (fun x => offset x + pscEnvelope row i H x) p.1 ∧
        p.2 = pscEnvelope row i H p.1 := by
  constructor
  · intro hp
    have he := psc_envelope_minimizer_height C row i H offset hp
    refine ⟨⟨hp.1.1, ?_⟩, he⟩
    intro z hz
    have hv := hp.2 (z, pscEnvelope row i H z)
      ((psc_envelope_epigraph_iff C row i H _).mpr ⟨hz, le_rfl⟩)
    simpa only [pscEnvelopeObjective, he] using hv
  · rintro ⟨hmin, he⟩
    have hp := psc_envelope_minimum_transfer C row i H offset hmin
    simpa only [← he, Prod.mk.eta] using hp

theorem psc_floored_envelope_epigraph_iff (C : Set E) (row : I → E → ℝ)
    (H : List I) (floor : E → ℝ) (p : E × ℝ) :
    p ∈ pscFlooredEnvelopeEpigraph C row H floor ↔
      p.1 ∈ C ∧ pscEnvelopeTail row H floor p.1 ≤ p.2 := by
  simp only [pscFlooredEnvelopeEpigraph, Set.mem_setOf_eq, psc_envelope_tail_le_iff]

theorem psc_floored_envelope_projection (C : Set E) (row : I → E → ℝ)
    (H : List I) (floor : E → ℝ) (z : E) :
    (∃ beta, (z, beta) ∈ pscFlooredEnvelopeEpigraph C row H floor) ↔ z ∈ C := by
  constructor
  · rintro ⟨beta, hp⟩
    exact hp.1
  · intro hz
    exact ⟨pscEnvelopeTail row H floor z,
      (psc_floored_envelope_epigraph_iff C row H floor _).mpr ⟨hz, le_rfl⟩⟩

theorem psc_floored_envelope_minimum_transfer (C : Set E) (row : I → E → ℝ)
    (H : List I) (floor offset : E → ℝ) {z : E}
    (hz : IsMinimizer C (fun x => offset x + pscEnvelopeTail row H floor x) z) :
    IsMinimizer (pscFlooredEnvelopeEpigraph C row H floor) (pscEnvelopeObjective offset)
      (z, pscEnvelopeTail row H floor z) := by
  refine ⟨(psc_floored_envelope_epigraph_iff C row H floor _).mpr ⟨hz.1, le_rfl⟩, ?_⟩
  intro p hp
  have h := (psc_floored_envelope_epigraph_iff C row H floor p).mp hp
  exact (hz.2 p.1 h.1).trans (add_le_add_right h.2 _)

theorem psc_floored_envelope_minimizer_height (C : Set E) (row : I → E → ℝ)
    (H : List I) (floor offset : E → ℝ) {p : E × ℝ}
    (hp : IsMinimizer (pscFlooredEnvelopeEpigraph C row H floor)
      (pscEnvelopeObjective offset) p) :
    p.2 = pscEnvelopeTail row H floor p.1 := by
  have hm := (psc_floored_envelope_epigraph_iff C row H floor p).mp hp.1
  have hv := hp.2 (p.1, pscEnvelopeTail row H floor p.1)
    ((psc_floored_envelope_epigraph_iff C row H floor _).mpr ⟨hm.1, le_rfl⟩)
  dsimp [pscEnvelopeObjective] at hv
  linarith [hm.2]

theorem psc_floored_envelope_minimizer_iff (C : Set E) (row : I → E → ℝ)
    (H : List I) (floor offset : E → ℝ) (p : E × ℝ) :
    IsMinimizer (pscFlooredEnvelopeEpigraph C row H floor) (pscEnvelopeObjective offset) p ↔
      IsMinimizer C (fun x => offset x + pscEnvelopeTail row H floor x) p.1 ∧
        p.2 = pscEnvelopeTail row H floor p.1 := by
  constructor
  · intro hp
    have he := psc_floored_envelope_minimizer_height C row H floor offset hp
    refine ⟨⟨hp.1.1, ?_⟩, he⟩
    intro z hz
    have hv := hp.2 (z, pscEnvelopeTail row H floor z)
      ((psc_floored_envelope_epigraph_iff C row H floor _).mpr ⟨hz, le_rfl⟩)
    simpa only [pscEnvelopeObjective, he] using hv
  · rintro ⟨hmin, he⟩
    have hp := psc_floored_envelope_minimum_transfer C row H floor offset hmin
    simpa only [← he, Prod.mk.eta] using hp

/-- A concrete nonempty-row witness; no topology or tangent structure is needed. -/
theorem psc_constant_row_minimum (C : Set E) (z : E) (hz : z ∈ C) (a b : ℝ) :
    IsMinimizer (pscEnvelopeEpigraph C (fun (_ : Unit) (_ : E) => b) [()])
      (pscEnvelopeObjective (fun _ => a)) (z, b) := by
  refine ⟨⟨hz, ?_⟩, ?_⟩
  · simp [pscEnvelopeRows]
  · intro p hp
    have hb := hp.2 () (by simp)
    exact add_le_add_right hb a

/-- An empty row family with an explicit floor has the expected concrete minimum. -/
theorem psc_empty_floor_minimum (C : Set E) (z : E) (hz : z ∈ C)
    (row : I → E → ℝ) (a b : ℝ) :
    IsMinimizer (pscFlooredEnvelopeEpigraph C row [] (fun _ => b))
      (pscEnvelopeObjective (fun _ => a)) (z, b) := by
  refine ⟨⟨hz, le_rfl, psc_envelope_rows_nil row _ _⟩, ?_⟩
  intro p hp
  exact add_le_add_right hp.2.1 a

/-- Empty rows impose no lower bound on height, even on a compact base. -/
theorem psc_empty_envelope_unbounded (C : Set E) (row : I → E → ℝ)
    (offset : E → ℝ) (hne : C.Nonempty) :
    ∀ B : ℝ, ∃ p ∈ pscEnvelopeEpigraph C row [], pscEnvelopeObjective offset p < B := by
  obtain ⟨z, hz⟩ := hne
  intro B
  refine ⟨(z, B - offset z - 1), ⟨hz, psc_envelope_rows_nil row _ _⟩, ?_⟩
  dsimp [pscEnvelopeObjective]
  linarith

theorem psc_empty_envelope_no_minimum (C : Set E) (row : I → E → ℝ)
    (offset : E → ℝ) (hne : C.Nonempty) :
    ¬ ∃ p, IsMinimizer (pscEnvelopeEpigraph C row []) (pscEnvelopeObjective offset) p := by
  rintro ⟨p, hp⟩
  obtain ⟨q, hq, hlt⟩ := psc_empty_envelope_unbounded C row offset hne
    (pscEnvelopeObjective offset p)
  exact (not_lt_of_ge (hp.2 q hq)) hlt

end Envelopes

section Continuity
variable {E I : Type*} [TopologicalSpace E]

theorem psc_envelope_tail_continuousOn (C : Set E) (row : I → E → ℝ)
    (H : List I) (floor : E → ℝ)
    (hf : ContinuousOn floor C) (hr : ∀ i ∈ H, ContinuousOn (row i) C) :
    ContinuousOn (pscEnvelopeTail row H floor) C := by
  induction H with
  | nil => exact hf
  | cons i H ih =>
    exact (hr i (by simp)).sup (ih (fun j hj => hr j (by simp [hj])))

theorem psc_envelope_continuousOn (C : Set E) (row : I → E → ℝ)
    (i : I) (H : List I) (hr : ∀ j ∈ i :: H, ContinuousOn (row j) C) :
    ContinuousOn (pscEnvelope row i H) C :=
  psc_envelope_tail_continuousOn C row H (row i) (hr i (by simp))
    (fun j hj => hr j (by simp [hj]))

/-- Nonempty finite envelopes attain a minimum on the compact retained domain. -/
theorem psc_envelope_attains_minimum (C : Set E) (row : I → E → ℝ)
    (i : I) (H : List I) (offset : E → ℝ)
    (hC : IsCompact C) (hne : C.Nonempty) (hoff : ContinuousOn offset C)
    (hr : ∀ j ∈ i :: H, ContinuousOn (row j) C) :
    ∃ z, IsMinimizer C (fun x => offset x + pscEnvelope row i H x) z :=
  compact_feasible_attainment hC hne
    (hoff.add (psc_envelope_continuousOn C row i H hr))

/-- Existence on the epigraph is derived without compactifying its height. -/
theorem psc_envelope_epigraph_attainment (C : Set E) (row : I → E → ℝ)
    (H : List I) (offset : E → ℝ) (hH : H ≠ [])
    (hC : IsCompact C) (hne : C.Nonempty) (hoff : ContinuousOn offset C)
    (hr : ∀ j ∈ H, ContinuousOn (row j) C) :
    ∃ p, IsMinimizer (pscEnvelopeEpigraph C row H) (pscEnvelopeObjective offset) p := by
  cases H with
  | nil => exact (hH rfl).elim
  | cons i H =>
    obtain ⟨z, hz⟩ := psc_envelope_attains_minimum C row i H offset hC hne hoff hr
    exact ⟨_, psc_envelope_minimum_transfer C row i H offset hz⟩

/-- A continuous explicit floor also treats the empty-history case. -/
theorem psc_floored_envelope_attainment (C : Set E) (row : I → E → ℝ)
    (H : List I) (floor offset : E → ℝ)
    (hC : IsCompact C) (hne : C.Nonempty)
    (hf : ContinuousOn floor C) (hoff : ContinuousOn offset C)
    (hr : ∀ j ∈ H, ContinuousOn (row j) C) :
    ∃ p, IsMinimizer (pscFlooredEnvelopeEpigraph C row H floor)
      (pscEnvelopeObjective offset) p := by
  obtain ⟨z, hz⟩ := compact_feasible_attainment hC hne
    (hoff.add (psc_envelope_tail_continuousOn C row H floor hf hr))
  exact ⟨_, psc_floored_envelope_minimum_transfer C row H floor offset hz⟩

theorem psc_constant_floor_attainment (C : Set E) (row : I → E → ℝ)
    (H : List I) (floor : ℝ) (offset : E → ℝ)
    (hC : IsCompact C) (hne : C.Nonempty) (hoff : ContinuousOn offset C)
    (hr : ∀ j ∈ H, ContinuousOn (row j) C) :
    ∃ p, IsMinimizer (pscFlooredEnvelopeEpigraph C row H (fun _ => floor))
      (pscEnvelopeObjective offset) p :=
  psc_floored_envelope_attainment C row H (fun _ => floor) offset
    hC hne continuousOn_const hoff hr

end Continuity

section AffineRows
variable {n : ℕ} {I : Type*}

/-- Actual affine rows supply the continuity needed by the generic envelope. -/
theorem psc_affine_row_continuous (L : RealVector n →L[ℝ] ℝ) (b : ℝ) :
    Continuous (fun z => b + L z) := continuous_const.add L.continuous

theorem psc_affine_envelope_attainment (C : Set (RealVector n))
    (L : I → RealVector n →L[ℝ] ℝ) (b : I → ℝ) (H : List I)
    (A : RealVector n →L[ℝ] ℝ) (c : ℝ)
    (hH : H ≠ []) (hC : IsCompact C) (hne : C.Nonempty) :
    ∃ p, IsMinimizer (pscEnvelopeEpigraph C (fun i z => b i + L i z) H)
      (pscEnvelopeObjective (fun z => c + A z)) p :=
  psc_envelope_epigraph_attainment C _ H _ hH hC hne
    (psc_affine_row_continuous A c).continuousOn
    (fun i _ => (psc_affine_row_continuous (L i) (b i)).continuousOn)

end AffineRows
end Chapter02

#print axioms Chapter02.psc_envelope_rows_nil
#print axioms Chapter02.psc_envelope_rows_cons
#print axioms Chapter02.psc_envelope_rows_append
#print axioms Chapter02.psc_envelope_tail_le_iff
#print axioms Chapter02.psc_envelope_le_iff
#print axioms Chapter02.psc_envelope_epigraph_iff
#print axioms Chapter02.psc_envelope_epigraph_projection
#print axioms Chapter02.psc_envelope_minimum_transfer
#print axioms Chapter02.psc_envelope_minimizer_height
#print axioms Chapter02.psc_envelope_minimizer_iff
#print axioms Chapter02.psc_floored_envelope_epigraph_iff
#print axioms Chapter02.psc_floored_envelope_projection
#print axioms Chapter02.psc_floored_envelope_minimum_transfer
#print axioms Chapter02.psc_floored_envelope_minimizer_height
#print axioms Chapter02.psc_floored_envelope_minimizer_iff
#print axioms Chapter02.psc_constant_row_minimum
#print axioms Chapter02.psc_empty_floor_minimum
#print axioms Chapter02.psc_empty_envelope_unbounded
#print axioms Chapter02.psc_empty_envelope_no_minimum
#print axioms Chapter02.psc_envelope_tail_continuousOn
#print axioms Chapter02.psc_envelope_continuousOn
#print axioms Chapter02.psc_envelope_attains_minimum
#print axioms Chapter02.psc_envelope_epigraph_attainment
#print axioms Chapter02.psc_floored_envelope_attainment
#print axioms Chapter02.psc_constant_floor_attainment
#print axioms Chapter02.psc_affine_row_continuous
#print axioms Chapter02.psc_affine_envelope_attainment
