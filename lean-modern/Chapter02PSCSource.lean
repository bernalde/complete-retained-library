module

public import Chapter02PSCKKT
public import Chapter02PSCOrder
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Candidate end-to-end qualified PSC source-history comparison. Each entry
starts from an actual fixed-y source minimum with actual full anchor derivatives
and a strict nonlinear point in that same affine fiber. Common convexity is
relative to V. The selected KKT multipliers govern every master in one matched
history. No validity, solver or all-fiber constraint-qualification oracle occurs. -/
noncomputable section
namespace Chapter02

variable {p q m l s nw nv : ℕ}

/-- Source hypotheses at this one chosen feasible anchor. In particular the CQ
is not asserted for every feasible fixed-y fiber of the model. -/
structure PSCSourceAnchor (d : PSCData p q m l s nw nv) where
  w : RealVector p
  v : RealVector q
  y : RealVector m
  Dr : RealVector q →L[ℝ] ℝ
  Dt : Fin l → RealVector q →L[ℝ] ℝ
  y_mem : y ∈ d.Y
  derivative_r : HasFDerivAt d.r Dr v
  derivative_t : ∀ j, HasFDerivAt (d.t j) (Dt j) v
  minimum : IsMinimizer (d.fiberFeasible y) (d.fiberObjective y) (weightedInsert w v)
  slater : ∃ z ∈ d.affineFiber y, ∀ j, d.fiberNonlinear y j z < 0

def pscSourceMatches {d : PSCData p q m l s nw nv}
    (a : PSCSourceAnchor d) (e : PSCEntry d) : Prop :=
  e.data.w = a.w ∧ e.data.v = a.v ∧ e.data.y = a.y ∧
    e.data.Dr = a.Dr ∧ e.data.Dt = a.Dt

/-- Only the derived multipliers are selected; all source point and derivative
data have an exact preservation theorem. Classical selection is not a numerical
multiplier-computation claim. -/
def pscSelectSourceEntry (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (a : PSCSourceAnchor d) : PSCEntry d :=
  Classical.choose (psc_entry_exists_of_minimum d a.w a.v a.y a.Dr a.Dt
    a.y_mem hr ht a.derivative_r a.derivative_t a.minimum a.slater)

theorem psc_select_source_entry_matches (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (a : PSCSourceAnchor d) : pscSourceMatches a (pscSelectSourceEntry d hr ht a) :=
  Classical.choose_spec (psc_entry_exists_of_minimum d a.w a.v a.y a.Dr a.Dt
    a.y_mem hr ht a.derivative_r a.derivative_t a.minimum a.slater)

/-- A single selected list is shared by OA, PSC and GBD, with repeated source
anchors and the empty history both retained literally. -/
def pscSourceHistory (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (S : List (PSCSourceAnchor d)) : List (PSCEntry d) :=
  S.map (pscSelectSourceEntry d hr ht)

theorem psc_source_history_matches (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (S : List (PSCSourceAnchor d)) :
    List.Forall₂ pscSourceMatches S (pscSourceHistory d hr ht S) := by
  induction S with
  | nil => exact .nil
  | cons a S ih => exact .cons (psc_select_source_entry_matches d hr ht a) ih

@[simp] theorem psc_source_history_length (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (S : List (PSCSourceAnchor d)) : (pscSourceHistory d hr ht S).length = S.length := by
  simp [pscSourceHistory]

@[simp] theorem psc_source_history_nil (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j)) :
    pscSourceHistory d hr ht [] = [] := rfl

/-- End-to-end source-to-comparison statement. Actual source minima and their
local CQs produce one matched history; the literal master containments and
outer property then follow. No cut-validity conclusion is a premise. -/
theorem psc_source_history_comparison (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (S : List (PSCSourceAnchor d)) :
    let H := pscSourceHistory d hr ht S
    List.Forall₂ pscSourceMatches S H ∧ H.length = S.length ∧
      pscOAMaster d H ⊆ pscMaster d H ∧
      pscProject (pscOAMaster d H) ⊆ pscProject (pscMaster d H) ∧
      pscProject (pscMaster d H) ⊆ pscGBDMaster d H ∧
      ∀ w v y, d.feasible w v y →
        pscOriginalPoint d w v y ∈ pscOAMaster d H ∧
        pscOriginalPoint d w v y ∈ pscMaster d H ∧
        (y,d.objective w v y) ∈ pscGBDMaster d H := by
  dsimp only
  refine ⟨psc_source_history_matches d hr ht S,psc_source_history_length d hr ht S,
    psc_oa_subset d _,psc_projected_oa_subset d _,psc_projected_subset_gbd d _,?_⟩
  intro w v y hf
  exact ⟨psc_original_mem_oa d _ hr ht w v y hf,
    psc_original_mem_psc d _ hr ht w v y hf,
    psc_original_mem_gbd d _ hr ht w v y hf⟩

/-- An existential version exposes the absence of a supplied multiplier or
cut-validity oracle while retaining the exact matched source correspondence. -/
theorem psc_source_history_exists (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (S : List (PSCSourceAnchor d)) :
    ∃ H : List (PSCEntry d), List.Forall₂ pscSourceMatches S H ∧ H.length = S.length ∧
      pscOAMaster d H ⊆ pscMaster d H ∧
      pscProject (pscOAMaster d H) ⊆ pscProject (pscMaster d H) ∧
      pscProject (pscMaster d H) ⊆ pscGBDMaster d H ∧
      ∀ w v y, d.feasible w v y →
        pscOriginalPoint d w v y ∈ pscOAMaster d H ∧
        pscOriginalPoint d w v y ∈ pscMaster d H ∧
        (y,d.objective w v y) ∈ pscGBDMaster d H :=
  ⟨pscSourceHistory d hr ht S,psc_source_history_comparison d hr ht S⟩

/-- Finite real value ordering is conditional on actual attained master minima.
No totalized infimum or implicit compactness is used; outer validity also
bounds the OA minimum by each actually feasible original objective. -/
theorem psc_source_history_attained_order (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (S : List (PSCSourceAnchor d))
    (oa ps : PSCPoint p q m) (gb : RealVector m × ℝ)
    (ho : IsMinimizer (pscOAMaster d (pscSourceHistory d hr ht S)) PSCPoint.alpha oa)
    (hp : IsMinimizer (pscMaster d (pscSourceHistory d hr ht S)) PSCPoint.alpha ps)
    (hg : IsMinimizer (pscGBDMaster d (pscSourceHistory d hr ht S)) Prod.snd gb) :
    gb.2 ≤ ps.alpha ∧ ps.alpha ≤ oa.alpha ∧
      ∀ w v y, d.feasible w v y → oa.alpha ≤ d.objective w v y := by
  have h := psc_attained_value_order d (pscSourceHistory d hr ht S) oa ps gb ho hp hg
  exact ⟨h.1,h.2,fun w v y hf =>
    psc_attained_value_original_bound d _ hr ht oa ho w v y hf⟩

#print axioms psc_select_source_entry_matches
#print axioms psc_source_history_matches
#print axioms psc_source_history_length
#print axioms psc_source_history_nil
#print axioms psc_source_history_comparison
#print axioms psc_source_history_exists
#print axioms psc_source_history_attained_order

end Chapter02
