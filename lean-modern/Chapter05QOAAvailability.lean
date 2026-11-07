module

public import Chapter05QuadraticMaster
public import Chapter02PSCEnvelope
public import Chapter02WeightedRestoration
public import Chapter05QOAModel

@[expose] public section

/-! Mathematical availability of the exact queries used by the repaired QOA
execution. The free master height is not assumed compact. Fixed rows are
continuous even without differentiability hypotheses, since their derivative
values are fixed continuous linear maps. This does not certify a numerical
solver or supply a new solver assumption. -/
noncomputable section
open Set
open scoped BigOperators
namespace Chapter05.QOA
open Chapter02 Chapter05.Quadratic

section FiniteMaster
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cut_continuous (f : E → ℝ) (a : E) (α : ℝ) :
    Continuous (cut f a α) := by
  have hs : Continuous (fun x : E => x - a) := continuous_id.sub continuous_const
  exact (continuous_const.add ((fderiv ℝ f a).continuous.comp hs)).add
    (continuous_const.mul (((fderiv ℝ (fderiv ℝ f) a).continuous.comp hs).clm_apply hs))

/-- Retained constraint base; no objective height is compactified. -/
def constraintBase (d : MasterData E I J) (H : List I) : Set E :=
  {x | x ∈ d.base ∧ ∀ i ∈ H, ∀ j, cut (d.g j) (d.anchor i)
    (d.constraintScale i j) x ≤ 0}

theorem constraintBase_compact (d : MasterData E I J) (H : List I)
    (hB : IsCompact d.base) : IsCompact (constraintBase d H) := by
  have he : constraintBase d H = d.base ∩
      ⋂ i ∈ H, ⋂ j, {x | cut (d.g j) (d.anchor i) (d.constraintScale i j) x ≤ 0} := by
    ext x
    simp [constraintBase]
  rw [he]
  exact hB.inter_right (isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_iInter fun j => isClosed_le (cut_continuous _ _ _) continuous_const)

theorem quadraticMaster_eq_envelope [DecidableEq I]
    (d : MasterData E I J) (H : List I) :
    quadraticMaster d H.toFinset = pscEnvelopeEpigraph (constraintBase d H)
      (fun i => cut d.f (d.anchor i) (d.objectiveScale i)) H := by
  ext p
  simp only [quadraticMaster, pscEnvelopeEpigraph, constraintBase,
    pscEnvelopeRows, mem_setOf_eq, List.mem_toFinset]
  tauto

/-- A nonempty finite objective history supplies the lower height envelope.
Existence follows from the unchanged Chapter 2 finite-envelope theorem. -/
theorem quadraticMaster_attainment [DecidableEq I]
    (d : MasterData E I J) (H : List I) (hH : H ≠ [])
    (hB : IsCompact d.base) (hne : (quadraticMaster d H.toFinset).Nonempty) :
    ∃ q, IsMinimizer (quadraticMaster d H.toFinset) Prod.snd q := by
  have hC : (constraintBase d H).Nonempty := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨q.1, hq.1, fun i hi j => hq.2.2 i (List.mem_toFinset.mpr hi) j⟩
  obtain ⟨q, hq⟩ := psc_envelope_epigraph_attainment (constraintBase d H)
    (fun i => cut d.f (d.anchor i) (d.objectiveScale i)) H (fun _ => 0)
    hH (constraintBase_compact d H hB) hC continuousOn_const
    (fun i _ => (cut_continuous _ _ _).continuousOn)
  refine ⟨q, ?_⟩
  have hoff : pscEnvelopeObjective (fun _ : E => (0 : ℝ)) = Prod.snd := by
    funext p
    simp [pscEnvelopeObjective]
  rw [hoff] at hq
  simpa only [quadraticMaster_eq_envelope d H] using hq

end FiniteMaster

section SourceQueries
variable {n p m r : ℕ} {d : Data n p m r}

theorem affineFiber_compact (hX : IsCompact d.X) (y : RealVector p) :
    IsCompact (d.affineFiber y) := by
  have he : d.affineFiber y = weightedHardRegion d.X
      (fun i x => LinearForm (d.A i) (d.E i) (x,y) - d.b i) := by
    ext x
    simp [Data.affineFiber, weightedHardRegion, sub_nonpos]
  rw [he]
  exact weightedHardRegion_compact _ _ hX (fun i =>
    ((linearForm_continuous _ _).comp (continuous_id.prodMk continuous_const)).sub
      continuous_const)

theorem hardFiber_compact (hX : IsCompact d.X) (y : IntVector p) :
    IsCompact (d.hardFiber y) := affineFiber_compact hX _

theorem soft_continuous (hr : Regularity d) (y : IntVector p) (j : Fin m) :
    Continuous (d.soft y j) :=
  (hr.constraint_C2 j).continuous.comp (continuous_id.prodMk continuous_const)

theorem fiberObjective_continuous (hr : Regularity d) (y : IntVector p) :
    Continuous (d.fiberObjective y) :=
  hr.objective_C2.continuous.comp (continuous_id.prodMk continuous_const)

theorem feasibleFiber_compact (hr : Regularity d) (y : IntVector p) :
    IsCompact (d.feasibleFiber y) :=
  weightedHardRegion_compact _ _ (hardFiber_compact hr.X_compact y)
    (soft_continuous hr y)

theorem base_compact (hX : IsCompact d.X) : IsCompact d.base := by
  have he : d.base = ⋃ y ∈ d.Y, (fun x => (x,Chapter03.OAKKT.intCast y)) ''
      d.hardFiber y := by
    ext z
    simp only [Data.base, mem_setOf_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨y, hy, hz, hx⟩
      exact ⟨y, hy, z.1, hx, Prod.ext rfl hz.symm⟩
    · rintro ⟨y, hy, x, hx, rfl⟩
      exact ⟨y, hy, rfl, hx⟩
  rw [he]
  exact d.Y.isCompact_biUnion (fun y _ => (hardFiber_compact hX y).image
    (continuous_id.prodMk continuous_const))

theorem original_compact (hr : Regularity d) : IsCompact d.original :=
  weightedHardRegion_compact _ _ (base_compact hr.X_compact)
    (fun j => (hr.constraint_C2 j).continuous)

theorem fixed_minimum_exists (hr : Regularity d) (y : IntVector p)
    (hne : (d.feasibleFiber y).Nonempty) :
    ∃ x, IsMinimizer (d.feasibleFiber y) (d.fiberObjective y) x :=
  compact_feasible_attainment (feasibleFiber_compact hr y) hne
    (fiberObjective_continuous hr y).continuousOn

theorem original_minimum_exists (hr : Regularity d) (hne : d.original.Nonempty) :
    ∃ z, IsMinimizer d.original d.f z :=
  compact_feasible_attainment (original_compact hr) hne hr.objective_C2.continuous.continuousOn

/-- The source separate-slack problem has an actual minimum on every nonempty
hard fiber. The slack coordinates themselves need not form a compact set. -/
theorem restoration_minimum_exists (hr : Regularity d) (y : IntVector p)
    (hne : (d.hardFiber y).Nonempty) :
    ∃ x s, IsMinimizer (d.restSet y) d.restCost (weightedInsert x s) := by
  obtain ⟨x, hx⟩ := weighted_hard_minimum_exists (d.hardFiber y)
    (Fin.elim0 : Fin 0 → RealVector n → ℝ) (d.soft y) (fun _ => 1)
    (hardFiber_compact hr.X_compact y)
    (by simpa only [empty_hard_region] using hne)
    (fun j => Fin.elim0 j) (soft_continuous hr y)
  exact ⟨x, (fun j => max (d.soft y j x) 0),
    weighted_lift_minimizer _ _ _ _ (fun _ => by norm_num) hx⟩

theorem relaxation_compact (hr : Regularity d) (hY : RelaxationRegularity d) :
    IsCompact d.relaxation := by
  have he : d.relaxation = weightedHardRegion
      (weightedHardRegion (d.X ×ˢ d.relaxedY)
        (fun i z => LinearForm (d.A i) (d.E i) z - d.b i)) d.g := by
    ext z
    simp [Data.relaxation, weightedHardRegion, sub_nonpos, and_assoc]
  rw [he]
  exact weightedHardRegion_compact _ _
    (weightedHardRegion_compact _ _ (hr.X_compact.prod hY.compact)
      (fun i => (linearForm_continuous _ _).sub continuous_const))
    (fun j => (hr.constraint_C2 j).continuous)

theorem relaxation_minimum_exists (hr : Regularity d) (hY : RelaxationRegularity d)
    (hne : d.relaxation.Nonempty) : ∃ z, IsMinimizer d.relaxation d.f z :=
  compact_feasible_attainment (relaxation_compact hr hY) hne
    hr.objective_C2.continuous.continuousOn

theorem master_minimum_exists (hX : IsCompact d.X) (H : List (Token n p m))
    (hH : H ≠ []) (hne : (master d H).Nonempty) :
    ∃ q, IsMinimizer (master d H) Prod.snd q := by
  classical
  exact quadraticMaster_attainment (masterData d) H hH (base_compact hX) hne

/-- Zero scales witness existence; the event relation still permits every
scale in the independently established safe interval. -/
theorem zero_token_safe (hr : Regularity d) (a : Point n p) :
    (Token.mk a 0 (fun _ => 0)).Safe d :=
  ⟨⟨le_rfl, (safeScale_bounds hr.objective_convex hr.objective_C2 a d.base).1⟩,
    fun j => ⟨le_rfl,
      (safeScale_bounds (hr.constraint_convex j) (hr.constraint_C2 j) a d.base).1⟩⟩

theorem event_exists (hr : Regularity d) (y : IntVector p) (hy : y ∈ d.Y)
    (hne : (d.hardFiber y).Nonempty) : ∃ e : Event d, e.target = y ∧ EventValid d e := by
  classical
  by_cases hf : (d.feasibleFiber y).Nonempty
  · obtain ⟨x, hx⟩ := fixed_minimum_exists hr y hf
    exact ⟨⟨y, hy, x, none, 0, fun _ => 0⟩, rfl, zero_token_safe hr _, hx⟩
  · obtain ⟨x, s, hs⟩ := restoration_minimum_exists hr y hne
    exact ⟨⟨y, hy, x, some s, 0, fun _ => 0⟩, rfl, zero_token_safe hr _, hf, hs⟩

end SourceQueries
end Chapter05.QOA
