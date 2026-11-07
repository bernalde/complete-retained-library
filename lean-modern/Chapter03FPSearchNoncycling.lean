module

public import Chapter03FPSearchAffineCQ
public import Chapter03FPSearchMaster
public import Chapter03FPSearchCQControl

@[expose] public section

/-! Convex finite-row bridge for the held Bonami manuscript Theorem 1.
Its printed CQ is at the new full projection, whereas its contradiction uses
first-order optimality at an old full projection with the same integer block.
Global convexity of every indexed residual transports a strict feasible point
from the new LICQ point to MFCQ at the old point. No full-point equality or
transport of LICQ is asserted. The original finite-target endpoints are reused,
not reproved here. Certification and accepted scope are governed by the separate
certificate and its review evidence. -/
noncomputable section
open scoped BigOperators Topology RealInnerProductSpace
open Filter Set Chapter02 Chapter03.FP
namespace Chapter03.FPSearch

section FiniteRows
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strengthening of the accepted small-step lemma: all finite rows become
strict, including initially inactive rows. No row is discarded. -/
theorem joint_strict_active_strict_small_steps {J : Type*} [Fintype J]
    (c : J → E → ℝ) (A : J → E →L[ℝ] ℝ) (p v : E)
    (hp : ∀ i, c i p ≤ 0)
    (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hv : ∀ i, c i p = 0 → A i v < 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i, c i (p + t • v) < 0 := by
  rw [Filter.eventually_all]
  intro i
  have hpath : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hc : HasDerivAt (fun t : ℝ => c i (p + t • v)) (A i v) 0 := by
    simpa [Function.comp_def] using (hA i).comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  by_cases hi : c i p = 0
  · have he := hc.tendsto_slope_zero_right.eventually_lt_const (hv i hi)
    filter_upwards [he, self_mem_nhdsWithin] with t ht htpos
    have hq : t⁻¹ * c i (p + t • v) < 0 := by simpa [hi] using ht
    have ht0 : 0 < t := htpos
    have hinv : 0 < t⁻¹ := inv_pos.mpr ht0
    nlinarith
  · have hslack : c i p < 0 := lt_of_le_of_ne (hp i) hi
    have he : ∀ᶠ t : ℝ in 𝓝 0, c i (p + t • v) < 0 :=
      hc.continuousAt.tendsto.eventually_lt_const (by simpa using hslack)
    exact he.filter_mono nhdsWithin_le_nhds

/-- A feasible full-space MFCQ point supplies one point strict in every finite
indexed residual. This step needs differentiability but not convexity. -/
theorem joint_strict_feasible_of_mfcq {J : Type*} [Fintype J]
    (c : J → E → ℝ) (A : J → E →L[ℝ] ℝ) (p : E)
    (hp : ∀ i, c i p ≤ 0)
    (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hcq : JointMFCQ c A p) : ∃ z : E, ∀ i, c i z < 0 := by
  obtain ⟨v, hv⟩ := hcq
  obtain ⟨t, ht⟩ := (joint_strict_active_strict_small_steps c A p v hp hA hv).exists
  exact ⟨p + t • v, ht⟩

/-- Full-space LICQ at the new feasible point supplies strict feasibility;
the active subtype contains every indexed row, including redundant rows. -/
theorem joint_strict_feasible_of_licq {J : Type*} [Fintype J]
    (c : J → E → ℝ) (A : J → E →L[ℝ] ℝ) (p : E)
    (hp : ∀ i, c i p ≤ 0)
    (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hcq : JointLICQ c A p) : ∃ z : E, ∀ i, c i z < 0 :=
  joint_strict_feasible_of_mfcq c A p hp hA (joint_mfcq_of_licq c A p hcq)

/-- Global convexity transports strict feasibility to an old-point MFCQ
direction. This does not transport linear independence of active gradients. -/
theorem joint_mfcq_of_strict_feasible {J : Type*}
    (c : J → E → ℝ) (A : J → E →L[ℝ] ℝ) (p z : E)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (c i))
    (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hz : ∀ i, c i z < 0) : JointMFCQ c A p := by
  refine ⟨z - p, fun i hi => ?_⟩
  have hsupport := tangent_underestimator (hconv i) (hA i) (b := z)
  rw [hi, zero_add] at hsupport
  exact hsupport.trans_lt (hz i)

/-- The missing location bridge in the convex-functions proof: CQ at `new`
gives MFCQ at `old`. No equality of the full points is needed. -/
theorem joint_mfcq_at_old_of_licq_at_new {J : Type*} [Fintype J]
    (c : J → E → ℝ) (Anew Aold : J → E →L[ℝ] ℝ) (new old : E)
    (hnew : ∀ i, c i new ≤ 0)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (c i))
    (hAnew : ∀ i, HasFDerivAt (c i) (Anew i) new)
    (hAold : ∀ i, HasFDerivAt (c i) (Aold i) old)
    (hcq : JointLICQ c Anew new) : JointMFCQ c Aold old := by
  obtain ⟨z, hz⟩ := joint_strict_feasible_of_licq c Anew new hnew hAnew hcq
  exact joint_mfcq_of_strict_feasible c Aold old z hconv hAold hz

end FiniteRows

variable {n m : ℕ}

/-- The squared-distance objective depends only on the relaxed integer block.
Thus an old feasible full point with that same block is also a current minimum. -/
theorem projection_minimum_of_same_integer_coordinates
    (C : Set (Point n m)) (q : IntVector m) (new old : Point n m)
    (hmin : IsMinimizer C (distance q) new) (hold : old ∈ C)
    (heq : Chapter03.yMap n m old = Chapter03.yMap n m new) :
    IsMinimizer C (distance q) old := by
  have hvalue : distance q old = distance q new := by simp only [distance, heq]
  exact ⟨hold, fun z hz => hvalue.trans_le (hmin.2 z hz)⟩

/-- Qualified nonconvex-row form: CQ is required at the old full anchor.
The master point satisfies its active tangents and has integer block `q`.
The old block differs from `q`; no assumption about integrality of the new
projection or convexity of the represented feasible set is needed. -/
theorem projection_integer_distinct_of_old_mfcq {J : Type*} [Fintype J]
    (c : J → Point n m → ℝ) (Aold : J → Point n m →L[ℝ] ℝ)
    (q : IntVector m) (new old masterPoint : Point n m)
    (hmin : IsMinimizer {w | ∀ i, c i w ≤ 0} (distance q) new)
    (hold : ∀ i, c i old ≤ 0)
    (hAold : ∀ i, HasFDerivAt (c i) (Aold i) old)
    (hcq : JointMFCQ c Aold old)
    (htangent : ∀ i, c i old = 0 → Aold i (masterPoint - old) ≤ 0)
    (hmaster : Chapter03.yMap n m masterPoint = intY q)
    (hold_ne : Chapter03.yMap n m old ≠ intY q) :
    Chapter03.yMap n m new ≠ Chapter03.yMap n m old := by
  intro heq
  have holdmin := projection_minimum_of_same_integer_coordinates
    {w | ∀ i, c i w ≤ 0} q new old hmin hold heq.symm
  have hnormal := joint_projection_normal_of_mfcq c Aold q old masterPoint
    holdmin hAold hcq htangent
  rw [hmaster] at hnormal
  exact (not_lt_of_ge hnormal) (Chapter03.projection_cut_excludes hold_ne)

/-- Pairwise convex-all-rows core of the held manuscript Theorem 1: the CQ is
at the new full projection and the conclusion distinguishes integer blocks.
The explicit `hold_ne` is discharged for an actual continuing run by its
nonintegral-old-anchor stopping convention. The printed fixed-i statement omits
that convention and is not asserted without it. No bounded target set,
algorithmic fuel, fractional-new-point premise, or old-point LICQ is assumed. -/
theorem projection_integer_distinct_of_current_licq_convex_rows
    {J : Type*} [Fintype J]
    (c : J → Point n m → ℝ)
    (Anew Aold : J → Point n m →L[ℝ] ℝ)
    (q : IntVector m) (new old masterPoint : Point n m)
    (hmin : IsMinimizer {w | ∀ i, c i w ≤ 0} (distance q) new)
    (hold : ∀ i, c i old ≤ 0)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (c i))
    (hAnew : ∀ i, HasFDerivAt (c i) (Anew i) new)
    (hAold : ∀ i, HasFDerivAt (c i) (Aold i) old)
    (hcq : JointLICQ c Anew new)
    (htangent : ∀ i, c i old = 0 → Aold i (masterPoint - old) ≤ 0)
    (hmaster : Chapter03.yMap n m masterPoint = intY q)
    (hold_ne : Chapter03.yMap n m old ≠ intY q) :
    Chapter03.yMap n m new ≠ Chapter03.yMap n m old :=
  projection_integer_distinct_of_old_mfcq c Aold q new old masterPoint hmin hold
    hAold (joint_mfcq_at_old_of_licq_at_new c Anew Aold new old
      hmin.1 hconv hAnew hAold hcq) htangent hmaster hold_ne

/-- Literal unsquared Euclidean projection objective from the held source.
The accepted norm/square equivalence is applied to the actual minimum; this
endpoint needs neither compactness nor boundedness of the feasible region. -/
theorem norm_projection_integer_distinct_of_current_licq_convex_rows
    {J : Type*} [Fintype J]
    (c : J → Point n m → ℝ)
    (Anew Aold : J → Point n m →L[ℝ] ℝ)
    (q : IntVector m) (new old masterPoint : Point n m)
    (hmin : IsMinimizer {w | ∀ i, c i w ≤ 0}
      (fun w => ‖intY q - Chapter03.yMap n m w‖) new)
    (hold : ∀ i, c i old ≤ 0)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (c i))
    (hAnew : ∀ i, HasFDerivAt (c i) (Anew i) new)
    (hAold : ∀ i, HasFDerivAt (c i) (Aold i) old)
    (hcq : JointLICQ c Anew new)
    (htangent : ∀ i, c i old = 0 → Aold i (masterPoint - old) ≤ 0)
    (hmaster : Chapter03.yMap n m masterPoint = intY q)
    (hold_ne : Chapter03.yMap n m old ≠ intY q) :
    Chapter03.yMap n m new ≠ Chapter03.yMap n m old :=
  projection_integer_distinct_of_current_licq_convex_rows c Anew Aold q
    new old masterPoint ((norm_projection_iff _ q new).mp hmin) hold hconv
    hAnew hAold hcq htangent hmaster hold_ne

variable {l r : ℕ}

/-- Literal held Bonami basic (FOA) feasible set: all g rows are linearized at
the seed and at every retained old projection. Variable bounds are g rows and
the ambient base is univ in the source theorem below. Master optimality is not
part of this set and is not needed for the noncycling implication. -/
def bonamiAllRowMaster (d : Data n m l) (s : State n m) : Set (Point n m) :=
  {p | Integral p ∧ (∀ j, tangent d s.seed j p ≤ 0) ∧
    ∀ e ∈ s.history, ∀ j, tangent d e.projection j p ≤ 0}

/-- Bonami's all-row master is contained in the existing selected-row basic
master, with all domain bounds represented as g rows. Containment preserves
feasibility only; a minimizer of the smaller set need not minimize the larger. -/
theorem bonami_all_row_master_subset_basic (d : Data n m l) (s : State n m)
    (hbase : d.base = Set.univ) : bonamiAllRowMaster d s ⊆ master d .basic s := by
  intro p hp
  refine ⟨?_, hp.1, ⟨hp.2.1, fun e he j _ => hp.2.2 e he j⟩, ?_⟩
  · rw [hbase]
    exact Set.mem_univ p
  · intro hmode
    cases hmode

/-- Literal convex-row Bonami iteration, under the continuing-run convention
that the seed and every older projection are nonintegral. The printed fixed-i
statement omits this convention; continuing after an integral old point may
repeat its integer block. This endpoint retains every g row in the source
master, uses the unsquared Euclidean projection minimum and only current-point
LICQ. A merely feasible integer master point suffices. There is no Analytic,
boundedness, convex objective, closed-base, or master-minimum hypothesis. -/
theorem bonami_all_row_iteration_integer_distinct
    (d : Data n m l) (s : State n m) (hbase : d.base = Set.univ)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hD : ∀ j p, HasFDerivAt (d.g j) (d.Dg j p) p)
    (hseed : s.seed ∈ d.relaxation) (hseed_fractional : ¬Integral s.seed)
    (hhistory : ∀ e ∈ s.history,
      e.projection ∈ d.relaxation ∧ ¬Integral e.projection)
    (masterPoint new : Point n m) (q : IntVector m)
    (hmaster : masterPoint ∈ bonamiAllRowMaster d s)
    (htarget : masterPoint.2 = intCast q)
    (hmin : IsMinimizer d.relaxation
      (fun w => ‖intY q - Chapter03.yMap n m w‖) new)
    (hcq : JointLICQ d.g (fun j => d.Dg j new) new) :
    Chapter03.yMap n m new ≠ Chapter03.yMap n m s.seed ∧
      ∀ e ∈ s.history,
        Chapter03.yMap n m new ≠ Chapter03.yMap n m e.projection := by
  have hrel : {w | ∀ j, d.g j w ≤ 0} = d.relaxation := by
    ext w
    simp only [Data.relaxation, hbase, Set.mem_setOf_eq, Set.mem_univ, true_and]
  have hnorm : IsMinimizer {w | ∀ j, d.g j w ≤ 0}
      (fun w => ‖intY q - Chapter03.yMap n m w‖) new := by
    simpa only [hrel] using hmin
  have hdistinct : ∀ old : Point n m, old ∈ d.relaxation → ¬Integral old →
      (∀ j, tangent d old j masterPoint ≤ 0) →
      Chapter03.yMap n m new ≠ Chapter03.yMap n m old := by
    intro old hold hfractional htangent
    apply norm_projection_integer_distinct_of_current_licq_convex_rows
      d.g (fun j => d.Dg j new) (fun j => d.Dg j old)
      q new old masterPoint hnorm hold.2 hconv
    · exact fun j => hD j new
    · exact fun j => hD j old
    · exact hcq
    · intro j hj
      simpa only [tangent, hj, zero_add] using htangent j
    · exact (yMap_eq_intY_iff _ _).mpr htarget
    · intro heq
      exact hfractional ⟨q, (yMap_eq_intY_iff _ _).mp heq⟩
  refine ⟨hdistinct s.seed hseed hseed_fractional hmaster.2.1, ?_⟩
  intro e he
  exact hdistinct e.projection (hhistory e he).1 (hhistory e he).2 (hmaster.2.2 e he)

/-- Qualified thesis/DICOPT selected-row corollary for a basic/enhanced search
step, including the old seed (`k = 0`). This is separate from the literal
Bonami all-row iteration endpoint above.
The seed must be fractional for the first-search loop to run; every retained
history point is already fractional by `Valid`. Current LICQ applies to the
exact joint rows including every finite affine base row. The extra global
convex-row premise is explicit and is not inferred from convexity of the set.
No choice of tied master or projection minima is excluded. `Analytic` carries
boundedness and objective assumptions for the existing algorithm API; these
are additional sufficient assumptions, absent from the generic theorem above. -/
theorem step_integer_projection_distinct_of_current_licq_convex_rows
    (d : Data n m l) (b : BaseRows d r) (h : Analytic d)
    {mode : Mode} {s : State n m} (hs : Valid d s)
    (hseed : ¬Integral s.seed) (step : Step d mode s)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (jointRows d b i))
    (hcq : JointLICQ (jointRows d b) (jointRowD d b step.projection)
      step.projection) :
    Chapter03.yMap n m step.projection ≠ Chapter03.yMap n m s.seed ∧
      ∀ e ∈ s.history,
        Chapter03.yMap n m step.projection ≠ Chapter03.yMap n m e.projection := by
  have hmaster := step.master_min.1
  have hnew : IsMinimizer {w | ∀ i, jointRows d b i w ≤ 0}
      (distance step.target) step.projection := by
    simpa only [jointRows_relaxation d b] using step.projection_min
  have hdistinct : ∀ old : Point n m, old ∈ d.relaxation → ¬Integral old →
      (∀ j, d.g j old = 0 → d.Dg j old (step.point - old) ≤ 0) →
      Chapter03.yMap n m step.projection ≠ Chapter03.yMap n m old := by
    intro old hold hfractional htangent
    apply projection_integer_distinct_of_current_licq_convex_rows
      (jointRows d b) (jointRowD d b step.projection) (jointRowD d b old)
      step.target step.projection old step.point hnew
    · have he : old ∈ {w | ∀ i, jointRows d b i w ≤ 0} := by
        simpa only [jointRows_relaxation d b] using hold
      exact he
    · exact hconv
    · exact jointRows_derivative d b h step.projection step.projection_min.1.1
    · exact jointRows_derivative d b h old hold.1
    · exact hcq
    · intro i hi
      cases i with
      | inl i => exact b.active_direction old step.point hmaster.1 i hi
      | inr j => exact htangent j hi
    · exact (yMap_eq_intY_iff _ _).mpr step.target_eq
    · intro heq
      exact hfractional ⟨step.target, (yMap_eq_intY_iff _ _).mp heq⟩
  constructor
  · apply hdistinct s.seed hs.seed hseed
    intro j hj
    simpa only [tangent, hj, zero_add] using hmaster.2.2.1.1 j
  · intro e he
    apply hdistinct e.projection (hs.events e he).projection_min.1
      (hs.events e he).fractional
    exact fun j hj => master_active_tangent d h hs hmaster he j hj

end Chapter03.FPSearch

namespace Chapter03.FPSearchCQControl
open Chapter03.FPSearch Chapter03.FPUnboundedControls

/-- Reuse the accepted nonlinear interval control, with both actual affine
bound rows retained. Global row convexity is proved, not inferred from C. -/
theorem noncycling_jointRows_convex :
    ∀ i, ConvexOn ℝ Set.univ (jointRows data baseRows i) := by
  intro i
  cases i with
  | inl i =>
    exact ((baseRows.linear i).toLinearMap.convexOn convex_univ).add_const
      (baseRows.offset i)
  | inr j =>
    change ConvexOn ℝ Set.univ (fun p : Point 0 1 => (p.2 0-1/2)^2-1/16)
    simpa [Pi.add_def,sub_eq_add_neg] using
      (square_convex convex_univ (yc 0) (1/2)).add_const (-(1/16))

/-- The old-history branch is the accepted actual first projection, not a
synthetic feasible anchor supplied solely to instantiate the new theorem. -/
theorem noncycling_stateOne_valid : Valid data stateOne := by
  exact append_valid data (initial_valid data initializer.1)
    (show EventValid data eventZero from
      ⟨projection_zero, fractional_of_relaxation projection_zero.1⟩)

/-- Apply the new actual-step theorem at the accepted second master and
projection minima. The new block 3/4 differs from both the original seed 1/2
and the retained projection 1/4. Its nonlinear active row has nonzero gradient
and current joint LICQ was already proved in the accepted control. -/
theorem noncycling_second_step :
    Chapter03.yMap 0 1 (pt (3/4)) ≠ Chapter03.yMap 0 1 (pt (1/2)) ∧
    Chapter03.yMap 0 1 (pt (3/4)) ≠ Chapter03.yMap 0 1 (pt (1/4)) := by
  have h := step_integer_projection_distinct_of_current_licq_convex_rows
    data baseRows analytic noncycling_stateOne_valid
    (fractional_of_relaxation initializer.1) secondStep noncycling_jointRows_convex
    (endpoint_licq (3/4) (Or.inr rfl))
  exact ⟨h.1, h.2 eventZero (by
    simp [stateOne, FPSearch.append, stateZero, FPSearch.initialState])⟩

end Chapter03.FPSearchCQControl
