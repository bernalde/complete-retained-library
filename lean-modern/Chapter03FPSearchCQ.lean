module

public import Chapter03OAExistenceCQ
public import Chapter03FPUnboundedAnalytic
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Full ambient-space finite inequality CQ for the first-feasibility search.
The first four proofs generalize accepted Chapter03.OAExistence finite-row
lemmas from a single RealVector to an arbitrary real normed space. In particular
Point n m varies both coordinate blocks; no fixed-y x-gradient CQ is used.
All indexed inequalities are retained. Supporting results, no counted endpoint. -/
noncomputable section
open scoped BigOperators Topology RealInnerProductSpace
open Filter Set Chapter02 Chapter03.FP
namespace Chapter03.FPSearch

section FiniteRows
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite independent covectors attain arbitrary prescribed values; no
nonempty index or positive dimension is required. -/
theorem joint_independent_functionals_surjective {J : Type*} [Fintype J]
    (A : J → E →L[ℝ] ℝ)
    (hA : LinearIndependent ℝ A) (b : J → ℝ) :
    ∃ w : E, ∀ i, A i w = b i := by
  classical
  let B : (J → ℝ) →ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
    (ContinuousLinearMap.coeLM ℝ).comp (Fintype.linearCombination ℝ A)
  have hB : Function.Injective B :=
    ContinuousLinearMap.coe_injective.comp hA.fintypeLinearCombination_injective
  let target : (J → ℝ) →ₗ[ℝ] ℝ :=
    ∑ i, b i • (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ)
  obtain ⟨w, hw⟩ := (LinearMap.flip_surjective_iff₁.mpr hB) target
  refine ⟨w, fun i => ?_⟩
  have hi := LinearMap.congr_fun hw (Pi.single i 1)
  simpa [B, target, LinearMap.flip_apply, Pi.single_apply, mul_ite] using hi

/-- Actual derivatives make every strictly active-feasible direction feasible
for sufficiently small positive steps; inactive rows use their strict slack. -/
theorem joint_strict_active_feasible_small_steps {J : Type*} [Fintype J]
    (c : J → E → ℝ)
    (A : J → E →L[ℝ] ℝ) (p v : E)
    (hp : ∀ i, c i p ≤ 0)
    (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hv : ∀ i, c i p = 0 → A i v < 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i, c i (p + t • v) ≤ 0 := by
  rw [Filter.eventually_all]
  intro i
  have hpath : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hc : HasDerivAt (fun t : ℝ => c i (p + t • v)) (A i v) 0 := by
    simpa [Function.comp_def] using (hA i).comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  by_cases hi : c i p = 0
  · have he := hc.tendsto_slope_zero_right.eventually_lt_const (hv i hi)
    filter_upwards [he, self_mem_nhdsWithin] with t ht htpos
    have hq : t⁻¹ * c i (p + t • v) < 0 := by
      simpa [hi] using ht
    have ht0 : 0 < t := htpos
    have hinv : 0 < t⁻¹ := inv_pos.mpr ht0
    nlinarith
  · have hslack : c i p < 0 := lt_of_le_of_ne (hp i) hi
    have he : ∀ᶠ t : ℝ in 𝓝 0, c i (p + t • v) ≤ 0 :=
      hc.continuousAt.tendsto.eventually_le_const (by simpa using hslack)
    exact he.filter_mono nhdsWithin_le_nhds

/-- The strict active direction is obtained from independence, not supplied as
an additional qualification. The subtype keeps precisely all active rows. -/
theorem joint_strict_direction_of_active_independent {J : Type*} [Fintype J]
    (c : J → E → ℝ)
    (A : J → E →L[ℝ] ℝ) (p : E)
    (hlicq : LinearIndependent ℝ (fun i : {i : J // c i p = 0} => A i.val)) :
    ∃ w : E, ∀ i, c i p = 0 → A i w < 0 := by
  classical
  obtain ⟨w, hw⟩ := joint_independent_functionals_surjective
    (fun i : {i : J // c i p = 0} => A i.val) hlicq (fun _ => -1)
  refine ⟨w, fun i hi => ?_⟩
  have he := hw ⟨i, hi⟩
  change A i w = -1 at he
  rw [he]
  norm_num

/-- At an actual differentiable minimum, MFCQ makes the objective derivative
nonnegative on every weakly active-feasible direction. Strict perturbation is
used before taking the limit; no nonlinear weak feasible-ray claim is assumed. -/
theorem joint_minimum_linearized_nonneg_of_mfcq {J : Type*} [Fintype J]
    (c : J → E → ℝ)
    (A : J → E →L[ℝ] ℝ) (p : E)
    (F : E → ℝ) (D : E →L[ℝ] ℝ)
    (hmin : IsMinimizer {z | ∀ i, c i z ≤ 0} F p)
    (hF : HasFDerivAt F D p) (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hmfcq : ∃ w : E, ∀ i, c i p = 0 → A i w < 0)
    (v : E) (hv : ∀ i, c i p = 0 → A i v ≤ 0) : 0 ≤ D v := by
  obtain ⟨w, hw⟩ := hmfcq
  have hm : IsMinOn F {z | ∀ i, c i z ≤ 0} p := isMinOn_iff.mpr hmin.2
  have hpositive : ∀ t : ℝ, 0 < t → 0 ≤ D (v + t • w) := by
    intro t ht
    apply hm.localize.hasFDerivWithinAt_nonneg hF.hasFDerivWithinAt
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    exact joint_strict_active_feasible_small_steps c A p (v + t • w) hmin.1 hA
      (fun i hi => by
        simp only [map_add, map_smul, smul_eq_mul]
        exact add_neg_of_nonpos_of_neg (hv i hi) (mul_neg_of_pos_of_neg ht (hw i hi)))
  by_contra hn
  have hneg : D v < 0 := lt_of_not_ge hn
  have hc : ContinuousAt (fun t : ℝ => D (v + t • w)) 0 :=
    (D.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousAt
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, D (v + t • w) < 0 :=
    (hc.tendsto.eventually_lt_const (by simpa using hneg)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := (he.and self_mem_nhdsWithin).exists
  exact (not_lt_of_ge (hpositive t htpos)) ht


/-- Exact active covectors of every indexed residual. -/
def JointLICQ {J : Type*} (c : J → E → ℝ)
    (A : J → E →L[ℝ] ℝ) (p : E) : Prop :=
  LinearIndependent ℝ (fun i : {i : J // c i p = 0} => A i.val)

/-- Full-space strict active direction, without deleting zero/duplicate rows. -/
def JointMFCQ {J : Type*} (c : J → E → ℝ)
    (A : J → E →L[ℝ] ℝ) (p : E) : Prop :=
  ∃ w : E, ∀ i, c i p = 0 → A i w < 0

theorem joint_mfcq_of_licq {J : Type*} [Fintype J]
    (c : J → E → ℝ) (A : J → E →L[ℝ] ℝ) (p : E)
    (h : JointLICQ c A p) : JointMFCQ c A p :=
  joint_strict_direction_of_active_independent c A p h

end FiniteRows

variable {n m : ℕ}

/-- Continuous full-space projection onto the integer-coordinate block. -/
def searchYMap (n m : ℕ) : Point n m →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap (Chapter03.yMap n m)

/-- Actual ambient derivative of the squared coordinate projection objective. -/
def searchDistanceD (q : IntVector m) (p : Point n m) : Point n m →L[ℝ] ℝ :=
  2 • (innerSL ℝ (Chapter03.yMap n m p - intY q)).comp (searchYMap n m)

theorem searchDistanceD_apply (q : IntVector m) (p v : Point n m) :
    searchDistanceD q p v =
      2 * @inner ℝ _ _ (Chapter03.yMap n m p - intY q) (Chapter03.yMap n m v) := by
  simp only [searchDistanceD, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rfl

theorem search_distance_hasFDerivAt (q : IntVector m) (p : Point n m) :
    HasFDerivAt (distance q) (searchDistanceD q p) p := by
  have h := (((searchYMap n m).hasFDerivAt (x := p)).sub_const (intY q)).norm_sq
  have he : (fun z : Point n m => ‖searchYMap n m z - intY q‖ ^ 2) = distance q := by
    funext z
    simp only [distance, searchYMap, LinearMap.coe_toContinuousLinearMap', norm_sub_rev]
  rw [← he]
  exact h

/-- The finite-row normal implication uses actual minimization and derivatives,
not convexity or an assumed normal. All full-domain rows must occur in c. -/
theorem joint_projection_normal_of_mfcq {J : Type*} [Fintype J]
    (c : J → Point n m → ℝ) (A : J → Point n m →L[ℝ] ℝ)
    (q : IntVector m) (p z : Point n m)
    (hmin : IsMinimizer {w | ∀ i, c i w ≤ 0} (distance q) p)
    (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hcq : JointMFCQ c A p)
    (hz : ∀ i, c i p = 0 → A i (z-p) ≤ 0) :
    0 ≤ @inner ℝ _ _ (Chapter03.yMap n m p - intY q)
      (Chapter03.yMap n m z - Chapter03.yMap n m p) := by
  have h := joint_minimum_linearized_nonneg_of_mfcq c A p (distance q)
    (searchDistanceD q p) hmin (search_distance_hasFDerivAt q p) hA hcq (z-p) hz
  rw [searchDistanceD_apply, map_sub] at h
  linarith

theorem joint_projection_normal_of_licq {J : Type*} [Fintype J]
    (c : J → Point n m → ℝ) (A : J → Point n m →L[ℝ] ℝ)
    (q : IntVector m) (p z : Point n m)
    (hmin : IsMinimizer {w | ∀ i, c i w ≤ 0} (distance q) p)
    (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hcq : JointLICQ c A p)
    (hz : ∀ i, c i p = 0 → A i (z-p) ≤ 0) :
    0 ≤ @inner ℝ _ _ (Chapter03.yMap n m p - intY q)
      (Chapter03.yMap n m z - Chapter03.yMap n m p) :=
  joint_projection_normal_of_mfcq c A q p z hmin hA (joint_mfcq_of_licq c A p hcq) hz

end Chapter03.FPSearch
