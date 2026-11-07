module

public import Chapter03OAKKTSource
public import Chapter02FiniteCone
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Pointwise fixed-coordinate constraint qualification. All literal soft and
hard rows remain present. Independence concerns active x covectors, with no
y-fixing equations. No convexity, Slater point or minimum existence is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Filter Set Chapter02

namespace Chapter03.OAKKT
variable {n m l r : ℕ}

def fixedRows (d : ModelData n m l r) (y : RealVector m) :
    (Fin l ⊕ Fin r) → RealVector n → ℝ :=
  Sum.elim (soft d y) (hard d y)

def fixedRowD (d : ModelData n m l r)
    (Dg : Fin l → Point n m →L[ℝ] ℝ) :
    (Fin l ⊕ Fin r) → RealVector n →L[ℝ] ℝ :=
  Sum.elim (fun j => restrict (Dg j)) (fiberLinearRow d)

/-- Every actual active row participates, including affine and constant g rows
and all retained hard bounds. Empty active families and zero dimensions are allowed. -/
def FixedLICQ (d : ModelData n m l r)
    (x : RealVector n) (y : RealVector m)
    (Dg : Fin l → Point n m →L[ℝ] ℝ) : Prop :=
  LinearIndependent ℝ
    (fun i : {i : Fin l ⊕ Fin r // fixedRows d y i x = 0} =>
      fixedRowD d Dg i.val)

def FixedMFCQ (d : ModelData n m l r)
    (x : RealVector n) (y : RealVector m)
    (Dg : Fin l → Point n m →L[ℝ] ℝ) : Prop :=
  ∃ w : RealVector n, ∀ i : Fin l ⊕ Fin r,
    fixedRows d y i x = 0 → fixedRowD d Dg i w < 0

end Chapter03.OAKKT

namespace Chapter03.OAExistence

/-- Finite independent covectors attain arbitrary prescribed values; no
nonempty index or positive dimension is required. -/
theorem independent_functionals_surjective {J : Type*} [Fintype J]
    {n : ℕ} (A : J → RealVector n →L[ℝ] ℝ)
    (hA : LinearIndependent ℝ A) (b : J → ℝ) :
    ∃ w : RealVector n, ∀ i, A i w = b i := by
  classical
  let B : (J → ℝ) →ₗ[ℝ] (RealVector n →ₗ[ℝ] ℝ) :=
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
theorem strict_active_feasible_small_steps {J : Type*} [Fintype J]
    {n : ℕ} (c : J → RealVector n → ℝ)
    (A : J → RealVector n →L[ℝ] ℝ) (p v : RealVector n)
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
theorem strict_direction_of_active_independent {J : Type*} [Fintype J]
    {n : ℕ} (c : J → RealVector n → ℝ)
    (A : J → RealVector n →L[ℝ] ℝ) (p : RealVector n)
    (hlicq : LinearIndependent ℝ (fun i : {i : J // c i p = 0} => A i.val)) :
    ∃ w : RealVector n, ∀ i, c i p = 0 → A i w < 0 := by
  classical
  obtain ⟨w, hw⟩ := independent_functionals_surjective
    (fun i : {i : J // c i p = 0} => A i.val) hlicq (fun _ => -1)
  refine ⟨w, fun i hi => ?_⟩
  have he := hw ⟨i, hi⟩
  change A i w = -1 at he
  rw [he]
  norm_num

/-- At an actual differentiable minimum, MFCQ makes the objective derivative
nonnegative on every weakly active-feasible direction. Strict perturbation is
used before taking the limit; no nonlinear weak feasible-ray claim is assumed. -/
theorem minimum_linearized_nonneg_of_mfcq {J : Type*} [Fintype J]
    {n : ℕ} (c : J → RealVector n → ℝ)
    (A : J → RealVector n →L[ℝ] ℝ) (p : RealVector n)
    (F : RealVector n → ℝ) (D : RealVector n →L[ℝ] ℝ)
    (hmin : IsMinimizer {z | ∀ i, c i z ≤ 0} F p)
    (hF : HasFDerivAt F D p) (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hmfcq : ∃ w : RealVector n, ∀ i, c i p = 0 → A i w < 0)
    (v : RealVector n) (hv : ∀ i, c i p = 0 → A i v ≤ 0) : 0 ≤ D v := by
  obtain ⟨w, hw⟩ := hmfcq
  have hm : IsMinOn F {z | ∀ i, c i z ≤ 0} p := isMinOn_iff.mpr hmin.2
  have hpositive : ∀ t : ℝ, 0 < t → 0 ≤ D (v + t • w) := by
    intro t ht
    apply hm.localize.hasFDerivWithinAt_nonneg hF.hasFDerivWithinAt
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    exact strict_active_feasible_small_steps c A p (v + t • w) hmin.1 hA
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

/-- Actual finite-row KKT multipliers derived from a minimum and MFCQ.
Inactive coefficients are zeroed on their original indices. -/
theorem minimum_multipliers_of_mfcq {J : Type*} [Fintype J]
    {n : ℕ} (c : J → RealVector n → ℝ)
    (A : J → RealVector n →L[ℝ] ℝ) (p : RealVector n)
    (F : RealVector n → ℝ) (D : RealVector n →L[ℝ] ℝ)
    (hmin : IsMinimizer {z | ∀ i, c i z ≤ 0} F p)
    (hF : HasFDerivAt F D p) (hA : ∀ i, HasFDerivAt (c i) (A i) p)
    (hmfcq : ∃ w : RealVector n, ∀ i, c i p = 0 → A i w < 0) :
    ∃ mu : J → ℝ, (∀ i, 0 ≤ mu i) ∧ (∀ i, mu i * c i p = 0) ∧
      D + ∑ i, mu i • A i = 0 := by
  classical
  let activeA : J → RealVector n →L[ℝ] ℝ :=
    fun i => if c i p = 0 then A i else 0
  obtain ⟨rho, hrho, hrep⟩ := finite_normal_representation activeA D (by
    intro v hv
    apply minimum_linearized_nonneg_of_mfcq c A p F D hmin hF hA hmfcq v
    intro i hi
    simpa [activeA, hi] using hv i)
  let mu : J → ℝ := fun i => if c i p = 0 then rho i else 0
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : c i p = 0 <;> simp [mu, hi, hrho i]
  · intro i
    by_cases hi : c i p = 0 <;> simp [mu, hi]
  · have he : (∑ i, mu i • A i) = ∑ i, rho i • activeA i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i p = 0 <;> simp [mu, activeA, hi]
    rw [he]
    exact hrep

end Chapter03.OAExistence

#check Chapter03.OAKKT.FixedLICQ
#check Chapter03.OAKKT.FixedMFCQ
#check Chapter03.OAExistence.independent_functionals_surjective
#print axioms Chapter03.OAExistence.independent_functionals_surjective
#check Chapter03.OAExistence.strict_active_feasible_small_steps
#print axioms Chapter03.OAExistence.strict_active_feasible_small_steps
#check Chapter03.OAExistence.strict_direction_of_active_independent
#print axioms Chapter03.OAExistence.strict_direction_of_active_independent
#check Chapter03.OAExistence.minimum_linearized_nonneg_of_mfcq
#print axioms Chapter03.OAExistence.minimum_linearized_nonneg_of_mfcq
#check Chapter03.OAExistence.minimum_multipliers_of_mfcq
#print axioms Chapter03.OAExistence.minimum_multipliers_of_mfcq
