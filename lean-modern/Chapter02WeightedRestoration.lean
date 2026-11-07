module

public import Chapter02MultiplierExistence

@[expose] public section

/-! Actual weighted-positive-part restoration with retained hard rows.
The sufficient CQ concerns only the hard rows on the selected fiber. The
empty hard family needs no nonlinear CQ. The normal functional is derived
from an actual lifted minimum and retains the entire original convex domain. -/
noncomputable section
open scoped BigOperators
open Set
namespace Chapter02

def weightedHardRegion {E : Type*} {h : ℕ} (C : Set E)
    (hard : Fin h → E → ℝ) : Set E := {x ∈ C | ∀ j, hard j x ≤ 0}

def weightedPositive {E : Type*} {s : ℕ} (w : Fin s → ℝ)
    (soft : Fin s → E → ℝ) (x : E) : ℝ := ∑ j, w j * max (soft j x) 0

theorem weightedPositive_nonneg {E : Type*} {s : ℕ} (w : Fin s → ℝ)
    (soft : Fin s → E → ℝ) (hw : ∀ j, 0 ≤ w j) (x : E) :
    0 ≤ weightedPositive w soft x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (le_max_right _ _)

theorem weightedPositive_eq_zero_iff {E : Type*} {s : ℕ} (w : Fin s → ℝ)
    (soft : Fin s → E → ℝ) (hw : ∀ j, 0 < w j) (x : E) :
    weightedPositive w soft x = 0 ↔ ∀ j, soft j x ≤ 0 := by
  rw [weightedPositive, Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hw j).le (le_max_right _ _))]
  constructor
  · intro hz j
    have h := (mul_eq_zero.mp (hz j (Finset.mem_univ j))).resolve_left (ne_of_gt (hw j))
    exact (max_eq_right_iff.mp h)
  · intro hx j _
    rw [max_eq_right (hx j), mul_zero]

theorem weightedPositive_continuous {E : Type*} [TopologicalSpace E] {s : ℕ}
    (w : Fin s → ℝ) (soft : Fin s → E → ℝ) (hg : ∀ j, Continuous (soft j)) :
    Continuous (weightedPositive w soft) := by
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul ((hg j).max continuous_const)

theorem weightedHardRegion_compact {E : Type*} [TopologicalSpace E] {h : ℕ}
    (C : Set E) (hard : Fin h → E → ℝ) (hC : IsCompact C)
    (hh : ∀ j, Continuous (hard j)) : IsCompact (weightedHardRegion C hard) := by
  have he : weightedHardRegion C hard = C ∩ ⋂ j, {x | hard j x ≤ 0} := by
    ext x; simp [weightedHardRegion]
  rw [he]
  exact hC.inter_right (isClosed_iInter fun j => isClosed_le (hh j) continuous_const)

theorem weighted_hard_minimum_exists {E : Type*} [TopologicalSpace E] {h s : ℕ}
    (C : Set E) (hard : Fin h → E → ℝ) (soft : Fin s → E → ℝ)
    (w : Fin s → ℝ) (hC : IsCompact C)
    (hne : (weightedHardRegion C hard).Nonempty)
    (hh : ∀ j, Continuous (hard j)) (hs : ∀ j, Continuous (soft j)) :
    ∃ p, IsMinimizer (weightedHardRegion C hard) (weightedPositive w soft) p :=
  compact_feasible_attainment (weightedHardRegion_compact C hard hC hh) hne
    (weightedPositive_continuous w soft hs).continuousOn

theorem weighted_hard_value_pos_iff_empty {E : Type*} {h s : ℕ}
    (C : Set E) (hard : Fin h → E → ℝ) (soft : Fin s → E → ℝ)
    (w : Fin s → ℝ) (hw : ∀ j, 0 < w j) {p : E}
    (hp : IsMinimizer (weightedHardRegion C hard) (weightedPositive w soft) p) :
    0 < weightedPositive w soft p ↔
      ¬ ∃ x ∈ weightedHardRegion C hard, ∀ j, soft j x ≤ 0 := by
  constructor
  · rintro hpos ⟨x,hx,hs⟩
    have hm := hp.2 x hx
    rw [(weightedPositive_eq_zero_iff w soft hw x).mpr hs] at hm
    exact (not_le_of_gt hpos) hm
  · intro he
    have hn := weightedPositive_nonneg w soft (fun j => (hw j).le) p
    refine lt_of_le_of_ne hn ?_
    intro hz
    exact he ⟨p,hp.1,(weightedPositive_eq_zero_iff w soft hw p).mp hz.symm⟩

def weightedX {n s : ℕ} : RealVector (n+s) →L[ℝ] RealVector n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (i.castAdd s)

def weightedV {n s : ℕ} : RealVector (n+s) →L[ℝ] RealVector s :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (j.natAdd n)

def weightedInsert {n s : ℕ} (x : RealVector n) (v : RealVector s) : RealVector (n+s) :=
  Fin.addCases x v

@[simp] theorem weightedX_insert {n s : ℕ} (x : RealVector n) (v : RealVector s) :
    weightedX (weightedInsert x v) = x := by ext i; simp [weightedX,weightedInsert]

@[simp] theorem weightedV_insert {n s : ℕ} (x : RealVector n) (v : RealVector s) :
    weightedV (weightedInsert x v) = v := by ext i; simp [weightedV,weightedInsert]

@[simp] theorem weightedInsert_project {n s : ℕ} (q : RealVector (n+s)) :
    weightedInsert (weightedX q) (weightedV q) = q := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [weightedInsert,weightedX,weightedV]

def weightedLiftRows {n h s : ℕ} (hard : Fin h → RealVector n → ℝ)
    (soft : Fin s → RealVector n → ℝ) : Fin (h+(s+s)) → RealVector (n+s) → ℝ :=
  Fin.addCases (fun j q => hard j (weightedX q))
    (Fin.addCases (fun j q => soft j (weightedX q)-weightedV q j)
      (fun j q => -weightedV q j))

def weightedLiftObjective {n s : ℕ} (w : Fin s → ℝ) : RealVector (n+s) →L[ℝ] ℝ :=
  ∑ j, w j • (ContinuousLinearMap.proj (j.natAdd n))

@[simp] theorem weightedLiftObjective_apply {n s : ℕ} (w : Fin s → ℝ)
    (q : RealVector (n+s)) :
    weightedLiftObjective w q = ∑ j, w j * weightedV q j := by
  simp [weightedLiftObjective,weightedV]

theorem weighted_lift_rows_iff {n h s : ℕ}
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (q : RealVector (n+s)) :
    (∀ i, weightedLiftRows hard soft i q ≤ 0) ↔
      (∀ j, hard j (weightedX q) ≤ 0) ∧
      (∀ j, soft j (weightedX q) ≤ weightedV q j) ∧ (∀ j, 0 ≤ weightedV q j) := by
  constructor
  · intro ha
    refine ⟨?_,?_,?_⟩
    · intro j
      simpa [weightedLiftRows] using ha (j.castAdd (s+s))
    · intro j
      have hj := ha ((j.castAdd s).natAdd h)
      simpa [weightedLiftRows,sub_nonpos] using hj
    · intro j
      have hj := ha ((j.natAdd s).natAdd h)
      rw [weightedLiftRows,Fin.addCases_right,Fin.addCases_right] at hj
      exact neg_nonpos.mp hj
  · rintro ⟨hh,hs,hv⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [weightedLiftRows] using hh j
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa [weightedLiftRows,sub_nonpos] using hs k
      · rw [weightedLiftRows,Fin.addCases_right,Fin.addCases_right]
        exact neg_nonpos.mpr (hv k)

theorem weighted_lift_minimizer {n h s : ℕ} (C : Set (RealVector n))
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (w : Fin s → ℝ) (hw : ∀ j, 0 ≤ w j) {p : RealVector n}
    (hp : IsMinimizer (weightedHardRegion C hard) (weightedPositive w soft) p) :
    IsMinimizer {q ∈ weightedX ⁻¹' C | ∀ i, weightedLiftRows hard soft i q ≤ 0}
      (weightedLiftObjective w)
      (weightedInsert p (fun j => max (soft j p) 0)) := by
  refine ⟨⟨by simpa using hp.1.1,?_⟩,?_⟩
  · rw [weighted_lift_rows_iff]
    simp only [weightedX_insert,weightedV_insert]
    exact ⟨hp.1.2,fun j => le_max_left _ _,fun j => le_max_right _ _⟩
  · intro q hq
    obtain ⟨hh,hs,hv⟩ := (weighted_lift_rows_iff hard soft q).mp hq.2
    calc
      weightedLiftObjective w (weightedInsert p (fun j => max (soft j p) 0)) =
          weightedPositive w soft p := by simp [weightedPositive]
      _ ≤ weightedPositive w soft (weightedX q) := hp.2 _ ⟨hq.1,hh⟩
      _ ≤ weightedLiftObjective w q := by
        rw [weightedLiftObjective_apply]
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (max_le (hs j) (hv j)) (hw j)

theorem weighted_lift_project_minimizer {n h s : ℕ} (C : Set (RealVector n))
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (w : Fin s → ℝ) (hw : ∀ j, 0 ≤ w j) {q : RealVector (n+s)}
    (hq : IsMinimizer {z ∈ weightedX ⁻¹' C | ∀ i, weightedLiftRows hard soft i z ≤ 0}
      (weightedLiftObjective w) q) :
    IsMinimizer (weightedHardRegion C hard) (weightedPositive w soft) (weightedX q) := by
  obtain ⟨hh,hs,hv⟩ := (weighted_lift_rows_iff hard soft q).mp hq.1.2
  refine ⟨⟨hq.1.1,hh⟩,?_⟩
  intro x hx
  have ha : weightedPositive w soft (weightedX q) ≤ weightedLiftObjective w q := by
    rw [weightedLiftObjective_apply]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (max_le (hs j) (hv j)) (hw j)
  have hb := hq.2 (weightedInsert x (fun j => max (soft j x) 0))
    ⟨by simpa using hx.1, (weighted_lift_rows_iff _ _ _).mpr
      (by simpa using And.intro hx.2 (And.intro (fun j => le_max_left (soft j x) 0)
        (fun j => le_max_right (soft j x) 0)))⟩
  exact ha.trans (by simpa [weightedPositive] using hb)

theorem convex_minimum_derivative_nonneg {n : ℕ} {C : Set (RealVector n)}
    {f : RealVector n → ℝ} {p : RealVector n} {D : RealVector n →L[ℝ] ℝ}
    (hC : Convex ℝ C) (hp : IsMinimizer C f p) (hd : HasFDerivAt f D p)
    {q : RealVector n} (hq : q ∈ C) : 0 ≤ D (q-p) := by
  have hm : IsMinOn f C p := isMinOn_iff.mpr hp.2
  exact hm.localize.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hp.1 hq))

def weightedLiftDerivative {n h s : ℕ}
    (Dh : Fin h → RealVector n →L[ℝ] ℝ) (Ds : Fin s → RealVector n →L[ℝ] ℝ) :
    Fin (h+(s+s)) → RealVector (n+s) →L[ℝ] ℝ :=
  Fin.addCases (fun j => (Dh j).comp weightedX)
    (Fin.addCases (fun j => (Ds j).comp weightedX - ContinuousLinearMap.proj (j.natAdd n))
      (fun j => -ContinuousLinearMap.proj (j.natAdd n)))

theorem weighted_lift_derivative {n h s : ℕ}
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (Dh : Fin h → RealVector n →L[ℝ] ℝ) (Ds : Fin s → RealVector n →L[ℝ] ℝ)
    {p : RealVector n} (v : RealVector s)
    (hh : ∀ j, HasFDerivAt (hard j) (Dh j) p)
    (hs : ∀ j, HasFDerivAt (soft j) (Ds j) p) :
    ∀ i, HasFDerivAt (weightedLiftRows hard soft i) (weightedLiftDerivative Dh Ds i)
      (weightedInsert p v) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [weightedLiftRows,weightedLiftDerivative,Fin.addCases_left, Function.comp_def, ContinuousLinearMap.coe_coe] using
      ((show HasFDerivAt (hard j) (Dh j) (weightedX (weightedInsert p v)) by simpa using hh j).comp _
        weightedX.hasFDerivAt)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [weightedLiftRows,weightedLiftDerivative,Fin.addCases_right,Fin.addCases_left,
        weightedV,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply, Function.comp_def, Pi.sub_apply, Pi.neg_apply] using
        (((show HasFDerivAt (soft k) (Ds k) (weightedX (weightedInsert p v)) by simpa using hs k).comp _
          weightedX.hasFDerivAt).fun_sub (ContinuousLinearMap.proj (k.natAdd n)).hasFDerivAt)
    · simpa only [weightedLiftRows,weightedLiftDerivative,Fin.addCases_right,weightedV,
        ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply, Function.comp_def, Pi.sub_apply, Pi.neg_apply] using
        ((ContinuousLinearMap.proj (k.natAdd n) : RealVector (n+s) →L[ℝ] ℝ).hasFDerivAt (x := weightedInsert p v)).fun_neg

theorem weighted_lift_rows_convex {n h s : ℕ}
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (hh : ∀ j, ConvexOn ℝ Set.univ (hard j))
    (hs : ∀ j, ConvexOn ℝ Set.univ (soft j)) :
    ∀ i, ConvexOn ℝ Set.univ (weightedLiftRows hard soft i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [weightedLiftRows,Fin.addCases_left,Set.preimage_univ, Function.comp_def, ContinuousLinearMap.coe_coe] using
      (hh j).comp_linearMap (weightedX (n:=n) (s:=s)).toLinearMap
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · have hc : ConvexOn ℝ Set.univ (fun q : RealVector (n+s) => soft k (weightedX q)) := by
        simpa only [Set.preimage_univ, Function.comp_def, ContinuousLinearMap.coe_coe] using (hs k).comp_linearMap weightedX.toLinearMap
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      have h := hc.2 hx hy ha hb hab
      simp only [weightedLiftRows, Fin.addCases_right, Fin.addCases_left, weightedV,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at *
      linarith
    · refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [weightedLiftRows, Fin.addCases_right, weightedV,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      exact le_of_eq (by ring)

theorem weighted_lift_slater {n h s : ℕ} (C : Set (RealVector n))
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (hslater : ∃ z ∈ C, ∀ j, hard j z < 0) :
    ∃ z ∈ weightedX ⁻¹' C, ∀ i, weightedLiftRows hard soft i z < 0 := by
  obtain ⟨z,hz,hh⟩ := hslater
  refine ⟨weightedInsert z (fun j => max (soft j z) 0 + 1), by simpa using hz, ?_⟩
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [weightedLiftRows,Fin.addCases_left,weightedX_insert] using hh j
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [weightedLiftRows,Fin.addCases_right,Fin.addCases_left,
        weightedX_insert,weightedV_insert]
      have := le_max_left (soft k z) 0
      linarith
    · simp only [weightedLiftRows,Fin.addCases_right,weightedV_insert]
      have := le_max_right (soft k z) 0
      linarith

def weightedHardMultiplier {h s : ℕ} (lambda : Fin (h+(s+s)) → ℝ) (j : Fin h) : ℝ :=
  lambda (j.castAdd (s+s))
def weightedSoftMultiplier {h s : ℕ} (lambda : Fin (h+(s+s)) → ℝ) (j : Fin s) : ℝ :=
  lambda ((j.castAdd s).natAdd h)
def weightedSlackMultiplier {h s : ℕ} (lambda : Fin (h+(s+s)) → ℝ) (j : Fin s) : ℝ :=
  lambda ((j.natAdd s).natAdd h)

def weightedPartialDerivative {n h s : ℕ} (w : Fin s → ℝ)
    (Dh : Fin h → RealVector n →L[ℝ] ℝ) (Ds : Fin s → RealVector n →L[ℝ] ℝ)
    (lambda : Fin (h+(s+s)) → ℝ) : RealVector (n+s) →L[ℝ] ℝ :=
  weightedLiftObjective w + ∑ i, lambda i • weightedLiftDerivative Dh Ds i

theorem weighted_partial_apply {n h s : ℕ} (w : Fin s → ℝ)
    (Dh : Fin h → RealVector n →L[ℝ] ℝ) (Ds : Fin s → RealVector n →L[ℝ] ℝ)
    (lambda : Fin (h+(s+s)) → ℝ) (q : RealVector (n+s)) :
    weightedPartialDerivative w Dh Ds lambda q =
      (∑ j, w j * weightedV q j) +
      (∑ j, weightedHardMultiplier lambda j * Dh j (weightedX q)) +
      (∑ j, weightedSoftMultiplier lambda j * (Ds j (weightedX q)-weightedV q j)) +
      (∑ j, weightedSlackMultiplier lambda j * (-weightedV q j)) := by
  simp only [weightedPartialDerivative,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    weightedLiftObjective_apply,Fin.sum_univ_add,weightedLiftDerivative,
    Fin.addCases_left,Fin.addCases_right,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.proj_apply,
    weightedHardMultiplier,weightedSoftMultiplier,weightedSlackMultiplier]
  simp only [weightedV,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply]
  ring

structure WeightedHardKKT {n h s : ℕ} (C : Set (RealVector n))
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (w : Fin s → ℝ) (p : RealVector n)
    (Dh : Fin h → RealVector n →L[ℝ] ℝ) (Ds : Fin s → RealVector n →L[ℝ] ℝ)
    (mu : Fin h → ℝ) (lambda : Fin s → ℝ) (normal : RealVector n →L[ℝ] ℝ) : Prop where
  mem : p ∈ weightedHardRegion C hard
  hard_nonneg : ∀ j, 0 ≤ mu j
  soft_nonneg : ∀ j, 0 ≤ lambda j
  soft_le_weight : ∀ j, lambda j ≤ w j
  hard_compl : ∀ j, mu j * hard j p = 0
  soft_compl : ∀ j, lambda j * (soft j p - max (soft j p) 0) = 0
  slack_compl : ∀ j, (w j-lambda j) * max (soft j p) 0 = 0
  normal_le : ∀ q ∈ C, normal (q-p) ≤ 0
  stationarity : (∑ j, mu j • Dh j) + (∑ j, lambda j • Ds j) + normal = 0

theorem weighted_hard_kkt_exists {n h s : ℕ} (C : Set (RealVector n))
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (w : Fin s → ℝ) (p : RealVector n)
    (Dh : Fin h → RealVector n →L[ℝ] ℝ) (Ds : Fin s → RealVector n →L[ℝ] ℝ)
    (hC : Convex ℝ C) (hw : ∀ j, 0 ≤ w j)
    (hhconv : ∀ j, ConvexOn ℝ Set.univ (hard j))
    (hsconv : ∀ j, ConvexOn ℝ Set.univ (soft j))
    (hhd : ∀ j, HasFDerivAt (hard j) (Dh j) p)
    (hsd : ∀ j, HasFDerivAt (soft j) (Ds j) p)
    (hp : IsMinimizer (weightedHardRegion C hard) (weightedPositive w soft) p)
    (hslater : ∃ z ∈ C, ∀ j, hard j z < 0) :
    ∃ mu lambda normal, WeightedHardKKT C hard soft w p Dh Ds mu lambda normal := by
  let v : RealVector s := fun j => max (soft j p) 0
  let z := weightedInsert p v
  let P : Set (RealVector (n+s)) := weightedX ⁻¹' C
  have hP : Convex ℝ P := hC.linear_preimage weightedX.toLinearMap
  have hrc := weighted_lift_rows_convex hard soft hhconv hsconv
  obtain ⟨L,hL,hcomp,hmin⟩ := convex_slater_partialLagrangian_minimum P
    (weightedLiftObjective w) (weightedLiftRows hard soft) z hP
    ((weightedLiftObjective w).toLinearMap.convexOn hP)
    (fun j => (hrc j).subset (subset_univ _) hP)
    (weighted_lift_minimizer C hard soft w hw hp) (weighted_lift_slater C hard soft hslater)
  have hd : HasFDerivAt
      (fun q => weightedLiftObjective w q + ∑ i, L i * weightedLiftRows hard soft i q)
      (weightedPartialDerivative w Dh Ds L) z := by
    exact (weightedLiftObjective w).hasFDerivAt.add (HasFDerivAt.fun_sum fun i _ =>
      ((weighted_lift_derivative hard soft Dh Ds v hhd hsd i).const_mul (L i)))
  have hdir : ∀ q : RealVector (n+s), weightedX q ∈ C →
      0 ≤ weightedPartialDerivative w Dh Ds L (q-z) := by
    intro q hq
    exact convex_minimum_derivative_nonneg hP hmin hd hq
  have hbalance : ∀ j, w j-weightedSoftMultiplier L j-weightedSlackMultiplier L j=0 := by
    intro j
    have hp0 := hdir (z + weightedInsert (0 : RealVector n) (Pi.single j 1))
      (by simpa [z] using hp.1.1)
    have hn0 := hdir (z - weightedInsert (0 : RealVector n) (Pi.single j 1))
      (by simpa [z] using hp.1.1)
    simp only [add_sub_cancel_left,sub_sub_cancel_left,map_neg] at hp0 hn0
    have he : weightedPartialDerivative w Dh Ds L
        (weightedInsert (0 : RealVector n) (Pi.single j 1)) =
        w j-weightedSoftMultiplier L j-weightedSlackMultiplier L j := by
      rw [weighted_partial_apply]
      simp [Pi.single_apply, sub_eq_add_neg]
    rw [he] at hp0 hn0
    linarith
  let normal : RealVector n →L[ℝ] ℝ :=
    -((∑ j, weightedHardMultiplier L j • Dh j) + (∑ j, weightedSoftMultiplier L j • Ds j))
  refine ⟨weightedHardMultiplier L,weightedSoftMultiplier L,normal,
    hp.1,fun j => hL _,fun j => hL _,?_,?_,?_,?_,?_,by dsimp [normal]; abel⟩
  · intro j
    have := hL ((j.natAdd s).natAdd h)
    dsimp [weightedSlackMultiplier] at hbalance
    linarith [hbalance j]
  · intro j
    simpa only [z,v,weightedLiftRows,Fin.addCases_left,weightedX_insert,
      weightedHardMultiplier] using hcomp (j.castAdd (s+s))
  · intro j
    simpa only [z,v,weightedLiftRows,Fin.addCases_right,Fin.addCases_left,weightedX_insert,
      weightedV_insert,weightedSoftMultiplier] using hcomp ((j.castAdd s).natAdd h)
  · intro j
    have hj := hcomp ((j.natAdd s).natAdd h)
    simp only [z,v,weightedLiftRows,Fin.addCases_right,weightedV_insert] at hj
    change weightedSlackMultiplier L j * (-max (soft j p) 0)=0 at hj
    have hb : w j - weightedSoftMultiplier L j = weightedSlackMultiplier L j := by linarith [hbalance j]
    rw [hb]
    simpa only [mul_neg,neg_eq_zero] using hj
  · intro q hq
    have hh := hdir (weightedInsert q v) (by simpa using hq)
    rw [weighted_partial_apply] at hh
    simp only [z,map_sub,weightedX_insert,weightedV_insert,sub_self,map_zero,mul_zero,
      Finset.sum_const_zero,zero_add,sub_zero,neg_zero,Pi.zero_apply] at hh
    simp only [normal,ContinuousLinearMap.neg_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,map_sub]
    simp only [mul_sub,Finset.sum_sub_distrib] at hh
    linarith


theorem WeightedHardKKT.soft_value {n h s : ℕ} {C : Set (RealVector n)}
    {hard : Fin h → RealVector n → ℝ} {soft : Fin s → RealVector n → ℝ}
    {w : Fin s → ℝ} {p : RealVector n}
    {Dh : Fin h → RealVector n →L[ℝ] ℝ} {Ds : Fin s → RealVector n →L[ℝ] ℝ}
    {mu : Fin h → ℝ} {lambda : Fin s → ℝ} {normal : RealVector n →L[ℝ] ℝ}
    (hk : WeightedHardKKT C hard soft w p Dh Ds mu lambda normal) (j : Fin s) :
    lambda j * soft j p = w j * max (soft j p) 0 := by
  nlinarith [hk.soft_compl j,hk.slack_compl j]

theorem weighted_hard_tangent_lower {n h s : ℕ} {C : Set (RealVector n)}
    {hard : Fin h → RealVector n → ℝ} {soft : Fin s → RealVector n → ℝ}
    {w : Fin s → ℝ} {p : RealVector n}
    {Dh : Fin h → RealVector n →L[ℝ] ℝ} {Ds : Fin s → RealVector n →L[ℝ] ℝ}
    {mu : Fin h → ℝ} {lambda : Fin s → ℝ} {normal : RealVector n →L[ℝ] ℝ}
    (hk : WeightedHardKKT C hard soft w p Dh Ds mu lambda normal)
    {q : RealVector n} (hq : q ∈ C) :
    weightedPositive w soft p ≤
      (∑ j, mu j * (hard j p + Dh j (q-p))) +
      (∑ j, lambda j * (soft j p + Ds j (q-p))) := by
  have he := congrArg (fun D : RealVector n →L[ℝ] ℝ => D (q-p)) hk.stationarity
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.zero_apply] at he
  simp only [mul_add,Finset.sum_add_distrib,hk.hard_compl,Finset.sum_const_zero,
    zero_add,hk.soft_value,weightedPositive]
  linarith [hk.normal_le q hq]

theorem weighted_hard_tangent_exclusion {n h s : ℕ} {C : Set (RealVector n)}
    {hard : Fin h → RealVector n → ℝ} {soft : Fin s → RealVector n → ℝ}
    {w : Fin s → ℝ} {p : RealVector n}
    {Dh : Fin h → RealVector n →L[ℝ] ℝ} {Ds : Fin s → RealVector n →L[ℝ] ℝ}
    {mu : Fin h → ℝ} {lambda : Fin s → ℝ} {normal : RealVector n →L[ℝ] ℝ}
    (hk : WeightedHardKKT C hard soft w p Dh Ds mu lambda normal)
    (hpos : 0 < weightedPositive w soft p) :
    ¬ ∃ q ∈ C, (∀ j, hard j p + Dh j (q-p) ≤ 0) ∧
      (∀ j, soft j p + Ds j (q-p) ≤ 0) := by
  rintro ⟨q,hq,hh,hs⟩
  have ht := weighted_hard_tangent_lower hk hq
  have h1 : (∑ j, mu j * (hard j p + Dh j (q-p))) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hk.hard_nonneg j) (hh j)
  have h2 : (∑ j, lambda j * (soft j p + Ds j (q-p))) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hk.soft_nonneg j) (hs j)
  linarith

/-- Derived exclusion for the actual chosen restoration minimizer. The retained
hard-family Slater premise is a named sufficient repair, not global Slater. -/
theorem weighted_hard_actual_minimum_excludes {n h s : ℕ} (C : Set (RealVector n))
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (w : Fin s → ℝ) (p : RealVector n)
    (Dh : Fin h → RealVector n →L[ℝ] ℝ) (Ds : Fin s → RealVector n →L[ℝ] ℝ)
    (hC : Convex ℝ C) (hw : ∀ j, 0 < w j)
    (hhconv : ∀ j, ConvexOn ℝ Set.univ (hard j))
    (hsconv : ∀ j, ConvexOn ℝ Set.univ (soft j))
    (hhd : ∀ j, HasFDerivAt (hard j) (Dh j) p)
    (hsd : ∀ j, HasFDerivAt (soft j) (Ds j) p)
    (hp : IsMinimizer (weightedHardRegion C hard) (weightedPositive w soft) p)
    (hslater : ∃ z ∈ C, ∀ j, hard j z < 0)
    (hempty : ¬ ∃ x ∈ weightedHardRegion C hard, ∀ j, soft j x ≤ 0) :
    ¬ ∃ q ∈ C, (∀ j, hard j p + Dh j (q-p) ≤ 0) ∧
      (∀ j, soft j p + Ds j (q-p) ≤ 0) := by
  obtain ⟨mu,lambda,normal,hk⟩ := weighted_hard_kkt_exists C hard soft w p Dh Ds hC
    (fun j => (hw j).le) hhconv hsconv hhd hsd hp hslater
  exact weighted_hard_tangent_exclusion hk
    ((weighted_hard_value_pos_iff_empty C hard soft w hw hp).mpr hempty)

/-- With no retained hard rows, the sufficient CQ is automatic at the actual
minimizer. No strict original nonlinear point is assumed. -/
theorem weighted_empty_hard_actual_minimum_excludes {n s : ℕ} (C : Set (RealVector n))
    (soft : Fin s → RealVector n → ℝ) (w : Fin s → ℝ) (p : RealVector n)
    (Ds : Fin s → RealVector n →L[ℝ] ℝ)
    (hC : Convex ℝ C) (hw : ∀ j, 0 < w j)
    (hsconv : ∀ j, ConvexOn ℝ Set.univ (soft j))
    (hsd : ∀ j, HasFDerivAt (soft j) (Ds j) p)
    (hp : IsMinimizer C (weightedPositive w soft) p)
    (hempty : ¬ ∃ x ∈ C, ∀ j, soft j x ≤ 0) :
    ¬ ∃ q ∈ C, ∀ j, soft j p + Ds j (q-p) ≤ 0 := by
  let hard : Fin 0 → RealVector n → ℝ := Fin.elim0
  let Dh : Fin 0 → RealVector n →L[ℝ] ℝ := Fin.elim0
  have he : weightedHardRegion C hard = C := by ext x; simp [weightedHardRegion]
  have hx := weighted_hard_actual_minimum_excludes C hard soft w p Dh Ds hC hw
    (fun j => Fin.elim0 j) hsconv (fun j => Fin.elim0 j) hsd
    (by simpa only [he] using hp) ⟨p,hp.1,fun j => Fin.elim0 j⟩
    (by simpa only [he] using hempty)
  rintro ⟨q,hq,hcut⟩
  exact hx ⟨q,hq,fun j => Fin.elim0 j,hcut⟩

/-- Strictly positive weights force every individual slack to be tight at
an arbitrary actual lift minimizer, including tied primal minimizers. -/
theorem weighted_lift_slacks_tight {n h s : ℕ} (C : Set (RealVector n))
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (w : Fin s → ℝ) (hw : ∀j,0<w j) {q : RealVector (n+s)}
    (hq : IsMinimizer {z ∈ weightedX ⁻¹' C | ∀i,weightedLiftRows hard soft i z≤0}
      (weightedLiftObjective w) q) : ∀j,weightedV q j=max (soft j (weightedX q)) 0 := by
  obtain ⟨hh,hs,hv⟩ := (weighted_lift_rows_iff hard soft q).mp hq.1.2
  have hc := hq.2 (weightedInsert (weightedX q) (fun j => max (soft j (weightedX q)) 0))
    ⟨by simpa using hq.1.1,(weighted_lift_rows_iff hard soft _).mpr
      (by simpa using And.intro hh (And.intro (fun j => le_max_left (soft j (weightedX q)) 0)
        (fun j => le_max_right (soft j (weightedX q)) 0)))⟩
  simp only [weightedLiftObjective_apply,weightedV_insert] at hc
  have hnon : ∀j,0≤w j*(weightedV q j-max (soft j (weightedX q)) 0) := by
    intro j
    exact mul_nonneg (hw j).le (sub_nonneg.mpr (max_le (hs j) (hv j)))
  have hz : (∑j,w j*(weightedV q j-max (soft j (weightedX q)) 0))=0 := by
    apply le_antisymm
    · simp only [mul_sub,Finset.sum_sub_distrib]
      linarith
    · exact Finset.sum_nonneg fun j _ => hnon j
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnon j)).mp hz
  intro j
  have hzero := (mul_eq_zero.mp (hall j (Finset.mem_univ j))).resolve_left (ne_of_gt (hw j))
  exact sub_eq_zero.mp hzero

theorem weighted_lift_minimizer_iff {n h s : ℕ} (C : Set (RealVector n))
    (hard : Fin h → RealVector n → ℝ) (soft : Fin s → RealVector n → ℝ)
    (w : Fin s → ℝ) (hw : ∀j,0<w j) (q : RealVector (n+s)) :
    IsMinimizer {z ∈ weightedX ⁻¹' C | ∀i,weightedLiftRows hard soft i z≤0}
      (weightedLiftObjective w) q ↔
    IsMinimizer (weightedHardRegion C hard) (weightedPositive w soft) (weightedX q) ∧
      ∀j,weightedV q j=max (soft j (weightedX q)) 0 := by
  constructor
  · intro hq
    exact ⟨weighted_lift_project_minimizer C hard soft w (fun j => (hw j).le) hq,
      weighted_lift_slacks_tight C hard soft w hw hq⟩
  · rintro ⟨hp,ht⟩
    have he : weightedV q=(fun j => max (soft j (weightedX q)) 0) := funext ht
    have hm := weighted_lift_minimizer C hard soft w (fun j => (hw j).le) hp
    rw [←he,weightedInsert_project] at hm
    exact hm

end Chapter02

#print axioms Chapter02.weightedPositive_nonneg
#print axioms Chapter02.weightedPositive_eq_zero_iff
#print axioms Chapter02.weightedPositive_continuous
#print axioms Chapter02.weightedHardRegion_compact
#print axioms Chapter02.weighted_hard_minimum_exists
#print axioms Chapter02.weighted_hard_value_pos_iff_empty
#print axioms Chapter02.weightedX_insert
#print axioms Chapter02.weightedV_insert
#print axioms Chapter02.weightedInsert_project
#print axioms Chapter02.weightedLiftObjective_apply
#print axioms Chapter02.weighted_lift_rows_iff
#print axioms Chapter02.weighted_lift_minimizer
#print axioms Chapter02.weighted_lift_project_minimizer
#print axioms Chapter02.convex_minimum_derivative_nonneg
#print axioms Chapter02.weighted_lift_derivative
#print axioms Chapter02.weighted_lift_rows_convex
#print axioms Chapter02.weighted_lift_slater
#print axioms Chapter02.weighted_partial_apply
#print axioms Chapter02.weighted_hard_kkt_exists
#print axioms Chapter02.WeightedHardKKT.soft_value
#print axioms Chapter02.weighted_hard_tangent_lower
#print axioms Chapter02.weighted_hard_tangent_exclusion
#print axioms Chapter02.weighted_hard_actual_minimum_excludes
#print axioms Chapter02.weighted_empty_hard_actual_minimum_excludes
#print axioms Chapter02.weighted_lift_slacks_tight
#print axioms Chapter02.weighted_lift_minimizer_iff
