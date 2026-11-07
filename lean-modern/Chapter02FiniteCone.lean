module

public import Chapter02
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

/-! Exact finite conic combinations and the finite-dimensional normal alternative.
No closure membership is substituted for a finite nonnegative coefficient
witness. The finite coefficient family can be empty or linearly dependent. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteCone (a : J → E) : Set E :=
  {z | ∃ w : J → ℝ, (∀ i, 0 ≤ w i) ∧ z = ∑ i, w i • a i}

theorem finiteCone_zero (a : J → E) : (0 : E) ∈ finiteCone a := by
  refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
  simp

theorem finiteCone_generator (a : J → E) (i : J) : a i ∈ finiteCone a := by
  classical
  refine ⟨Pi.single i 1, ?_, ?_⟩
  · intro j; by_cases h : j = i <;> simp [Pi.single_apply, h]
  · simp [Pi.single_apply, ite_smul]

theorem finiteCone_smul {a : J → E} {z : E} {c : ℝ}
    (hc : 0 ≤ c) (hz : z ∈ finiteCone a) : c • z ∈ finiteCone a := by
  obtain ⟨w, hw, rfl⟩ := hz
  refine ⟨fun i => c * w i, fun i => mul_nonneg hc (hw i), ?_⟩
  simp [Finset.smul_sum, mul_smul]

theorem finiteCone_add {a : J → E} {x y : E}
    (hx : x ∈ finiteCone a) (hy : y ∈ finiteCone a) : x + y ∈ finiteCone a := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨fun i => u i + v i, fun i => add_nonneg (hu i) (hv i), ?_⟩
  simp [add_smul, Finset.sum_add_distrib]

theorem finiteCone_convex (a : J → E) : Convex ℝ (finiteCone a) := by
  intro x hx y hy c d hc hd _
  exact finiteCone_add (finiteCone_smul hc hx) (finiteCone_smul hd hy)

def conePositiveSupport (w : J → ℝ) : Finset J :=
  Finset.univ.filter (fun i => 0 < w i)

def coneExtend (s : Finset J) (w : s → ℝ) (i : J) : ℝ := by
  classical
  exact if h : i ∈ s then w ⟨i,h⟩ else 0

theorem coneExtend_sum (s : Finset J) (w : s → ℝ) (a : J → E) :
    (∑ i, coneExtend s w i • a i) = ∑ i : s, w i • a i := by
  classical
  calc
    (∑ i, coneExtend s w i • a i) = ∑ i ∈ s, coneExtend s w i • a i := by
      symm
      exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by simp [coneExtend, hi])
    _ = ∑ i : s, w i • a i := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro i _
      simp [coneExtend, i.property]

/-- A dependent positive support can be reduced without changing the vector or
introducing negative weights. A minimum positive ratio removes a coefficient. -/
theorem finiteCone_reduce_support (a : J → E) (w : J → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hdep : ¬ LinearIndependent ℝ (fun i : conePositiveSupport w => a i)) :
    ∃ v : J → ℝ, (∀ i, 0 ≤ v i) ∧
      (∑ i, v i • a i) = ∑ i, w i • a i ∧
      (conePositiveSupport v).card < (conePositiveSupport w).card := by
  classical
  let s := conePositiveSupport w
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hex : ∃ d : s → ℝ, (∑ i : s, d i • a i) = 0 ∧ ∃ i, 0 < d i := by
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · refine ⟨fun i => -c i, ?_, i, by dsimp only; linarith⟩
      simpa only [neg_smul, Finset.sum_neg_distrib, neg_zero] using congrArg Neg.neg hc
    · exact ⟨c, hc, i, hpos⟩
  obtain ⟨d, hd, k, hk⟩ := hex
  let P : Finset s := Finset.univ.filter (fun i => 0 < d i)
  have hP : P.Nonempty := ⟨k, by simp [P, hk]⟩
  obtain ⟨k, hkP, hmin⟩ := P.exists_min_image (fun i => w i / d i) hP
  have hdk : 0 < d k := (Finset.mem_filter.mp hkP).2
  have hwk : 0 < w k := (Finset.mem_filter.mp k.property).2
  let t := w k / d k
  have ht : 0 < t := div_pos hwk hdk
  let u : s → ℝ := fun i => w i - t * d i
  have hu : ∀ i, 0 ≤ u i := by
    intro i
    dsimp [u]
    by_cases hdi : 0 < d i
    · have hrat : t ≤ w i / d i := hmin i (by simp [P, hdi])
      have := (le_div_iff₀ hdi).mp hrat
      linarith
    · have hprod : t * d i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hdi)
      linarith [hw i]
  have huk : u k = 0 := by
    dsimp [u, t]
    rw [div_mul_cancel₀ _ hdk.ne']
    exact sub_self _
  let v : J → ℝ := coneExtend s u
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    dsimp [v, coneExtend]
    split_ifs with h
    · exact hu ⟨i,h⟩
    · exact le_rfl
  have hsumw : (∑ i : s, w i • a i) = ∑ i, w i • a i := by
    rw [show (∑ i : s, w i • a i) = ∑ i ∈ s, w i • a i from
      Finset.sum_coe_sort s (fun i => w i • a i)]
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _ hi
    have hwi : w i = 0 := le_antisymm (by simpa [s, conePositiveSupport] using hi) (hw i)
    simp [hwi]
  have hsumv : (∑ i, v i • a i) = ∑ i, w i • a i := by
    rw [coneExtend_sum]
    simp only [u, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hd,
      smul_zero, sub_zero, hsumw]
  have hsubset : conePositiveSupport v ⊆ s := by
    intro i hi
    by_cases his : i ∈ s
    · exact his
    · have hvi : v i = 0 := by simp [v, coneExtend, his]
      simp [conePositiveSupport, hvi] at hi
  have hnot : k.val ∉ conePositiveSupport v := by
    have hvk : v k.val = 0 := by simpa [v, coneExtend, k.property] using huk
    simp [conePositiveSupport, hvk]
  refine ⟨v, hv, hsumv, Finset.card_lt_card ?_⟩
  exact ⟨hsubset, fun hrev => hnot (hrev k.property)⟩

theorem finiteCone_independent_representation (a : J → E) {z : E}
    (hz : z ∈ finiteCone a) :
    ∃ w : J → ℝ, (∀ i, 0 ≤ w i) ∧ z = ∑ i, w i • a i ∧
      LinearIndependent ℝ (fun i : conePositiveSupport w => a i) := by
  classical
  let P : ℕ → Prop := fun k => ∃ w : J → ℝ, (∀ i, 0 ≤ w i) ∧
    z = ∑ i, w i • a i ∧ (conePositiveSupport w).card = k
  have hex : ∃ k, P k := by
    obtain ⟨w, hw, hz⟩ := hz
    exact ⟨_, w, hw, hz, rfl⟩
  obtain ⟨w, hw, hzw, hcard⟩ := Nat.find_spec hex
  refine ⟨w, hw, hzw, ?_⟩
  by_contra hdep
  obtain ⟨v, hv, hsum, hlt⟩ := finiteCone_reduce_support a w hw hdep
  have hmin : Nat.find hex ≤ (conePositiveSupport v).card :=
    Nat.find_min' hex ⟨v, hv, hzw.trans hsum.symm, rfl⟩
  rw [← hcard] at hmin
  exact (not_lt_of_ge hmin) hlt

theorem finiteCone_independent_support (a : J → E) {z : E} (hz : z ∈ finiteCone a) :
    ∃ s : Finset J, LinearIndependent ℝ (fun i : s => a i) ∧
      z ∈ finiteCone (fun i : s => a i) := by
  classical
  obtain ⟨w, hw, hzw, hind⟩ := finiteCone_independent_representation a hz
  refine ⟨conePositiveSupport w, hind, fun i => w i, fun i => hw i, ?_⟩
  rw [hzw]
  symm
  calc
    (∑ i : conePositiveSupport w, w i • a i) =
        ∑ i ∈ conePositiveSupport w, w i • a i :=
      Finset.sum_coe_sort _ (fun i => w i • a i)
    _ = ∑ i, w i • a i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hwi : w i = 0 := le_antisymm (by simpa [conePositiveSupport] using hi) (hw i)
      simp [hwi]

theorem finiteCone_isClosed_of_independent (a : J → E) (ha : LinearIndependent ℝ a) :
    IsClosed (finiteCone a) := by
  let L := Fintype.linearCombination ℝ a
  have hL : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr ha.fintypeLinearCombination_injective
  have horth : IsClosed {w : J → ℝ | ∀ i, 0 ≤ w i} := by
    have heq : {w : J → ℝ | ∀ i, 0 ≤ w i} = ⋂ i, {w | 0 ≤ w i} := by ext; simp
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have heq : finiteCone a = L '' {w : J → ℝ | ∀ i, 0 ≤ w i} := by
    ext z
    simp only [finiteCone, Set.mem_setOf_eq, Set.mem_image, L,
      Fintype.linearCombination_apply, eq_comm]
  rw [heq]
  exact (LinearMap.isClosedEmbedding_of_injective hL).isClosedMap _ horth

/-- Finite positive spans are closed, including dependent and empty families.
The proof is a finite union of closed independent orthant images. -/
theorem finiteCone_isClosed (a : J → E) : IsClosed (finiteCone a) := by
  classical
  have heq : finiteCone a = ⋃ s : Finset J,
      ⋃ (_ : LinearIndependent ℝ (fun i : s => a i)), finiteCone (fun i : s => a i) := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · intro hz
      obtain ⟨s, hs, hz⟩ := finiteCone_independent_support a hz
      exact ⟨s, hs, hz⟩
    · rintro ⟨s, _, w, hw, hzw⟩
      refine ⟨coneExtend s w, ?_, ?_⟩
      · intro i
        dsimp [coneExtend]
        split_ifs with hi
        · exact hw ⟨i,hi⟩
        · exact le_rfl
      · rw [coneExtend_sum]
        exact hzw
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro s
  apply isClosed_iUnion_of_finite
  intro hs
  exact finiteCone_isClosed_of_independent _ hs

/-- Strict exact separation from the finite cone, with signs derived using
zero membership and nonnegative scaling. -/
theorem finiteCone_separation (a : J → E) {b : E} (hb : b ∉ finiteCone a) :
    ∃ f : E →L[ℝ] ℝ, (∀ i, 0 ≤ f (a i)) ∧ f b < 0 := by
  obtain ⟨f, u, hbu, hcone⟩ :=
    geometric_hahn_banach_point_closed (finiteCone_convex a) (finiteCone_isClosed a) hb
  have hu : u < 0 := by simpa using hcone 0 (finiteCone_zero a)
  refine ⟨f, ?_, hbu.trans hu⟩
  intro i
  by_contra hneg
  have hi : f (a i) < 0 := lt_of_not_ge hneg
  let c : ℝ := (u - 1) / f (a i)
  have hc : 0 ≤ c := (div_pos_of_neg_of_neg (by linarith : u - 1 < 0) hi).le
  have hh := hcone (c • a i) (finiteCone_smul hc (finiteCone_generator a i))
  rw [map_smul, smul_eq_mul] at hh
  have heq : c * f (a i) = u - 1 := div_mul_cancel₀ _ hi.ne
  rw [heq] at hh
  linarith

/-- Coordinate representation of an actual functional on the existing sup-norm
Pi space. No Euclidean/Riesz identification is used. -/
theorem coneFunctional_coordinates {n : ℕ} (f : RealVector n →L[ℝ] ℝ) (x : RealVector n) :
    f x = ∑ k, f (Pi.single k 1) * x k := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : ℝ) : RealVector n) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  calc
    f x = f (∑ k, x k • (Pi.single k (1 : ℝ) : RealVector n)) := congrArg f hx
    _ = ∑ k, f (Pi.single k 1) * x k := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _

theorem coneFunctional_ext {n : ℕ} {f g : RealVector n →L[ℝ] ℝ}
    (h : ∀ k, f (Pi.single k 1) = g (Pi.single k 1)) : f = g := by
  ext x
  rw [coneFunctional_coordinates f x, coneFunctional_coordinates g x]
  simp only [h]

def conePair {n : ℕ} (b x : RealVector n) : ℝ := ∑ k, b k * x k

/-- Exact finite Farkas implication, with the <= orientation matching active
affine rows. The conclusion contains actual finite nonnegative coefficients. -/
theorem finiteCone_of_dual {n : ℕ} (a : J → RealVector n) (b : RealVector n)
    (hdual : ∀ x, (∀ i, conePair (a i) x ≤ 0) → conePair b x ≤ 0) :
    b ∈ finiteCone a := by
  classical
  by_contra hb
  obtain ⟨f, hfa, hfb⟩ := finiteCone_separation a hb
  let x : RealVector n := fun k => -f (Pi.single k 1)
  have hp (v : RealVector n) : conePair v x = -f v := by
    rw [coneFunctional_coordinates f v]
    simp only [conePair, x, mul_neg, ← Finset.sum_neg_distrib, mul_comm]
  have hx : ∀ i, conePair (a i) x ≤ 0 := by
    intro i
    rw [hp]
    exact neg_nonpos.mpr (hfa i)
  have h := hdual x hx
  rw [hp] at h
  linarith

/-- The exact continuous-linear-map normal alternative on RealVector.
Empty, zero, opposite and dependent row families are allowed. -/
theorem finite_normal_representation {n : ℕ}
    (a : J → RealVector n →L[ℝ] ℝ) (D : RealVector n →L[ℝ] ℝ)
    (hdual : ∀ v, (∀ i, a i v ≤ 0) → 0 ≤ D v) :
    ∃ mu : J → ℝ, (∀ i, 0 ≤ mu i) ∧ D + ∑ i, mu i • a i = 0 := by
  let ac : J → RealVector n := fun i k => a i (Pi.single k 1)
  let bc : RealVector n := fun k => (-D) (Pi.single k 1)
  have hb : bc ∈ finiteCone ac := by
    apply finiteCone_of_dual
    intro v hv
    have hrows : ∀ i, a i v ≤ 0 := by
      intro i
      rw [coneFunctional_coordinates (a i) v]
      exact hv i
    have hD := hdual v hrows
    change (∑ k, (-D) (Pi.single k 1) * v k) ≤ 0
    rw [← coneFunctional_coordinates (-D) v]
    exact neg_nonpos.mpr hD
  obtain ⟨mu, hmu, hrep⟩ := hb
  refine ⟨mu, hmu, ?_⟩
  apply coneFunctional_ext
  intro k
  have hk := congrFun hrep k
  simp only [bc, ac, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.neg_apply] at hk
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
  linarith

namespace FiniteConeControls

/-- With no generators the exact cone consists of its empty sum, zero. -/
theorem empty_generators [IsEmpty J] (a : J → E) :
    finiteCone a = {0} := by
  ext z
  constructor
  · rintro ⟨w, _, h⟩
    simpa using h
  · intro h
    have hz : z = 0 := h
    rw [hz]
    exact finiteCone_zero a

/-- Zero rows remain admissible; they do not create additional cone points. -/
theorem zero_generators : finiteCone (fun _ : J => (0 : E)) = {0} := by
  ext z
  constructor
  · rintro ⟨w, _, h⟩
    simpa using h
  · intro h
    have hz : z = 0 := h
    rw [hz]
    exact finiteCone_zero _

/-- Duplicate generators retain the same exact ray, without independence. -/
theorem duplicate_generators (u : E) :
    finiteCone (fun _ : Fin 2 => u) = {z | ∃ t : ℝ, 0 ≤ t ∧ z = t • u} := by
  ext z
  constructor
  · rintro ⟨w, hw, hz⟩
    refine ⟨w 0 + w 1, add_nonneg (hw 0) (hw 1), ?_⟩
    simpa [Fin.sum_univ_two, add_smul] using hz
  · rintro ⟨t, ht, rfl⟩
    exact finiteCone_smul ht (finiteCone_generator (fun _ : Fin 2 => u) 0)

/-- Opposite generators produce the complete line, including negative rays. -/
theorem opposite_generators (u : E) :
    finiteCone (fun i : Fin 2 => if i = 0 then u else -u) =
      Set.range (fun t : ℝ => t • u) := by
  ext z
  constructor
  · rintro ⟨w, _, hz⟩
    refine ⟨w 0 - w 1, ?_⟩
    simpa [Fin.sum_univ_two, sub_eq_add_neg, add_smul] using hz.symm
  · rintro ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · have hg := finiteCone_generator (fun i : Fin 2 => if i = 0 then u else -u) 0
      simpa using finiteCone_smul ht hg
    · have hg := finiteCone_generator (fun i : Fin 2 => if i = 0 then u else -u) 1
      have hn : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
      simpa using finiteCone_smul hn hg

def coord (k : Fin 2) : RealVector 2 →L[ℝ] ℝ := ContinuousLinearMap.proj k

def dependentRows (i : Fin 3) : RealVector 2 →L[ℝ] ℝ :=
  if i = 0 then coord 0 else if i = 1 then coord 1 else coord 0 + coord 1

/-- An explicitly dependent family exercises exact normal representation.
The third row is the sum of the first two, and the coordinate equations fix
the exact represented normal rather than merely its closure membership. -/
theorem dependent_normal_coefficients :
    ∃ mu : Fin 3 → ℝ, (∀ i, 0 ≤ mu i) ∧
      mu 0 + mu 2 = 1 ∧ mu 1 + mu 2 = 1 := by
  obtain ⟨mu, hmu, hrep⟩ := finite_normal_representation dependentRows
    (-(coord 0 + coord 1)) (by
      intro v hv
      have h0 := hv 0
      have h1 := hv 1
      simp [dependentRows, coord] at h0 h1 ⊢
      linarith)
  have h0 := congrArg (fun f : RealVector 2 →L[ℝ] ℝ => f (Pi.single 0 1)) hrep
  have h1 := congrArg (fun f : RealVector 2 →L[ℝ] ℝ => f (Pi.single 1 1)) hrep
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [Fin.sum_univ_three, dependentRows, coord, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.zero_apply, Pi.single_apply, h20, h21] at h0 h1
  exact ⟨mu, hmu, by linarith, by linarith⟩

end FiniteConeControls

end Chapter02

#print axioms Chapter02.finiteCone_zero
#print axioms Chapter02.finiteCone_generator
#print axioms Chapter02.finiteCone_smul
#print axioms Chapter02.finiteCone_add
#print axioms Chapter02.finiteCone_convex
#print axioms Chapter02.coneExtend_sum
#print axioms Chapter02.finiteCone_reduce_support
#print axioms Chapter02.finiteCone_independent_representation
#print axioms Chapter02.finiteCone_independent_support
#print axioms Chapter02.finiteCone_isClosed_of_independent
#print axioms Chapter02.finiteCone_isClosed
#print axioms Chapter02.finiteCone_separation
#print axioms Chapter02.coneFunctional_coordinates
#print axioms Chapter02.coneFunctional_ext
#print axioms Chapter02.finiteCone_of_dual
#print axioms Chapter02.finite_normal_representation
#print axioms Chapter02.FiniteConeControls.empty_generators
#print axioms Chapter02.FiniteConeControls.zero_generators
#print axioms Chapter02.FiniteConeControls.duplicate_generators
#print axioms Chapter02.FiniteConeControls.opposite_generators
#print axioms Chapter02.FiniteConeControls.dependent_normal_coefficients
