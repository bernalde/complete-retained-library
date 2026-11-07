module

public import Chapter02Model
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! Candidate labelled repair of Hijazi Example1/Lemma2.1/Theorem2.2.
The smaller squared radius is (n-1)/4. We count actual valid scalar cuts,
not iterations, nodes or an algorithm's selection of complementary anchors. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

abbrev BinaryBallVertex (n : ℕ) := Fin n → Bool

def binaryBallPoint {n : ℕ} (v : BinaryBallVertex n) : RealVector n :=
  fun i => if v i then 1 else 0

def binaryBallEnergy {n : ℕ} (x : RealVector n) : ℝ := ∑ i, (x i-1/2)^2

def binaryBallRegion (n : ℕ) : Set (RealVector n) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ binaryBallEnergy x ≤ ((n : ℝ)-1)/4}

def binaryBallMidpoint {n : ℕ} (v w : BinaryBallVertex n) : RealVector n :=
  fun i => (binaryBallPoint v i+binaryBallPoint w i)/2

def binaryBallHamming {n : ℕ} (v w : BinaryBallVertex n) : ℝ :=
  ∑ i, if v i ≠ w i then 1 else 0

theorem binary_hamming_count {n : ℕ} (v w : BinaryBallVertex n) :
    binaryBallHamming v w = ((Finset.univ.filter fun i => v i ≠ w i).card : ℝ) := by
  rw [binaryBallHamming, ← Finset.sum_filter]
  simp

theorem binary_hamming_positive {n : ℕ} {v w : BinaryBallVertex n} (h : v ≠ w) :
    1 ≤ binaryBallHamming v w := by
  have hex : ∃ i, v i ≠ w i := by
    by_contra hn
    push_neg at hn
    exact h (funext hn)
  obtain ⟨j,hj⟩ := hex
  have hsum := Finset.single_le_sum
    (f := fun i => if v i ≠ w i then (1 : ℝ) else 0)
    (fun i (_ : i ∈ Finset.univ) => by split_ifs <;> norm_num)
    (Finset.mem_univ j)
  simpa [binaryBallHamming,hj] using hsum

theorem binary_midpoint_energy {n : ℕ} (v w : BinaryBallVertex n) :
    binaryBallEnergy (binaryBallMidpoint v w) =
      ((n : ℝ)-binaryBallHamming v w)/4 := by
  have h (i : Fin n) : (binaryBallMidpoint v w i-1/2)^2 =
      (1-(if v i ≠ w i then (1 : ℝ) else 0))/4 := by
    cases hv : v i <;> cases hw : w i <;>
      norm_num [binaryBallMidpoint,binaryBallPoint,hv,hw]
  simp only [binaryBallEnergy,h]
  simp only [div_eq_mul_inv,← Finset.sum_mul,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    binaryBallHamming]

theorem binary_ball_midpoint_mem {n : ℕ} (_hn : 1 ≤ n)
    {v w : BinaryBallVertex n} (hvw : v ≠ w) :
    binaryBallMidpoint v w ∈ binaryBallRegion n := by
  constructor
  · intro i
    cases hv : v i <;> cases hw : w i <;>
      norm_num [binaryBallMidpoint,binaryBallPoint,hv,hw]
  · rw [binary_midpoint_energy]
    have := binary_hamming_positive hvw
    linarith

theorem binary_ball_nonvacuity {n : ℕ} (hn : 1 ≤ n) :
    (fun _ : Fin n => (1/2 : ℝ)) ∈ binaryBallRegion n ∧
    ∀ v : BinaryBallVertex n, binaryBallPoint v ∉ binaryBallRegion n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · constructor
    · intro i; norm_num
    · simp [binaryBallEnergy]
      linarith
  · intro v hv
    have he : binaryBallEnergy (binaryBallPoint v) = (n : ℝ)/4 := by
      have hi (i : Fin n) : (binaryBallPoint v i-1/2)^2 = (1 : ℝ)/4 := by
        cases h : v i <;> norm_num [binaryBallPoint,h]
      simp only [binaryBallEnergy,hi]
      simp [div_eq_mul_inv]
    have hv2 := hv.2
    rw [he] at hv2
    linarith

structure BinaryBallCut (n : ℕ) where
  coefficient : RealVector n
  offset : ℝ
  rhs : ℝ

def BinaryBallCut.value {n : ℕ} (c : BinaryBallCut n) (x : RealVector n) : ℝ :=
  c.offset+∑ i, c.coefficient i*x i

def BinaryBallCut.Valid {n : ℕ} (c : BinaryBallCut n) : Prop :=
  ∀ x ∈ binaryBallRegion n, c.value x ≤ c.rhs

theorem binary_cut_midpoint_identity {n : ℕ} (c : BinaryBallCut n)
    (v w : BinaryBallVertex n) :
    c.value (binaryBallMidpoint v w) =
      (c.value (binaryBallPoint v)+c.value (binaryBallPoint w))/2 := by
  have hs : (∑ i, c.coefficient i*((binaryBallPoint v i+binaryBallPoint w i)/2)) =
      ((∑ i, c.coefficient i*binaryBallPoint v i)+
        (∑ i, c.coefficient i*binaryBallPoint w i))/2 := by
    calc
      _ = ∑ i, (c.coefficient i*binaryBallPoint v i+
          c.coefficient i*binaryBallPoint w i)*(1/2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← Finset.sum_mul,Finset.sum_add_distrib]; ring
  simp only [BinaryBallCut.value,binaryBallMidpoint,hs]
  ring

theorem binary_valid_cut_excludes_at_most_one {n : ℕ} (hn : 1 ≤ n)
    (c : BinaryBallCut n) (hc : c.Valid) (v w : BinaryBallVertex n)
    (hv : c.rhs < c.value (binaryBallPoint v))
    (hw : c.rhs < c.value (binaryBallPoint w)) : v = w := by
  by_contra hne
  have hm := hc _ (binary_ball_midpoint_mem hn hne)
  rw [binary_cut_midpoint_identity] at hm
  linarith

/-- Each index is one scalar inequality; duplicate cuts still consume indices.
Validity is on the actual continuous ball intersected with the unit cube. -/
theorem binary_scalar_cut_lower_bound {n k : ℕ} (hn : 1 ≤ n)
    (cuts : Fin k → BinaryBallCut n) (hc : ∀ i, (cuts i).Valid)
    (hk : k < 2^n) :
    ∃ v : BinaryBallVertex n, ∀ i, (cuts i).value (binaryBallPoint v) ≤ (cuts i).rhs := by
  by_contra h
  push_neg at h
  choose pick hpick using h
  have hinj : Function.Injective pick := by
    intro v w heq
    apply binary_valid_cut_excludes_at_most_one hn (cuts (pick v)) (hc _) v w (hpick v)
    simpa only [heq] using hpick w
  have hcard := Fintype.card_le_of_injective pick hinj
  have hbad : 2^n ≤ k := by simpa using hcard
  omega

def binaryComponentTangent (a x : ℝ) : ℝ :=
  (a-1/2)^2+2*(a-1/2)*(x-a)

theorem binary_component_derivative (a : ℝ) :
    HasDerivAt (fun x : ℝ => (x-1/2)^2) (2*(a-1/2)) a := by
  convert ((hasDerivAt_id a).sub_const (1/2 : ℝ)).pow 2 using 1 <;>
    (try ext x) <;> norm_num [id_eq] <;> ring

def binaryBallGradient {n : ℕ} (a : RealVector n) : RealVector n →L[ℝ] ℝ :=
  ∑ i, (2*(a i-1/2)) • (ContinuousLinearMap.proj i : RealVector n →L[ℝ] ℝ)

theorem binary_ball_derivative {n : ℕ} (a : RealVector n) :
    HasFDerivAt binaryBallEnergy (binaryBallGradient a) a := by
  unfold binaryBallEnergy binaryBallGradient
  apply HasFDerivAt.fun_sum
  intro i _
  exact (binary_component_derivative (a i)).comp_hasFDerivAt a
    (hasFDerivAt_apply (𝕜 := ℝ) i a)

theorem binary_component_support (a x : ℝ) :
    binaryComponentTangent a x ≤ (x-1/2)^2 := by
  unfold binaryComponentTangent
  nlinarith [sq_nonneg (x-a)]

def binaryTangentCut {n : ℕ} (v : BinaryBallVertex n) : BinaryBallCut n where
  coefficient := fun i => 2*(binaryBallPoint v i-1/2)
  offset := ∑ i, ((binaryBallPoint v i-1/2)^2-
    2*(binaryBallPoint v i-1/2)*binaryBallPoint v i)
  rhs := ((n : ℝ)-1)/4

theorem binary_tangent_row_identity {n : ℕ} (v : BinaryBallVertex n)
    (x : RealVector n) :
    (binaryTangentCut v).value x = ∑ i, binaryComponentTangent (binaryBallPoint v i) (x i) := by
  simp only [BinaryBallCut.value,binaryTangentCut,binaryComponentTangent,
    mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

theorem binary_tangent_actual_linearization {n : ℕ} (v : BinaryBallVertex n)
    (x : RealVector n) :
    (binaryTangentCut v).value x = binaryBallEnergy (binaryBallPoint v)+
      binaryBallGradient (binaryBallPoint v) (x-binaryBallPoint v) := by
  rw [binary_tangent_row_identity]
  simp [binaryComponentTangent,binaryBallEnergy,binaryBallGradient,
    Finset.sum_add_distrib,smul_eq_mul]

theorem binary_tangent_cut_valid {n : ℕ} (v : BinaryBallVertex n) :
    (binaryTangentCut v).Valid := by
  intro x hx
  rw [binary_tangent_row_identity]
  exact (Finset.sum_le_sum fun i _ => binary_component_support _ _).trans hx.2

theorem binary_tangent_hamming_value {n : ℕ} (v w : BinaryBallVertex n) :
    (binaryTangentCut v).value (binaryBallPoint w) = (n : ℝ)/4-binaryBallHamming v w := by
  rw [binary_tangent_row_identity]
  have hi (i : Fin n) :
      binaryComponentTangent (binaryBallPoint v i) (binaryBallPoint w i) =
        (1 : ℝ)/4-(if v i ≠ w i then 1 else 0) := by
    cases hv : v i <;> cases hw : w i <;>
      norm_num [binaryComponentTangent,binaryBallPoint,hv,hw]
  simp [hi,Finset.sum_sub_distrib,binaryBallHamming,div_eq_mul_inv]

theorem binary_tangent_excludes_exactly_anchor {n : ℕ} (_hn : 1 ≤ n)
    (v w : BinaryBallVertex n) :
    (binaryTangentCut v).rhs < (binaryTangentCut v).value (binaryBallPoint w) ↔ v = w := by
  rw [binary_tangent_hamming_value]
  change ((n : ℝ)-1)/4 < (n : ℝ)/4-binaryBallHamming v w ↔ v = w
  constructor
  · intro h
    by_contra hn
    have := binary_hamming_positive hn
    linarith
  · rintro rfl
    simp [binaryBallHamming]
    linarith

/-- The lower count is achieved by this actual family of valid tangent rows.
This asserts feasibility/infeasibility of static masters, not an algorithm run. -/
theorem binary_tangent_full_family {n : ℕ} (hn : 1 ≤ n) :
    Fintype.card (BinaryBallVertex n) = 2^n ∧
    (∀ v : BinaryBallVertex n, (binaryTangentCut v).Valid) ∧
    ¬ ∃ w : BinaryBallVertex n, ∀ v : BinaryBallVertex n,
      (binaryTangentCut v).value (binaryBallPoint w) ≤ (binaryTangentCut v).rhs := by
  refine ⟨by simp [BinaryBallVertex],binary_tangent_cut_valid,?_⟩
  rintro ⟨w,hw⟩
  exact (not_le_of_gt ((binary_tangent_excludes_exactly_anchor hn w w).2 rfl)) (hw w)

def binaryBallComplement {n : ℕ} (v : BinaryBallVertex n) : BinaryBallVertex n :=
  fun i => !(v i)

/-- One shared continuous height vector; the two anchor families provide
2*n component rows, followed by one separately counted budget row. -/
def binaryLiftedPairHolds {n : ℕ} (anchor vertex : BinaryBallVertex n)
    (z : RealVector n) : Prop :=
  (∀ i, binaryComponentTangent (binaryBallPoint anchor i) (binaryBallPoint vertex i) ≤ z i) ∧
  (∀ i, binaryComponentTangent (binaryBallPoint (binaryBallComplement anchor) i)
      (binaryBallPoint vertex i) ≤ z i) ∧
  ∑ i, z i ≤ ((n : ℝ)-1)/4

theorem binary_complementary_lifted_empty {n : ℕ} (_hn : 1 ≤ n)
    (anchor vertex : BinaryBallVertex n) (z : RealVector n) :
    ¬ binaryLiftedPairHolds anchor vertex z := by
  rintro ⟨ha,hb,hbudget⟩
  have hi (i : Fin n) : (1 : ℝ)/4 ≤ z i := by
    have h1 := ha i
    have h2 := hb i
    cases hv : anchor i <;> cases hw : vertex i <;>
      norm_num [binaryComponentTangent,binaryBallPoint,binaryBallComplement,hv,hw] at h1 h2 <;>
      linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hi i
  have hlow : (n : ℝ)/4 ≤ ∑ i, z i := by simpa [div_eq_mul_inv] using hsum
  linarith

abbrev BinaryLiftedRowIndex (n : ℕ) := (Bool × Fin n) ⊕ Unit

def binaryLiftedRowHolds {n : ℕ} (anchor vertex : BinaryBallVertex n)
    (z : RealVector n) : BinaryLiftedRowIndex n → Prop
  | .inl (false,i) =>
      binaryComponentTangent (binaryBallPoint anchor i) (binaryBallPoint vertex i) ≤ z i
  | .inl (true,i) =>
      binaryComponentTangent (binaryBallPoint (binaryBallComplement anchor) i)
        (binaryBallPoint vertex i) ≤ z i
  | .inr _ => ∑ i, z i ≤ ((n : ℝ)-1)/4

/-- The row indices are the actual two families of component cuts and one
budget row. The complementary pair works for every initial binary anchor. -/
theorem binary_complementary_scalar_row_control {n : ℕ} (hn : 1 ≤ n)
    (anchor : BinaryBallVertex n) :
    Fintype.card (Bool × Fin n) = 2*n ∧
    Fintype.card (BinaryLiftedRowIndex n) = 2*n+1 ∧
    ¬ ∃ (vertex : BinaryBallVertex n) (z : RealVector n),
      ∀ row, binaryLiftedRowHolds anchor vertex z row := by
  refine ⟨by simp,by simp [BinaryLiftedRowIndex],?_⟩
  rintro ⟨vertex,z,h⟩
  exact binary_complementary_lifted_empty hn anchor vertex z
    ⟨fun i => h (.inl (false,i)),fun i => h (.inl (true,i)),h (.inr ())⟩

/-- Concrete n=1 singleton and n=2 finite-model controls. The latter has four
actual valid direct tangents, or four component rows plus one budget row. -/
theorem binary_small_dimension_control :
    binaryBallRegion 1 = {(fun _ : Fin 1 => (1/2 : ℝ))} ∧
    binaryBallMidpoint (fun _ : Fin 2 => false) (fun _ => true) ∈ binaryBallRegion 2 ∧
    Fintype.card (BinaryBallVertex 2) = 4 ∧
    (∀ v : BinaryBallVertex 2, (binaryTangentCut v).Valid) ∧
    (¬ ∃ w : BinaryBallVertex 2, ∀ v : BinaryBallVertex 2,
      (binaryTangentCut v).value (binaryBallPoint w) ≤ (binaryTangentCut v).rhs) ∧
    Fintype.card (BinaryLiftedRowIndex 2) = 5 ∧
    ¬ ∃ (vertex : BinaryBallVertex 2) (z : RealVector 2),
      ∀ row, binaryLiftedRowHolds (fun _ => false) vertex z row := by
  have h1 : binaryBallRegion 1 = {(fun _ : Fin 1 => (1/2 : ℝ))} := by
    ext x
    constructor
    · intro hx
      have he := hx.2
      norm_num [binaryBallEnergy,Fin.sum_univ_one] at he
      have heq : x 0 = (1/2 : ℝ) := by nlinarith [sq_nonneg (x 0-1/2)]
      apply Set.mem_singleton_iff.mpr
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      simpa [hi] using heq
    · intro hx
      have heq := Set.mem_singleton_iff.mp hx
      rw [heq]
      exact (binary_ball_nonvacuity (n := 1) (by decide)).1
  have h2 := binary_tangent_full_family (n := 2) (by decide)
  have hl := binary_complementary_scalar_row_control (n := 2) (by decide) (fun _ => false)
  refine ⟨h1,?_,by norm_num [BinaryBallVertex],h2.2.1,h2.2.2,
    by norm_num [BinaryLiftedRowIndex],hl.2.2⟩
  apply binary_ball_midpoint_mem (by decide)
  intro heq
  have hbad := congrFun heq (0 : Fin 2)
  cases hbad

#print axioms binary_hamming_count
#print axioms binary_hamming_positive
#print axioms binary_midpoint_energy
#print axioms binary_ball_midpoint_mem
#print axioms binary_ball_nonvacuity
#print axioms binary_cut_midpoint_identity
#print axioms binary_valid_cut_excludes_at_most_one
#print axioms binary_scalar_cut_lower_bound
#print axioms binary_component_derivative
#print axioms binary_ball_derivative
#print axioms binary_component_support
#print axioms binary_tangent_row_identity
#print axioms binary_tangent_actual_linearization
#print axioms binary_tangent_cut_valid
#print axioms binary_tangent_hamming_value
#print axioms binary_tangent_excludes_exactly_anchor
#print axioms binary_tangent_full_family
#print axioms binary_complementary_lifted_empty
#print axioms binary_complementary_scalar_row_control
#print axioms binary_small_dimension_control

end Chapter02
