module

public import Chapter02Model
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Chapter8: bounded binary conic hull formulation and exact formula diagnostics.
The binary theorem concerns one finite disjunction with finite real box bounds;
it does not certify a continuous convex-hull theorem or numerical solvers. -/
noncomputable section
open scoped BigOperators
namespace Chapter08

abbrev Vec (n : ℕ) := Fin n → ℝ

def InBox {n : ℕ} (lo hi x : Vec n) : Prop := ∀ j, lo j ≤ x j ∧ x j ≤ hi j

def ConicUnion {n m q : ℕ} (A : Fin q → Vec n →ₗ[ℝ] Vec m)
    (b : Fin q → Vec m) (K : Fin q → Set (Vec m)) (lo hi : Vec n) : Set (Vec n) :=
  {x | InBox lo hi x ∧ ∃ i, A i x - b i ∈ K i}

def BinaryConicHull {n m q : ℕ} (A : Fin q → Vec n →ₗ[ℝ] Vec m)
    (b : Fin q → Vec m) (K : Fin q → Set (Vec m)) (lo hi : Vec n) : Set (Vec n) :=
  {x | ∃ y : Fin q → ℝ, ∃ v : Fin q → Vec n,
    (∀ i, y i = 0 ∨ y i = 1) ∧ (∑ i, y i) = 1 ∧ x = ∑ i, v i ∧
    (∀ i, A i (v i) - y i • b i ∈ K i) ∧
    (∀ i j, lo j * y i ≤ v i j ∧ v i j ≤ hi j * y i)}

theorem binary_partition_one_hot {q : ℕ} (y : Fin q → ℝ)
    (hb : ∀ i, y i = 0 ∨ y i = 1) (hs : (∑ i, y i) = 1) :
    ∃ i, y i = 1 ∧ ∀ j, j ≠ i → y j = 0 := by
  have hn : ∃ i, y i ≠ 0 := by
    by_contra h
    have hz : ∀ i, y i = 0 := by simpa using h
    simp [hz] at hs
  obtain ⟨i, hi⟩ := hn
  have hi1 : y i = 1 := (hb i).resolve_left hi
  refine ⟨i, hi1, ?_⟩
  intro j hji
  rcases hb j with hj | hj
  · exact hj
  · have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin q)), 0 ≤ y k := by
      intro k _; rcases hb k with hk | hk <;> simp [hk]
    have htwo : y i + y j ≤ ∑ k, y k := by
      have hsub : ({i,j} : Finset (Fin q)) ⊆ Finset.univ := Finset.subset_univ _
      have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro k _ _; exact hnonneg k (Finset.mem_univ _))
      simpa [Finset.sum_pair (Ne.symm hji)] using h
    rw [hi1, hj, hs] at htwo
    norm_num at htwo

theorem zero_weight_box_forces_zero {n : ℕ} (lo hi v : Vec n) (y : ℝ)
    (hy : y = 0) (hv : ∀ j, lo j * y ≤ v j ∧ v j ≤ hi j * y) : v = 0 := by
  ext j
  have h := hv j
  simp [hy] at h
  exact le_antisymm h.2 h.1

/-- Exact source HR-Cone projection for one bounded finite disjunction. The
origin condition follows from each source proper cone; it is explicit here.
No nonempty-disjunct assumption or convexity is needed for binary exactness. -/
theorem bounded_binary_conic_hull_exact {n m q : ℕ}
    (A : Fin q → Vec n →ₗ[ℝ] Vec m) (b : Fin q → Vec m)
    (K : Fin q → Set (Vec m)) (lo hi : Vec n) (hK0 : ∀ i, 0 ∈ K i) :
    BinaryConicHull A b K lo hi = ConicUnion A b K lo hi := by
  ext x
  constructor
  · rintro ⟨y, v, hb, hs, hx, hc, hv⟩
    obtain ⟨i, hiy, hz⟩ := binary_partition_one_hot y hb hs
    have hv0 : ∀ j, j ≠ i → v j = 0 := fun j hj =>
      zero_weight_box_forces_zero lo hi (v j) (y j) (hz j hj) (hv j)
    have hsum : (∑ j, v j) = v i := by
      exact Finset.sum_eq_single i (by intro j _ hj; exact hv0 j hj)
        (by intro h; exact False.elim (h (Finset.mem_univ i)))
    have hxi : x = v i := hx.trans hsum
    refine ⟨?_, i, ?_⟩
    · intro j; simpa [hxi, hiy] using hv i j
    · simpa [hxi, hiy] using hc i
  · rintro ⟨hbox, i, hi⟩
    refine ⟨(fun j => if j = i then 1 else 0), (fun j => if j = i then x else 0),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro j; by_cases h : j=i <;> simp [h]
    · simp
    · simp
    · intro j; by_cases h : j=i
      · subst j; simpa using hi
      · simpa [h] using hK0 j
    · intro j t; by_cases h : j=i
      · subst j; simpa using hbox t
      · simp [h]

def Rotated (u v w : ℝ) : Prop := 0 ≤ u ∧ 0 ≤ v ∧ w^2 ≤ 2*u*v

def PrintedRotated (u v w : ℝ) : Prop := 0 ≤ u ∧ 0 ≤ v ∧ |w| ≤ 2*u*v

theorem rotated_square_epigraph (x t : ℝ) : Rotated (1/2) t x ↔ x^2 ≤ t := by
  constructor
  · intro h; dsimp [Rotated] at h; nlinarith
  · intro h; exact ⟨by norm_num, (sq_nonneg x).trans h, by nlinarith⟩

theorem rotated_square_perspective (x t y : ℝ) (hy : 0 ≤ y) (ht : 0 ≤ t) :
    Rotated (y/2) t x ↔ x^2 ≤ t*y := by
  simp only [Rotated]
  constructor
  · intro h; nlinarith
  · intro h; exact ⟨by linarith, ht, by nlinarith⟩

theorem rotated_scaling (u v w a : ℝ) (h : Rotated u v w) (ha : 0 ≤ a) :
    Rotated (a*u) (a*v) (a*w) := by
  refine ⟨mul_nonneg ha h.1, mul_nonneg ha h.2.1, ?_⟩
  have hsq := mul_le_mul_of_nonneg_left h.2.2 (sq_nonneg a)
  nlinarith

theorem printed_rotated_not_cone :
    PrintedRotated (1/2) 1 1 ∧ ¬ PrintedRotated (1/4) (1/2) (1/2) := by
  norm_num [PrintedRotated, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]

theorem printed_rotated_wrong_square_epigraph :
    PrintedRotated (1/2) (1/2) (1/2) ∧
    ((1/2:ℝ)^2 ≤ 1/4) ∧ ¬ PrintedRotated (1/2) (1/4) (1/2) := by
  norm_num [PrintedRotated, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]

/-- Correct closed exponential cone, with its zero-scale branch explicit. -/
def ExpCone (u v w : ℝ) : Prop :=
  (0 < v ∧ v * Real.exp (w/v) ≤ u) ∨ (v = 0 ∧ 0 ≤ u ∧ w ≤ 0)

theorem exp_cone_positive (u v w : ℝ) (hv : 0 < v) :
    ExpCone u v w ↔ v * Real.exp (w/v) ≤ u := by
  simp [ExpCone, hv, ne_of_gt hv]

theorem exp_cone_zero (u w : ℝ) : ExpCone u 0 w ↔ 0 ≤ u ∧ w ≤ 0 := by
  simp [ExpCone]

theorem exp_cone_epigraph (t x : ℝ) : ExpCone t 1 x ↔ Real.exp x ≤ t := by
  simp [ExpCone]

theorem exp_cone_perspective (t x y : ℝ) (hy : 0 < y) :
    ExpCone t y x ↔ y * Real.exp (x/y) ≤ t := exp_cone_positive t y x hy

theorem exp_cone_scaling (u v w a : ℝ) (h : ExpCone u v w) (ha : 0 ≤ a) :
    ExpCone (a*u) (a*v) (a*w) := by
  by_cases hz : a = 0
  · subst a; simp [ExpCone]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    rcases h with ⟨hv, hu⟩ | ⟨hv, hu, hw⟩
    · left
      refine ⟨mul_pos hap hv, ?_⟩
      rw [mul_div_mul_left w v (ne_of_gt hap)]
      have hmul := mul_le_mul_of_nonneg_left hu ha
      simpa [mul_assoc] using hmul
    · right
      exact ⟨by simp [hv], mul_nonneg ha hu, mul_nonpos_of_nonneg_of_nonpos ha hw⟩

theorem exp_cone_negative_scale_empty (u v w : ℝ) (hv : v < 0) : ¬ ExpCone u v w := by
  rintro (⟨h, _⟩ | ⟨h, _, _⟩)
  · linarith
  · linarith

theorem exp_totalized_zero_is_wrong :
    0 * Real.exp ((1:ℝ)/0) ≤ 1 ∧ ¬ ExpCone 1 0 1 := by
  norm_num [ExpCone]

theorem epigraph_nonnegative_slack_is_vacuous (g : ℝ) :
    ∃ s : ℝ, 0 ≤ s ∧ g ≤ s := ⟨max 0 g, le_max_left _ _, le_max_right _ _⟩

theorem epigraph_nonpositive_slack_repair (g : ℝ) :
    (∃ s : ℝ, s ≤ 0 ∧ g ≤ s) ↔ g ≤ 0 := by
  constructor
  · rintro ⟨s, hs, hg⟩; exact hg.trans hs
  · intro hg; exact ⟨0, le_rfl, hg⟩

theorem bigM_wrong_domain_witness :
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → x ≤ 1) ∧
    ¬ ((2:ℝ)-1 ≤ 0*(1-0)) := by norm_num

theorem scalar_bigM_binary_exact (g M y : ℝ) (hM : g ≤ M) (hy : y=0 ∨ y=1) :
    g ≤ M*(1-y) ↔ (y=1 → g ≤ 0) := by
  rcases hy with rfl | rfl <;> simp [hM]

/-- With residual r=Ax-b and >=_K convention, the inactive offset must be a
lower cone-order bound, not an upper bound. Orthant scalar specialization. -/
theorem conic_bigM_lower_offset_exact (r M y : ℝ) (hM : M ≤ r) (hy : y=0 ∨ y=1) :
    M*(1-y) ≤ r ↔ (y=1 → 0 ≤ r) := by
  rcases hy with rfl | rfl <;> simp [hM]

theorem conic_bigM_upper_offset_counterexample :
    (-1:ℝ) ≤ 1 ∧ ¬ (1*(1-0) ≤ (-1:ℝ)) := by norm_num

theorem affine_orthant_sign_counterexample :
    (-1:ℝ) ≤ 0 ∧ ¬ (0 ≤ (-1:ℝ)) := by norm_num

theorem affine_orthant_sign_repair (r : ℝ) : r ≤ 0 ↔ 0 ≤ -r := by
  constructor <;> intro h <;> linarith

theorem duplicated_softplus_variable_counterexample :
    (∃ u v : ℝ, u+v ≤ 1 ∧ ExpCone v 1 0 ∧ ExpCone v 1 0) ∧
      ¬ (Real.log (1 + Real.exp (0:ℝ)) ≤ 0) := by
  constructor
  · exact ⟨0, 1, by norm_num, by simp [ExpCone], by simp [ExpCone]⟩
  · simp only [Real.exp_zero]
    have h : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    norm_num at *
    linarith

theorem quadratic_distance_expansion (x p : ℝ) : (x-p)^2 = x^2 - 2*p*x + p^2 := by ring

theorem printed_clustering_sign_counterexample :
    ((1:ℝ)-1)^2 = 0 ∧ (1:ℝ)^2 + 2*1*1 + 1^2 = 4 := by norm_num

theorem process_missing_time_factor_counterexample :
    Real.exp ((0:ℝ)/2) - 1 ≤ 0 ∧ ¬ ExpCone (2*0+1) 2 0 := by
  norm_num [ExpCone]

theorem process_time_factor_repair (u t x : ℝ) (ht : 0 < t) :
    ExpCone (t*u+t) t x ↔ Real.exp (x/t) - 1 ≤ u := by
  rw [exp_cone_positive _ _ _ ht]
  have heq : t*u+t = t*(u+1) := by ring
  rw [heq, mul_le_mul_iff_right₀ ht]
  constructor <;> intro h <;> linarith

end Chapter08

#print axioms Chapter08.binary_partition_one_hot
#print axioms Chapter08.zero_weight_box_forces_zero
#print axioms Chapter08.bounded_binary_conic_hull_exact
#print axioms Chapter08.rotated_square_epigraph
#print axioms Chapter08.rotated_square_perspective
#print axioms Chapter08.rotated_scaling
#print axioms Chapter08.printed_rotated_not_cone
#print axioms Chapter08.printed_rotated_wrong_square_epigraph
#print axioms Chapter08.exp_cone_positive
#print axioms Chapter08.exp_cone_zero
#print axioms Chapter08.exp_cone_epigraph
#print axioms Chapter08.exp_cone_perspective
#print axioms Chapter08.exp_cone_scaling
#print axioms Chapter08.exp_cone_negative_scale_empty
#print axioms Chapter08.exp_totalized_zero_is_wrong
#print axioms Chapter08.epigraph_nonnegative_slack_is_vacuous
#print axioms Chapter08.epigraph_nonpositive_slack_repair
#print axioms Chapter08.bigM_wrong_domain_witness
#print axioms Chapter08.scalar_bigM_binary_exact
#print axioms Chapter08.conic_bigM_lower_offset_exact
#print axioms Chapter08.conic_bigM_upper_offset_counterexample
#print axioms Chapter08.affine_orthant_sign_counterexample
#print axioms Chapter08.affine_orthant_sign_repair
#print axioms Chapter08.duplicated_softplus_variable_counterexample
#print axioms Chapter08.quadratic_distance_expansion
#print axioms Chapter08.printed_clustering_sign_counterexample
#print axioms Chapter08.process_missing_time_factor_counterexample
#print axioms Chapter08.process_time_factor_repair
