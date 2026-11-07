module

public import Chapter08ExponentialGeometry

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter08.Exponential

/-- Literal distinct-auxiliary softplus system; defined even at zero scale. -/
def softplusSystem (x t y : ℝ) : Prop :=
  ∃ u v : ℝ, u+v ≤ y ∧ ExpCone u y (x-t) ∧ ExpCone v y (-t)

theorem softplus_sum_iff (x t : ℝ) :
    Real.exp (x-t) + Real.exp (-t) ≤ 1 ↔ Real.log (1+Real.exp x) ≤ t := by
  have ht := Real.exp_pos t
  have hi : (Real.exp (x-t)+Real.exp (-t))*Real.exp t = 1+Real.exp x := by
    rw [Real.exp_sub, Real.exp_neg]
    field_simp
    ring
  rw [Real.log_le_iff_le_exp (by positivity : 0 < 1+Real.exp x)]
  constructor
  · intro h
    have hh := mul_le_mul_of_nonneg_right h ht.le
    rwa [hi, one_mul] at hh
  · intro h
    apply (mul_le_mul_iff_left₀ ht).mp
    rwa [hi, one_mul]

/-- Thesis duplicated-v row is repaired by distinct u and v, as in held v3/VOR. -/
theorem softplus_iff (x t : ℝ) :
    Real.log (1+Real.exp x) ≤ t ↔ softplusSystem x t 1 := by
  rw [← softplus_sum_iff]
  constructor
  · intro h
    exact ⟨Real.exp (x-t), Real.exp (-t), h,
      (exp_cone_epigraph _ _).mpr le_rfl, (exp_cone_epigraph _ _).mpr le_rfl⟩
  · rintro ⟨u,v,hs,hu,hv⟩
    exact le_trans (add_le_add ((exp_cone_epigraph _ _).mp hu)
      ((exp_cone_epigraph _ _).mp hv)) hs

/-- The positive-scale perspective, with no quotient interpretation at y=0. -/
theorem softplus_perspective_iff (x t y : ℝ) (hy : 0 < y) :
    y*Real.log (1+Real.exp (x/y)) ≤ t ↔ softplusSystem x t y := by
  have hsub : (x-t)/y = x/y-t/y := sub_div x t y
  have hneg : -t/y = -(t/y) := neg_div y t
  have hc : softplusSystem x t y ↔ Real.exp (x/y-t/y)+Real.exp (-(t/y)) ≤ 1 := by
    constructor
    · rintro ⟨u,v,hs,hu,hv⟩
      have hu' := (exp_cone_positive _ _ _ hy).mp hu
      have hv' := (exp_cone_positive _ _ _ hy).mp hv
      rw [hsub] at hu'
      rw [hneg] at hv'
      apply (mul_le_mul_iff_right₀ hy).mp
      calc
        y*(Real.exp (x/y-t/y)+Real.exp (-(t/y))) =
          y*Real.exp (x/y-t/y)+y*Real.exp (-(t/y)) := by ring
        _ ≤ u+v := add_le_add hu' hv'
        _ ≤ y*1 := by simpa using hs
    · intro h
      refine ⟨y*Real.exp (x/y-t/y), y*Real.exp (-(t/y)), ?_, ?_, ?_⟩
      · have hh := mul_le_mul_of_nonneg_left h hy.le
        simpa [mul_add] using hh
      · apply (exp_cone_positive _ _ _ hy).mpr
        rw [hsub]
      · apply (exp_cone_positive _ _ _ hy).mpr
        rw [hneg]
  rw [hc, softplus_sum_iff, le_div_iff₀ hy]
  rw [mul_comm]

/-- The closed zero-scale softplus face is t >= max(0,x). -/
theorem softplus_zero_iff (x t : ℝ) :
    softplusSystem x t 0 ↔ 0 ≤ t ∧ x ≤ t := by
  constructor
  · rintro ⟨u,v,hs,hu,hv⟩
    obtain ⟨hu0,hx⟩ := (exp_cone_zero _ _).mp hu
    obtain ⟨hv0,ht⟩ := (exp_cone_zero _ _).mp hv
    constructor <;> linarith
  · rintro ⟨ht,hx⟩
    refine ⟨0,0,by norm_num, ?_, ?_⟩
    · exact (exp_cone_zero _ _).mpr ⟨le_rfl, by linarith⟩
    · exact (exp_cone_zero _ _).mpr ⟨le_rfl, by linarith⟩

/-- Affine score substitution does not assert any statistical-model equivalence. -/
theorem affine_softplus_iff {n : ℕ} (a x : Fin n → ℝ) (b t : ℝ) :
    Real.log (1+Real.exp ((∑ j, a j*x j)+b)) ≤ t ↔
      softplusSystem ((∑ j, a j*x j)+b) t 1 :=
  softplus_iff _ _

/-- Strict positivity of the logarithm argument is a visible domain premise. -/
theorem logarithm_cone_iff (x t : ℝ) (hx : 0 < x) :
    t ≤ Real.log x ↔ ExpCone x 1 t := by
  rw [exp_cone_epigraph, Real.le_log_iff_exp_le hx]

/-- Literal nonnegative-weight exponential aggregation, including zero weights and no rows. -/
theorem weighted_exponential_iff {n : ℕ} (d s : Fin n → ℝ) (L : ℝ)
    (hd : ∀ j, 0 ≤ d j) :
    (∑ j, d j*Real.exp (s j)) ≤ L ↔
      ∃ u : Fin n → ℝ, (∑ j, d j*u j) ≤ L ∧ ∀ j, ExpCone (u j) 1 (s j) := by
  constructor
  · intro h
    exact ⟨fun j => Real.exp (s j), h, fun j => (exp_cone_epigraph _ _).mpr le_rfl⟩
  · rintro ⟨u,hu,hc⟩
    apply le_trans _ hu
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      ((exp_cone_epigraph _ _).mp (hc j)) (hd j)

/-- Exact process row: time multiplies both u and the constant one; u stays free. -/
theorem process_cone_iff (u t x : ℝ) (ht : 0 < t) :
    ExpCone (t*(u+1)) t x ↔ Real.exp (x/t)-1 ≤ u := by
  simpa only [mul_add, mul_one] using process_time_factor_repair u t x ht

theorem weighted_process_iff {n : ℕ} (d t x : Fin n → ℝ) (L : ℝ)
    (hd : ∀ j, 0 ≤ d j) (ht : ∀ j, 0 < t j) :
    (∑ j, d j*(Real.exp (x j/t j)-1)) ≤ L ↔
      ∃ u : Fin n → ℝ, (∑ j, d j*u j) ≤ L ∧
        ∀ j, ExpCone (t j*(u j+1)) (t j) (x j) := by
  constructor
  · intro h
    exact ⟨fun j => Real.exp (x j/t j)-1, h,
      fun j => (process_cone_iff _ _ _ (ht j)).mpr le_rfl⟩
  · rintro ⟨u,hu,hc⟩
    apply le_trans _ hu
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      ((process_cone_iff _ _ _ (ht j)).mp (hc j)) (hd j)

theorem random_exponential_cone_iff (a s R : ℝ) (ha : 0 < a) :
    a*Real.exp s ≤ R ↔ ∃ v : ℝ, a*v ≤ R ∧ ExpCone v 1 s := by
  constructor
  · intro h
    exact ⟨Real.exp s,h,(exp_cone_epigraph _ _).mpr le_rfl⟩
  · rintro ⟨v,hv,hc⟩
    exact le_trans (mul_le_mul_of_nonneg_left ((exp_cone_epigraph _ _).mp hc) ha.le) hv

/-- The original row forces R>0; no sign on parameters defining R or valid cap is inferred. -/
theorem random_exponential_log_iff (a s R : ℝ) (ha : 0 < a) :
    a*Real.exp s ≤ R ↔ 0 < R ∧ Real.log a+s ≤ Real.log R := by
  have he : Real.exp (Real.log a+s) = a*Real.exp s := by
    rw [Real.exp_add, Real.exp_log ha]
  constructor
  · intro h
    have hR : 0 < R := lt_of_lt_of_le (mul_pos ha (Real.exp_pos s)) h
    refine ⟨hR, (Real.le_log_iff_exp_le hR).mpr ?_⟩
    rwa [he]
  · rintro ⟨hR,h⟩
    have hh := (Real.le_log_iff_exp_le hR).mp h
    rwa [he] at hh

/-- Literal source process affine right side; the local time-factor repair is explicit. -/
theorem source_process_iff {n : ℕ} (d t s x : Fin n → ℝ)
    (hd : ∀ j, 0 ≤ d j) (ht : ∀ j, 0 < t j) :
    (∑ j, d j*(Real.exp (x j/t j)-1)) - (∑ j, s j*x j) ≤ 0 ↔
      ∃ u : Fin n → ℝ, (∑ j, d j*u j) - (∑ j, s j*x j) ≤ 0 ∧
        ∀ j, ExpCone (t j*(u j+1)) (t j) (x j) := by
  simpa only [sub_nonpos] using weighted_process_iff d t x (∑ j, s j*x j) hd ht

/-- Exact random-row affine substitutions; the source z cap is not a premise or conclusion. -/
theorem source_random_cone_iff {n : ℕ} (a b c z : ℝ) (q x : Fin n → ℝ)
    (ha : 0 < a) :
    a*Real.exp (∑ j, q j*x j) ≤ b*z+c ↔
      ∃ v : ℝ, a*v ≤ b*z+c ∧ ExpCone v 1 (∑ j, q j*x j) :=
  random_exponential_cone_iff _ _ _ ha

theorem source_random_log_iff {n : ℕ} (a b c z : ℝ) (q x : Fin n → ℝ)
    (ha : 0 < a) :
    a*Real.exp (∑ j, q j*x j) ≤ b*z+c ↔
      0 < b*z+c ∧ Real.log a+(∑ j, q j*x j) ≤ Real.log (b*z+c) :=
  random_exponential_log_iff _ _ _ ha

/-- The negative-log logistic table expression is the softplus of the negative score. -/
theorem logistic_cost_iff (score t : ℝ) :
    -Real.log (1/(1+Real.exp (-score))) ≤ t ↔ softplusSystem (-score) t 1 := by
  simpa only [one_div, Real.log_inv, neg_neg] using softplus_iff (-score) t

theorem logistic_cost_perspective_iff (score t y : ℝ) (hy : 0 < y) :
    -y*Real.log (1/(1+Real.exp (-score/y))) ≤ t ↔ softplusSystem (-score) t y := by
  simpa only [one_div, Real.log_inv, neg_mul_neg] using
    softplus_perspective_iff (-score) t y hy

/-- Positive-scale logarithm row with both source-domain restrictions visible. -/
theorem logarithm_perspective_iff (x t y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    t ≤ y*Real.log (x/y) ↔ ExpCone x y t := by
  rw [exp_cone_positive _ _ _ hy, mul_comm y (Real.log (x/y)),
    ← div_le_iff₀ hy, Real.le_log_iff_exp_le (div_pos hx hy), le_div_iff₀ hy,
    mul_comm (Real.exp (t/y)) y]

end Chapter08.Exponential
