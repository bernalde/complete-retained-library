module

public import Chapter10FiniteAdapters

@[expose] public section

/-! Signed integer residuals and domain-explicit exact penalties.
Source adapters must prove their literal rows coincide with these residuals. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Algebra

def IsMinOn {α : Type*} (D : Set α) (f : α → ℝ) (x : α) : Prop :=
  x ∈ D ∧ ∀ y ∈ D, f x ≤ f y

def penalized {α : Type*} (f w : α → ℝ) (ρ : ℝ) (x : α) : ℝ := f x + ρ * w x

theorem penalty_every_bad_gt {α : Type*} (D : Set α) (P : α → Prop)
    (f w : α → ℝ) (B ρ : ℝ) (hB : 0 ≤ B) (hρ : B < ρ)
    (hzero : ∀ y ∈ D, P y → w y = 0)
    (hgap : ∀ x ∈ D, ¬ P x → 1 ≤ w x)
    (hcost : ∀ x ∈ D, ∀ y ∈ D, f x - f y ≤ B)
    (x y : α) (hx : x ∈ D) (hbad : ¬ P x) (hy : y ∈ D) (hgood : P y) :
    penalized f w ρ y < penalized f w ρ x := by
  have hz := hzero y hy hgood
  have hg := hgap x hx hbad
  have hc := hcost y hy x hx
  have hp : 0 < ρ := hB.trans_lt hρ
  simp only [penalized, hz, mul_zero, add_zero]
  nlinarith

theorem penalty_minimizers_exact {α : Type*} (D : Set α) (P : α → Prop)
    (f w : α → ℝ) (B ρ : ℝ) (hB : 0 ≤ B) (hρ : B < ρ)
    (hzero : ∀ y ∈ D, P y → w y = 0)
    (hgap : ∀ x ∈ D, ¬ P x → 1 ≤ w x)
    (hcost : ∀ x ∈ D, ∀ y ∈ D, f x - f y ≤ B) (x : α) :
    (IsMinOn D (penalized f w ρ) x ∧ ∃ y ∈ D, P y) ↔
      IsMinOn {y | y ∈ D ∧ P y} f x := by
  constructor
  · rintro ⟨⟨hx, hm⟩, y, hy, hp⟩
    have hpx : P x := by
      by_contra hn
      have hlt := penalty_every_bad_gt D P f w B ρ hB hρ hzero hgap hcost x y hx hn hy hp
      exact (not_lt_of_ge (hm y hy)) hlt
    refine ⟨⟨hx, hpx⟩, ?_⟩
    intro z hz
    have hc := hm z hz.1
    simpa only [penalized, hzero x hx hpx, hzero z hz.1 hz.2, mul_zero, add_zero] using hc
  · rintro ⟨⟨hx, hp⟩, hm⟩
    refine ⟨⟨hx, ?_⟩, x, hx, hp⟩
    intro y hy
    by_cases hpy : P y
    · simpa only [penalized, hzero x hx hp, hzero y hy hpy, mul_zero, add_zero] using hm y ⟨hy, hpy⟩
    · exact (penalty_every_bad_gt D P f w B ρ hB hρ hzero hgap hcost y x hy hpy hx hp).le

def integerResidual {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (r : κ) : ℤ :=
  (∑ i, A r i * (if x i = 1 then 1 else 0)) - b r

def integerFeasible {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) : Prop :=
  ∀ r, (∑ i, (A r i : ℝ) * x i) = (b r : ℝ)

def integerPenalty {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) : ℝ :=
  squaredResidual (fun r i => (A r i : ℝ)) (fun r => (b r : ℝ)) x

theorem real_residual_eq_integer {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (hx : Binary x) (r : κ) :
    (∑ i, (A r i : ℝ) * x i) - (b r : ℝ) = (integerResidual A b x r : ℝ) := by
  simp only [integerResidual, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases hx i with h | h <;> simp [h]

theorem integer_square_gap (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ (z : ℝ)^2 := by
  have hd : z ≤ -1 ∨ 1 ≤ z := by omega
  rcases hd with hn | hp
  · have hr : (z : ℝ) ≤ -1 := by exact_mod_cast hn
    nlinarith [sq_nonneg ((z : ℝ) + 1)]
  · have hr : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hp
    nlinarith [sq_nonneg ((z : ℝ) - 1)]

theorem integer_penalty_nonnegative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) : 0 ≤ integerPenalty A b x := by
  exact Finset.sum_nonneg (fun r _ => sq_nonneg _)

theorem integer_feasible_penalty_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (hf : integerFeasible A b x) :
    integerPenalty A b x = 0 := by
  unfold integerPenalty squaredResidual
  apply Finset.sum_eq_zero
  intro r _
  rw [hf r]
  ring

theorem integer_penalty_gap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (hx : Binary x)
    (hf : ¬ integerFeasible A b x) : 1 ≤ integerPenalty A b x := by
  obtain ⟨r, hr⟩ := not_forall.mp hf
  have hn : integerResidual A b x r ≠ 0 := by
    have hh := sub_ne_zero.mpr hr
    rw [real_residual_eq_integer A b x hx r] at hh
    exact_mod_cast hh
  have hg := integer_square_gap (integerResidual A b x r) hn
  rw [← real_residual_eq_integer A b x hx r] at hg
  exact hg.trans (Finset.single_le_sum
    (fun j _ => sq_nonneg ((∑ i, (A j i : ℝ) * x i) - (b j : ℝ))) (Finset.mem_univ r))

theorem integer_penalty_zero_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (x : ι → ℝ) (hx : Binary x) :
    integerPenalty A b x = 0 ↔ integerFeasible A b x := by
  constructor
  · intro hz
    by_contra hn
    have hg := integer_penalty_gap A b x hx hn
    linarith
  · exact integer_feasible_penalty_zero A b x

theorem integer_penalty_every_bad_gt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (c : ι → ℝ) (D : Set (ι → ℝ))
    (hD : ∀ x ∈ D, Binary x) (ρ : ℝ) (hρ : (∑ i, |c i|) < ρ)
    (x y : ι → ℝ) (hx : x ∈ D) (hbad : ¬ integerFeasible A b x)
    (hy : y ∈ D) (hgood : integerFeasible A b y) :
    penalized (linearCost c) (integerPenalty A b) ρ y <
      penalized (linearCost c) (integerPenalty A b) ρ x := by
  apply penalty_every_bad_gt D (integerFeasible A b) (linearCost c) (integerPenalty A b)
    (∑ i, |c i|) ρ (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hρ
    (fun z _ hz => integer_feasible_penalty_zero A b z hz)
    (fun z hz hn => integer_penalty_gap A b z (hD z hz) hn)
    (fun z hz w hw => finite_binary_cost_range_from_accepted c z w (hD z hz) (hD w hw))
    x y hx hbad hy hgood

theorem min_add_constant_iff {α : Type*} (D : Set α) (f : α → ℝ) (κ : ℝ) (x : α) :
    IsMinOn D (fun y => f y + κ) x ↔ IsMinOn D f x := by
  simp only [IsMinOn, add_le_add_iff_right]

theorem integer_penalty_minimizers_exact {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (b : κ → ℤ) (c : ι → ℝ) (D : Set (ι → ℝ))
    (hD : ∀ x ∈ D, Binary x) (ρ : ℝ) (hρ : (∑ i, |c i|) < ρ) (x : ι → ℝ) :
    (IsMinOn D (penalized (linearCost c) (integerPenalty A b) ρ) x ∧
      ∃ y ∈ D, integerFeasible A b y) ↔
      IsMinOn {y | y ∈ D ∧ integerFeasible A b y} (linearCost c) x := by
  apply penalty_minimizers_exact D (integerFeasible A b) (linearCost c) (integerPenalty A b)
    (∑ i, |c i|) ρ (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hρ
  · intro y _ hy
    exact integer_feasible_penalty_zero A b y hy
  · intro y hy hn
    exact integer_penalty_gap A b y (hD y hy) hn
  · intro y hy z hz
    exact finite_binary_cost_range_from_accepted c y z (hD y hy) (hD z hz)

end Chapter10.Algebra

#print axioms Chapter10.Algebra.integer_penalty_minimizers_exact
#print axioms Chapter10.Algebra.integer_penalty_gap
