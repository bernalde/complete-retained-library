module

public import Chapter10SequencePenalty

@[expose] public section

/-! Literal quadratic cost range and strict exactness on all source-fixed
coordinates. Product-index multiplicity is preserved. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

def coefficient {n v k} (D : Data n) (r : Transition n v k) : ℝ :=
  if D.allowed r.2.2.1 r.2.2.2 then D.cost r.2.2.1 r.2.2.2 else 0
def monomial {n v k} (x : Sequence.Array n v k) (r : Transition n v k) : ℝ :=
  x r.1 (Sequence.left r.2.1) r.2.2.1 * x r.1 (Sequence.right r.2.1) r.2.2.2
def arcAbsCost {n} (D : Data n) : ℝ :=
  ∑ i, ∑ j, if D.allowed i j then |D.cost i j| else 0
def printedBound {n} (D : Data n) (v k : ℕ) : ℝ := (k+2 : ℕ) * (v : ℝ) * arcAbsCost D

theorem monomial_binary {n v k} (x : Sequence.Array n v k) (hx : Sequence.Binary x) :
    Algebra.Binary (monomial x) := fun _ => product_binary _ _ (hx _ _ _) (hx _ _ _)

theorem objective_as_linearCost {n v k} (D : Data n) (x : Sequence.Array n v k) :
    Sequence.objective D x = linearCost (coefficient D) (monomial x) := by
  simp only [Sequence.objective, linearCost, coefficient, monomial, Fintype.sum_prod_type,
    ite_mul, zero_mul, mul_assoc]

theorem coefficient_abs_sum {n v k} (D : Data n) :
    (∑ r : Transition n v k, |coefficient D r|) = (k+1 : ℕ) * (v : ℝ) * arcAbsCost D := by
  simp only [coefficient, Fintype.sum_prod_type, apply_ite abs, abs_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold arcAbsCost
  ring

theorem arcAbsCost_nonnegative {n} (D : Data n) : 0 ≤ arcAbsCost D := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

theorem objective_range {n v k} (D : Data n) (x y : Sequence.Array n v k)
    (hx : Sequence.Binary x) (hy : Sequence.Binary y) :
    Sequence.objective D x - Sequence.objective D y ≤ (k+1 : ℕ) * (v : ℝ) * arcAbsCost D := by
  rw [objective_as_linearCost, objective_as_linearCost, ← coefficient_abs_sum (v := v) (k := k) D]
  exact finite_binary_cost_range_from_accepted _ _ _ (monomial_binary x hx) (monomial_binary y hy)

theorem objective_range_printed {n v k} (D : Data n) (x y : Sequence.Array n v k)
    (hx : Sequence.Binary x) (hy : Sequence.Binary y) :
    Sequence.objective D x - Sequence.objective D y ≤ printedBound D v k := by
  apply (objective_range D x y hx hy).trans
  unfold printedBound
  apply mul_le_mul_of_nonneg_right _ (arcAbsCost_nonnegative D)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg v)
  exact_mod_cast (by omega : k+1 ≤ k+2)

theorem printedBound_nonnegative {n} (D : Data n) (v k : ℕ) : 0 ≤ printedBound D v k := by
  unfold printedBound
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (arcAbsCost_nonnegative D)

theorem every_bad_gt_every_feasible {n v k} (D : Data n) (ρ : ℝ)
    (hρ : printedBound D v k < ρ) (x y : Sequence.Array n v k)
    (hx : x ∈ domain D) (hbad : ¬ Sequence.Literal D x) (hgood : Sequence.Literal D y) :
    energy D ρ y < energy D ρ x := by
  have hy := (literal_iff_domain_rows D y).mp hgood
  have hn : ¬ Rows D x := fun h => hbad ((literal_iff_domain_rows D x).mpr ⟨hx,h⟩)
  exact penalty_every_bad_gt (domain D) (Rows D) (Sequence.objective D) (penalty D)
    (printedBound D v k) ρ (printedBound_nonnegative D v k) hρ
    (fun z _ hz => rows_penalty_zero D z hz)
    (fun z hz hn => penalty_gap D z hz.1 hn)
    (fun z hz w hw => objective_range_printed D z w hz.1 hw.1) x y hx hn hy.1 hy.2

theorem minimizers_exact {n v k} (D : Data n) (ρ : ℝ)
    (hρ : printedBound D v k < ρ) (x : Sequence.Array n v k) :
    (IsMinOn (domain D) (energy D ρ) x ∧ ∃ y : Sequence.Array n v k, Sequence.Literal D y) ↔
      IsMinOn {y | Sequence.Literal D y} (Sequence.objective D) x := by
  have h := penalty_minimizers_exact (domain D) (Rows D) (Sequence.objective D) (penalty D)
    (printedBound D v k) ρ (printedBound_nonnegative D v k) hρ
    (fun z _ hz => rows_penalty_zero D z hz)
    (fun z hz hn => penalty_gap D z hz.1 hn)
    (fun z hz w hw => objective_range_printed D z w hz.1 hw.1) x
  simpa only [show energy D ρ = penalized (Sequence.objective D) (penalty D) ρ from rfl,
    ← literal_iff_domain_rows] using h

end Chapter10.SequencePenalty

#print axioms Chapter10.SequencePenalty.objective_range
#print axioms Chapter10.SequencePenalty.every_bad_gt_every_feasible
#print axioms Chapter10.SequencePenalty.minimizers_exact
