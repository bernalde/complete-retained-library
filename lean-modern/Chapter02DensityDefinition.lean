module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-! Finite-count contracts for thesis Eq. (2.9)–(2.10), printed p.56.
The positive denominator and disjoint variable-type counts are explicit.
No syntactic feature extractor or empirical benchmark classification is modeled.
-/
noncomputable section
namespace Chapter02.DensityDefinition

def percentage (selected total : ℕ) : ℝ :=
  (selected : ℝ) / (total : ℝ) * 100

/-- A separate reporting convention; the source quotient requires total > 0. -/
def checkedPercentage (selected total : ℕ) : Option ℝ :=
  if total = 0 then none else some (percentage selected total)

theorem percentage_bounds (selected total : ℕ) (ht : 0 < total)
    (hc : selected ≤ total) :
    0 ≤ percentage selected total ∧ percentage selected total ≤ 100 := by
  have ht' : (0 : ℝ) < total := by exact_mod_cast ht
  have hc' : (selected : ℝ) ≤ total := by exact_mod_cast hc
  constructor
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt ht')) (by norm_num)
  · dsimp [percentage]
    have h : (selected : ℝ) / total ≤ 1 := (div_le_one ht').mpr hc'
    nlinarith

theorem percentage_half_threshold (selected total : ℕ) (ht : 0 < total) :
    (50 ≤ percentage selected total ↔ total ≤ 2 * selected) ∧
    (percentage selected total < 50 ↔ 2 * selected < total) := by
  have ht' : (0 : ℝ) < total := by exact_mod_cast ht
  have heq : percentage selected total = (100 * (selected : ℝ)) / total := by
    simp [percentage, div_mul_eq_mul_div, mul_comm]
  rw [heq]
  constructor
  · rw [le_div_iff₀ ht']
    have hc : (total ≤ 2 * selected) ↔ (total : ℝ) ≤ 2 * (selected : ℝ) := by
      exact_mod_cast (Iff.rfl : total ≤ 2 * selected ↔ total ≤ 2 * selected)
    rw [hc]
    constructor <;> intro h <;> nlinarith
  · rw [div_lt_iff₀ ht']
    have hc : (2 * selected < total) ↔ 2 * (selected : ℝ) < (total : ℝ) := by
      exact_mod_cast (Iff.rfl : 2 * selected < total ↔ 2 * selected < total)
    rw [hc]
    constructor <;> intro h <;> nlinarith

section FiniteVariables
variable {α : Type*}

theorem nonlinear_density_contract (allVars nonlinear : Finset α)
    (ht : 0 < allVars.card) (hn : nonlinear ⊆ allVars) :
    0 ≤ percentage nonlinear.card allVars.card ∧
    percentage nonlinear.card allVars.card ≤ 100 ∧
    (50 ≤ percentage nonlinear.card allVars.card ↔
      allVars.card ≤ 2 * nonlinear.card) ∧
    (percentage nonlinear.card allVars.card < 50 ↔
      2 * nonlinear.card < allVars.card) := by
  exact ⟨(percentage_bounds _ _ ht (Finset.card_le_card hn)).1,
    (percentage_bounds _ _ ht (Finset.card_le_card hn)).2,
    (percentage_half_threshold _ _ ht).1,
    (percentage_half_threshold _ _ ht).2⟩

theorem discrete_density_contract [DecidableEq α]
    (allVars generalInteger binary : Finset α)
    (ht : 0 < allVars.card) (hi : generalInteger ⊆ allVars)
    (hb : binary ⊆ allVars) (hd : Disjoint generalInteger binary) :
    generalInteger.card + binary.card = (generalInteger ∪ binary).card ∧
    0 ≤ percentage (generalInteger.card + binary.card) allVars.card ∧
    percentage (generalInteger.card + binary.card) allVars.card ≤ 100 ∧
    (50 ≤ percentage (generalInteger.card + binary.card) allVars.card ↔
      allVars.card ≤ 2 * (generalInteger.card + binary.card)) ∧
    (percentage (generalInteger.card + binary.card) allVars.card < 50 ↔
      2 * (generalInteger.card + binary.card) < allVars.card) := by
  have heq : generalInteger.card + binary.card = (generalInteger ∪ binary).card :=
    (Finset.card_union_of_disjoint hd).symm
  have hc : generalInteger.card + binary.card ≤ allVars.card := by
    rw [heq]
    exact Finset.card_le_card (Finset.union_subset hi hb)
  exact ⟨heq, (percentage_bounds _ _ ht hc).1, (percentage_bounds _ _ ht hc).2,
    (percentage_half_threshold _ _ ht).1, (percentage_half_threshold _ _ ht).2⟩

end FiniteVariables

/-- The two reported categories cover a finite population without overlap.
The score is a mathematical supplied score, not a historical feature extractor. -/
theorem threshold_population_partition {α : Type*} [DecidableEq α]
    (population : Finset α) (score : α → ℝ) :
    (population.filter (fun x => 50 ≤ score x)) ∪
      (population.filter (fun x => score x < 50)) = population ∧
    Disjoint (population.filter (fun x => 50 ≤ score x))
      (population.filter (fun x => score x < 50)) ∧
    (population.filter (fun x => 50 ≤ score x)).card +
      (population.filter (fun x => score x < 50)).card = population.card := by
  classical
  have hu : (population.filter (fun x => 50 ≤ score x)) ∪
      (population.filter (fun x => score x < 50)) = population := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases le_or_gt 50 (score x) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hd : Disjoint (population.filter (fun x => 50 ≤ score x))
      (population.filter (fun x => score x < 50)) := by
    apply Finset.disjoint_left.mpr
    intro x hh hl
    exact not_lt_of_ge (Finset.mem_filter.mp hh).2 (Finset.mem_filter.mp hl).2
  exact ⟨hu, hd, by rw [← Finset.card_union_of_disjoint hd, hu]⟩

/-- Nonvacuity, exact-boundary, zero-denominator and overlap controls together. -/
theorem density_boundary_controls :
    percentage 1 2 = 50 ∧ ¬ percentage 1 2 < 50 ∧
    checkedPercentage 0 0 = none ∧ percentage 1 0 = 0 ∧
    percentage (({0} : Finset ℕ).card + ({0} : Finset ℕ).card)
      ({0} : Finset ℕ).card = 200 ∧
    ¬ Disjoint ({0} : Finset ℕ) ({0} : Finset ℕ) := by
  norm_num [percentage, checkedPercentage, Finset.disjoint_left]

/-- A genuine nonempty variable inventory satisfies all source premises;
its one counted variable out of two lies exactly at the high boundary. -/
theorem source_model_control :
    let allVars : Finset ℕ := {0, 1}
    let generalInteger : Finset ℕ := {0}
    let binary : Finset ℕ := ∅
    let nonlinear : Finset ℕ := {0}
    0 < allVars.card ∧ generalInteger ⊆ allVars ∧ binary ⊆ allVars ∧
    Disjoint generalInteger binary ∧ nonlinear ⊆ allVars ∧
    percentage (generalInteger.card + binary.card) allVars.card = 50 ∧
    percentage nonlinear.card allVars.card = 50 := by
  norm_num [percentage, Finset.subset_iff]

end Chapter02.DensityDefinition

#print axioms Chapter02.DensityDefinition.nonlinear_density_contract
#print axioms Chapter02.DensityDefinition.discrete_density_contract
#print axioms Chapter02.DensityDefinition.threshold_population_partition
#print axioms Chapter02.DensityDefinition.density_boundary_controls
#print axioms Chapter02.DensityDefinition.source_model_control
