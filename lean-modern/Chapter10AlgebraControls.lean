module

public import Chapter10FixedBits
public import Chapter10InventoryWindows

@[expose] public section

/-! Exact algebra/domain controls from proposal02. These are author controls,
not route validity, solver evidence, or chapter acceptance. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Algebra.Controls
open Chapter10.Algebra

def signedA : Fin 2 → Fin 2 → ℤ := ![![1, 2], ![-1, 1]]
def signedB : Fin 2 → ℤ := ![1, -1]
def signedC : Fin 2 → ℝ := ![-3, 2]
def goodX : Fin 2 → ℝ := ![1, 0]
def badX : Fin 2 → ℝ := ![1, 1]

theorem signed_binary_controls : Binary goodX ∧ Binary badX := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [goodX, badX]

theorem signed_feasibility_control : integerFeasible signedA signedB goodX ∧
    ¬ integerFeasible signedA signedB badX := by
  constructor
  · intro r
    fin_cases r <;> norm_num [signedA, signedB, goodX, Fin.sum_univ_two]
  · intro h
    have hh := h 0
    norm_num [signedA, signedB, badX, Fin.sum_univ_two] at hh

theorem signed_penalty_values : integerPenalty signedA signedB goodX = 0 ∧
    integerPenalty signedA signedB badX = 5 := by
  norm_num [integerPenalty, squaredResidual, signedA, signedB, goodX, badX, Fin.sum_univ_two]

theorem off_diagonal_matrix_control :
    quboMatrix (fun r i => (signedA r i : ℝ)) (fun r => (signedB r : ℝ)) signedC 5 0 1 = 5 ∧
    quboMatrix (fun r i => (signedA r i : ℝ)) (fun r => (signedB r : ℝ)) signedC 5 1 0 = 5 ∧
    quadratic (quboMatrix (fun r i => (signedA r i : ℝ)) (fun r => (signedB r : ℝ)) signedC 5) badX = 14 ∧
    5 * (∑ r, (signedB r : ℝ)^2) = 10 := by
  norm_num [quboMatrix, diagonal, quadratic, signedA, signedB, signedC, badX, Fin.sum_univ_two]

theorem full_signed_energy_control :
    linearCost signedC badX + 5 * integerPenalty signedA signedB badX =
      quadratic (quboMatrix (fun r i => (signedA r i : ℝ)) (fun r => (signedB r : ℝ)) signedC 5) badX + 10 := by
  norm_num [linearCost, integerPenalty, squaredResidual, quboMatrix, diagonal, quadratic,
    signedA, signedB, signedC, badX, Fin.sum_univ_two]

theorem signed_strict_threshold_control :
    (∑ i, |signedC i|) < (6 : ℝ) ∧
      penalized (linearCost signedC) (integerPenalty signedA signedB) 6 goodX <
      penalized (linearCost signedC) (integerPenalty signedA signedB) 6 badX := by
  norm_num [penalized, linearCost, integerPenalty, squaredResidual, signedA, signedB,
    signedC, goodX, badX, Fin.sum_univ_two]

def fixedA : Fin 2 → ℝ := ![1, 0]
def mixedM : (Fin 1 ⊕ Fin 2) → (Fin 1 ⊕ Fin 2) → ℝ
  | .inl _, .inl _ => 2
  | .inl _, .inr f => if f = 0 then 3 else 11
  | .inr f, .inl _ => if f = 0 then 5 else 13
  | .inr f, .inr g => if f = 0 ∧ g = 0 then 7 else 17

theorem fixed_one_zero_coefficient_control :
    fixedLinear mixedM fixedA 0 = 8 ∧ fixedMatrix mixedM fixedA 0 0 = 10 ∧
      fixedOffset mixedM fixedA 19 = 26 := by
  norm_num [fixedLinear, fixedMatrix, fixedOffset, diagonal, quadratic, mixedM, fixedA,
    Fin.sum_univ_two]

theorem fixed_one_zero_energy_control :
    quadratic mixedM (extend fixedA (fun _ : Fin 1 => 1)) + 19 = 36 ∧
      quadratic (fixedMatrix mixedM fixedA) (fun _ : Fin 1 => 1) + fixedOffset mixedM fixedA 19 = 36 := by
  norm_num [quadratic, Fintype.sum_sum_type, extend, mixedM, fixedA, fixedMatrix,
    fixedLinear, fixedOffset, diagonal, Fin.sum_univ_two]

theorem inconsistent_fixed_control :
    {x : Fin 1 → ℝ | Binary x ∧ x 0 = 0 ∧ x 0 = 1} = ∅ := by
  exact conflicting_fixed_bits_empty _ 0 (fun _ h => h.2.1) (fun _ h => h.2.2)

theorem infeasible_but_energy_minimum_control :
    (¬ ∃ x : Fin 1 → ℝ, Binary x ∧
      integerFeasible (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ℤ)) (fun _ => (1 : ℤ)) x) ∧
    IsMinOn {x : Fin 1 → ℝ | Binary x}
      (penalized (linearCost (fun _ => (0 : ℝ)))
        (integerPenalty (fun _ : Fin 1 => fun _ : Fin 1 => (0 : ℤ)) (fun _ => (1 : ℤ))) 1)
      (fun _ => 0) := by
  constructor
  · rintro ⟨x, _, hx⟩
    have h := hx 0
    norm_num at h
  · refine ⟨fun _ => Or.inl rfl, ?_⟩
    intro y _
    norm_num [penalized, linearCost, integerPenalty, squaredResidual]

theorem no_free_coordinate_control (M : Fin 0 ⊕ Fin 1 → Fin 0 ⊕ Fin 1 → ℝ)
    (κ : ℝ) :
    quadratic M (extend (fun _ : Fin 1 => 1) (fun i : Fin 0 => Fin.elim0 i)) + κ =
      fixedOffset M (fun _ : Fin 1 => 1) κ := by
  have h := fixed_qubo_identity M (fun _ : Fin 1 => 1)
    (fun i : Fin 0 => Fin.elim0 i) κ (fun i => Fin.elim0 i)
  simpa [quadratic] using h

end Chapter10.Algebra.Controls

#print axioms Chapter10.Algebra.Controls.full_signed_energy_control
#print axioms Chapter10.Algebra.Controls.fixed_one_zero_energy_control
#print axioms Chapter10.Algebra.Controls.infeasible_but_energy_minimum_control
