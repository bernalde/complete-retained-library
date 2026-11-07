module

public import Chapter10SequenceCost
public import Chapter10ProductMatrix

@[expose] public section

/-! Actual sequence QUBO: literal one-hot rows plus every ordered objective,
forbidden and absorbing monomial, with the full saved constant. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

abbrev OneHotRow (n v k : ℕ) := Fin n ⊕ (Fin v × Fin (k+2))
def rowMatrix {n v k} : OneHotRow n v k → Coord n v k → ℝ
  | .inl c, r => if r.2.2 = some c then 1 else 0
  | .inr ap, r => if r.1 = ap.1 then if r.2.1 = ap.2 then 1 else 0 else 0

theorem customer_row_sum {n v k} (x : Sequence.Array n v k) (c : Fin n) :
    (∑ r : Coord n v k, rowMatrix (Sum.inl c) r * flatten x r) =
      ∑ a, ∑ p, x a p (some c) := by
  simp [rowMatrix, flatten, Fintype.sum_prod_type, ite_mul]

theorem position_row_sum {n v k} (x : Sequence.Array n v k) (ap : Fin v × Fin (k+2)) :
    (∑ r : Coord n v k, rowMatrix (Sum.inr ap) r * flatten x r) = ∑ i, x ap.1 ap.2 i := by
  simp [rowMatrix, flatten, Fintype.sum_prod_type, ite_mul]

theorem onehot_squared_residual {n v k} (x : Sequence.Array n v k) :
    squaredResidual rowMatrix (fun _ : OneHotRow n v k => 1) (flatten x) =
      customerPenalty x + positionPenalty x := by
  unfold squaredResidual
  rw [Fintype.sum_sum_type]
  simp_rw [customer_row_sum, position_row_sum]
  rfl

theorem onehot_offset_count (n v k : ℕ) :
    (∑ _ : OneHotRow n v k, (1 : ℝ)^2) = (n : ℝ) + (v : ℝ) * (k+2 : ℕ) := by
  simp [Fintype.card_sum, Fintype.card_prod]

def transitionLeft {n v k} (r : Transition n v k) : Coord n v k := (r.1, Sequence.left r.2.1, r.2.2.1)
def transitionRight {n v k} (r : Transition n v k) : Coord n v k := (r.1, Sequence.right r.2.1, r.2.2.2)
def absorptionLeft {n v k} (r : Absorption n v k) : Coord n v k := (r.1, Sequence.left r.2.1, none)
def absorptionRight {n v k} (r : Absorption n v k) : Coord n v k := (r.1, Sequence.right r.2.1, some r.2.2)

def objectiveMatrix {n v k} (D : Data n) : Coord n v k → Coord n v k → ℝ :=
  productMatrix (coefficient D) transitionLeft transitionRight
def forbiddenMatrix {n v k} (D : Data n) : Coord n v k → Coord n v k → ℝ :=
  productMatrix (fun r : Transition n v k => if D.allowed r.2.2.1 r.2.2.2 then 0 else 1) transitionLeft transitionRight
def absorbingMatrix (n v k : ℕ) : Coord n v k → Coord n v k → ℝ :=
  productMatrix (fun r : Absorption n v k => if 0 < r.2.1.val then 1 else 0) absorptionLeft absorptionRight

theorem objective_matrix_identity {n v k} (D : Data n) (x : Sequence.Array n v k) :
    quadratic (objectiveMatrix D) (flatten x) = Sequence.objective D x := by
  rw [objectiveMatrix, productMatrix_quadratic, objective_as_linearCost]
  simp only [linearCost, transitionLeft, transitionRight, flatten, monomial, mul_assoc]

theorem forbidden_matrix_identity {n v k} (D : Data n) (x : Sequence.Array n v k) :
    quadratic (forbiddenMatrix D) (flatten x) = forbiddenPenalty D x := by
  rw [forbiddenMatrix, productMatrix_quadratic]
  unfold forbiddenPenalty
  apply Finset.sum_congr rfl
  intro r _
  simp only [transitionLeft, transitionRight, flatten, forbiddenTerm]
  split_ifs <;> simp

theorem absorbing_matrix_identity {n v k} (x : Sequence.Array n v k) :
    quadratic (absorbingMatrix n v k) (flatten x) = absorbingPenalty x := by
  rw [absorbingMatrix, productMatrix_quadratic]
  unfold absorbingPenalty
  apply Finset.sum_congr rfl
  intro r _
  simp only [absorptionLeft, absorptionRight, flatten, absorbingTerm]
  split_ifs <;> simp

def matrix {n v k} (D : Data n) (ρ : ℝ) : Coord n v k → Coord n v k → ℝ :=
  fun i j => quboMatrix rowMatrix (fun _ : OneHotRow n v k => 1) (fun _ => 0) ρ i j +
    objectiveMatrix D i j + ρ * forbiddenMatrix D i j + ρ * absorbingMatrix n v k i j

theorem matrix_quadratic {n v k} (D : Data n) (x : Sequence.Array n v k) (ρ : ℝ) :
    quadratic (matrix D ρ) (flatten x) =
      quadratic (quboMatrix rowMatrix (fun _ : OneHotRow n v k => 1) (fun _ => 0) ρ) (flatten x) +
      Sequence.objective D x + ρ * forbiddenPenalty D x + ρ * absorbingPenalty x := by
  unfold matrix
  rw [quadratic_add, quadratic_add, quadratic_add, quadratic_smul, quadratic_smul,
    objective_matrix_identity, forbidden_matrix_identity, absorbing_matrix_identity]

theorem source_energy_matrix_identity {n v k} (D : Data n) (x : Sequence.Array n v k)
    (ρ : ℝ) (hx : Sequence.Binary x) :
    energy D ρ x = quadratic (matrix D ρ) (flatten x) +
      ρ * ((n : ℝ) + (v : ℝ) * (k+2 : ℕ)) := by
  have h := full_qubo_identity rowMatrix (fun _ : OneHotRow n v k => 1)
    (fun _ => 0) (flatten x) ρ (flatten_binary x hx)
  rw [onehot_squared_residual, onehot_offset_count] at h
  simp only [linearCost, zero_mul, Finset.sum_const_zero, zero_add] at h
  rw [matrix_quadratic]
  unfold energy penalty
  nlinarith

end Chapter10.SequencePenalty

#print axioms Chapter10.SequencePenalty.source_energy_matrix_identity
