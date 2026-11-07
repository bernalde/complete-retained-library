module

public import Chapter10

@[expose] public section

/-! Finite real binary algebra for the literal Chapter10 QUBO conversions.
The full matrix uses ordered entries; constants remain part of the energy. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Algebra

def Binary {ι : Type*} (x : ι → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1

def encode {ι : Type*} (x : ι → ℝ) : ι → Bool := fun i => decide (x i = 1)

theorem bit_encode {ι : Type*} {x : ι → ℝ} (hx : Binary x) (i : ι) :
    Chapter10.bit (encode x i) = x i := by
  rcases hx i with h | h <;> simp [encode, Chapter10.bit, h]

theorem binary_sq {ι : Type*} {x : ι → ℝ} (hx : Binary x) (i : ι) :
    x i * x i = x i := by
  rcases hx i with h | h <;> simp [h]

theorem binary_nonneg {ι : Type*} {x : ι → ℝ} (hx : Binary x) (i : ι) : 0 ≤ x i := by
  rcases hx i with h | h <;> simp [h]

def linearCost {ι : Type*} [Fintype ι] (c x : ι → ℝ) : ℝ := ∑ i, c i * x i

theorem binary_linear_cost_range {ι : Type*} [Fintype ι] (c x y : ι → ℝ)
    (hx : Binary x) (hy : Binary y) :
    linearCost c x - linearCost c y ≤ ∑ i, |c i| := by
  unfold linearCost
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [bit_encode hx, bit_encode hy] using
    Chapter10.binary_cost_change (c i) (encode x i) (encode y i)

def quadratic {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * x i * x j

def diagonal {ι : Type*} [DecidableEq ι] (d : ι → ℝ) : ι → ι → ℝ :=
  fun i j => if i = j then d i else 0

def squaredResidual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (b : κ → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ r, ((∑ i, A r i * x i) - b r)^2

def quboMatrix {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c : ι → ℝ) (ρ : ℝ) : ι → ι → ℝ :=
  fun i j => ρ * (∑ r, A r i * A r j) +
    diagonal (fun i => c i - 2 * ρ * (∑ r, A r i * b r)) i j

theorem quadratic_add {ι : Type*} [Fintype ι] (M N : ι → ι → ℝ) (x : ι → ℝ) :
    quadratic (fun i j => M i j + N i j) x = quadratic M x + quadratic N x := by
  simp only [quadratic, add_mul, Finset.sum_add_distrib]

theorem quadratic_smul {ι : Type*} [Fintype ι] (M : ι → ι → ℝ) (x : ι → ℝ) (ρ : ℝ) :
    quadratic (fun i j => ρ * M i j) x = ρ * quadratic M x := by
  simp only [quadratic, mul_assoc, Finset.mul_sum]

theorem quadratic_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d x : ι → ℝ) (hx : Binary x) : quadratic (diagonal d) x = linearCost d x := by
  simp only [quadratic, diagonal, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, linearCost]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, binary_sq hx]

theorem quadratic_rows {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : κ → ι → ι → ℝ) (x : ι → ℝ) :
    quadratic (fun i j => ∑ r, K r i j) x = ∑ r, quadratic (K r) x := by
  unfold quadratic
  simp only [Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ r, K r i j * x i * x j) =
        ∑ i, ∑ r, ∑ j, K r i j * x i * x j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ j, K r i j * x i * x j := Finset.sum_comm

theorem quadratic_outer {ι : Type*} [Fintype ι] (a x : ι → ℝ) :
    quadratic (fun i j => a i * a j) x = (∑ i, a i * x i)^2 := by
  simp only [quadratic, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem transpose_linear_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (b : κ → ℝ) (x : ι → ℝ) :
    (∑ i, (∑ r, A r i * b r) * x i) = ∑ r, b r * (∑ i, A r i * x i) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem full_qubo_identity {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c x : ι → ℝ) (ρ : ℝ) (hx : Binary x) :
    linearCost c x + ρ * squaredResidual A b x =
      quadratic (quboMatrix A b c ρ) x + ρ * ∑ r, (b r)^2 := by
  unfold quboMatrix
  rw [quadratic_add, quadratic_smul, quadratic_rows]
  simp_rw [quadratic_outer]
  rw [quadratic_diagonal _ _ hx]
  unfold linearCost squaredResidual
  simp only [sub_mul, Finset.sum_sub_distrib]
  have ht := transpose_linear_sum A b x
  have hlin : (∑ i, 2 * ρ * (∑ r, A r i * b r) * x i) =
      2 * ρ * ∑ r, b r * (∑ i, A r i * x i) := by
    rw [← ht]
    calc
      _ = ∑ i, (2 * ρ) * ((∑ r, A r i * b r) * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hlin]
  have hs : (∑ r, ((∑ i, A r i * x i) - b r)^2) =
      (∑ r, (∑ i, A r i * x i)^2) -
      2 * (∑ r, b r * (∑ i, A r i * x i)) + ∑ r, (b r)^2 := by
    calc
      _ = ∑ r, ((∑ i, A r i * x i)^2 - 2 * (b r * (∑ i, A r i * x i)) + (b r)^2) := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hs]
  ring

end Chapter10.Algebra

#print axioms Chapter10.Algebra.full_qubo_identity
#print axioms Chapter10.Algebra.binary_linear_cost_range
