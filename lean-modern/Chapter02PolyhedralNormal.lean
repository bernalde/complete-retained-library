module

public import Chapter02
public import Chapter02FiniteCone
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Actual differentiable minima on finite affine polyhedra.
Inactive-row strict slack supplies small feasible positive steps. Opposing
active rows and polyhedra with empty ambient interior are permitted. The
derivative hypothesis is always full-space `HasFDerivAt`. -/
noncomputable section
open scoped BigOperators Topology
open Filter Set
namespace Chapter02

def affinePolyhedron {n r : ℕ}
    (a : Fin r → RealVector n →L[ℝ] ℝ) (b : Fin r → ℝ) : Set (RealVector n) :=
  {x | ∀ i, a i x ≤ b i}

/-- A direction satisfying only the active affine inequalities gives feasible
positive steps sufficiently near zero. Finiteness intersects the inactive
rows' positive-slack neighborhoods; no strict affine Slater point is required. -/
theorem polyhedral_feasible_small_steps {n r : ℕ}
    (a : Fin r → RealVector n →L[ℝ] ℝ) (b : Fin r → ℝ)
    {p v : RealVector n} (hp : p ∈ affinePolyhedron a b)
    (hv : ∀ i, a i p = b i → a i v ≤ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, p + t • v ∈ affinePolyhedron a b := by
  change ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i, a i (p + t • v) ≤ b i
  rw [Filter.eventually_all]
  intro i
  by_cases hactive : a i p = b i
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    simp only [map_add, map_smul, smul_eq_mul, hactive]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht0 (hv i hactive))
  · have hslack : a i p < b i := lt_of_le_of_ne (hp i) hactive
    have hc : ContinuousAt (fun t : ℝ => a i (p + t • v)) 0 :=
      ((a i).continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousAt
    have he : ∀ᶠ t : ℝ in 𝓝 0, a i (p + t • v) ≤ b i :=
      hc.tendsto.eventually_le_const (by simpa using hslack)
    exact he.filter_mono nhdsWithin_le_nhds

theorem polyhedral_direction_mem_posTangentCone {n r : ℕ}
    (a : Fin r → RealVector n →L[ℝ] ℝ) (b : Fin r → ℝ)
    {p v : RealVector n} (hp : p ∈ affinePolyhedron a b)
    (hv : ∀ i, a i p = b i → a i v ≤ 0) :
    v ∈ posTangentConeAt (affinePolyhedron a b) p :=
  mem_posTangentConeAt_of_frequently_mem (polyhedral_feasible_small_steps a b hp hv).frequently

/-- The actual full derivative at a constrained minimum is nonnegative on
every direction satisfying the active rows, including degenerate polyhedra. -/
theorem polyhedral_minimum_directional_nonneg {n r : ℕ}
    (a : Fin r → RealVector n →L[ℝ] ℝ) (b : Fin r → ℝ)
    {f : RealVector n → ℝ} {p : RealVector n} {D : RealVector n →L[ℝ] ℝ}
    (hmin : IsMinimizer (affinePolyhedron a b) f p) (hd : HasFDerivAt f D p)
    (v : RealVector n) (hv : ∀ i, a i p = b i → a i v ≤ 0) : 0 ≤ D v := by
  have hm : IsMinOn f (affinePolyhedron a b) p := isMinOn_iff.mpr hmin.2
  exact hm.localize.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    (polyhedral_direction_mem_posTangentCone a b hmin.1 hv)

def activeAffineRows {n r : ℕ} (a : Fin r → RealVector n →L[ℝ] ℝ)
    (b : Fin r → ℝ) (p : RealVector n) : Fin r → RealVector n →L[ℝ] ℝ := by
  classical
  exact fun i => if a i p = b i then a i else 0

def activeAffineMultipliers {n r : ℕ} (a : Fin r → RealVector n →L[ℝ] ℝ)
    (b : Fin r → ℝ) (p : RealVector n) (mu : Fin r → ℝ) : Fin r → ℝ := by
  classical
  exact fun i => if a i p = b i then mu i else 0

theorem activeAffineMultipliers_sum {n r : ℕ}
    (a : Fin r → RealVector n →L[ℝ] ℝ) (b : Fin r → ℝ)
    (p : RealVector n) (mu : Fin r → ℝ) :
    (∑ i, activeAffineMultipliers a b p mu i • a i) =
      ∑ i, mu i • activeAffineRows a b p i := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a i p = b i <;> simp [activeAffineMultipliers, activeAffineRows, hi]

/-- Finite active-row coefficients are extended by zero to the literal row
family. This algebraic helper is not a multiplier-existence theorem. -/
theorem activeAffineMultipliers_transport {n r : ℕ}
    (a : Fin r → RealVector n →L[ℝ] ℝ) (b : Fin r → ℝ) (p : RealVector n)
    (D : RealVector n →L[ℝ] ℝ) (mu : Fin r → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (hD : D + ∑ i, mu i • activeAffineRows a b p i = 0) :
    (∀ i, 0 ≤ activeAffineMultipliers a b p mu i) ∧
    (∀ i, activeAffineMultipliers a b p mu i * (a i p - b i) = 0) ∧
    D + ∑ i, activeAffineMultipliers a b p mu i • a i = 0 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : a i p = b i <;> simp [activeAffineMultipliers, hi, hmu i]
  · intro i
    by_cases hi : a i p = b i <;> simp [activeAffineMultipliers, hi]
  · rw [activeAffineMultipliers_sum]
    exact hD

theorem polyhedral_minimum_active_dual {n r : ℕ}
    (a : Fin r → RealVector n →L[ℝ] ℝ) (b : Fin r → ℝ)
    {f : RealVector n → ℝ} {p : RealVector n} {D : RealVector n →L[ℝ] ℝ}
    (hmin : IsMinimizer (affinePolyhedron a b) f p) (hd : HasFDerivAt f D p) :
    ∀ v, (∀ i, activeAffineRows a b p i v ≤ 0) → 0 ≤ D v := by
  intro v hv
  apply polyhedral_minimum_directional_nonneg a b hmin hd v
  intro i hi
  simpa [activeAffineRows, hi] using hv i

/-- Every attained differentiable minimum on a finite affine polyhedron has
exact nonnegative row multipliers, with complementarity and stationarity.
Neither strict affine feasibility nor a normal-representation hypothesis is
required. The full-space derivative is supplied at this same minimum. -/
theorem polyhedral_minimum_multipliers {n r : ℕ}
    (a : Fin r → RealVector n →L[ℝ] ℝ) (b : Fin r → ℝ)
    {f : RealVector n → ℝ} {p : RealVector n} {D : RealVector n →L[ℝ] ℝ}
    (hmin : IsMinimizer (affinePolyhedron a b) f p) (hd : HasFDerivAt f D p) :
    ∃ mu : Fin r → ℝ, (∀ i, 0 ≤ mu i) ∧
      (∀ i, mu i * (a i p - b i) = 0) ∧ D + ∑ i, mu i • a i = 0 := by
  obtain ⟨mu, hmu, hD⟩ := finite_normal_representation (activeAffineRows a b p) D
    (polyhedral_minimum_active_dual a b hmin hd)
  exact ⟨activeAffineMultipliers a b p mu,
    activeAffineMultipliers_transport a b p D mu hmu hD⟩

namespace PolyhedralNormalControls

def coord : RealVector 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0

def signRows (_ : Fin 1) : RealVector 1 →L[ℝ] ℝ := -coord

theorem sign_minimum :
    IsMinimizer (affinePolyhedron signRows (fun _ => 0)) coord 0 := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [signRows]
  · intro q hq
    have h := hq 0
    simpa [signRows] using h

def oppositeRows (i : Fin 2) : RealVector 1 →L[ℝ] ℝ :=
  if i = 0 then coord else -coord

theorem opposite_minimum :
    IsMinimizer (affinePolyhedron oppositeRows (fun _ => 0)) coord 0 := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [oppositeRows]
  · intro q hq
    have h := hq 1
    simpa [oppositeRows] using h

theorem opposite_rows_not_strict :
    ¬ ∃ p : RealVector 1, ∀ i, oppositeRows i p < 0 := by
  rintro ⟨p, hp⟩
  have h0 := hp 0
  have h1 := hp 1
  norm_num [oppositeRows] at h0 h1
  linarith

def zeroDimensionRows (_ : Fin 2) : RealVector 0 →L[ℝ] ℝ := 0
def zeroDimensionBounds (i : Fin 2) : ℝ := if i = 0 then 0 else 1

theorem zero_dimension_minimum :
    IsMinimizer (affinePolyhedron zeroDimensionRows zeroDimensionBounds)
      (fun _ => (0 : ℝ)) 0 := by
  refine ⟨?_, fun _ _ => le_rfl⟩
  intro i
  fin_cases i <;> norm_num [zeroDimensionRows, zeroDimensionBounds]

/-- The coefficient is derived by the normal theorem; its value one checks
the sign orientation for minimizing x subject to -x≤0. -/
theorem one_dimensional_sign_control :
    ∃ mu : Fin 1 → ℝ, (∀ i, 0 ≤ mu i) ∧ mu 0 = 1 ∧
      coord + ∑ i, mu i • signRows i = 0 := by
  obtain ⟨mu, hmu, _, hD⟩ := polyhedral_minimum_multipliers signRows (fun _ => 0)
    sign_minimum coord.hasFDerivAt
  refine ⟨mu, hmu, ?_, hD⟩
  have he := congrArg (fun L : RealVector 1 →L[ℝ] ℝ => L (fun _ => 1)) hD
  norm_num [signRows, coord, Fin.sum_univ_one] at he
  linarith

/-- Opposite active rows have no strict affine point, but the theorem supplies
a nonzero normal: the two nonnegative coefficients differ by one. -/
theorem opposite_rows_normal_control :
    (¬ ∃ p : RealVector 1, ∀ i, oppositeRows i p < 0) ∧
    ∃ mu : Fin 2 → ℝ, (∀ i, 0 ≤ mu i) ∧ mu 1 - mu 0 = 1 ∧
      coord + ∑ i, mu i • oppositeRows i = 0 := by
  obtain ⟨mu, hmu, _, hD⟩ := polyhedral_minimum_multipliers oppositeRows (fun _ => 0)
    opposite_minimum coord.hasFDerivAt
  refine ⟨opposite_rows_not_strict, mu, hmu, ?_, hD⟩
  have he := congrArg (fun L : RealVector 1 →L[ℝ] ℝ => L (fun _ => 1)) hD
  norm_num [oppositeRows, coord, Fin.sum_univ_two] at he
  linarith

/-- Empty rows reduce the conclusion to ambient Fermat, via the same normal
theorem. This imposes no nonzero-dimension assumption. -/
theorem empty_rows_fermat {n : ℕ} {f : RealVector n → ℝ} {p : RealVector n}
    {D : RealVector n →L[ℝ] ℝ} (hmin : IsMinimizer Set.univ f p)
    (hd : HasFDerivAt f D p) : D = 0 := by
  have hm : IsMinimizer (affinePolyhedron (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)) f p := by
    simpa [affinePolyhedron] using hmin
  obtain ⟨mu, _, _, hD⟩ := polyhedral_minimum_multipliers
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) hm hd
  simpa using hD

/-- Zero ambient dimension and an active/inactive pair of zero rows are valid
inputs. The inactive row receives coefficient zero by complementarity. -/
theorem zero_dimension_normal_control :
    ∃ mu : Fin 2 → ℝ, (∀ i, 0 ≤ mu i) ∧ mu 1 = 0 ∧
      (0 : RealVector 0 →L[ℝ] ℝ) + ∑ i, mu i • zeroDimensionRows i = 0 := by
  obtain ⟨mu, hmu, hc, hD⟩ := polyhedral_minimum_multipliers
    zeroDimensionRows zeroDimensionBounds zero_dimension_minimum (hasFDerivAt_const 0 0)
  refine ⟨mu, hmu, ?_, hD⟩
  have h := hc 1
  simpa [zeroDimensionRows, zeroDimensionBounds] using h

end PolyhedralNormalControls

end Chapter02

#print axioms Chapter02.polyhedral_feasible_small_steps
#print axioms Chapter02.polyhedral_direction_mem_posTangentCone
#print axioms Chapter02.polyhedral_minimum_directional_nonneg
#print axioms Chapter02.polyhedral_minimum_multipliers
#print axioms Chapter02.PolyhedralNormalControls.one_dimensional_sign_control
#print axioms Chapter02.PolyhedralNormalControls.opposite_rows_normal_control
#print axioms Chapter02.PolyhedralNormalControls.empty_rows_fermat
#print axioms Chapter02.PolyhedralNormalControls.zero_dimension_normal_control
