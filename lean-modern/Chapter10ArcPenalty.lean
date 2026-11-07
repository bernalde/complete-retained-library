module

public import Chapter10ArcMatrix
public import Chapter10IntegerPenalty

@[expose] public section

/-! Exactness and full QUBO identity for the literal time-indexed arc model,
using the actual signed integer row matrix and all repeated cost coordinates. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Algebra
variable {n k : ℕ}

def arcPenalty (D : Data n) (T : Grid k) (x : Assignment n k) : ℝ :=
  integerPenalty (rowMatrix D T) rowRhs (fun e => Chapter10.bit (x e))

def arcEnergy (D : Data n) (T : Grid k) (ρ : ℝ) (x : Assignment n k) : ℝ :=
  objective D x + ρ * arcPenalty D T x

theorem arc_penalty_zero_iff (D : Data n) (T : Grid k) (x : Assignment n k) :
    arcPenalty D T x = 0 ↔ Feasible D T x := by
  have h := integer_penalty_zero_iff (rowMatrix D T) rowRhs (fun e => Chapter10.bit (x e)) (binary_bit x)
  exact h.trans (matrix_iff_feasible D T x)

theorem arc_penalty_gap (D : Data n) (T : Grid k) (x : Assignment n k)
    (hn : ¬ Feasible D T x) : 1 ≤ arcPenalty D T x := by
  apply integer_penalty_gap (rowMatrix D T) rowRhs _ (binary_bit x)
  intro h
  exact hn ((matrix_iff_feasible D T x).mp h)

theorem actual_arc_cost_range (D : Data n) (x y : Assignment n k) :
    objective D x - objective D y ≤ ∑ e : Edge n k, |coordinateCost D e| :=
  finite_binary_cost_range_from_accepted (coordinateCost D) (fun e => Chapter10.bit (x e))
    (fun e => Chapter10.bit (y e)) (binary_bit x) (binary_bit y)

theorem arc_every_bad_gt (D : Data n) (T : Grid k) (ρ : ℝ)
    (hρ : (∑ e : Edge n k, |coordinateCost D e|) < ρ)
    (x y : Assignment n k) (hbad : ¬ Feasible D T x) (hgood : Feasible D T y) :
    arcEnergy D T ρ y < arcEnergy D T ρ x := by
  exact penalty_every_bad_gt Set.univ (Feasible D T) (objective D) (arcPenalty D T)
    (∑ e : Edge n k, |coordinateCost D e|) ρ
    (Finset.sum_nonneg (fun e _ => abs_nonneg _)) hρ
    (fun z _ hz => (arc_penalty_zero_iff D T z).mpr hz)
    (fun z _ hz => arc_penalty_gap D T z hz)
    (fun z _ w _ => actual_arc_cost_range D z w)
    x y (Set.mem_univ _) hbad (Set.mem_univ _) hgood

theorem arc_minimizers_exact (D : Data n) (T : Grid k) (domain : Set (Assignment n k))
    (ρ : ℝ) (hρ : (∑ e : Edge n k, |coordinateCost D e|) < ρ) (x : Assignment n k) :
    (IsMinOn domain (arcEnergy D T ρ) x ∧ ∃ y ∈ domain, Feasible D T y) ↔
      IsMinOn {y | y ∈ domain ∧ Feasible D T y} (objective D) x := by
  exact penalty_minimizers_exact domain (Feasible D T) (objective D) (arcPenalty D T)
    (∑ e : Edge n k, |coordinateCost D e|) ρ
    (Finset.sum_nonneg (fun e _ => abs_nonneg _)) hρ
    (fun z _ hz => (arc_penalty_zero_iff D T z).mpr hz)
    (fun z _ hz => arc_penalty_gap D T z hz)
    (fun z _ w _ => actual_arc_cost_range D z w) x

def arcQUBO (D : Data n) (T : Grid k) (ρ : ℝ) : Edge n k → Edge n k → ℝ :=
  quboMatrix (fun r e => (rowMatrix D T r e : ℝ)) (fun r => (rowRhs r : ℝ)) (coordinateCost D) ρ

theorem actual_arc_qubo_identity (D : Data n) (T : Grid k) (ρ : ℝ) (x : Assignment n k) :
    arcEnergy D T ρ x = quadratic (arcQUBO D T ρ) (fun e => Chapter10.bit (x e)) + ρ * (n : ℝ) := by
  have h := full_qubo_identity (fun r e => (rowMatrix D T r e : ℝ))
    (fun r => (rowRhs r : ℝ)) (coordinateCost D) (fun e => Chapter10.bit (x e)) ρ (binary_bit x)
  have hc : (∑ r : Row n k, (rowRhs r : ℝ)^2) = n := by
    simp [Row,rowRhs,Fintype.sum_sum_type]
  simpa only [arcEnergy,arcPenalty,integerPenalty,arcQUBO,objective,coordinateCost,
    linearCost,hc] using h

end Chapter10.Routing.Arc
