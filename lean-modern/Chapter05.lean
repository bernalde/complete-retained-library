module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Scoped algebraic certificates for Chapter 5. Analytic hypotheses and
source-to-expression translations are independently reviewed outside this file.
No source quotient is evaluated when its denominator is zero. -/
namespace Chapter05
noncomputable section

def rankOneQuadratic (x y : ℝ) : ℝ := 2*x^2 + 4*x*y + 2*y^2

theorem rankOne_psd (x y : ℝ) : 0 ≤ rankOneQuadratic x y := by
  have h : rankOneQuadratic x y = 2 * (x+y)^2 := by
    unfold rankOneQuadratic
    ring
  rw [h]
  nlinarith [sq_nonneg (x+y)]

theorem rankOne_nonzero_entries : (2 : ℝ) ≠ 0 := by norm_num

theorem rankOne_null_direction : rankOneQuadratic 1 (-1) = 0 := by
  norm_num [rankOneQuadratic]

theorem rankOne_zero_remainder : ((1 : ℝ) + (-1))^2 = 0 := by norm_num

theorem underestimator_of_ratio_bound (f t q a : ℝ)
    (hq : 0 ≤ q) (hz : q = 0 → t ≤ f)
    (hp : 0 < q → a / 2 ≤ (f-t) / q) : t + (a/2)*q ≤ f := by
  rcases eq_or_lt_of_le hq with h | h
  · have hq0 : q = 0 := h.symm
    simpa [hq0] using hz hq0
  · have hm := (le_div_iff₀ h).mp (hp h)
    linarith

theorem stronger_than_tangent (t q a : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a) :
    t ≤ t + (a/2)*q := by
  have : 0 ≤ (a/2)*q := mul_nonneg (by linarith) hq
  linarith

def quartic (x : ℝ) : ℝ := x^2 + x^4

theorem quartic_remainder_factor (x : ℝ) :
    quartic x = (2*x^2) * ((1+x^2)/2) := by
  unfold quartic
  ring

theorem quartic_appendix_condition (x : ℝ) (hx : x ≠ 0) :
    4*x*(x^2+x^4) ≠ (2*x^2)*(2*x+4*x^3) := by
  intro h
  have hp : x^5 = 0 := by nlinarith [h]
  exact hx (eq_zero_of_pow_eq_zero hp)

theorem quartic_vertex_cut_fails :
    quartic (1/2) - 2*(1/2 : ℝ)^2 = -3/16 := by
  norm_num [quartic]

def pdQuadratic (x y : ℝ) : ℝ := 2*x^2 + 2*x*y + 2*y^2
def vertexExample (x y : ℝ) : ℝ :=
  pdQuadratic x y * (1/2 + x/1000 + (x^2+y^2)/10000)

theorem pdQuadratic_identity (x y : ℝ) :
    pdQuadratic x y = x^2 + y^2 + (x+y)^2 := by
  unfold pdQuadratic
  ring

theorem vertexExample_gap :
    vertexExample (-1) 0 - (312/625)*pdQuadratic (-1) 0 = -1/5000 := by
  norm_num [vertexExample, pdQuadratic]

theorem vertexExample_corner_values :
    (1/2 + (-1 : ℝ)/1000 + ((-1)^2 + 1^2)/10000 = 312/625) ∧
    (1/2 + (1 : ℝ)/1000 + (1^2 + 1^2)/10000 = 1253/2500) := by
  norm_num

def oaObjective (x y : ℝ) : ℝ := (x+y)^2/10 + x-y
def oaConstraint (x y : ℝ) : ℝ := (x+y-2/5)^4-1/10
def oaConstraintCut (x y : ℝ) : ℝ :=
  16/625-1/10 - (32/125)*(x+y) + (8/25)*(x+y)^2

theorem oa_spurious_point :
    oaConstraintCut 0 1 = -13/1250 ∧
    oaConstraint 0 1 = 37/1250 ∧ oaObjective 0 1 = -9/10 := by
  norm_num [oaConstraintCut, oaConstraint, oaObjective]

theorem oa_constraint_gap_factor (x y : ℝ) :
    oaConstraint x y - oaConstraintCut x y = (x+y)^2 * (x+y-4/5)^2 := by
  unfold oaConstraint oaConstraintCut
  ring

end
end Chapter05

#print axioms Chapter05.rankOne_psd
#print axioms Chapter05.rankOne_nonzero_entries
#print axioms Chapter05.rankOne_null_direction
#print axioms Chapter05.rankOne_zero_remainder
#print axioms Chapter05.underestimator_of_ratio_bound
#print axioms Chapter05.stronger_than_tangent
#print axioms Chapter05.quartic_remainder_factor
#print axioms Chapter05.quartic_appendix_condition
#print axioms Chapter05.quartic_vertex_cut_fails
#print axioms Chapter05.pdQuadratic_identity
#print axioms Chapter05.vertexExample_gap
#print axioms Chapter05.vertexExample_corner_values
#print axioms Chapter05.oa_spurious_point
#print axioms Chapter05.oa_constraint_gap_factor
