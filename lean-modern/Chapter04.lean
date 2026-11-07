module

public import Chapter02
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Chapter 4 local statements and explicit repairs. Actual trial centers and
fixed-integer NLP outputs are distinct. No solver, KKT or convergence oracle
is asserted. The compactness result is conditional on displayed geometric
bounds and monotonicity, rather than a certificate for Algorithm 3. -/
noncomputable section
open Filter
open scoped Topology
namespace Chapter04

theorem normalized_halfspace_ball_valid {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a x p z : E) (v r : ℝ)
    (hcut : v + inner ℝ a (x - p) + r * ‖a‖ ≤ 0)
    (hz : ‖z - x‖ ≤ r) : v + inner ℝ a (z - p) ≤ 0 := by
  have hc := real_inner_le_norm a (z - x)
  have hm := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
  have he : (inner ℝ a (z - p) : ℝ) = inner ℝ a (x - p) + inner ℝ a (z - x) := by
    rw [← inner_add_right]; congr 1; abel
  rw [he]
  nlinarith

theorem separating_cut_radius_le_distance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a x p : E) (v r : ℝ) (ha : a ≠ 0) (hv : 0 ≤ v)
    (hcut : v + inner ℝ a (x - p) + r * ‖a‖ ≤ 0) : r ≤ ‖x - p‖ := by
  have hab := abs_real_inner_le_norm a (x - p)
  have hl := neg_abs_le (inner ℝ a (x - p) : ℝ)
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr ha
  nlinarith

theorem compact_radius_tendsto_zero {E : Type*} [MetricSpace E]
    {K : Set E} (hK : IsCompact K) (x : ℕ → E) (r : ℕ → ℝ)
    (hx : ∀ n, x n ∈ K) (hr : ∀ n, 0 ≤ r n) (hm : Antitone r)
    (hp : ∀ j i, j < i → r i ≤ dist (x i) (x j)) :
    Tendsto r atTop (𝓝 0) := by
  rcases hK.tendsto_subseq hx with ⟨a, _, φ, hφ, ht⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  rcases Metric.tendsto_atTop.mp ht (ε / 2) (by linarith) with ⟨N, hN⟩
  have h1 := hN N (le_refl N)
  have h2 := hN (N + 1) (Nat.le_succ N)
  have hd : dist (x (φ (N + 1))) (x (φ N)) < ε := by
    have hh := dist_triangle (x (φ (N + 1))) a (x (φ N))
    rw [dist_comm a] at hh
    change dist (x (φ N)) a < ε / 2 at h1
    change dist (x (φ (N + 1))) a < ε / 2 at h2
    linarith
  refine ⟨φ (N + 1), ?_⟩
  intro i hi
  have hri := hm hi
  have hpair := hp (φ N) (φ (N + 1)) (hφ (Nat.lt_succ_self N))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hr i)]
  linarith

theorem exact_master_radius_lower_bound {A : Type*} (S : Set (A × ℝ))
    (candidate optimum : A × ℝ) (hc : candidate ∈ S)
    (hmax : ∀ z ∈ S, z.2 ≤ optimum.2) : candidate.2 ≤ optimum.2 := hmax candidate hc

theorem positive_radius_strict_improvement (value incumbent r normc : ℝ)
    (hr : 0 < r) (hc : 0 < normc)
    (h : value + r * normc ≤ incumbent) : value < incumbent := by
  have := mul_pos hr hc
  linarith

theorem zero_objective_no_strict_improvement :
    (0 : ℝ) + 1 * 0 ≤ 0 ∧ ¬ (0 : ℝ) < 0 := by norm_num

theorem empty_seed_no_radius_max {A : Type*} (S : Set A) (hS : S.Nonempty) :
    ¬ ∃ z : A × ℝ, z.1 ∈ S ∧ ∀ w : A × ℝ, w.1 ∈ S → w.2 ≤ z.2 := by
  rintro ⟨z, _, hz⟩
  rcases hS with ⟨a, ha⟩
  have hh := hz (a, z.2 + 1) ha
  dsimp at hh
  linarith

def OverwriteMaster (x r : ℝ) : Prop :=
  -3 ≤ x ∧ x ≤ 3 ∧ -1 / 4 + r ≤ x ∧ x + r ≤ 9 / 4

theorem overwrite_trial_master_optimal : OverwriteMaster 1 (5 / 4) ∧
    ∀ x r : ℝ, OverwriteMaster x r → r ≤ 5 / 4 := by
  constructor
  · norm_num [OverwriteMaster]
  · intro x r h; dsimp [OverwriteMaster] at h; linarith [h.2.2.1, h.2.2.2]

theorem overwritten_distance_violation :
    (5 / 4 : ℝ) > |(0 : ℝ) - (-1)| := by norm_num

theorem quadratic_source_cuts :
    ((-1 : ℝ) - 1)^2 - 1 = 3 ∧ (3 - 1 : ℝ)^2 - 1 = 3 ∧
    (∀ x : ℝ, 3 - 4 * (x + 1) ≤ 0 ↔ -1 / 4 ≤ x) ∧
    (∀ x : ℝ, 3 + 4 * (x - 3) ≤ 0 ↔ x ≤ 9 / 4) := by
  constructor; · norm_num
  constructor; · norm_num
  constructor <;> intro x <;> constructor <;> intro h <;> linarith

theorem quadratic_fixed_minimizer :
    Chapter02.IsMinimizer {x : ℝ | -3 ≤ x ∧ x ≤ 3 ∧ (x - 1)^2 - 1 ≤ 0}
      (fun x => x) 0 := by
  constructor
  · norm_num
  · intro x hx; change 0 ≤ x; nlinarith [hx.2.2, sq_nonneg x]

theorem strict_interpolation (a gs gb bound : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hs : gs ≤ 0) (hb : gb < 0) (hg : bound ≤ a * gs + (1-a)*gb) : bound < 0 := by
  have h1 := mul_nonpos_of_nonneg_of_nonpos ha hs
  have h2 := mul_neg_of_pos_of_neg (by linarith : 0 < 1-a) hb
  linarith

theorem epsilon_interpolation (ε gap : ℝ) (hε : 0 < ε) (hg : ε ≤ gap) :
    0 ≤ 1 - ε / (2 * gap) ∧ 1 - ε / (2 * gap) < 1 ∧
    (1 - (1 - ε / (2 * gap))) * gap = ε / 2 := by
  have hp : 0 < gap := lt_of_lt_of_le hε hg
  constructor
  · have hh : ε / (2 * gap) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  constructor
  · have hh : 0 < ε / (2 * gap) := by positivity
    linarith
  · field_simp; ring

def PositiveStep (e : ℝ) : ℝ := e^2 / (4 * (1 + e))

theorem positive_step_pos (e : ℝ) (h : 0 < e) : 0 < PositiveStep e := by
  unfold PositiveStep; positivity

theorem positive_step_stays_infeasible (e : ℝ) (h : 0 < e) :
    (1 + PositiveStep e)^2 - 1 > 0 := by
  have := positive_step_pos e h
  nlinarith [sq_nonneg (PositiveStep e)]

theorem positive_step_latest_row (e : ℝ) (h : 0 < e) :
    (1 + e)^2 - 1 + 2*(1+e)*((1+PositiveStep e)-(1+e)) +
      PositiveStep e * (2*(1+e)) = 0 := by
  unfold PositiveStep
  have hn : 1+e ≠ 0 := by linarith
  field_simp; ring

theorem nonlinear_zero_gradient_cut :
    ∀ x r : ℝ, (0 : ℝ)^2 + (2*0)*(x-0) + r*|2*0| ≤ 0 := by
  intro x r; norm_num

end Chapter04

#print axioms Chapter04.normalized_halfspace_ball_valid
#print axioms Chapter04.separating_cut_radius_le_distance
#print axioms Chapter04.compact_radius_tendsto_zero
#print axioms Chapter04.exact_master_radius_lower_bound
#print axioms Chapter04.positive_radius_strict_improvement
#print axioms Chapter04.zero_objective_no_strict_improvement
#print axioms Chapter04.empty_seed_no_radius_max
#print axioms Chapter04.overwrite_trial_master_optimal
#print axioms Chapter04.overwritten_distance_violation
#print axioms Chapter04.quadratic_source_cuts
#print axioms Chapter04.quadratic_fixed_minimizer
#print axioms Chapter04.strict_interpolation
#print axioms Chapter04.epsilon_interpolation
#print axioms Chapter04.positive_step_pos
#print axioms Chapter04.positive_step_stays_infeasible
#print axioms Chapter04.positive_step_latest_row
#print axioms Chapter04.nonlinear_zero_gradient_cut
