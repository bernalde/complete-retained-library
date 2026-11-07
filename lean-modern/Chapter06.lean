module

public import Chapter02Model
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Chapter6 local source-wired bounds, level geometry and explicit finite KKT
algebra. KKT existence and solver correctness are not axioms: the actual finite
stationarity, sign and complementarity equations are theorem hypotheses.
Source objective functions are supplied separately from Chapter02's linear
objective; its typed feasibility/selected nonlinear cuts are reused unchanged. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter06

def Level (LB UB α : ℝ) : ℝ := (1-α)*UB + α*LB

theorem level_bounds (LB UB α : ℝ) (h : LB ≤ UB) (ha : 0 ≤ α) (ha1 : α ≤ 1) :
    LB ≤ Level LB UB α ∧ Level LB UB α ≤ UB := by
  unfold Level
  have h1 := mul_nonneg (sub_nonneg.mpr h) ha
  have h2 := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ha1)
  constructor <;> nlinarith

theorem level_strict_upper (LB UB α : ℝ) (h : LB < UB) (ha : 0 < α) :
    Level LB UB α < UB := by
  have := mul_pos (sub_pos.mpr h) ha
  unfold Level; nlinarith

theorem level_at_one (LB UB : ℝ) : Level LB UB 1 = LB := by simp [Level]

theorem weighted_lagrangian_convex {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {l : ℕ} (S : Set E) (f : E → ℝ) (g : Fin l → E → ℝ) (lam : Fin l → ℝ)
    (hf : ConvexOn ℝ S f) (hg : ∀ j, ConvexOn ℝ S (g j))
    (hlam : ∀ j, 0 ≤ lam j) :
    ConvexOn ℝ S (fun x => f x + ∑ j, lam j * g j x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hfs := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hfs ⊢
  have hgs : (∑ j, lam j * g j (a • x + b • y)) ≤
      a*(∑ j, lam j*g j x) + b*(∑ j, lam j*g j y) := by
    have h : (∑ j, lam j * g j (a • x + b • y)) ≤
        ∑ j, (a*(lam j*g j x)+b*(lam j*g j y)) := by
      apply Finset.sum_le_sum
      intro j _
      have hj := mul_le_mul_of_nonneg_left ((hg j).2 hx hy ha hb hab) (hlam j)
      simp only [smul_eq_mul] at hj
      calc
        lam j*g j (a • x+b • y) ≤ lam j*(a*g j x+b*g j y) := hj
        _ = a*(lam j*g j x)+b*(lam j*g j y) := by ring
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h
  calc
    f (a • x+b • y)+(∑ j, lam j*g j (a • x+b • y)) ≤
        (a*f x+b*f y)+(a*(∑ j, lam j*g j x)+b*(∑ j, lam j*g j y)) := add_le_add hfs hgs
    _ = a*(f x+∑ j, lam j*g j x)+b*(f y+∑ j, lam j*g j y) := by ring

def EpigraphMaster {n m l r k : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (c : TangentFamily n m l k)
    (Df : Fin k → Point n m →L[ℝ] ℝ) (S : Set (Point n m)) :
    Set (Point n m × ℝ) :=
  {p | p.1 ∈ d.masterOn c S ∧ ∀ i, f (c.origin i) + Df i (p.1-c.origin i) ≤ p.2}

theorem source_feasible_epigraph_in_master {n m l r k : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (c : TangentFamily n m l k)
    (Df : Fin k → Point n m →L[ℝ] ℝ) (S : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ S (d.g j)) (hf : ConvexOn ℝ S f)
    (ha : ∀ i, c.origin i ∈ S)
    (hdg : ∀ i j, j ∈ c.selected i → HasFDerivAt (d.g j) (c.derivative i j) (c.origin i))
    (hdf : ∀ i, HasFDerivAt f (Df i) (c.origin i))
    {q : Point n m} (hq : q ∈ d.feasibleOn S) :
    (q,f q) ∈ EpigraphMaster d f c Df S := by
  refine ⟨source_feasible_subset_master d c S hg ha hdg hq, ?_⟩
  intro i
  exact tangent_underestimator_on hf (ha i) hq.1.1.1 (hdf i)

theorem source_epigraph_master_lower_bound {n m l r k : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (c : TangentFamily n m l k)
    (Df : Fin k → Point n m →L[ℝ] ℝ) (S : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ S (d.g j)) (hf : ConvexOn ℝ S f)
    (ha : ∀ i, c.origin i ∈ S)
    (hdg : ∀ i j, j ∈ c.selected i → HasFDerivAt (d.g j) (c.derivative i j) (c.origin i))
    (hdf : ∀ i, HasFDerivAt f (Df i) (c.origin i))
    {p : Point n m × ℝ} (hp : IsMinimizer (EpigraphMaster d f c Df S) Prod.snd p) :
    IsLowerBound (d.feasibleOn S) f p.2 := by
  intro q hq
  exact hp.2 (q,f q) (source_feasible_epigraph_in_master d f c Df S hg hf ha hdg hdf hq)

theorem master_candidate_satisfies_level {E : Type*} (S : Set (E × ℝ))
    (p : E × ℝ) (LB UB α : ℝ) (hp : p ∈ S) (hv : p.2 = LB)
    (h : LB ≤ UB) (ha : 0 ≤ α) (ha1 : α ≤ 1) :
    p ∈ {z ∈ S | z.2 ≤ Level LB UB α} := by
  exact ⟨hp, hv ▸ (level_bounds LB UB α h ha ha1).1⟩

theorem trust_minimizer_is_projection_minimizer {E : Type*}
    (S : Set E) (cost distance : E → ℝ) (level : ℝ) (p q : E)
    (hp : IsMinimizer {z ∈ S | cost z ≤ level} distance p)
    (hq : IsMinimizer {z ∈ S | distance z ≤ distance p} cost q) :
    IsMinimizer {z ∈ S | cost z ≤ level} distance q := by
  have hpmem : p ∈ {z ∈ S | distance z ≤ distance p} := ⟨hp.1.1, le_refl _⟩
  have hqc : cost q ≤ level := (hq.2 p hpmem).trans hp.1.2
  have hqmem : q ∈ {z ∈ S | cost z ≤ level} := ⟨hq.1.1, hqc⟩
  have heq : distance q = distance p := le_antisymm hq.1.2 (hp.2 q hqmem)
  refine ⟨hqmem, ?_⟩
  intro z hz
  rw [heq]; exact hp.2 z hz

theorem stationarity_dot_zero {n l r : ℕ} (gf : Fin n → ℝ)
    (gg : Fin l → Fin n → ℝ) (A : Fin r → Fin n → ℝ)
    (lam : Fin l → ℝ) (γ : Fin r → ℝ) (Δ : Fin n → ℝ)
    (hs : ∀ i, gf i + (∑ j, lam j * gg j i) + (∑ row, γ row * A row i) = 0) :
    gf ⬝ᵥ Δ + (∑ j, lam j * (gg j ⬝ᵥ Δ)) +
      (∑ row, γ row * (A row ⬝ᵥ Δ)) = 0 := by
  have hv : gf + (fun i => lam ⬝ᵥ (fun j => gg j i)) +
      (fun i => γ ⬝ᵥ (fun row => A row i)) = 0 := by
    funext i
    exact hs i
  have hh : (gf + (fun i => lam ⬝ᵥ (fun j => gg j i)) +
      (fun i => γ ⬝ᵥ (fun row => A row i))) ⬝ᵥ Δ = 0 := by rw [hv, zero_dotProduct]
  rw [add_dotProduct, add_dotProduct] at hh
  rw [dotProduct_assoc lam Δ (fun j i => gg j i),
    dotProduct_assoc γ Δ (fun row i => A row i)] at hh
  exact hh

theorem fixed_fiber_kkt_master_lower_bound {n l r : ℕ} (f0 μ : ℝ)
    (gf : Fin n → ℝ) (v : Fin l → ℝ) (gg : Fin l → Fin n → ℝ)
    (b : Fin r → ℝ) (A : Fin r → Fin n → ℝ)
    (lam : Fin l → ℝ) (γ : Fin r → ℝ) (Δ : Fin n → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hγ : ∀ row, 0 ≤ γ row)
    (hcompg : ∀ j, lam j * v j = 0) (hcompl : ∀ row, γ row * b row = 0)
    (hs : ∀ i, gf i + (∑ j, lam j * gg j i) + (∑ row, γ row * A row i) = 0)
    (hcut : ∀ j, lam j ≠ 0 → v j + gg j ⬝ᵥ Δ ≤ 0)
    (hlin : ∀ row, b row + A row ⬝ᵥ Δ ≤ 0)
    (hobj : f0 + gf ⬝ᵥ Δ ≤ μ) : f0 ≤ μ := by
  have hgs : (∑ j, lam j * (gg j ⬝ᵥ Δ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : lam j = 0
    · simp [hj]
    · have h := mul_le_mul_of_nonneg_left (hcut j hj) (hlam j)
      rw [mul_add, mul_zero, hcompg] at h
      simpa using h
  have hls : (∑ row, γ row * (A row ⬝ᵥ Δ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro row _
    have h := mul_le_mul_of_nonneg_left (hlin row) (hγ row)
    rw [mul_add, mul_zero, hcompl] at h
    simpa using h
  have hz := stationarity_dot_zero gf gg A lam γ Δ hs
  linarith

theorem level_excludes_old_fiber (f0 μ LB UB α : ℝ) (hold : f0 ≤ μ)
    (hu : UB ≤ f0) (hl : μ ≤ Level LB UB α) (hgap : LB < UB) (ha : 0 < α) : False := by
  have := level_strict_upper LB UB α hgap ha
  linarith

theorem restoration_rows_exclude_fiber {n l r : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (v : Fin l → ℝ) (gg : Fin l → Fin n → ℝ)
    (b : Fin r → ℝ) (A : Fin r → Fin n → ℝ)
    (lam : Fin l → ℝ) (γ : Fin r → ℝ) (Δ : Fin n → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hγ : ∀ row, 0 ≤ γ row) (hsum : ∑ j, lam j = 1)
    (hcompg : ∀ j, lam j * (v j-ρ) = 0) (hcompl : ∀ row, γ row * b row = 0)
    (hs : ∀ i, (∑ j, lam j * gg j i) + (∑ row, γ row * A row i) = 0)
    (hcut : ∀ j, lam j ≠ 0 → v j + gg j ⬝ᵥ Δ ≤ 0)
    (hlin : ∀ row, b row + A row ⬝ᵥ Δ ≤ 0) : False := by
  have hval : (∑ j, lam j * v j) = ρ := by
    have heq : ∀ j, lam j * v j = lam j * ρ := by
      intro j; have h := hcompg j; nlinarith
    simp_rw [heq]
    rw [← Finset.sum_mul, hsum, one_mul]
  have hgs : (∑ j, lam j * (v j + gg j ⬝ᵥ Δ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : lam j = 0
    · simp [hj]
    · exact mul_nonpos_of_nonneg_of_nonpos (hlam j) (hcut j hj)
  have hls : (∑ row, γ row * (A row ⬝ᵥ Δ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro row _
    have h := mul_le_mul_of_nonneg_left (hlin row) (hγ row)
    rw [mul_add, mul_zero, hcompl] at h
    simpa using h
  have hz := stationarity_dot_zero (fun _ => 0) gg A lam γ Δ (by intro i; simpa using hs i)
  simp only [zero_dotProduct', zero_add] at hz
  simp_rw [mul_add] at hgs
  rw [Finset.sum_add_distrib, hval] at hgs
  linarith

theorem no_infinite_distinct_integer_box {m : ℕ} (lo hi : RealVector m)
    (y : ℕ → IntVector m) (hy : ∀ i, y i ∈ IntegerBox lo hi) :
    ¬ Function.Injective y := by
  intro hinj
  have hfinite : (Set.range y).Finite := (integerBox_finite lo hi).subset (by
    rintro z ⟨i,rfl⟩; exact hy i)
  exact (Set.infinite_range_of_injective hinj) hfinite

def bit (b : Bool) : ℝ := if b then 1 else 0
abbrev TrustToy := ℝ × Bool × Bool
def toyCost (p : TrustToy) : ℝ := -bit p.2.1 - 2*bit p.2.2
def toyDistance (p : TrustToy) : ℝ := p.1^2 + (bit p.2.1)^2 + (bit p.2.2)^2
def toyBase : Set TrustToy := {p | -1 ≤ p.1 ∧ p.1 ≤ 1}
def toyLevel : Set TrustToy := {p ∈ toyBase | toyCost p ≤ -1/2}
def toyTrust : Set TrustToy := {p ∈ toyBase | toyDistance p ≤ 1}
def toyA : TrustToy := (0,true,false)
def toyB : TrustToy := (0,false,true)

theorem toy_projection_A_optimal : IsMinimizer toyLevel toyDistance toyA := by
  constructor
  · norm_num [toyLevel,toyBase,toyCost,bit,toyA]
  · rintro ⟨x,b1,b2⟩ hp
    cases b1 <;> cases b2 <;> simp [toyLevel,toyBase,toyCost,toyDistance,bit,toyA] at *
    all_goals nlinarith [sq_nonneg x]

theorem toy_trust_B_optimal : IsMinimizer toyTrust toyCost toyB := by
  constructor
  · norm_num [toyTrust,toyBase,toyDistance,bit,toyB]
  · rintro ⟨x,b1,b2⟩ hp
    cases b1 <;> cases b2 <;> simp [toyTrust,toyBase,toyCost,toyDistance,bit,toyB] at *
    all_goals nlinarith [sq_nonneg x]

theorem toy_projection_A_not_trust_optimal : ¬ IsMinimizer toyTrust toyCost toyA := by
  intro h
  have hh := h.2 toyB toy_trust_B_optimal.1
  norm_num [toyCost,toyA,toyB,bit] at hh

def toyQ (y : ℝ) : ℝ := 8*y^2 - 4*y
theorem unlevelled_taylor_stagnates :
    ∀ y : ℤ, 0 ≤ y → y ≤ 2 → toyQ 0 ≤ toyQ y := by
  intro y hy hy2
  interval_cases y <;> norm_num [toyQ]

theorem levelled_taylor_selects_one :
    ∀ y : ℤ, 1 ≤ y → y ≤ 2 → toyQ 1 ≤ toyQ y := by
  intro y hy hy2
  interval_cases y <;> norm_num [toyQ]

theorem literal_optimizer_interpolation_fails : (1/4 : ℝ)*2 ≠ 1 := by norm_num

theorem initial_incumbent_violates_printed_constraint :
    (1 : ℝ)/(529/100) + 1/3 - Real.sqrt (1587/100) > -4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1587/100 by norm_num)
  have hn := Real.sqrt_nonneg (1587/100 : ℝ)
  have hb : Real.sqrt (1587/100 : ℝ) < 4 := by nlinarith
  norm_num at *
  linarith

theorem non_kkt_seed_allows_old_integer :
    Level (-3) 1 (1/2 : ℝ) = -1 ∧ (1 : ℝ) + 2*(0-1) ≤ -1 ∧
      -1 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ)^2 < 1 := by norm_num [Level]

theorem shifted_diagonal_psd :
    ∀ x y : ℝ, (-1+|-1|)*x^2 + (2+|-1|)*y^2 ≥ 0 := by
  intro x y; norm_num; positivity

theorem shift_does_not_make_positive_definite :
    (-1+|-1| : ℝ)*(1:ℝ)^2 + (2+|-1|)*(0:ℝ)^2 = 0 ∧ (1:ℝ) ≠ 0 := by norm_num

theorem relative_gap_denominator_positive (UB : ℝ) : 0 < |UB| + (1/10^10 : ℝ) := by
  exact add_pos_of_nonneg_of_pos (abs_nonneg UB) (by norm_num)

end Chapter06

#print axioms Chapter06.level_bounds
#print axioms Chapter06.level_strict_upper
#print axioms Chapter06.level_at_one
#print axioms Chapter06.weighted_lagrangian_convex
#print axioms Chapter06.source_feasible_epigraph_in_master
#print axioms Chapter06.source_epigraph_master_lower_bound
#print axioms Chapter06.master_candidate_satisfies_level
#print axioms Chapter06.trust_minimizer_is_projection_minimizer
#print axioms Chapter06.stationarity_dot_zero
#print axioms Chapter06.fixed_fiber_kkt_master_lower_bound
#print axioms Chapter06.level_excludes_old_fiber
#print axioms Chapter06.restoration_rows_exclude_fiber
#print axioms Chapter06.no_infinite_distinct_integer_box
#print axioms Chapter06.toy_projection_A_optimal
#print axioms Chapter06.toy_trust_B_optimal
#print axioms Chapter06.toy_projection_A_not_trust_optimal
#print axioms Chapter06.unlevelled_taylor_stagnates
#print axioms Chapter06.levelled_taylor_selects_one
#print axioms Chapter06.literal_optimizer_interpolation_fails
#print axioms Chapter06.initial_incumbent_violates_printed_constraint
#print axioms Chapter06.non_kkt_seed_allows_old_integer
#print axioms Chapter06.shifted_diagonal_psd
#print axioms Chapter06.shift_does_not_make_positive_definite
#print axioms Chapter06.relative_gap_denominator_positive
