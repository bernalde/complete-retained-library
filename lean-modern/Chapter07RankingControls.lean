module

public import Chapter06LevelControlTrace
public import Chapter07SevenRankings

@[expose] public section

/-! Exact auxiliary-domain controls for the seven Chapter7 rankings.
These are invented exact mathematical witnesses, not numerical reruns.
The accepted Chapter6 seed is feasible and deliberately unpolished. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter06.Level Chapter06.LevelControl
namespace Chapter07.RankingControls

def level : Set (P × ℝ) := levelSet d seed [] (-5) (1/2)

theorem level_iff (z : P × ℝ) : z ∈ level ↔
    z.1 ∈ d.mixed ∧ 2*z.1.1 0-2*z.1.2 0-1 ≤ z.2 ∧ z.2 ≤ -2 := by
  unfold level levelSet
  simp only [Set.mem_setOf_eq]
  rw [master0_iff]
  norm_num [Chapter06.Level, incumbent, seed_value, and_assoc]

theorem level_bounds {z : P × ℝ} (hz : z ∈ level) :
    0 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1 ∧ 1 ≤ z.1.2 0 ∧ z.1.2 0 ≤ 2 ∧
      z.1.1 0+1/2 ≤ z.1.2 0 := by
  obtain ⟨hm, ht, hc⟩ := (level_iff z).mp hz
  obtain ⟨hx0,hx1,hy0,hy2⟩ := (hard_iff z.1).mp hm.1
  obtain ⟨y,hy⟩ := hm.2
  have he : z.1.2 0=(y 0:ℝ) := congrFun hy 0
  have hypos : (0:ℝ)<(y 0:ℝ) := by linarith
  have hi : 0<y 0 := by exact_mod_cast hypos
  have hi1 : 1≤y 0 := by omega
  have hy1 : (1:ℝ)≤(y 0:ℝ) := by exact_mod_cast hi1
  exact ⟨hx0,hx1,by linarith,hy2,by linarith⟩

theorem level_y_cases {z : P × ℝ} (hz : z ∈ level) :
    z.1.2 0=1 ∨ z.1.2 0=2 := by
  have h := level_bounds hz
  obtain ⟨y,hy⟩ := ((level_iff z).mp hz).1.2
  have he : z.1.2 0=(y 0:ℝ) := congrFun hy 0
  have lo : (1:ℝ)≤(y 0:ℝ) := by linarith [h.2.2.1]
  have up : (y 0:ℝ)≤2 := by linarith [h.2.2.2.1]
  have il : 1≤y 0 := by exact_mod_cast lo
  have iu : y 0≤2 := by exact_mod_cast up
  have ih : y 0=1 ∨ y 0=2 := by omega
  rcases ih with h1 | h2
  · left; simpa [h1] using he
  · right; simpa [h2] using he

theorem lift_mem (x : ℝ) (y : ℤ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤(y:ℝ)) (hy2 : (y:ℝ)≤2) (hcut : x+1/2≤(y:ℝ)) :
    (pt x y,-2) ∈ level := by
  apply (level_iff _).mpr
  refine ⟨mixed_pt x y hx0 hx1 hy0 hy2,?_,by norm_num⟩
  change 2*x-2*(y:ℝ)-1≤-2
  linarith

def normWitness : P × ℝ := (pt (1/2) 1,-2)
def taylorWitness : P × ℝ := (pt 0 2,-2)
def hessianWitness : P × ℝ := (pt 1 2,-2)
def scaledWitness : P × ℝ := (pt 0 1,-2)

theorem normWitness_mem : normWitness ∈ level := by
  simpa [normWitness] using lift_mem (1/2) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
theorem taylorWitness_mem : taylorWitness ∈ level := by
  simpa [taylorWitness] using lift_mem 0 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
theorem hessianWitness_mem : hessianWitness ∈ level := by
  simpa [hessianWitness] using lift_mem 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
theorem scaledWitness_mem : scaledWitness ∈ level := by
  simpa [scaledWitness] using lift_mem 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem l1_polynomial_minimum : IsMinimizer level
    (fun z => 1-z.1.1 0+z.1.2 0) normWitness := by
  refine ⟨normWitness_mem,?_⟩
  intro z hz
  have h := level_bounds hz
  change 1-(1/2:ℝ)+1 ≤ 1-z.1.1 0+z.1.2 0
  rcases level_y_cases hz with hy | hy
  · linarith [h.2.2.2.2]
  · linarith [h.2.1]

theorem linf_polynomial_minimum : IsMinimizer level
    (fun z => max (1-z.1.1 0) (z.1.2 0)) normWitness := by
  refine ⟨normWitness_mem,?_⟩
  intro z hz
  have h := level_bounds hz
  change max (1-(1/2:ℝ)) 1 ≤ max (1-z.1.1 0) (z.1.2 0)
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num, max_eq_right (by norm_num : (1/2:ℝ)≤1)]
  exact h.2.2.1.trans (le_max_right _ _)

theorem squared_polynomial_minimum : IsMinimizer level
    (fun z => (z.1.1 0-1)^2+(z.1.2 0)^2) normWitness := by
  refine ⟨normWitness_mem,?_⟩
  intro z hz
  have h := level_bounds hz
  change ((1/2:ℝ)-1)^2+1^2 ≤ (z.1.1 0-1)^2+(z.1.2 0)^2
  rcases level_y_cases hz with hy | hy
  · rw [hy]
    have hx : z.1.1 0≤1/2 := by linarith [h.2.2.2.2]
    nlinarith [sq_nonneg (z.1.1 0-1/2)]
  · rw [hy]
    nlinarith [sq_nonneg (z.1.1 0-1)]

theorem taylor_polynomial_minimum : IsMinimizer level
    (fun z => (z.1.1 0)^2-1-2*z.1.2 0) taylorWitness := by
  refine ⟨taylorWitness_mem,?_⟩
  intro z hz
  have h := level_bounds hz
  change (0:ℝ)^2-1-2*2 ≤ (z.1.1 0)^2-1-2*z.1.2 0
  nlinarith [sq_nonneg (z.1.1 0),h.2.2.2.1]

theorem hessian_polynomial_minimum : IsMinimizer level
    (fun z => 2*(z.1.1 0-1)^2) hessianWitness := by
  refine ⟨hessianWitness_mem,?_⟩
  intro z _
  change 2*((1:ℝ)-1)^2 ≤ 2*(z.1.1 0-1)^2
  nlinarith [sq_nonneg (z.1.1 0-1)]

theorem scaled_polynomial_minimum : IsMinimizer level
    (fun z => (z.1.1 0)^2-1-2*z.1.2 0+(z.1.2 0)^2) scaledWitness := by
  refine ⟨scaledWitness_mem,?_⟩
  intro z hz
  change (0:ℝ)^2-1-2*1+1^2 ≤
    (z.1.1 0)^2-1-2*z.1.2 0+(z.1.2 0)^2
  nlinarith [sq_nonneg (z.1.1 0),sq_nonneg (z.1.2 0-1)]

theorem linear_polynomial_minimum : IsMinimizer level
    (fun z => 2*(z.1.1 0-1)-2*z.1.2 0) taylorWitness := by
  refine ⟨taylorWitness_mem,?_⟩
  intro z hz
  have h := level_bounds hz
  change 2*((0:ℝ)-1)-2*2 ≤ 2*(z.1.1 0-1)-2*z.1.2 0
  linarith [h.1,h.2.2.2.1]

theorem fderiv_objective_function : fderiv ℝ d.f =
    fun a => (2*a.1 0) • X - (2:ℝ) • Y := by
  funext a
  apply ContinuousLinearMap.ext
  intro h
  simpa only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, X_apply, Y_apply] using
    fderiv_f_apply a h

theorem actual_hessian_apply (a h k : P) :
    fderiv ℝ (fderiv ℝ d.f) a h k=2*h.1 0*k.1 0 := by
  rw [fderiv_objective_function]
  have he : (fun a : P => (2*a.1 0) • X - (2:ℝ) • Y) =
      fun a => (2*X a) • X - (2:ℝ) • Y := by
    funext a
    simp
  rw [he]
  have hh := (((X.hasFDerivAt (x := a)).const_mul 2).smul_const X).sub_const ((2:ℝ) • Y)
  rw [hh.fderiv]
  simp

theorem unpolished_seed_reused :
    seed ∈ d.original ∧ ∃ q ∈ d.feasibleFiber (iy 0), d.f q < d.f seed :=
  ⟨seed_feasible,seed_unpolished⟩

theorem zero_weight_lagrangian :
    FullLagrangian.lagrangian d (fun _ => 0) (fun _ => 0) = d.f := by
  funext z
  simp [FullLagrangian.lagrangian]

theorem linear_formula (z : P) :
    FullLagrangian.linear d (fun _ => 0) (fun _ => 0) seed z =
      2*(z.1 0-1)-2*z.2 0 := by
  unfold FullLagrangian.linear
  rw [zero_weight_lagrangian,fderiv_f_apply]
  simp [seed,pt]

theorem hessian_formula (z : P) :
    FullLagrangian.hessian d (fun _ => 0) (fun _ => 0) seed z =
      2*(z.1 0-1)^2 := by
  unfold FullLagrangian.hessian
  rw [zero_weight_lagrangian,actual_hessian_apply]
  simp only [Prod.fst_sub,Pi.sub_apply,seed,pt]
  ring

theorem squared_formula (z : P) : SevenRankings.squared seed z =
    (z.1 0-1)^2+(z.2 0)^2 := by
  simp [SevenRankings.squared,seed,pt]

theorem linf_formula (z : P) : SevenRankings.linf seed z =
    max |z.1 0-1| |z.2 0| := by
  have he (s : ℝ) : SevenRankings.linf seed z ≤ s ↔
      max |z.1 0-1| |z.2 0| ≤ s := by
    rw [SevenRankings.linf_le_iff,max_le_iff]
    simp only [seed,pt,Fin.forall_fin_one,sub_zero]
    constructor
    · exact fun h => ⟨h.2.1,h.2.2⟩
    · exact fun h => ⟨(abs_nonneg _).trans h.1,h.1,h.2⟩
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

def polynomial : SevenRankings.Kind → P × ℝ → ℝ
  | .l1, z => 1-z.1.1 0+z.1.2 0
  | .linf, z => max (1-z.1.1 0) (z.1.2 0)
  | .squared, z => (z.1.1 0-1)^2+(z.1.2 0)^2
  | .taylor, z => (z.1.1 0)^2-1-2*z.1.2 0
  | .hessian, z => 2*(z.1.1 0-1)^2
  | .scaled, z => (z.1.1 0)^2-1-2*z.1.2 0+(z.1.2 0)^2
  | .linear, z => 2*(z.1.1 0-1)-2*z.1.2 0

def witness : SevenRankings.Kind → P × ℝ
  | .l1 | .linf | .squared => normWitness
  | .taylor | .linear => taylorWitness
  | .hessian => hessianWitness
  | .scaled => scaledWitness

def expected : SevenRankings.Kind → ℝ
  | .l1 => 3/2
  | .linf => 1
  | .squared => 5/4
  | .taylor => -5
  | .hessian => 0
  | .scaled => -2
  | .linear => -6

theorem ranking_polynomial (k : SevenRankings.Kind) {z : P × ℝ}
    (hz : z ∈ level) :
    SevenRankings.ranking d (fun _ => 0) (fun _ => 0) seed 1 k z.1 = polynomial k z := by
  have h := level_bounds hz
  have hx : z.1.1 0-1 ≤ 0 := by linarith [h.2.1]
  have hy : 0≤z.1.2 0 := by linarith [h.2.2.1]
  cases k <;>
    simp only [SevenRankings.ranking,SevenRankings.taylor,SevenRankings.scaled,
      linf_formula,squared_formula,linear_formula,hessian_formula] <;>
    simp [polynomial,SevenRankings.l1,seed,pt,
      abs_of_nonpos hx,abs_of_nonneg hy] <;> ring

theorem polynomial_minimum (k : SevenRankings.Kind) :
    IsMinimizer level (polynomial k) (witness k) := by
  cases k with
  | l1 => exact l1_polynomial_minimum
  | linf => exact linf_polynomial_minimum
  | squared => exact squared_polynomial_minimum
  | taylor => exact taylor_polynomial_minimum
  | hessian => exact hessian_polynomial_minimum
  | scaled => exact scaled_polynomial_minimum
  | linear => exact linear_polynomial_minimum

/-- All seven actual literal rankings attain the independently computed minima
on the actual source level set. Zero weights are supplied, not seed KKT data. -/
theorem seven_actual_minima (k : SevenRankings.Kind) :
    IsMinimizer level
      (fun z => SevenRankings.ranking d (fun _ => 0) (fun _ => 0) seed 1 k z.1)
      (witness k) ∧
    SevenRankings.ranking d (fun _ => 0) (fun _ => 0) seed 1 k (witness k).1 =
      expected k := by
  have hp := polynomial_minimum k
  refine ⟨⟨hp.1,?_⟩,?_⟩
  · intro z hz
    change SevenRankings.ranking d (fun _ => 0) (fun _ => 0) seed 1 k (witness k).1 ≤
      SevenRankings.ranking d (fun _ => 0) (fun _ => 0) seed 1 k z.1
    rw [ranking_polynomial k hp.1,ranking_polynomial k hz]
    exact hp.2 z hz
  · rw [ranking_polynomial k hp.1]
    cases k <;> norm_num [polynomial,witness,expected,normWitness,taylorWitness,
      hessianWitness,scaledWitness,pt]

end Chapter07.RankingControls

#print axioms Chapter07.RankingControls.level_iff
#print axioms Chapter07.RankingControls.actual_hessian_apply
#print axioms Chapter07.RankingControls.seven_actual_minima
