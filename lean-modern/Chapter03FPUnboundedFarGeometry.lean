module

public import Chapter03FPUnboundedFarData

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedFar

def firstEvent : Event 0 2 := ⟨target 0,minus,none,none⟩
def secondEvent : Event 0 2 := ⟨target 1,plus,none,none⟩
def state0 : State 0 2 := initialState seed
def state1 : State 0 2 := append state0 firstEvent
def state2 : State 0 2 := append state1 secondEvent

theorem tangent_line (t u : ℝ) :
    data.f (line t)+data.Df (line t) (line u-line t)=1220*t*u-610*t^2 := by
  change obj (line t)+deriv (line t) (line u-line t)=_
  rw [obj_line,deriv_apply]
  simp only [line,pt_zero,pt_one,Prod.snd_sub,Pi.sub_apply]
  ring

theorem constraint_tangent_line (j : Fin 1) (t u : ℝ) :
    data.g j (line t)+data.Dg j (line t) (line u-line t)=
      1220*t*u-610*t^2-610/1000000 := by
  have h := tangent_line t u
  change obj (line t)-610/1000000+deriv (line t) (line u-line t)=_
  change obj (line t)+deriv (line t) (line u-line t)=_ at h
  linarith

theorem projection_cost (k : ℤ) (t : ℝ) :
    distance (target k) (line t)=610*((k:ℝ)-233/610-t)^2 := by
  rw [FPTrace.distance_two]
  simp [target,line]
  ring

theorem minus_feasible : minus ∈ data.relaxation :=
  (relaxation_param minus).mpr ⟨-1/1000,le_rfl,by norm_num,rfl⟩

theorem plus_feasible : plus ∈ data.relaxation :=
  (relaxation_param plus).mpr ⟨1/1000,by norm_num,le_rfl,rfl⟩

theorem projection_minimum_first :
    IsMinimizer (data.region none) (distance (target 0)) minus := by
  refine ⟨⟨minus_feasible,True.intro⟩,?_⟩
  intro p hp
  obtain ⟨t,ht,ht',rfl⟩ := (relaxation_param p).mp hp.1
  simp only [minus,projection_cost,Int.cast_zero]
  nlinarith [sq_nonneg (t+1/1000)]

theorem projection_minimum_second :
    IsMinimizer (data.region none) (distance (target 1)) plus := by
  refine ⟨⟨plus_feasible,True.intro⟩,?_⟩
  intro p hp
  obtain ⟨t,ht,ht',rfl⟩ := (relaxation_param p).mp hp.1
  simp only [plus,projection_cost,Int.cast_one]
  nlinarith [sq_nonneg (t-1/1000)]

theorem projection_first_unique {p : P}
    (hp : IsMinimizer (data.region none) (distance (target 0)) p) : p=minus := by
  have hmin := hp.2 minus ⟨minus_feasible,True.intro⟩
  obtain ⟨t,ht,ht',rfl⟩ := (relaxation_param p).mp hp.1.1
  simp only [minus,projection_cost,Int.cast_zero] at hmin
  have he : t = -1/1000 := by nlinarith [sq_nonneg (t+1/1000)]
  exact congrArg line he

theorem projection_second_unique {p : P}
    (hp : IsMinimizer (data.region none) (distance (target 1)) p) : p=plus := by
  have hmin := hp.2 plus ⟨plus_feasible,True.intro⟩
  obtain ⟨t,ht,ht',rfl⟩ := (relaxation_param p).mp hp.1.1
  simp only [plus,projection_cost,Int.cast_one] at hmin
  have he : t = 1/1000 := by nlinarith [sq_nonneg (t-1/1000)]
  exact congrArg line he

theorem projection_first_nonzero : distance (target 0) minus ≠ 0 := by
  norm_num [minus,projection_cost]
theorem projection_second_nonzero : distance (target 1) plus ≠ 0 := by
  norm_num [plus,projection_cost]

theorem normal_first_line (t : ℝ) :
    firstEvent.normal (line t)=610*(233/610-1/1000)*(t+1/1000) := by
  rw [FPTrace.normal_two]
  simp [firstEvent,minus,line,target]
  ring

theorem normal_second_line (t : ℝ) :
    secondEvent.normal (line t)=610*(1/1000-377/610)*(t-1/1000) := by
  rw [FPTrace.normal_two]
  simp [secondEvent,plus,line,target]
  ring

theorem first_integer_normal (k : ℤ) :
    0 ≤ firstEvent.normal (integerPoint k) ↔ 1 ≤ k := by
  rw [integer_point_line,normal_first_line]
  constructor
  · intro h
    have hk : (0:ℝ)<k := by linarith
    have hk' : (0:ℤ)<k := by exact_mod_cast hk
    omega
  · intro h
    have hk : (1:ℝ)≤k := by exact_mod_cast h
    linarith

theorem second_integer_normal (k : ℤ) :
    0 ≤ secondEvent.normal (integerPoint k) ↔ k ≤ 0 := by
  rw [integer_point_line,normal_second_line]
  constructor
  · intro h
    have hk : (k:ℝ)<1 := by linarith
    have hk' : k<(1:ℤ) := by exact_mod_cast hk
    omega
  · intro h
    have hk : (k:ℝ)≤0 := by exact_mod_cast h
    linarith

theorem l1_nonpositive (t : ℝ) (ht : -1/1000 ≤ t) (_ht' : t ≤ 1/1000)
    (k : ℤ) (hk : k ≤ 0) :
    l1 (line t) (integerPoint k)=13-34*(k:ℝ)-8/610+34*t := by
  have hk' : (k:ℝ)≤0 := by exact_mod_cast hk
  rw [FPTrace.l1_two]
  change |(-8+21*(k:ℝ))-(13/610+21*t)|+|(5-13*(k:ℝ))-(21/610-13*t)|=_
  rw [abs_of_nonpos (by linarith),abs_of_nonneg (by linarith)]
  ring

theorem l1_positive (t : ℝ) (_ht : -1/1000 ≤ t) (ht' : t ≤ 1/1000)
    (k : ℤ) (hk : 1 ≤ k) :
    l1 (line t) (integerPoint k)=34*(k:ℝ)-13+8/610-34*t := by
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  rw [FPTrace.l1_two]
  change |(-8+21*(k:ℝ))-(13/610+21*t)|+|(5-13*(k:ℝ))-(21/610-13*t)|=_
  rw [abs_of_nonneg (by linarith),abs_of_nonpos (by linarith)]
  ring

theorem first_cost_min (k : ℤ) : l1 seed (integerPoint 0) ≤ l1 seed (integerPoint k) := by
  change l1 (line 0) (integerPoint 0) ≤ _
  rw [l1_nonpositive 0 (by norm_num) (by norm_num) 0 (by omega)]
  by_cases hk : k ≤ 0
  · rw [show seed=line 0 from rfl,l1_nonpositive 0 (by norm_num) (by norm_num) k hk]
    have hk' : (k:ℝ)≤0 := by exact_mod_cast hk
    norm_num
    linarith
  · have hk' : 1 ≤ k := by omega
    rw [show seed=line 0 from rfl,l1_positive 0 (by norm_num) (by norm_num) k hk']
    have hk'' : (1:ℝ)≤k := by exact_mod_cast hk'
    norm_num
    linarith

theorem first_cost_unique (k : ℤ)
    (hc : l1 seed (integerPoint k) ≤ l1 seed (integerPoint 0)) : k=0 := by
  change l1 (line 0) (integerPoint k) ≤ l1 (line 0) (integerPoint 0) at hc
  rw [l1_nonpositive 0 (by norm_num) (by norm_num) 0 (by omega)] at hc
  by_cases hk : k ≤ 0
  · rw [l1_nonpositive 0 (by norm_num) (by norm_num) k hk] at hc
    norm_num at hc
    omega
  · have hk' : 1 ≤ k := by omega
    rw [l1_positive 0 (by norm_num) (by norm_num) k hk'] at hc
    have hkr : (1:ℝ)≤k := by exact_mod_cast hk'
    norm_num at hc
    linarith

theorem second_cost_min (k : ℤ) (hk : 1 ≤ k) :
    l1 minus (integerPoint 1) ≤ l1 minus (integerPoint k) := by
  change l1 (line (-1/1000)) _ ≤ l1 (line (-1/1000)) _
  rw [l1_positive _ (by norm_num) (by norm_num) 1 (by omega),
    l1_positive _ (by norm_num) (by norm_num) k hk]
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  norm_num
  linarith

theorem second_cost_unique (k : ℤ) (hk : 1 ≤ k)
    (hc : l1 minus (integerPoint k) ≤ l1 minus (integerPoint 1)) : k=1 := by
  change l1 (line (-1/1000)) _ ≤ l1 (line (-1/1000)) _ at hc
  rw [l1_positive _ (by norm_num) (by norm_num) k hk,
    l1_positive _ (by norm_num) (by norm_num) 1 (by omega)] at hc
  have hkr : (k:ℝ)≤1 := by norm_num at hc; linarith
  have hki : k≤(1:ℤ) := by exact_mod_cast hkr
  omega

end Chapter03.FPUnboundedFar
