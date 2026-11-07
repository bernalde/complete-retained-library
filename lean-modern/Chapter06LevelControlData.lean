module

public import Chapter06LevelFiber
public import Chapter06QuadraticRanking
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! Exact invented nonvacuity control for the source-level Chapter 6 interfaces.
The seed is feasible but unpolished. All minima concern the actual nonlinear
objective or the literal nonnegative common slack, not supplied support axioms. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter06.Level
namespace Chapter06.LevelControl

abbrev P := Point 1 1
def pt (x y : ℝ) : P := (fun _ => x, fun _ => y)
def iy (y : ℤ) : IntVector 1 := fun _ => y

def d : Data 1 1 1 4 where
  f := fun p => (p.1 0)^2 - 2*p.2 0
  g := fun _ p => p.2 0-p.1 0-1/2
  A := fun i _ => if i.val=0 then -1 else if i.val=1 then 1 else 0
  B := fun i _ => if i.val=2 then -1 else if i.val=3 then 1 else 0
  b := fun i => if i.val=1 then 1 else if i.val=3 then 2 else 0

theorem hard_iff (p : P) : p ∈ d.hard ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 2 := by
  constructor
  · intro h
    have h0 := h ⟨0,by decide⟩; have h1 := h ⟨1,by decide⟩
    have h2 := h ⟨2,by decide⟩; have h3 := h ⟨3,by decide⟩
    norm_num [d, LinearForm] at h0 h1 h2 h3
    exact ⟨by linarith, h1, by linarith, h3⟩
  · rintro ⟨hx0,hx1,hy0,hy2⟩ i
    fin_cases i <;> norm_num [d, LinearForm] <;> linarith

theorem hard_eq_rectangle : d.hard = Set.Icc (pt 0 0) (pt 1 2) := by
  ext p
  rw [hard_iff]
  simp [Set.mem_Icc, Prod.le_def, Pi.le_def, pt, Fin.forall_fin_one, and_assoc, and_left_comm, and_comm]

theorem hard_compact : IsCompact d.hard := by
  rw [hard_eq_rectangle]
  exact isCompact_Icc

theorem objective_C2 : ContDiff ℝ 2 d.f := by
  change ContDiff ℝ 2 (fun p : P => (p.1 0)^2-2*p.2 0)
  fun_prop

theorem soft_C2 (j : Fin 1) : ContDiff ℝ 2 (d.g j) := by
  change ContDiff ℝ 2 (fun p : P => p.2 0-p.1 0-1/2)
  fun_prop

theorem objective_convex : ConvexOn ℝ Set.univ d.f := by
  refine ⟨convex_univ,?_⟩
  intro p _ q _ a b ha hb hab
  change (a*p.1 0+b*q.1 0)^2-2*(a*p.2 0+b*q.2 0) ≤
    a*((p.1 0)^2-2*p.2 0)+b*((q.1 0)^2-2*q.2 0)
  have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.1 0-q.1 0))
  have hb' : b=1-a := by linarith
  subst b
  nlinarith

theorem soft_convex (j : Fin 1) : ConvexOn ℝ Set.univ (d.g j) := by
  refine ⟨convex_univ,?_⟩
  intro p _ q _ a b ha hb hab
  change (a*p.2 0+b*q.2 0)-(a*p.1 0+b*q.1 0)-1/2 ≤
    a*(p.2 0-p.1 0-1/2)+b*(q.2 0-q.1 0-1/2)
  nlinarith

theorem fiber_y {y : IntVector 1} {p : P} (hp : p ∈ d.hardFiber y) :
    p.2 0 = (y 0 : ℝ) := congrFun hp.2 0

theorem fiber_slater (y : IntVector 1) (hne : (d.feasibleFiber y).Nonempty) :
    ∃ p ∈ d.hardFiber y, ∀ j, d.g j p < 0 := by
  obtain ⟨q,hq⟩ := hne
  have hhard := (hard_iff q).mp hq.1.1
  have hy := fiber_y hq.1
  have hg := hq.2 0
  change q.2 0-q.1 0-1/2 ≤ 0 at hg
  have hylt : (y 0 : ℝ)<2 := by linarith
  have hyint : y 0<2 := by exact_mod_cast hylt
  have hyone : (y 0 : ℝ)≤1 := by exact_mod_cast (show y 0≤1 by omega)
  refine ⟨pt 1 (y 0),⟨(hard_iff _).mpr ?_,?_⟩,?_⟩
  · simp only [pt]
    exact ⟨by norm_num,le_rfl,by linarith,by linarith⟩
  · funext i
    fin_cases i
    rfl
  · intro j
    change (y 0 : ℝ)-1-1/2<0
    linarith

def regularity : Regularity d where
  hard_compact := hard_compact
  hard_nonempty := ⟨pt 0 0,(hard_iff _).mpr (by norm_num [pt])⟩
  objective_convex := objective_convex
  objective_C1 := objective_C2.of_le (by norm_num)
  constraint_convex := soft_convex
  constraint_C1 := fun j => (soft_C2 j).of_le (by norm_num)
  fiber_slater := fiber_slater

def seed : P := pt 1 0
def restored : P := pt 1 2
def optimum : P := pt (1/2) 1

theorem seed_feasible : seed ∈ d.original := by
  refine ⟨⟨(hard_iff _).mpr (by norm_num [seed,pt]),iy 0,by funext i; change (0:ℝ)=((0:ℤ):ℝ); norm_num⟩,?_⟩
  intro j
  norm_num [d,seed,pt]

theorem seed_unpolished : ∃ q ∈ d.feasibleFiber (iy 0), d.f q < d.f seed := by
  refine ⟨pt 0 0,⟨⟨(hard_iff _).mpr (by norm_num [pt]),by funext i; change (0:ℝ)=((0:ℤ):ℝ); norm_num⟩,?_⟩,?_⟩
  · intro j; norm_num [d,pt]
  · norm_num [d,pt,seed]

theorem optimum_fiber : optimum ∈ d.feasibleFiber (iy 1) := by
  refine ⟨⟨(hard_iff _).mpr (by norm_num [optimum,pt]),by funext i; change (1:ℝ)=((1:ℤ):ℝ); norm_num⟩,?_⟩
  intro j
  norm_num [d,optimum,pt]

theorem feasible_minimum : IsMinimizer (d.feasibleFiber (iy 1)) d.f optimum := by
  refine ⟨optimum_fiber,?_⟩
  intro q hq
  have hy := fiber_y hq.1
  have hg := hq.2 0
  norm_num [iy] at hy
  change q.2 0-q.1 0-1/2≤0 at hg
  have hx : 1/2≤q.1 0 := by linarith
  change (1/2:ℝ)^2-2*1 ≤ (q.1 0)^2-2*q.2 0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0≤q.1 0+1/2 by linarith)]

theorem fiber_two_infeasible : ¬(d.feasibleFiber (iy 2)).Nonempty := by
  rintro ⟨q,hq⟩
  have hx := ((hard_iff q).mp hq.1.1).2.1
  have hy := fiber_y hq.1
  have hg := hq.2 0
  norm_num [iy] at hy
  change q.2 0-q.1 0-1/2≤0 at hg
  linarith

theorem restoration_minimum :
    IsMinimizer (d.restoration (iy 2)) Prod.snd (restored,1/2) := by
  refine ⟨⟨⟨(hard_iff _).mpr (by norm_num [restored,pt]),by funext i; change (2:ℝ)=((2:ℤ):ℝ); norm_num⟩,?_,by norm_num⟩,?_⟩
  · intro j; norm_num [d,restored,pt]
  · intro z hz
    have hx := ((hard_iff z.1).mp hz.1.1).2.1
    have hy := fiber_y hz.1
    have hg := hz.2.1 0
    norm_num [iy] at hy
    change z.1.2 0-z.1.1 0-1/2≤z.2 at hg
    change (1/2:ℝ)≤z.2
    linarith

theorem restoration_positive : (0:ℝ)<1/2 :=
  infeasible_restoration_positive d (iy 2) fiber_two_infeasible restoration_minimum

theorem optimum_value : d.f optimum = -7/4 := by norm_num [d,optimum,pt]
theorem seed_value : d.f seed = 1 := by norm_num [d,seed,pt]

def X : P →L[ℝ] ℝ := linearFormCLM (fun _ => 1) (fun _ => 0)
def Y : P →L[ℝ] ℝ := linearFormCLM (fun _ => 0) (fun _ => 1)
@[simp] theorem X_apply (p : P) : X p=p.1 0 := by simp [X,LinearForm]
@[simp] theorem Y_apply (p : P) : Y p=p.2 0 := by simp [Y,LinearForm]

theorem fderiv_f_apply (a h : P) :
    fderiv ℝ d.f a h=2*a.1 0*h.1 0-2*h.2 0 := by
  have hd : d.f=(fun p : P => X p*X p-2*Y p) := by
    funext p; simp [d,pow_two]
  have hf := (X.hasFDerivAt (x := a)).fun_mul (X.hasFDerivAt (x := a))
  have hh := hf.fun_sub ((Y.hasFDerivAt (x := a)).const_mul 2)
  rw [hd,hh.fderiv]
  simp
  ring

theorem fderiv_g_apply (j : Fin 1) (a h : P) :
    fderiv ℝ (d.g j) a h=h.2 0-h.1 0 := by
  have hd : d.g j=(fun p : P => Y p-X p-1/2) := by
    funext p; simp [d]
  have hh := ((Y.hasFDerivAt (x := a)).fun_sub (X.hasFDerivAt (x := a))).sub_const (1/2)
  rw [hd,hh.fderiv]
  simp

theorem objective_tangent (a q : P) :
    tangent d.f a q=2*a.1 0*q.1 0-2*q.2 0-(a.1 0)^2 := by
  unfold tangent
  rw [fderiv_f_apply]
  change (a.1 0)^2-2*a.2 0+(2*a.1 0*(q.1 0-a.1 0)-2*(q.2 0-a.2 0))=_
  ring

theorem soft_tangent (a q : P) (j : Fin 1) : tangent (d.g j) a q=d.g j q := by
  unfold tangent
  rw [fderiv_g_apply]
  change a.2 0-a.1 0-1/2+((q.2 0-a.2 0)-(q.1 0-a.1 0))=q.2 0-q.1 0-1/2
  ring

theorem seed_rows (q : P) : selectedRows d seed 0 q := by
  intro j hj
  norm_num [d,seed,pt] at hj

theorem restoration_rows (q : P) : selectedRows d restored (1/2) q ↔ d.g 0 q≤0 := by
  constructor
  · intro h
    simpa only [soft_tangent] using h 0 (by norm_num [d,restored,pt])
  · intro h j hj
    rw [soft_tangent]
    exact h

theorem optimum_rows (q : P) : selectedRows d optimum 0 q ↔ d.g 0 q≤0 := by
  constructor
  · intro h
    simpa only [soft_tangent] using h 0 (by norm_num [d,optimum,pt])
  · intro h j hj
    rw [soft_tangent]
    exact h

def lam : Fin 1 → ℝ := fun _ => 1
def mu : Fin 4 → ℝ := fun i => if i.val=1 then 1 else 0

theorem restoration_explicit_KKT : RestorationKKT (boxedModel d regularity)
    restored (1/2) (fun j => fderiv ℝ (d.g j) restored) lam mu := by
  refine ⟨restoration_minimum.1.1.1,restoration_minimum.1.2.1,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    exact (((regularity.constraint_C1 j).differentiable (by norm_num)) restored).hasFDerivAt
  · intro j; norm_num [lam]
  · intro i; simp [mu]; split_ifs <;> norm_num
  · intro j; norm_num [lam,boxedModel,d,restored,pt]
  · intro i
    fin_cases i <;> norm_num [mu,linearResidual,boxedModel,d,LinearForm,restored,pt]
  · intro dx
    simp only [lam,Fin.sum_univ_one,one_mul,fderiv_g_apply]
    simp [mu,Fin.sum_univ_succ,boxedModel,d,LinearForm]
  · norm_num [lam]

def feasible_explicit_KKT : FeasibleKKT d regularity optimum where
  lambda := lam
  mu := fun _ => 0
  lambda_nonneg := by intro j; norm_num [lam]
  mu_nonneg := by intro i; norm_num
  soft_compl := by intro j; norm_num [lam,d,optimum,pt]
  hard_compl := by intro i; simp
  stationarity := by
    ext dx
    simp [lam,Chapter03.OAKKT.restrict_apply,fderiv_f_apply,fderiv_g_apply,optimum,pt]

theorem actual_multiplier_and_normal_nonzero :
    lam 0=1 ∧ mu ⟨1,by decide⟩=1 ∧
      mu ⟨1,by decide⟩ * d.A ⟨1,by decide⟩ 0=1 ∧ d.g 0 restored=(1/2:ℝ) := by
  norm_num [lam,mu,d,restored,pt]

theorem derived_feasible_KKT : Nonempty (FeasibleKKT d regularity optimum) :=
  feasibleKKT_exists d regularity (iy 1) feasible_minimum

theorem actual_lambda_ranking_convex : ConvexOn ℝ Set.univ
    (Chapter06.QuadraticRanking.ranking d.f d.g lam optimum) :=
  Chapter06.QuadraticRanking.ranking_convex d.f d.g lam objective_convex soft_convex
    (by intro j; norm_num [lam]) objective_C2 soft_C2 optimum

theorem derived_restoration_exclusion (q : P) (hq : q∈d.hardFiber (iy 2))
    (hrows : selectedRows d restored (1/2) q) : False :=
  restoration_selected_excludes d regularity (iy 2) fiber_two_infeasible
    restoration_minimum hq hrows

end Chapter06.LevelControl

#print axioms Chapter06.LevelControl.pt
#print axioms Chapter06.LevelControl.iy
#print axioms Chapter06.LevelControl.d
#print axioms Chapter06.LevelControl.hard_iff
#print axioms Chapter06.LevelControl.hard_eq_rectangle
#print axioms Chapter06.LevelControl.hard_compact
#print axioms Chapter06.LevelControl.objective_C2
#print axioms Chapter06.LevelControl.soft_C2
#print axioms Chapter06.LevelControl.objective_convex
#print axioms Chapter06.LevelControl.soft_convex
#print axioms Chapter06.LevelControl.fiber_y
#print axioms Chapter06.LevelControl.fiber_slater
#print axioms Chapter06.LevelControl.regularity
#print axioms Chapter06.LevelControl.seed
#print axioms Chapter06.LevelControl.restored
#print axioms Chapter06.LevelControl.optimum
#print axioms Chapter06.LevelControl.seed_feasible
#print axioms Chapter06.LevelControl.seed_unpolished
#print axioms Chapter06.LevelControl.optimum_fiber
#print axioms Chapter06.LevelControl.feasible_minimum
#print axioms Chapter06.LevelControl.fiber_two_infeasible
#print axioms Chapter06.LevelControl.restoration_minimum
#print axioms Chapter06.LevelControl.restoration_positive
#print axioms Chapter06.LevelControl.optimum_value
#print axioms Chapter06.LevelControl.seed_value
#print axioms Chapter06.LevelControl.X
#print axioms Chapter06.LevelControl.Y
#print axioms Chapter06.LevelControl.X_apply
#print axioms Chapter06.LevelControl.Y_apply
#print axioms Chapter06.LevelControl.fderiv_f_apply
#print axioms Chapter06.LevelControl.fderiv_g_apply
#print axioms Chapter06.LevelControl.objective_tangent
#print axioms Chapter06.LevelControl.soft_tangent
#print axioms Chapter06.LevelControl.seed_rows
#print axioms Chapter06.LevelControl.restoration_rows
#print axioms Chapter06.LevelControl.optimum_rows
#print axioms Chapter06.LevelControl.lam
#print axioms Chapter06.LevelControl.mu
#print axioms Chapter06.LevelControl.restoration_explicit_KKT
#print axioms Chapter06.LevelControl.feasible_explicit_KKT
#print axioms Chapter06.LevelControl.actual_multiplier_and_normal_nonzero
#print axioms Chapter06.LevelControl.derived_feasible_KKT
#print axioms Chapter06.LevelControl.actual_lambda_ranking_convex
#print axioms Chapter06.LevelControl.derived_restoration_exclusion
