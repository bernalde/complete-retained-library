module

public import Chapter03FPUnboundedControlAnalytic
public import Chapter03FPUnboundedLattice

@[expose] public section

/-! An affine integer line with a compact nonlinear segment and no hard bounds.
All data and ambient derivatives are explicit. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedFar

abbrev P := Point 0 2
def pt (a b : ℝ) : P := (0, ![a,b])
def line (t : ℝ) : P := pt (13/610+21*t) (21/610-13*t)
def seed : P := line 0
def minus : P := line (-1/1000)
def plus : P := line (1/1000)
def target (k : ℤ) : IntVector 2 := ![-8+21*k,5-13*k]
def integerPoint (k : ℤ) : P := pt (-8+21*(k:ℝ)) (5-13*(k:ℝ))
def obj (p : P) : ℝ := (p.2 0-13/610)^2+(p.2 1-21/610)^2
def deriv (p : P) : P →L[ℝ] ℝ :=
  (2*(p.2 0-13/610)) • FPTrace.y0 + (2*(p.2 1-21/610)) • FPTrace.y1
def data : FPUnbounded.Data 0 2 1 where
  base := {p | 13*p.2 0+21*p.2 1=1}
  f := obj
  g := fun _ p => obj p-610/1000000
  Df := deriv
  Dg := fun _ => deriv
  delta := 1/20

@[simp] theorem pt_zero (a b : ℝ) : (pt a b).2 0 = a := rfl
@[simp] theorem pt_one (a b : ℝ) : (pt a b).2 1 = b := rfl
@[simp] theorem target_zero (k : ℤ) : target k 0 = -8+21*k := rfl
@[simp] theorem target_one (k : ℤ) : target k 1 = 5-13*k := rfl
@[simp] theorem deriv_apply (p q : P) :
    deriv p q = 2*(p.2 0-13/610)*q.2 0+2*(p.2 1-21/610)*q.2 1 := by simp [deriv]

theorem pt_eta (p : P) : pt (p.2 0) (p.2 1) = p := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · funext j; fin_cases j <;> rfl

theorem line_base (t : ℝ) : line t ∈ data.base := by
  change 13*(13/610+21*t)+21*(21/610-13*t)=1
  ring

theorem base_param (p : P) : p ∈ data.base ↔ ∃ t : ℝ, p=line t := by
  constructor
  · intro hp
    refine ⟨(p.2 0-13/610)/21, ?_⟩
    change 13*p.2 0+21*p.2 1=1 at hp
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext j; fin_cases j
      · change p.2 0=13/610+21*((p.2 0-13/610)/21); ring
      · change p.2 1=21/610-13*((p.2 0-13/610)/21); linarith
  · rintro ⟨t,rfl⟩; exact line_base t

theorem line_injective : Function.Injective line := by
  intro t u he
  have h := congrArg (fun p : P => p.2 0) he
  change 13/610+21*t=13/610+21*u at h
  linarith

theorem obj_line (t : ℝ) : obj (line t)=610*t^2 := by simp [obj,line]; ring

theorem derivative_obj (p : P) : HasFDerivAt obj (deriv p) p := by
  exact (FPTrace.square_derivative FPTrace.y0 (13/610) p).add
    (FPTrace.square_derivative FPTrace.y1 (21/610) p)

theorem derivative_constraint (p : P) (j : Fin 1) :
    HasFDerivAt (data.g j) (data.Dg j p) p :=
  (derivative_obj p).sub_const (610/1000000)

theorem base_closed : IsClosed data.base := by
  apply isClosed_eq _ continuous_const
  exact (continuous_const.mul ((continuous_apply 0).comp continuous_snd)).add
    (continuous_const.mul ((continuous_apply 1).comp continuous_snd))

theorem base_convex : Convex ℝ data.base := by
  intro p hp q hq a b ha hb hab
  change 13*p.2 0+21*p.2 1=1 at hp
  change 13*q.2 0+21*q.2 1=1 at hq
  change 13*(a*p.2 0+b*q.2 0)+21*(a*p.2 1+b*q.2 1)=1
  nlinarith

theorem obj_convex : ConvexOn ℝ data.base obj :=
  (FPTrace.square_convex base_convex FPTrace.y0 (13/610)).add
    (FPTrace.square_convex base_convex FPTrace.y1 (21/610))

theorem relaxation_param (p : P) : p ∈ data.relaxation ↔
    ∃ t : ℝ, -1/1000 ≤ t ∧ t ≤ 1/1000 ∧ p=line t := by
  constructor
  · rintro ⟨hb,hg⟩
    obtain ⟨t,rfl⟩ := (base_param p).mp hb
    have hh := hg 0
    change obj (line t)-610/1000000 ≤ 0 at hh
    rw [obj_line] at hh
    refine ⟨t, ?_, ?_, rfl⟩ <;> nlinarith [sq_nonneg (t-1/1000),sq_nonneg (t+1/1000)]
  · rintro ⟨t,ht,ht',rfl⟩
    refine ⟨line_base t, ?_⟩
    intro j
    change obj (line t)-610/1000000 ≤ 0
    rw [obj_line]
    nlinarith [mul_nonneg (by linarith : 0 ≤ t+1/1000) (by linarith : 0 ≤ 1/1000-t)]

theorem line_continuous : Continuous line := by
  unfold line pt
  apply continuous_const.prodMk
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp <;> fun_prop

theorem relaxation_compact : IsCompact data.relaxation := by
  have he : data.relaxation = line '' Set.Icc (-1/1000 : ℝ) (1/1000) := by
    ext p
    rw [relaxation_param]
    constructor
    · rintro ⟨t,ht,ht',rfl⟩; exact ⟨t,⟨ht,ht'⟩,rfl⟩
    · rintro ⟨t,⟨ht,ht'⟩,rfl⟩; exact ⟨t,ht,ht',rfl⟩
  rw [he]
  exact isCompact_Icc.image line_continuous

theorem analytic : FPUnbounded.Analytic data := by
  refine ⟨base_closed,base_convex,obj_convex,?_,?_,?_,relaxation_compact.isBounded,?_⟩
  · intro j
    simpa [data,Pi.add_def,sub_eq_add_neg] using obj_convex.add_const (-(610/1000000))
  · intro p _; exact derivative_obj p
  · intro j p _; exact derivative_constraint p j
  · norm_num [data]

theorem nonlinear_all : data.nonlinear=Set.univ := by
  ext j
  simp only [FPUnbounded.Data.nonlinear,Set.mem_setOf_eq,Set.mem_univ,iff_true]
  intro ha
  have hd : HasFDerivAt (data.g j) (0 : P →L[ℝ] ℝ) seed := by
    have he : data.Dg j seed = 0 := by
      apply ContinuousLinearMap.ext
      intro p
      simp [data,seed,line,deriv]
    simpa [he] using derivative_constraint seed j
  have ht := OAKKT.affine_tangent ha hd (pt (13/610+1) (21/610))
  norm_num [data,obj,seed,line,pt] at ht

theorem integer_point_cast (k : ℤ) : (integerPoint k).2=intCast (target k) := by
  funext j; fin_cases j <;> simp [integerPoint,pt,target,intCast]

theorem integer_point_line (k : ℤ) : integerPoint k=line ((k:ℝ)-233/610) := by
  apply Prod.ext
  · rfl
  · funext j; fin_cases j <;> simp [integerPoint,line] <;> ring

theorem integer_line_param {y : IntVector 2}
    (h : 13*(y 0 : ℝ)+21*(y 1 : ℝ)=1) : ∃ k : ℤ, y=target k := by
  have hi : 13*y 0+21*y 1=1 := by exact_mod_cast h
  refine ⟨5*y 0+8*y 1, ?_⟩
  funext j
  fin_cases j <;> simp [target] <;> omega

theorem base_integer_param (p : P) :
    (p ∈ data.base ∧ ∃ y : IntVector 2, p.2=intCast y) ↔
      ∃ k : ℤ, p=integerPoint k := by
  constructor
  · rintro ⟨hb,y,hy⟩
    have h : 13*(y 0 : ℝ)+21*(y 1 : ℝ)=1 := by
      simpa [data,hy,intCast] using hb
    obtain ⟨k,rfl⟩ := integer_line_param h
    refine ⟨k, ?_⟩
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact hy.trans (integer_point_cast k).symm
  · rintro ⟨k,rfl⟩
    exact ⟨integer_point_line k ▸ line_base _,target k,integer_point_cast k⟩

theorem original_empty : ¬data.original.Nonempty := by
  rintro ⟨p,hp,y,hy⟩
  obtain ⟨k,hk⟩ := (base_integer_param p).mp ⟨hp.1,y,hy⟩
  obtain ⟨t,ht,ht',he⟩ := (relaxation_param p).mp hp
  have heq : t=(k:ℝ)-233/610 := line_injective (he.symm.trans (hk.trans (integer_point_line k)))
  have hk0 : (0:ℝ)<k := by linarith
  have hk1 : (k:ℝ)<1 := by linarith
  have hk0' : (0:ℤ)<k := by exact_mod_cast hk0
  have hk1' : k<(1:ℤ) := by exact_mod_cast hk1
  omega

theorem seed_minimum : IsMinimizer data.relaxation data.f seed := by
  refine ⟨(relaxation_param seed).mpr ⟨0,by norm_num,by norm_num,rfl⟩,?_⟩
  intro p _
  change obj seed ≤ obj p
  simp only [seed,obj_line]
  dsimp [obj]
  nlinarith [sq_nonneg (p.2 0-13/610),sq_nonneg (p.2 1-21/610)]

theorem projected_norm_sq (t : ℝ) : ‖Chapter03.yMap 0 2 (line t)‖^2=1/610+610*t^2 := by
  simp [Chapter03.yMap,line,pt,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]
  ring

theorem projected_norm_lt_one {p : P} (hp : p ∈ data.relaxation) :
    ‖Chapter03.yMap 0 2 p‖ < 1 := by
  obtain ⟨t,ht,ht',rfl⟩ := (relaxation_param p).mp hp
  have hsq := projected_norm_sq t
  have hb := mul_nonneg (by linarith : 0 ≤ t+1/1000) (by linarith : 0 ≤ 1/1000-t)
  nlinarith [norm_nonneg (Chapter03.yMap 0 2 (line t))]

theorem selected_targets_far : 4 < ‖intY (target 0)‖ ∧ 4 < ‖intY (target 1)‖ := by
  have h0 : ‖intY (target 0)‖^2=89 := by
    norm_num [intY,intCast,target,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two,Real.norm_eq_abs]
  have h1 : ‖intY (target 1)‖^2=233 := by
    norm_num [intY,intCast,target,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two,Real.norm_eq_abs]
  constructor <;> nlinarith [norm_nonneg (intY (target 0)),norm_nonneg (intY (target 1))]

end Chapter03.FPUnboundedFar
