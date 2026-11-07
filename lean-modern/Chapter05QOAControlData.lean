module

public import Chapter05QOAModel
public import Chapter03OAKKTSource
public import Chapter05QuadraticMaster
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The one prescribed N2 polynomial control. These analytic and domain facts
do not by themselves prove complete-history exactness or execution/return. -/
noncomputable section
open Set Chapter02 Chapter03.OAKKT
open scoped BigOperators
namespace Chapter05.QOA.Control

abbrev P := Point 2 1

def pt (v w y : ℝ) : P := (![v,w], fun _ => y)
def iv (y : ℤ) : IntVector 1 := fun _ => y
def vc : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ _ _)
def wc : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.fst ℝ _ _)
def yc : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem vc_apply (p : P) : vc p = p.1 0 := rfl
@[simp] theorem wc_apply (p : P) : wc p = p.1 1 := rfl
@[simp] theorem yc_apply (p : P) : yc p = p.2 0 := rfl
@[simp] theorem iv_apply (y : ℤ) (i : Fin 1) : iv y i = y := rfl
@[simp] theorem pt_v (v w y : ℝ) : (pt v w y).1 0 = v := rfl
@[simp] theorem pt_w (v w y : ℝ) : (pt v w y).1 1 = w := rfl
@[simp] theorem pt_y (v w y : ℝ) (i : Fin 1) : (pt v w y).2 i = y := rfl

theorem pt_eta (z : P) : pt (z.1 0) (z.1 1) (z.2 0) = z := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

def objective (z : P) : ℝ := (z.1 0+1)^2 + (z.1 1)^2 + z.2 0
def constraint (z : P) : ℝ := (z.1 1)^2 + 1 - 2*z.2 0
def Dobjective (z : P) : P →L[ℝ] ℝ :=
  (2*(z.1 0+1)) • vc + (2*z.1 1) • wc + yc
def Dconstraint (z : P) : P →L[ℝ] ℝ := (2*z.1 1) • wc - (2 : ℝ) • yc

theorem square_derivative (L : P →L[ℝ] ℝ) (c : ℝ) (z : P) :
    HasFDerivAt (fun p => (L p-c)^2) ((2*(L z-c)) • L) z := by
  have hd := ((L.hasFDerivAt (x := z)).sub_const c).fun_mul
    ((L.hasFDerivAt (x := z)).sub_const c)
  simpa only [pow_two] using hd.congr_fderiv (show
    (L z-c) • L + (L z-c) • L = (2*(L z-c)) • L by
      apply ContinuousLinearMap.ext; intro p; simp; ring)

theorem objective_hasFDerivAt (z : P) :
    HasFDerivAt objective (Dobjective z) z := by
  unfold objective Dobjective
  simpa using
    ((square_derivative vc (-1) z).fun_add (square_derivative wc 0 z)).fun_add
      (yc.hasFDerivAt (x := z))

theorem constraint_hasFDerivAt (z : P) :
    HasFDerivAt constraint (Dconstraint z) z := by
  unfold constraint Dconstraint
  simpa using
    ((square_derivative wc 0 z).add_const 1).fun_sub
      ((yc.hasFDerivAt (x := z)).const_mul 2)

@[simp] theorem objective_fderiv (z : P) : fderiv ℝ objective z = Dobjective z :=
  (objective_hasFDerivAt z).fderiv

@[simp] theorem constraint_fderiv (z : P) : fderiv ℝ constraint z = Dconstraint z :=
  (constraint_hasFDerivAt z).fderiv

theorem objective_C2 : ContDiff ℝ 2 objective := by
  exact (((vc.contDiff.add contDiff_const).pow 2).add (wc.contDiff.pow 2)).add yc.contDiff

theorem constraint_C2 : ContDiff ℝ 2 constraint := by
  exact ((wc.contDiff.pow 2).add contDiff_const).sub (contDiff_const.mul yc.contDiff)

theorem square_convex (L : P →L[ℝ] ℝ) (c : ℝ) :
    ConvexOn ℝ univ (fun z => (L z-c)^2) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  simp only [map_add, map_smul, smul_eq_mul]
  have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (L p-L q))
  have he : b = 1-a := by linarith
  subst b
  nlinarith

theorem objective_convex : ConvexOn ℝ univ objective := by
  have h := ((square_convex vc (-1)).add (square_convex wc 0)).add
    (yc.toLinearMap.convexOn convex_univ)
  exact h.congr (fun _ _ => by simp [objective, Pi.add_def])

theorem constraint_convex : ConvexOn ℝ univ constraint := by
  have h := ((square_convex wc 0).add (convexOn_const (1 : ℝ) (convex_univ : Convex ℝ (univ : Set P)))).add
    (((-2 : ℝ) • yc).toLinearMap.convexOn convex_univ)
  convert h using 1
  ext z
  simp [constraint]
  ring

def X : Set (RealVector 2) := Icc ![0,-2] ![1,2]
def Y : Finset (IntVector 1) := {iv 0,iv 1}
def relaxedY : Set (RealVector 1) := Icc 0 1

theorem mem_X (x : RealVector 2) :
    x ∈ X ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ -2 ≤ x 1 ∧ x 1 ≤ 2 := by
  simp only [X, mem_Icc, Pi.le_def, Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  tauto

theorem X_compact : IsCompact X := isCompact_Icc
theorem X_convex : Convex ℝ X := convex_Icc _ _
theorem zero_mem_X : (0 : RealVector 2) ∈ X := by norm_num [mem_X]
theorem X_nonempty : X.Nonempty := ⟨0,zero_mem_X⟩
theorem mem_Y (y : IntVector 1) : y ∈ Y ↔ y = iv 0 ∨ y = iv 1 := by simp [Y]
theorem Y_card : Y.card = 2 := by
  have h : iv 0 ≠ iv 1 := by intro h; have := congrFun h 0; norm_num at this
  simp [Y,h]
theorem relaxedY_compact : IsCompact relaxedY := isCompact_Icc
theorem relaxedY_convex : Convex ℝ relaxedY := convex_Icc _ _
theorem cast_Y_mem_relaxedY {y : IntVector 1} (hy : y ∈ Y) :
    Chapter03.OAKKT.intCast y ∈ relaxedY := by
  rcases (mem_Y y).mp hy with rfl | rfl <;>
    norm_num [relaxedY, Chapter03.OAKKT.intCast, iv, mem_Icc, Pi.le_def]

def seed : P := pt 0 0 (1/2)
def optimum : P := pt 0 0 1
def trial : P := pt 0 2 1
def restorationAnchor : P := pt 0 0 0

theorem objective_seed : objective seed = 3/2 := by norm_num [objective, seed]
theorem objective_optimum : objective optimum = 2 := by norm_num [objective, optimum]
theorem constraint_optimum : constraint optimum = -1 := by norm_num [constraint, optimum]
theorem constraint_trial : constraint trial = 3 := by norm_num [constraint, trial]
theorem constraint_restorationAnchor : constraint restorationAnchor = 1 := by
  norm_num [constraint, restorationAnchor]
theorem trial_ne_optimum : trial ≠ optimum := by
  intro h
  have := congrArg (fun z : P => z.1 1) h
  norm_num [trial,optimum] at this

theorem objective_tangent_at (y : ℝ) (z : P) :
    Chapter05.Quadratic.tangent objective (pt 0 0 y) z = 1+2*z.1 0+z.2 0 := by
  simp [Chapter05.Quadratic.tangent, objective, Dobjective]
  ring

theorem constraint_tangent_at (y : ℝ) (z : P) :
    Chapter05.Quadratic.tangent constraint (pt 0 0 y) z = 1-2*z.2 0 := by
  simp [Chapter05.Quadratic.tangent, constraint, Dconstraint]
  ring

theorem objective_zero_cut_at (y : ℝ) (z : P) :
    Chapter05.Quadratic.cut objective (pt 0 0 y) 0 z = 1+2*z.1 0+z.2 0 := by
  rw [Chapter05.Quadratic.cut_zero, objective_tangent_at]

theorem constraint_zero_cut_at (y : ℝ) (z : P) :
    Chapter05.Quadratic.cut constraint (pt 0 0 y) 0 z = 1-2*z.2 0 := by
  rw [Chapter05.Quadratic.cut_zero, constraint_tangent_at]

def boundaryNormal : RealVector 2 →L[ℝ] ℝ :=
  (-2 : ℝ) • ContinuousLinearMap.proj 0

theorem boundaryNormal_derivative : boundaryNormal =
    -Chapter03.OAKKT.restrict (fderiv ℝ objective optimum) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [boundaryNormal, Dobjective, optimum, Chapter03.OAKKT.restrict_apply]

theorem boundaryNormal_nonzero : boundaryNormal ≠ 0 := by
  intro h
  have := congrArg (fun D : RealVector 2 →L[ℝ] ℝ => D ![1,0]) h
  norm_num [boundaryNormal] at this

theorem boundaryNormal_nonpos {x : RealVector 2} (hx : x ∈ X) :
    boundaryNormal (x-0) ≤ 0 := by
  have hv := ((mem_X x).mp hx).1
  simp [boundaryNormal]
  linarith


def data : Data 2 1 1 0 where
  f := objective
  g _ := constraint
  X := X
  Y := Y
  A := Fin.elim0
  E := Fin.elim0
  b := Fin.elim0
  relaxedY := relaxedY

theorem hardFiber_eq_X (y : IntVector 1) : data.hardFiber y = X := by
  ext x
  simp [Data.hardFiber,Data.affineFiber,data]

theorem feasibleFiber_mem (y : IntVector 1) (x : RealVector 2) :
    x ∈ data.feasibleFiber y ↔ x ∈ X ∧ (x 1)^2+1-2*(y 0 : ℝ) ≤ 0 := by
  change (x ∈ data.hardFiber y ∧ ∀ j : Fin 1, constraint (x,intCast y) ≤ 0) ↔ _
  rw [hardFiber_eq_X]
  simp [constraint,intCast]

theorem zero_fiber_empty : ¬ (data.feasibleFiber (iv 0)).Nonempty := by
  rintro ⟨x,hx⟩
  have h := ((feasibleFiber_mem (iv 0) x).mp hx).2
  norm_num at h
  nlinarith [sq_nonneg (x 1)]

theorem one_fiber_minimum :
    IsMinimizer (data.feasibleFiber (iv 1)) (data.fiberObjective (iv 1)) 0 := by
  refine ⟨?_,?_⟩
  · rw [feasibleFiber_mem]
    exact ⟨zero_mem_X,by norm_num⟩
  · intro x hx
    have hv := ((mem_X x).mp ((feasibleFiber_mem _ _).mp hx).1).1
    change objective (0,intCast (iv 1)) ≤ objective (x,intCast (iv 1))
    simp [objective,intCast,iv]
    nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]

theorem regularity : Regularity data where
  objective_convex := objective_convex
  objective_C2 := objective_C2
  constraint_convex _ := constraint_convex
  constraint_C2 _ := constraint_C2
  X_nonempty := X_nonempty
  X_compact := X_compact
  X_convex := X_convex
  fiber_slater := by
    intro y hy hne
    rcases (mem_Y y).mp hy with rfl | rfl
    · exact (zero_fiber_empty hne).elim
    · refine ⟨0,?_,?_⟩
      · simpa [hardFiber_eq_X] using zero_mem_X
      · intro j
        norm_num [Data.soft,data,constraint,intCast,iv]

theorem relaxation_regularity : RelaxationRegularity data :=
  ⟨relaxedY_compact,relaxedY_convex,fun _ hy => cast_Y_mem_relaxedY hy⟩

theorem zero_restoration_minimum :
    IsMinimizer (data.restSet (iv 0)) data.restCost
      (weightedInsert (0 : RealVector 2) (fun _ : Fin 1 => (1 : ℝ))) := by
  refine ⟨?_,?_⟩
  · rw [restSet_insert_iff]
    refine ⟨by simpa [hardFiber_eq_X] using zero_mem_X,?_,?_⟩ <;>
      intro j <;> norm_num [Data.soft,data,constraint,intCast,iv]
  · intro q hq
    have hrows := (weighted_lift_rows_iff
      (Fin.elim0 : Fin 0 → RealVector 2 → ℝ) (data.soft (iv 0)) q).mp hq.2
    have hs := hrows.2.1 (0 : Fin 1)
    simp only [Data.soft,data,constraint,intCast,iv,Int.cast_zero,mul_zero,sub_zero] at hs
    rw [restCost_insert]
    simp only [Fin.sum_univ_one,Data.restCost,weightedLiftObjective_apply,
      one_mul,Fin.sum_univ_one]
    nlinarith [sq_nonneg ((weightedX q) 1)]

def zeroToken (a : P) : Token 2 1 1 := ⟨a,0,fun _ => 0⟩

theorem zeroToken_safe (a : P) : (zeroToken a).Safe data := by
  refine ⟨⟨le_rfl,?_⟩,?_⟩
  · exact (Quadratic.safeScale_bounds objective_convex objective_C2 a data.base).1
  · intro j
    exact ⟨le_rfl,(Quadratic.safeScale_bounds constraint_convex constraint_C2 a data.base).1⟩

def feasibleEvent : Event data where
  target := iv 1
  target_mem := by simp [data,Y]
  x := 0
  restoration := none
  objectiveScale := 0
  constraintScale _ := 0

def restorationEvent : Event data where
  target := iv 0
  target_mem := by simp [data,Y]
  x := 0
  restoration := some (fun _ => 1)
  objectiveScale := 0
  constraintScale _ := 0

theorem feasibleEvent_valid : EventValid data feasibleEvent := by
  exact ⟨zeroToken_safe _,one_fiber_minimum⟩

theorem restorationEvent_valid : EventValid data restorationEvent := by
  exact ⟨zeroToken_safe _,zero_fiber_empty,zero_restoration_minimum⟩

@[simp] theorem feasibleEvent_anchor : feasibleEvent.anchor = optimum := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    norm_num [Event.anchor,feasibleEvent,optimum,pt,intCast,iv]

@[simp] theorem restorationEvent_anchor : restorationEvent.anchor = restorationAnchor := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    norm_num [Event.anchor,restorationEvent,restorationAnchor,pt,intCast,iv]

theorem optimum_original : optimum ∈ data.original := by
  rw [← feasibleEvent_anchor]
  exact event_feasible feasibleEvent_valid rfl

theorem trial_not_original : trial ∉ data.original := by
  intro h
  have h0 := h.2 (0 : Fin 1)
  change constraint trial ≤ 0 at h0
  rw [constraint_trial] at h0
  norm_num at h0

theorem seed_relaxation_minimum : IsMinimizer data.relaxation data.f seed := by
  refine ⟨?_,?_⟩
  · refine ⟨?_,?_,?_,?_⟩
    · norm_num [data,seed,pt,mem_X]
    · norm_num [data,seed,pt,relaxedY,mem_Icc,Pi.le_def]
    · intro i
      exact Fin.elim0 i
    · intro j
      norm_num [data,constraint,seed]
  · intro z hz
    have hv := ((mem_X z.1).mp hz.1).1
    have hg := hz.2.2.2 (0 : Fin 1)
    change constraint z ≤ 0 at hg
    change objective seed ≤ objective z
    rw [objective_seed]
    unfold constraint at hg
    unfold objective
    nlinarith [sq_nonneg (z.1 0),sq_nonneg (z.1 1)]

theorem seed_fractional : ¬ ∃ y ∈ data.Y, seed.2 = intCast y := by
  rintro ⟨y,hy,h⟩
  rcases (mem_Y y).mp hy with rfl | rfl <;>
    have hh := congrFun h 0 <;>
    norm_num [seed,intCast,iv] at hh

def completeEvents : List (Event data) := [restorationEvent,feasibleEvent]
def completeRows : List (Token 2 1 1) := completeEvents.map Event.token
def seedRows : List (Token 2 1 1) := [zeroToken seed]

@[simp] theorem feasibleEvent_token : feasibleEvent.token = zeroToken optimum := by
  change Token.mk feasibleEvent.anchor 0 (fun _ => 0) = _
  rw [feasibleEvent_anchor]
  rfl

@[simp] theorem restorationEvent_token : restorationEvent.token = zeroToken restorationAnchor := by
  change Token.mk restorationEvent.anchor 0 (fun _ => 0) = _
  rw [restorationEvent_anchor]
  rfl

def commonMaster : Set (P × ℝ) :=
  {q | q.1 ∈ data.base ∧ 1+2*q.1.1 0+q.1.2 0 ≤ q.2 ∧ 1-2*q.1.2 0 ≤ 0}

theorem master_common (H : List (Token 2 1 1)) (hne : H ≠ [])
    (hrows : ∀ t ∈ H, ∃ y : ℝ, t = zeroToken (pt 0 0 y)) :
    master data H = commonMaster := by
  cases H with
  | nil => exact (hne rfl).elim
  | cons t H =>
    ext q
    rw [master_mem_iff]
    constructor
    · rintro ⟨hb,hf,hg⟩
      obtain ⟨y,rfl⟩ := hrows t (by simp)
      have hf0 := hf (zeroToken (pt 0 0 y)) (by simp)
      have hg0 := hg (zeroToken (pt 0 0 y)) (by simp) (0 : Fin 1)
      change Quadratic.cut objective (pt 0 0 y) 0 q.1 ≤ q.2 at hf0
      change Quadratic.cut constraint (pt 0 0 y) 0 q.1 ≤ 0 at hg0
      rw [objective_zero_cut_at] at hf0
      rw [constraint_zero_cut_at] at hg0
      exact ⟨hb,hf0,hg0⟩
    · rintro ⟨hb,hf,hg⟩
      refine ⟨hb,?_,?_⟩
      · intro a ha
        obtain ⟨y,rfl⟩ := hrows a ha
        change Quadratic.cut objective (pt 0 0 y) 0 q.1 ≤ q.2
        rw [objective_zero_cut_at]
        exact hf
      · intro a ha j
        obtain ⟨y,rfl⟩ := hrows a ha
        change Quadratic.cut constraint (pt 0 0 y) 0 q.1 ≤ 0
        rw [constraint_zero_cut_at]
        exact hg

theorem trial_base : trial ∈ data.base := by
  refine ⟨iv 1,by simp [data,Y],?_,?_⟩
  · funext i
    norm_num [trial,intCast,iv]
  · rw [hardFiber_eq_X]
    norm_num [mem_X,trial]

theorem commonMaster_trial_minimum : IsMinimizer commonMaster Prod.snd (trial,2) := by
  refine ⟨⟨trial_base,?_,?_⟩,?_⟩
  · norm_num [trial]
  · norm_num [trial]
  · rintro q ⟨⟨y,hy,he,hx⟩,hf,hg⟩
    have hv := ((mem_X q.1.1).mp ((hardFiber_eq_X y) ▸ hx)).1
    have hy0 := congrFun he 0
    rcases (mem_Y y).mp hy with rfl | rfl
    · norm_num [intCast,iv] at hy0
      rw [hy0] at hg
      norm_num at hg
    · norm_num [intCast,iv] at hy0
      rw [hy0] at hf
      change 2 ≤ q.2
      linarith

theorem seed_master_eq : master data seedRows = commonMaster := by
  apply master_common
  · simp [seedRows]
  · intro t ht
    simp only [seedRows,List.mem_singleton] at ht
    subst t
    exact ⟨1/2,rfl⟩

theorem complete_master_eq : master data completeRows = commonMaster := by
  apply master_common
  · simp [completeRows,completeEvents]
  · intro t ht
    simp only [completeRows,completeEvents,List.map_cons,List.map_nil,
      List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨0,by rw [restorationEvent_token]; rfl⟩
    · exact ⟨1,by rw [feasibleEvent_token]; rfl⟩

theorem seed_master_minimum : IsMinimizer (master data seedRows) Prod.snd (trial,2) := by
  rw [seed_master_eq]
  exact commonMaster_trial_minimum

theorem complete_master_minimum : IsMinimizer (master data completeRows) Prod.snd (trial,2) := by
  rw [complete_master_eq]
  exact commonMaster_trial_minimum

end Chapter05.QOA.Control
