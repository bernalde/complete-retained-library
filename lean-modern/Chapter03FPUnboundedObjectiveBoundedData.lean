module

public import Chapter03FPUnboundedSourceAdapters
public import Chapter03FPTraceCommon
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Limitation control for the objective-bounded interpretation of A3. The
continuous feasible set is unbounded and the next exact projection has no
minimizer; this is outside the bounded-feasible-relaxation theorem's hypotheses. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedObjectiveBounded

abbrev P := Point 1 1

def pt (x y : ℝ) : P := (fun _ => x, fun _ => y)
def iv (y : ℤ) : IntVector 1 := fun _ => y

def xc : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ _ _)
def yc : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
@[simp] theorem xc_apply (p : P) : xc p = p.1 0 := rfl
@[simp] theorem yc_apply (p : P) : yc p = p.2 0 := rfl

@[simp] theorem pt_fst (x y : ℝ) (j : Fin 1) : (pt x y).1 j = x := rfl
@[simp] theorem pt_snd (x y : ℝ) (j : Fin 1) : (pt x y).2 j = y := rfl
@[simp] theorem iv_apply (y : ℤ) (j : Fin 1) : iv y j = y := rfl

def base : Set P := {p | 1 ≤ p.1 0 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1}
def objective (p : P) : ℝ := (p.2 0 - 1/2)^2
def row (_ : Fin 1) (p : P) : ℝ := (p.1 0)⁻¹ - p.2 0

def objectiveDerivative (p : P) : P →L[ℝ] ℝ := (2*(p.2 0-1/2)) • yc
def rowDerivative (_ : Fin 1) (p : P) : P →L[ℝ] ℝ :=
  (-(p.1 0 ^ 2)⁻¹) • xc - yc

def data : FPUnbounded.Data 1 1 1 :=
  ⟨base,objective,row,objectiveDerivative,rowDerivative,1/20⟩

def seed : P := pt 2 (1/2)
def integerOptimum : P := pt 1 1
def start : State 1 1 := initialState seed

def xBounds : OAKKT.Bounds 1 := ⟨fun _ => .finite 1, fun _ => .posInfinity⟩
def yBounds : OAKKT.Bounds 1 := ⟨fun _ => .finite 0, fun _ => .finite 1⟩

theorem base_source_identity : base = FPUnbounded.boundProduct xBounds yBounds := by
  ext p
  simp [base,FPUnbounded.boundProduct,OAKKT.Bounds.region,xBounds,yBounds,
    OAKKT.ExtendedBound.lowerHolds,OAKKT.ExtendedBound.upperHolds,Fin.forall_fin_one]

def article : FPUnbounded.ArticleData 1 1 1 where
  xBounds := xBounds
  yBounds := yBounds
  yLower_integral := by
    intro i a h
    have he : a = 0 := by simpa [yBounds] using h.symm
    exact ⟨0,by simpa using he⟩
  yUpper_integral := by
    intro i a h
    have he : a = 1 := by simpa [yBounds] using h.symm
    exact ⟨1,by simpa using he⟩
  f := objective
  g := row
  Df := objectiveDerivative
  Dg := rowDerivative
  delta := 1/20

theorem article_data_identity : article.toData = data := by
  simp only [article,FPUnbounded.ArticleData.toData,data,base_source_identity]

theorem base_closed : IsClosed base := by
  rw [base_source_identity]
  exact FPUnbounded.boundProduct_closed _ _

theorem base_convex : Convex ℝ base := by
  rw [base_source_identity]
  exact FPUnbounded.boundProduct_convex _ _

theorem objective_derivative (p : P) :
    HasFDerivAt objective (objectiveDerivative p) p :=
  FPTrace.square_derivative yc (1/2) p

theorem row_derivative (j : Fin 1) (p : P) (hp : p ∈ base) :
    HasFDerivAt (row j) (rowDerivative j p) p := by
  have hx : xc p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hp.1)
  exact ((hasDerivAt_inv hx).comp_hasFDerivAt p xc.hasFDerivAt).sub yc.hasFDerivAt

theorem objective_convex : ConvexOn ℝ base objective :=
  FPTrace.square_convex base_convex yc (1/2)

theorem row_convex (j : Fin 1) : ConvexOn ℝ base (row j) := by
  have hinv : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x⁻¹) := by
    simpa using (convexOn_zpow (-1 : ℤ) : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x^(-1:ℤ)))
  have hcomp := hinv.comp_linearMap xc.toLinearMap
  have hi : ConvexOn ℝ base (fun p => (xc p)⁻¹) :=
    hcomp.subset (fun p hp => lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hp.1) base_convex
  have hn : ConvexOn ℝ base (fun p => -yc p) := by
    exact (FPTrace.linear_convex base_convex (-yc)).congr (fun _ _ => rfl)
  change ConvexOn ℝ base (fun p : P => (p.1 0)⁻¹-p.2 0)
  simpa [Pi.add_def,sub_eq_add_neg] using hi.add hn

theorem objective_C1 : ContDiffOn ℝ 1 objective base := by
  have h : ContDiff ℝ 1 (fun p : P => (yc p - (1/2:ℝ))^2) :=
    (yc.contDiff.sub contDiff_const).pow 2
  exact h.contDiffOn

theorem row_C1 (j : Fin 1) : ContDiffOn ℝ 1 (row j) base := by
  have hi : ContDiffOn ℝ 1 (fun p : P => (xc p)⁻¹) base :=
    xc.contDiff.contDiffOn.inv (fun p hp =>
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hp.1))
  exact hi.sub yc.contDiff.contDiffOn

theorem relaxation_iff (p : P) : p ∈ data.relaxation ↔
    (1 ≤ p.1 0 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1) ∧ (p.1 0)⁻¹ ≤ p.2 0 := by
  simp [data,FPUnbounded.Data.relaxation,base,row,Fin.forall_fin_one,sub_nonpos]

theorem relaxation_y_positive {p : P} (hp : p ∈ data.relaxation) : 0 < p.2 0 := by
  have h := (relaxation_iff p).mp hp
  exact (inv_pos.mpr (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) h.1.1)).trans_le h.2

theorem objective_bounded {p : P} (hp : p ∈ data.relaxation) :
    0 ≤ data.f p ∧ data.f p ≤ 1/4 := by
  have h := (relaxation_iff p).mp hp
  change 0 ≤ (p.2 0-1/2)^2 ∧ (p.2 0-1/2)^2 ≤ 1/4
  refine ⟨sq_nonneg _,?_⟩
  nlinarith [mul_nonneg h.1.2.1 (sub_nonneg.mpr h.1.2.2)]

theorem seed_minimum : IsMinimizer data.relaxation data.f seed := by
  refine ⟨?_,?_⟩
  · rw [relaxation_iff]; norm_num [seed,pt]
  · intro p hp
    simpa [data,objective,seed,pt] using (objective_bounded hp).1

theorem original_iff (p : P) : p ∈ data.original ↔ 1 ≤ p.1 0 ∧ p.2 0 = 1 := by
  constructor
  · rintro ⟨hp,y,hy⟩
    have hr := (relaxation_iff p).mp hp
    have he : p.2 0 = (y 0 : ℝ) := congrFun hy 0
    have hpos := relaxation_y_positive hp
    have hi : (0:ℤ) < y 0 := by exact_mod_cast (show (0:ℝ) < (y 0 : ℝ) by linarith)
    have hu : y 0 ≤ (1:ℤ) := by exact_mod_cast (show (y 0 : ℝ) ≤ (1:ℝ) by linarith [hr.1.2.2])
    have hye : y 0 = 1 := by omega
    exact ⟨hr.1.1,by simpa [hye] using he⟩
  · rintro ⟨hx,hy⟩
    refine ⟨?_,iv 1,?_⟩
    · rw [relaxation_iff]
      refine ⟨⟨hx,by rw [hy]; norm_num,by rw [hy]⟩,?_⟩
      rw [hy]
      exact inv_le_one_of_one_le₀ hx
    · funext j
      fin_cases j
      simpa [FP.intCast,iv] using hy

theorem original_minimum : IsMinimizer data.original data.f integerOptimum := by
  refine ⟨(original_iff _).mpr (by norm_num [integerOptimum,pt]),?_⟩
  intro p hp
  have hy := ((original_iff p).mp hp).2
  norm_num [data,objective,integerOptimum,pt,hy]

theorem original_objective (p : P) (hp : p ∈ data.original) : data.f p = 1/4 := by
  have hy := ((original_iff p).mp hp).2
  norm_num [data,objective,hy]

theorem ray_feasible (x : ℝ) (hx : 1 ≤ x) : pt x 1 ∈ data.relaxation := by
  rw [relaxation_iff]
  exact ⟨⟨hx,by norm_num [pt],by simp [pt]⟩,inv_le_one_of_one_le₀ hx⟩

theorem relaxation_unbounded : ¬Bornology.IsBounded data.relaxation := by
  intro hb
  obtain ⟨R,hR⟩ := hb.exists_norm_le
  let x := max 1 (R+1)
  have hx : 1 ≤ x := le_max_left _ _
  have hm := hR (pt x 1) (ray_feasible x hx)
  have hc := (norm_le_pi_norm ((pt x 1).1) (0 : Fin 1)).trans (norm_fst_le (pt x 1))
  have hxr : R+1 ≤ x := le_max_right _ _
  have habs : |x| = x := abs_of_nonneg (le_trans (by norm_num) hx)
  have hcx : x ≤ ‖pt x 1‖ := by simpa [pt,Real.norm_eq_abs,habs] using hc
  linarith

theorem not_analytic : ¬FPUnbounded.Analytic data := fun h =>
  relaxation_unbounded h.bounded_relaxation

end Chapter03.FPUnboundedObjectiveBounded
