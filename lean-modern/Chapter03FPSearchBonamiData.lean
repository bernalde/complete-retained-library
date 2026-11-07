module

public import Chapter03FPSearchModel
public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! Held Bonami2006 Examples1/2, with coordinates renamed to the thesis's
continuous x and integer y convention. The omitted objective is instantiated as
zero, so the displayed feasible seed is an attained initialization minimum.
Every displayed row and the original binary bounds are retained. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch.Bonami

abbrev P := Point 2 1

def point (u v t : ℝ) : P := (![u,v], fun _ => t)
def integer (t : ℤ) : IntVector 1 := fun _ => t
def xc (i : Fin 2) : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
def yc : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem xc_apply (i : Fin 2) (p : P) : xc i p = p.1 i := rfl
@[simp] theorem yc_apply (p : P) : yc p = p.2 0 := rfl

def base : Set P := {p | 0 ≤ p.2 0 ∧ p.2 0 ≤ 1}
def row : Fin 3 → P → ℝ := ![
  fun p => (p.1 0-1/2)^2+(p.1 1-1/2)^2-1/4,
  fun p => p.2 0-p.1 0,
  fun p => p.1 1]
def rowD (j : Fin 3) (p : P) : P →L[ℝ] ℝ := ![
  (2*(p.1 0-1/2)) • xc 0 + (2*(p.1 1-1/2)) • xc 1,
  yc-xc 0,
  xc 1] j

def data : Data 2 1 3 where
  base := base
  f _ := 0
  g := row
  Df _ := 0
  Dg := rowD

def seed : P := point (1/2) 0 (1/2)
def projectedZero : P := point (1/2) 0 0
def masterOne : P := point 1 0 1

theorem base_closed : IsClosed base :=
  (isClosed_le continuous_const yc.continuous).inter
    (isClosed_le yc.continuous continuous_const)

theorem base_convex : Convex ℝ base := by
  intro p hp q hq a b ha hb hab
  constructor
  · change 0 ≤ a * p.2 0 + b * q.2 0
    exact add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)
  · change a * p.2 0 + b * q.2 0 ≤ 1
    nlinarith [mul_le_mul_of_nonneg_left hp.2 ha,
      mul_le_mul_of_nonneg_left hq.2 hb]

theorem row_derivative (j : Fin 3) (p : P) : HasFDerivAt (row j) (rowD j p) p := by
  fin_cases j
  · exact ((FPTrace.square_derivative (xc 0) (1/2) p).add
      (FPTrace.square_derivative (xc 1) (1/2) p)).sub_const (1/4)
  · exact yc.hasFDerivAt.sub (xc 0).hasFDerivAt
  · exact (xc 1).hasFDerivAt

theorem row_convex (j : Fin 3) : ConvexOn ℝ base (row j) := by
  fin_cases j
  · simpa [row,Pi.add_def,sub_eq_add_neg] using
      ((FPTrace.square_convex base_convex (xc 0) (1/2)).add
        (FPTrace.square_convex base_convex (xc 1) (1/2))).add_const (-(1/4))
  · exact FPTrace.linear_convex base_convex (yc-xc 0)
  · exact FPTrace.linear_convex base_convex (xc 1)

theorem feasible_iff (p : P) :
    (p ∈ base ∧ ∀ j, row j p ≤ 0) ↔
      p.1 0=1/2 ∧ p.1 1=0 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1/2 := by
  constructor
  · rintro ⟨hb,hg⟩
    have h0 := hg 0
    have h1 := hg 1
    have h2 := hg 2
    change (p.1 0-1/2)^2+(p.1 1-1/2)^2-1/4 ≤ 0 at h0
    change p.2 0-p.1 0 ≤ 0 at h1
    change p.1 1 ≤ 0 at h2
    have hv : p.1 1=0 := by nlinarith [sq_nonneg (p.1 0-1/2),sq_nonneg (p.1 1)]
    have hu : p.1 0=1/2 := by rw [hv] at h0; nlinarith [sq_nonneg (p.1 0-1/2)]
    exact ⟨hu,hv,hb.1,by linarith⟩
  · rintro ⟨hu,hv,ht0,ht1⟩
    refine ⟨⟨ht0,by linarith⟩,?_⟩
    intro j
    fin_cases j <;> simp [row,hu,hv] <;> linarith

theorem feasible_bounded : Bornology.IsBounded {p | p ∈ base ∧ ∀ j, row j p ≤ 0} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (point (1/2) 0 0)
    (point (1/2) 0 (1/2)))).isBounded.subset
  intro p hp
  obtain ⟨hu,hv,ht0,ht1⟩ := (feasible_iff p).mp hp
  constructor <;> constructor
  · intro i; fin_cases i <;> simp [point,hu,hv]
  · intro i; fin_cases i; exact ht0
  · intro i; fin_cases i <;> simp [point,hu,hv]
  · intro i; fin_cases i; exact ht1

theorem analytic : Analytic data := by
  refine ⟨base_closed,base_convex,convexOn_const 0 base_convex,row_convex,?_,?_,?_,?_⟩
  · intro p hp; exact hasFDerivAt_const 0 p
  · intro j p hp; exact row_derivative j p
  · exact feasible_bounded
  · norm_num [Data.toUnbounded]

theorem relaxation_iff (p : P) : p ∈ data.relaxation ↔
    p.1 0=1/2 ∧ p.1 1=0 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1/2 :=
  feasible_iff p

theorem seed_feasible : seed ∈ base ∧ ∀ j, row j seed ≤ 0 :=
  (feasible_iff seed).mpr (by norm_num [seed,point])

theorem zero_feasible : projectedZero ∈ base ∧ ∀ j, row j projectedZero ≤ 0 :=
  (feasible_iff projectedZero).mpr (by norm_num [projectedZero,point])

theorem seed_fractional : ¬∃ y : IntVector 1, seed.2=intCast y := by
  rintro ⟨y,hy⟩
  have he : (1/2:ℝ)=(y 0:ℝ) := congrFun hy 0
  have hl : (0:ℝ)<(y 0:ℝ) := by linarith
  have hu : (y 0:ℝ)<1 := by linarith
  have hl' : 0<y 0 := by exact_mod_cast hl
  have hu' : y 0<1 := by exact_mod_cast hu
  omega

theorem seed_minimum : IsMinimizer {p | p ∈ base ∧ ∀ j, row j p ≤ 0}
    (fun _ : P => (0:ℝ)) seed := ⟨seed_feasible,fun _ _ => le_rfl⟩

theorem projection_one : IsMinimizer {p | p ∈ base ∧ ∀ j, row j p ≤ 0}
    (distance (integer 1)) seed := by
  refine ⟨seed_feasible,?_⟩
  intro p hp
  have ht := ((feasible_iff p).mp hp).2.2.2
  simp only [FPUnboundedControls.scalar_distance]
  norm_num [integer,seed,point]
  nlinarith [sq_nonneg (p.2 0-1/2)]

theorem projection_zero : IsMinimizer {p | p ∈ base ∧ ∀ j, row j p ≤ 0}
    (distance (integer 0)) projectedZero := by
  refine ⟨zero_feasible,?_⟩
  intro p hp
  simpa [FPUnboundedControls.scalar_distance,integer,projectedZero,point] using sq_nonneg (p.2 0)

theorem first_row_nonlinear : ¬OAKKT.AffineRow (row 0) := by
  intro h
  have ht := OAKKT.affine_tangent h (row_derivative 0 seed) (point (3/2) 0 (1/2))
  norm_num [row,rowD,seed,point] at ht

end Chapter03.FPSearch.Bonami
