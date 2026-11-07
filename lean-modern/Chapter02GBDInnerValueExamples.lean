module

public import Chapter02GBDInnerValueSource
public import Chapter02MultiplierExistence
public import Chapter02KKTExamples

@[expose] public section

/-! Whole-model controls for the first all-row, unrestricted-continuous-space
inner-value bridge. Finite box facets remain literal affine residuals. These
models do not implement arbitrary retained-X infima, master equality or a
classical GBD procedure. Candidate only, pending frozen independent review. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter02GBDInnerValueExamples

def aPoint (z t y : ℝ) : Point 2 1 := (![z,t], ![y])
def aZ : Point 2 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ (RealVector 2) (RealVector 1))
def aT : Point 2 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.fst ℝ (RealVector 2) (RealVector 1))
def aY : Point 2 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ (RealVector 2) (RealVector 1))

def aModel : ModelData 2 1 1 4 where
  g := fun _ p => (p.1 0)^2 + p.2 0 - p.1 1
  A := ![![1,0], ![-1,0], ![0,1], ![0,-1]]
  B := 0
  rhs := ![1,1,4,1]
  c1 := ![0,1]
  c2 := ![1]
  lo := ![0]
  hi := ![2]

def aD (_ : Fin 1) : Point 2 1 →L[ℝ] ℝ := aY-aT

theorem a_linear (p : Point 2 1) : p ∈ aModel.linearRegion ↔
    p.1 0 ≤ 1 ∧ -p.1 0 ≤ 1 ∧ p.1 1 ≤ 4 ∧ -p.1 1 ≤ 1 := by
  simp [ModelData.linearRegion, aModel, LinearForm, Fin.forall_fin_succ,
    Fin.sum_univ_succ]

theorem a_objective (p : Point 2 1) : aModel.objective p = p.1 1 + p.2 0 := by
  simp [ModelData.objective, aModel, LinearForm, Fin.sum_univ_succ]

theorem a_convex : ∀ j, ConvexOn ℝ Set.univ (aModel.g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t hs ht hst
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 0-q.1 0))
  simp only [aModel, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

theorem a_derivative (p : Point 2 1) (j : Fin 1) :
    HasFDerivAt (aModel.g j) ((2*p.1 0) • aZ + aY - aT) p := by
  have h := (((hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p aZ.hasFDerivAt).add
    aY.hasFDerivAt).sub aT.hasFDerivAt
  convert h using 1 <;> (try ext v) <;> norm_num [aModel, aZ, aT, aY, Function.comp_def, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]

theorem a_kkt : FixedNLPKKT aModel (aPoint 0 0 0) aD (fun _ => 1) (fun _ => 0) := by
  constructor
  · exact (a_linear _).mpr (by norm_num [aPoint])
  · intro j; norm_num [aModel, aPoint]
  · intro j; simpa [aD, aPoint] using a_derivative (aPoint 0 0 0) j
  · intro j; norm_num
  · intro row; norm_num
  · intro j; norm_num [aModel, aPoint]
  · intro row; simp
  · intro dx
    simp [a_objective, aD, aY, aT, Fin.sum_univ_one]

theorem a_fixed_minimum (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 2) :
    IsMinimizer (aModel.fixedNonlinearFiber ![y]) aModel.objective (aPoint 0 y y) := by
  refine ⟨(mem_fixedNonlinearFiber _ _ _).mpr ⟨?_,rfl,?_⟩,?_⟩
  · apply (a_linear _).mpr
    dsimp [aPoint]; constructor; norm_num
    constructor; norm_num
    constructor <;> linarith [hy.1,hy.2]
  · intro j; norm_num [aModel, aPoint]
  · intro p hp
    obtain ⟨_,hpY,hg⟩ := (mem_fixedNonlinearFiber _ _ _).mp hp
    have hpy : p.2 0 = y := congrFun hpY 0
    have h := hg 0
    change (p.1 0)^2 + p.2 0 - p.1 1 ≤ 0 at h
    simp only [a_objective, aPoint, Matrix.cons_val_one, Matrix.cons_val_zero]
    nlinarith [sq_nonneg (p.1 0)]

theorem a_slater (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 2) :
    ∃ p ∈ aModel.fixedLinearFiber ![y], ∀ j, aModel.g j p < 0 := by
  refine ⟨aPoint 0 (y+1) y, ⟨?_,rfl⟩,?_⟩
  · apply (a_linear _).mpr
    dsimp [aPoint]; constructor; norm_num
    constructor; norm_num
    constructor <;> linarith [hy.1,hy.2]
  · intro j; norm_num [aModel, aPoint]

def bPoint (t y : ℝ) : Point 1 1 := (![t],![y])
def bX : Point 1 1 →L[ℝ] ℝ := Chapter02Examples.coordX
def bY : Point 1 1 →L[ℝ] ℝ := Chapter02KKTExamples.coordY

def bModel : ModelData 1 1 1 2 where
  g := fun _ p => (p.2 0)^2-p.1 0
  A := ![![-1],![1]]
  B := 0
  rhs := ![1,5]
  c1 := ![1]
  c2 := ![-1]
  lo := ![0]
  hi := ![2]

def bD (_ : Fin 1) : Point 1 1 →L[ℝ] ℝ := -bX

theorem b_linear (p : Point 1 1) : p ∈ bModel.linearRegion ↔
    -p.1 0 ≤ 1 ∧ p.1 0 ≤ 5 := by
  simp [ModelData.linearRegion, bModel, LinearForm, Fin.forall_fin_succ,
    Fin.sum_univ_succ]

theorem b_objective (p : Point 1 1) : bModel.objective p = p.1 0-p.2 0 := by
  simp [ModelData.objective, bModel, LinearForm, Fin.sum_univ_one, sub_eq_add_neg]

theorem b_convex : ∀ j, ConvexOn ℝ Set.univ (bModel.g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t hs ht hst
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.2 0-q.2 0))
  simp only [bModel, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

theorem b_derivative (p : Point 1 1) (j : Fin 1) :
    HasFDerivAt (bModel.g j) ((2*p.2 0) • bY-bX) p := by
  have h := ((hasDerivAt_pow 2 (p.2 0)).comp_hasFDerivAt p bY.hasFDerivAt).sub bX.hasFDerivAt
  convert h using 1 <;> (try ext v) <;> norm_num [bModel, bX, bY, Chapter02Examples.coordX,
    Chapter02KKTExamples.coordY, Function.comp_def, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]

theorem b_kkt : FixedNLPKKT bModel (bPoint 0 0) bD (fun _ => 1) (fun _ => 0) := by
  constructor
  · exact (b_linear _).mpr (by norm_num [bPoint])
  · intro j; norm_num [bModel, bPoint]
  · intro j; simpa [bD, bPoint] using b_derivative (bPoint 0 0) j
  · intro j; norm_num
  · intro row; norm_num
  · intro j; norm_num [bModel, bPoint]
  · intro row; simp
  · intro dx
    simp [b_objective, bD, bX, Chapter02Examples.coordX, Fin.sum_univ_one]

theorem b_fixed_minimum (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 2) :
    IsMinimizer (bModel.fixedNonlinearFiber ![y]) bModel.objective (bPoint (y^2) y) := by
  have hy2 : y^2 ≤ 4 := by nlinarith [hy.1,hy.2]
  refine ⟨(mem_fixedNonlinearFiber _ _ _).mpr ⟨?_,rfl,?_⟩,?_⟩
  · apply (b_linear _).mpr
    dsimp [bPoint]; constructor <;> nlinarith [sq_nonneg y]
  · intro j; norm_num [bModel, bPoint]
  · intro p hp
    obtain ⟨_,hpY,hg⟩ := (mem_fixedNonlinearFiber _ _ _).mp hp
    have hpy : p.2 0 = y := congrFun hpY 0
    have h := hg 0
    change (p.2 0)^2-p.1 0 ≤ 0 at h
    simp only [b_objective, bPoint, Matrix.cons_val_zero]
    rw [hpy] at h ⊢
    linarith

theorem b_slater (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 2) :
    ∃ p ∈ bModel.fixedLinearFiber ![y], ∀ j, bModel.g j p < 0 := by
  have hy2 : y^2 ≤ 4 := by nlinarith [hy.1,hy.2]
  refine ⟨bPoint ((y^2+5)/2) y, ⟨?_,rfl⟩,?_⟩
  · apply (b_linear _).mpr
    dsimp [bPoint]; constructor <;> nlinarith [sq_nonneg y]
  · intro j; dsimp [bModel,bPoint]; linarith

def zeroModel : ModelData 0 0 0 0 where
  g := 0
  A := 0
  B := 0
  rhs := 0
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

theorem zero_minimum : IsMinimizer (zeroModel.fixedNonlinearFiber 0)
    zeroModel.objective 0 := by
  refine ⟨(mem_fixedNonlinearFiber _ _ _).mpr ⟨?_,rfl,?_⟩,?_⟩
  · intro i; exact Fin.elim0 i
  · intro j; exact Fin.elim0 j
  · intro p _; simp [zeroModel,ModelData.objective,LinearForm]

theorem zero_slater : ∃ p ∈ zeroModel.fixedLinearFiber 0,
    ∀ j, zeroModel.g j p < 0 := by
  exact ⟨0,⟨fun i => Fin.elim0 i,rfl⟩,fun j => Fin.elim0 j⟩

theorem zero_kkt : FixedNLPKKT zeroModel 0 0 0 0 := by
  constructor
  · intro i; exact Fin.elim0 i
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i
  · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i
  · intro x; simp [zeroModel,ModelData.objective,LinearForm]

theorem zero_source_multipliers : ∃ lambda mu,
    FixedNLPKKT zeroModel 0 0 lambda mu := by
  exact exists_fixedNLPKKT zeroModel 0 0 (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j) zero_minimum zero_slater

/-- C's bound is an explicit dualized row, not an implicit retained-X normal. -/
def cModel : ModelData 1 1 1 2 where
  g := fun _ _ => -1
  A := ![![-1],![1]]
  B := 0
  rhs := ![0,1]
  c1 := ![1]
  c2 := ![1]
  lo := ![0]
  hi := ![1]

theorem c_linear (p : Point 1 1) : p ∈ cModel.linearRegion ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 1 := by
  simp [ModelData.linearRegion,cModel,LinearForm,Fin.forall_fin_succ,Fin.sum_univ_succ]

theorem c_kkt : FixedNLPKKT cModel (bPoint 0 0) 0 0 ![1,0] := by
  constructor
  · exact (c_linear _).mpr (by norm_num [bPoint])
  · intro j; norm_num [cModel]
  · intro j; exact hasFDerivAt_const (-1) _
  · intro j; simp
  · intro row; fin_cases row <;> norm_num
  · intro j; simp
  · intro row; fin_cases row <;> norm_num [linearResidual,cModel,LinearForm,bPoint,Fin.sum_univ_one]
  · intro x; simp [cModel,ModelData.objective,LinearForm,Fin.sum_univ_succ]

theorem c_source_data :
    (∀ j, ConvexOn ℝ Set.univ (cModel.g j)) ∧
    IsMinimizer (cModel.fixedNonlinearFiber ![0]) cModel.objective (bPoint 0 0) ∧
    (∃ p ∈ cModel.fixedLinearFiber ![0], ∀ j, cModel.g j p < 0) := by
  refine ⟨fun _ => convexOn_const (-1) convex_univ, ?_, ?_⟩
  · refine ⟨(mem_fixedNonlinearFiber _ _ _).mpr ⟨c_kkt.linear_feasible,rfl,c_kkt.nonlinear_feasible⟩,?_⟩
    intro p hp
    obtain ⟨hl,hy,_⟩ := (mem_fixedNonlinearFiber _ _ _).mp hp
    have hx := ((c_linear p).mp hl).1
    have hpy : p.2 0 = 0 := congrFun hy 0
    simpa [ModelData.objective,cModel,LinearForm,bPoint,Fin.sum_univ_one,hpy] using hx
  · refine ⟨bPoint 0 0,⟨c_kkt.linear_feasible,rfl⟩,?_⟩
    intro j; norm_num [cModel]

/-- H deliberately lacks joint convexity. It is not a counterexample to the
convex-source bridge; all remaining raw KKT and attained-fiber data are real. -/
def hModel : ModelData 1 1 1 2 :=
  {bModel with g := fun _ p => -(p.2 0)^2-p.1 0, c2 := 0}

theorem h_derivative (p : Point 1 1) (j : Fin 1) :
    HasFDerivAt (hModel.g j) (-((2*p.2 0) • bY)-bX) p := by
  have h := (((hasDerivAt_pow 2 (p.2 0)).comp_hasFDerivAt p bY.hasFDerivAt).neg).sub bX.hasFDerivAt
  convert h using 1 <;> (try ext v) <;> norm_num [hModel,bX,bY,Chapter02Examples.coordX,
    Chapter02KKTExamples.coordY,Function.comp_def, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]

theorem h_kkt : FixedNLPKKT hModel (bPoint 0 0) bD (fun _ => 1) (fun _ => 0) := by
  constructor
  · exact b_kkt.linear_feasible
  · intro j; norm_num [hModel,bPoint]
  · intro j; simpa [bD,bPoint] using h_derivative (bPoint 0 0) j
  · intro j; norm_num
  · intro row; norm_num
  · intro j; norm_num [hModel,bPoint]
  · intro row; simp
  · intro x; simp [hModel,bModel,ModelData.objective,LinearForm,bD,bX,
      Chapter02Examples.coordX,Fin.sum_univ_one]

theorem h_not_jointly_convex : ¬ ConvexOn ℝ Set.univ (hModel.g 0) := by
  intro hc
  have hm := hc.2 (show bPoint (-1) (-1) ∈ (Set.univ : Set (Point 1 1)) from Set.mem_univ _)
    (show bPoint (-1) 1 ∈ (Set.univ : Set (Point 1 1)) from Set.mem_univ _)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  norm_num [hModel,bPoint,smul_eq_mul] at hm

theorem h_fixed_minimum (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) :
    IsMinimizer (hModel.fixedNonlinearFiber ![y]) hModel.objective (bPoint (-(y^2)) y) := by
  have hy2 : y^2 ≤ 1 := by nlinarith [hy.1,hy.2]
  refine ⟨(mem_fixedNonlinearFiber _ _ _).mpr ⟨?_,rfl,?_⟩,?_⟩
  · apply (b_linear _).mpr
    dsimp [bPoint]; constructor <;> nlinarith [sq_nonneg y]
  · intro j; norm_num [hModel,bPoint]
  · intro p hp
    obtain ⟨_,hpY,hg⟩ := (mem_fixedNonlinearFiber _ _ _).mp hp
    have hpy : p.2 0 = y := congrFun hpY 0
    have h := hg 0
    change -(p.2 0)^2-p.1 0 ≤ 0 at h
    simp only [hpy] at h
    simp [ModelData.objective,hModel,bModel,LinearForm,bPoint,Fin.sum_univ_one]
    linarith

theorem h_slater (y : ℝ) :
    ∃ p ∈ hModel.fixedLinearFiber ![y], ∀ j, hModel.g j p < 0 := by
  refine ⟨bPoint 1 y,⟨(b_linear _).mpr (by norm_num [bPoint]),rfl⟩,?_⟩
  intro j; dsimp [hModel,bPoint]; nlinarith [sq_nonneg y]

private theorem a_lagrangian (p : Point 2 1) :
    partialLagrangian aModel (fun _ => 1) (fun _ => 0) p = (p.1 0)^2+2*p.2 0 := by
  simp [partialLagrangian,ModelData.objective,aModel,LinearForm,Fin.sum_univ_succ]
  all_goals ring

private theorem b_lagrangian (p : Point 1 1) :
    partialLagrangian bModel (fun _ => 1) (fun _ => 0) p = (p.2 0)^2-p.2 0 := by
  simp [partialLagrangian,ModelData.objective,bModel,LinearForm,Fin.sum_univ_one]
  all_goals ring

theorem a_inner_value (y : RealVector 1) :
    IsGLB (gbdInnerRange aModel (fun _ => 1) (fun _ => 0) y) (2*y 0) ∧
    IsMinimizer Set.univ (fun x : RealVector 2 => partialLagrangian aModel
      (fun _ => 1) (fun _ => 0) (x,y)) 0 ∧
    anchoredOptimalityCut aModel (aPoint 0 0 0) aD (fun _ => 1) (fun _ => 0) y = 2*y 0 := by
  refine ⟨⟨?_,?_⟩,⟨Set.mem_univ _,?_⟩,?_⟩
  · rintro v ⟨x,rfl⟩
    change 2*y 0 ≤ partialLagrangian aModel (fun _ => 1) (fun _ => 0) (x,y)
    rw [a_lagrangian]; nlinarith [sq_nonneg (x 0)]
  · intro b hb
    have hv := hb (show partialLagrangian aModel (fun _ => 1) (fun _ => 0) (0,y) ∈
      gbdInnerRange aModel (fun _ => 1) (fun _ => 0) y from ⟨0,rfl⟩)
    simpa [a_lagrangian] using hv
  · intro x _
    simp only [a_lagrangian,Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),zero_add]
    nlinarith [sq_nonneg (x 0)]
  · simp [anchoredOptimalityCut,ModelData.objective,LinearForm,aD,aModel,aPoint,aY,aT,Fin.sum_univ_succ]
    change y 0+y 0 = 2*y 0
    ring

theorem b_inner_value (y : RealVector 1) :
    IsGLB (gbdInnerRange bModel (fun _ => 1) (fun _ => 0) y) ((y 0)^2-y 0) ∧
    (∀ x : RealVector 1, IsMinimizer Set.univ (fun z : RealVector 1 =>
      partialLagrangian bModel (fun _ => 1) (fun _ => 0) (z,y)) x) ∧
    anchoredOptimalityCut bModel (bPoint 0 0) bD (fun _ => 1) (fun _ => 0) y = -y 0 := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · rintro v ⟨x,rfl⟩; simp only [b_lagrangian,le_refl]
  · intro b hb
    have hv := hb (show partialLagrangian bModel (fun _ => 1) (fun _ => 0) (0,y) ∈
      gbdInnerRange bModel (fun _ => 1) (fun _ => 0) y from ⟨0,rfl⟩)
    simpa only [b_lagrangian] using hv
  · intro x; refine ⟨Set.mem_univ _,?_⟩
    intro z _; simp only [b_lagrangian,le_refl]
  · simp [anchoredOptimalityCut,ModelData.objective,LinearForm,bD,bModel,bPoint,bX,
      Chapter02Examples.coordX,Fin.sum_univ_one]

/-- The new finite-value operator agrees with both exact formulas, with its
nonempty/bounded premises actually derived from the full-model KKT data. -/
theorem finite_value_formulas (y : RealVector 1) :
    gbdFiniteInnerValue aModel (fun _ => 1) (fun _ => 0) y
      (gbdInnerRange_nonempty _ _ _ _) (gbdInnerRange_bddBelow a_kkt a_convex y) = 2*y 0 ∧
    gbdFiniteInnerValue bModel (fun _ => 1) (fun _ => 0) y
      (gbdInnerRange_nonempty _ _ _ _) (gbdInnerRange_bddBelow b_kkt b_convex y) = (y 0)^2-y 0 := by
  constructor
  · exact (gbdFiniteInnerValue_isGLB _ _ _ _ _ _).unique (a_inner_value y).1
  · exact (gbdFiniteInnerValue_isGLB _ _ _ _ _ _).unique (b_inner_value y).1

theorem b_strict_away_from_anchor (y : RealVector 1) (hy : y 0 ≠ 0) :
    anchoredOptimalityCut bModel (bPoint 0 0) bD (fun _ => 1) (fun _ => 0) y <
    gbdFiniteInnerValue bModel (fun _ => 1) (fun _ => 0) y
      (gbdInnerRange_nonempty _ _ _ _) (gbdInnerRange_bddBelow b_kkt b_convex y) := by
  rw [(b_inner_value y).2.2,(finite_value_formulas y).2]
  nlinarith [sq_pos_of_ne_zero hy]

theorem b_actual_off_anchor_control :
    IsMinimizer (bModel.fixedNonlinearFiber ![2]) bModel.objective (bPoint 4 2) ∧
    IsGLB (gbdInnerRange bModel (fun _ => 1) (fun _ => 0) ![2]) 2 ∧
    anchoredOptimalityCut bModel (bPoint 0 0) bD (fun _ => 1) (fun _ => 0) ![2] = -2 ∧
    bModel.objective (bPoint 4 2) = 2 := by
  refine ⟨?_,?_,?_,?_⟩
  · convert b_fixed_minimum 2 (by norm_num) using 1
    all_goals norm_num
  · convert (b_inner_value ![2]).1 using 1
    all_goals norm_num
  · simpa using (b_inner_value ![2]).2.2
  · norm_num [b_objective,bPoint]

theorem ab_feasible_objective_comparison (y : RealVector 1)
    (xA : RealVector 2) (xB : RealVector 1)
    (hAL : (xA,y) ∈ aModel.linearRegion) (hAN : ∀ j, aModel.g j (xA,y) ≤ 0)
    (hBL : (xB,y) ∈ bModel.linearRegion) (hBN : ∀ j, bModel.g j (xB,y) ≤ 0) :
    2*y 0 ≤ aModel.objective (xA,y) ∧ (y 0)^2-y 0 ≤ bModel.objective (xB,y) := by
  exact ⟨gbd_inner_isGLB_weakDuality a_kkt.lambda_nonneg a_kkt.mu_nonneg (a_inner_value y).1 hAL hAN,
    gbd_inner_isGLB_weakDuality b_kkt.lambda_nonneg b_kkt.mu_nonneg (b_inner_value y).1 hBL hBN⟩

theorem zero_inner_and_anchor :
    IsGLB (gbdInnerRange zeroModel 0 0 0) 0 ∧
    gbdFiniteInnerValue zeroModel 0 0 0 (gbdInnerRange_nonempty _ _ _ _)
      (gbdInnerRange_bddBelow zero_kkt (fun j => Fin.elim0 j) 0) = 0 ∧
    anchoredOptimalityCut zeroModel 0 0 0 0 0 = 0 := by
  have hv : IsGLB (gbdInnerRange zeroModel 0 0 0) 0 := by
    refine ⟨?_,?_⟩
    · rintro v ⟨x,rfl⟩; simp [partialLagrangian,zeroModel,ModelData.objective,LinearForm]
    · intro b hb
      have h := hb (show partialLagrangian zeroModel 0 0 (0,0) ∈ gbdInnerRange zeroModel 0 0 0 from ⟨0,rfl⟩)
      simpa [partialLagrangian,zeroModel,ModelData.objective,LinearForm] using h
  exact ⟨hv,(gbdFiniteInnerValue_isGLB _ _ _ _ _ _).unique hv,
    by simp [anchoredOptimalityCut,zeroModel,ModelData.objective,LinearForm]⟩

private theorem c_lagrangian (p : Point 1 1) :
    partialLagrangian cModel 0 ![1,0] p = p.2 0 := by
  simp [partialLagrangian,cModel,ModelData.objective,LinearForm,linearResidual,Fin.sum_univ_succ]

theorem c_dualized_bound_value (y : RealVector 1) :
    IsGLB (gbdInnerRange cModel 0 ![1,0] y) (y 0) ∧
    anchoredOptimalityCut cModel (bPoint 0 0) 0 0 ![1,0] y = y 0 := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · rintro v ⟨x,rfl⟩; simp only [c_lagrangian,le_refl]
  · intro b hb
    have h := hb (show partialLagrangian cModel 0 ![1,0] (0,y) ∈ gbdInnerRange cModel 0 ![1,0] y from ⟨0,rfl⟩)
    simpa only [c_lagrangian] using h
  · simp [anchoredOptimalityCut,cModel,ModelData.objective,LinearForm,bPoint,Fin.sum_univ_succ]

theorem c_dropped_bound_weight_unbounded (y : RealVector 1) :
    ¬ BddBelow (gbdInnerRange cModel 0 0 y) := by
  rintro ⟨v,hv⟩
  have h := hv (show partialLagrangian cModel 0 0 (![v-y 0-1],y) ∈
    gbdInnerRange cModel 0 0 y from ⟨![v-y 0-1],rfl⟩)
  simp [partialLagrangian,cModel,ModelData.objective,LinearForm,Fin.sum_univ_one] at h
  linarith

private theorem h_lagrangian (p : Point 1 1) :
    partialLagrangian hModel (fun _ => 1) (fun _ => 0) p = -(p.2 0)^2 := by
  simp [partialLagrangian,hModel,bModel,ModelData.objective,LinearForm,Fin.sum_univ_one]

theorem h_inner_value (y : RealVector 1) :
    IsGLB (gbdInnerRange hModel (fun _ => 1) (fun _ => 0) y) (-(y 0)^2) := by
  refine ⟨?_,?_⟩
  · rintro v ⟨x,rfl⟩; simp only [h_lagrangian,le_refl]
  · intro b hb
    have h := hb (show partialLagrangian hModel (fun _ => 1) (fun _ => 0) (0,y) ∈
      gbdInnerRange hModel (fun _ => 1) (fun _ => 0) y from ⟨0,rfl⟩)
    simpa only [h_lagrangian] using h

theorem h_missing_joint_convexity_control :
    FixedNLPKKT hModel (bPoint 0 0) bD (fun _ => 1) (fun _ => 0) ∧
    (¬ ConvexOn ℝ Set.univ (hModel.g 0)) ∧
    IsMinimizer (hModel.fixedNonlinearFiber ![1]) hModel.objective (bPoint (-1) 1) ∧
    IsGLB (gbdInnerRange hModel (fun _ => 1) (fun _ => 0) ![1]) (-1) ∧
    anchoredOptimalityCut hModel (bPoint 0 0) bD (fun _ => 1) (fun _ => 0) ![1] = 0 := by
  refine ⟨h_kkt,h_not_jointly_convex,?_,?_,?_⟩
  · convert h_fixed_minimum 1 (by norm_num) using 1
    all_goals norm_num
  · convert h_inner_value ![1] using 1
    all_goals norm_num
  · simp [anchoredOptimalityCut,hModel,bModel,ModelData.objective,LinearForm,bD,bPoint,bX,
      Chapter02Examples.coordX,Fin.sum_univ_one]

theorem linked_offset_inner_value (y : RealVector 1) :
    IsGLB (gbdInnerRange (Chapter02KKTExamples.linkedModel 4) (fun _ => 0)
      (Chapter02KKTExamples.linkMu 1) y) (y 0) ∧
    anchoredOptimalityCut (Chapter02KKTExamples.linkedModel 4) Chapter02KKTExamples.anchor
      Chapter02KKTExamples.anchorD (fun _ => 0) (Chapter02KKTExamples.linkMu 1) y = y 0 ∧
    printedOptimalityCut (Chapter02KKTExamples.linkedModel 4) Chapter02KKTExamples.anchor
      Chapter02KKTExamples.anchorD (fun _ => 0) (Chapter02KKTExamples.linkMu 1) y = 1+y 0 := by
  have hL (x : RealVector 1) : partialLagrangian (Chapter02KKTExamples.linkedModel 4)
      (fun _ => 0) (Chapter02KKTExamples.linkMu 1) (x,y) = y 0 := by
    simp [partialLagrangian,Chapter02KKTExamples.linkedModel,Chapter02KKTExamples.linkMu,
      ModelData.objective,LinearForm,linearResidual,Fin.sum_univ_succ]
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · rintro v ⟨x,rfl⟩; simp only [hL,le_refl]
  · intro b hb
    have h := hb (show partialLagrangian (Chapter02KKTExamples.linkedModel 4) (fun _ => 0)
      (Chapter02KKTExamples.linkMu 1) (0,y) ∈ gbdInnerRange (Chapter02KKTExamples.linkedModel 4)
      (fun _ => 0) (Chapter02KKTExamples.linkMu 1) y from ⟨0,rfl⟩)
    simpa only [hL] using h
  · simp [anchoredOptimalityCut,Chapter02KKTExamples.linkedModel,Chapter02KKTExamples.linkMu,
      Chapter02KKTExamples.anchor,Chapter02KKTExamples.pt,ModelData.objective,LinearForm,
      Fin.sum_univ_succ]
  · simp [printedOptimalityCut,Chapter02KKTExamples.linkedModel,Chapter02KKTExamples.linkMu,
      Chapter02KKTExamples.anchor,Chapter02KKTExamples.pt,ModelData.objective,LinearForm,
      Fin.sum_univ_succ]

theorem linked_offset_excludes_true_optimum :
    IsMinimizer ((Chapter02KKTExamples.linkedModel 4).feasibleOn Set.univ)
      (Chapter02KKTExamples.linkedModel 4).objective (Chapter02KKTExamples.pt 0 0) ∧
    IsGLB (gbdInnerRange (Chapter02KKTExamples.linkedModel 4) (fun _ => 0)
      (Chapter02KKTExamples.linkMu 1) ![0]) 0 ∧
    (Chapter02KKTExamples.linkedModel 4).objective (Chapter02KKTExamples.pt 0 0) <
      printedOptimalityCut (Chapter02KKTExamples.linkedModel 4) Chapter02KKTExamples.anchor
      Chapter02KKTExamples.anchorD (fun _ => 0) (Chapter02KKTExamples.linkMu 1) ![0] := by
  refine ⟨Chapter02KKTExamples.linked_zero_global_minimizer 4 (by norm_num),?_,?_⟩
  · simpa using (linked_offset_inner_value ![0]).1
  · rw [(linked_offset_inner_value ![0]).2.2]
    norm_num [Chapter02KKTExamples.linked_objective,Chapter02KKTExamples.pt]

/-- Both new source wrappers have satisfiable zero-row/zero-dimensional
premises; compactness here is the finite singleton base, not an epigraph claim. -/
theorem zero_source_wrappers_nonvacuous :
    IsCompact (zeroModel.linearRegion ∩ IntegerCylinder (n := 0) zeroModel.lo zeroModel.hi) ∧
    (∃ lambda mu, FixedNLPKKT zeroModel 0 0 lambda mu ∧
      IsGLB (gbdInnerRange zeroModel lambda mu 0) 0) ∧
    (∃ p lambda mu, IsMinimizer (zeroModel.fixedNonlinearFiber 0) zeroModel.objective p ∧
      FixedNLPKKT zeroModel p (fun j => fderiv ℝ (zeroModel.g j) p) lambda mu ∧
      IsGLB (gbdInnerRange zeroModel lambda mu 0) 0) := by
  have hc : IsCompact (zeroModel.linearRegion ∩
      IntegerCylinder (n := 0) zeroModel.lo zeroModel.hi) := (Set.toFinite _).isCompact
  refine ⟨hc,?_,?_⟩
  · obtain ⟨lambda,mu,hk,hv,_⟩ := gbd_inner_family_of_minimum zeroModel 0 0
      (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) zero_minimum zero_slater
    exact ⟨lambda,mu,hk,by simpa [zeroModel,ModelData.objective,LinearForm] using hv⟩
  · have hy : (0 : IntVector 0) ∈ IntegerBox zeroModel.lo zeroModel.hi := fun i => Fin.elim0 i
    have hs : ∃ z ∈ zeroModel.fixedLinearFiber (fun i => ((0 : IntVector 0) i : ℝ)),
        ∀ j, zeroModel.g j z < 0 := by
      have hy0 : (fun i => ((0 : IntVector 0) i : ℝ)) = (0 : RealVector 0) := Subsingleton.elim _ _
      rw [hy0]
      exact zero_slater
    obtain ⟨p,lambda,mu,_,hmin,hk,hv,_⟩ := source_gbd_inner_family_attained zeroModel 0 hy hc
      (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) hs
    have hycast : (fun i => ((0 : IntVector 0) i : ℝ)) = (0 : RealVector 0) := Subsingleton.elim _ _
    rw [hycast] at hmin hv
    exact ⟨p,lambda,mu,hmin,hk,
      by simpa [zeroModel,ModelData.objective,LinearForm] using hv⟩

/-- Nonzero active rhs: the lower facet is -x≤-1, so its positive multiplier
contributes the constant +1. Omitting that constant changes the actual infimum. -/
def shiftedBoundModel : ModelData 1 1 1 2 := {cModel with rhs := ![-1,2]}

theorem nonzero_rhs_control :
    FixedNLPKKT shiftedBoundModel (bPoint 1 0) 0 0 ![1,0] ∧
    IsMinimizer (shiftedBoundModel.fixedNonlinearFiber ![0]) shiftedBoundModel.objective (bPoint 1 0) ∧
    (∃ p ∈ shiftedBoundModel.fixedLinearFiber ![0], ∀ j, shiftedBoundModel.g j p < 0) ∧
    ∀ y : RealVector 1,
      IsGLB (gbdInnerRange shiftedBoundModel 0 ![1,0] y) (1+y 0) ∧
      anchoredOptimalityCut shiftedBoundModel (bPoint 1 0) 0 0 ![1,0] y = 1+y 0 ∧
      ∀ x : RealVector 1, shiftedBoundModel.objective (x,y) +
        (∑ row : Fin 2, (![1,0] : RealVector 2) row *
          LinearForm (shiftedBoundModel.A row) (shiftedBoundModel.B row) (x,y)) = y 0 := by
  have hk : FixedNLPKKT shiftedBoundModel (bPoint 1 0) 0 0 ![1,0] := by
    constructor
    · intro row; fin_cases row <;> norm_num [shiftedBoundModel,cModel,bPoint,LinearForm,Fin.sum_univ_one]
    · intro j; norm_num [shiftedBoundModel,cModel]
    · intro j; exact hasFDerivAt_const (-1) _
    · intro j; simp
    · intro row; fin_cases row <;> norm_num
    · intro j; simp
    · intro row; fin_cases row <;> norm_num [linearResidual,shiftedBoundModel,cModel,LinearForm,bPoint,Fin.sum_univ_one]
    · intro x; simp [shiftedBoundModel,cModel,ModelData.objective,LinearForm,Fin.sum_univ_succ]
  have hconv : ∀ j, ConvexOn ℝ Set.univ (shiftedBoundModel.g j) :=
    fun _ => convexOn_const (-1) convex_univ
  refine ⟨hk,gbd_kkt_fixedFiber_minimizer hk hconv,?_,?_⟩
  · exact ⟨bPoint 1 0,⟨hk.linear_feasible,rfl⟩,fun _ => by norm_num [shiftedBoundModel,cModel]⟩
  · intro y
    have hL (x : RealVector 1) : partialLagrangian shiftedBoundModel 0 ![1,0] (x,y) = 1+y 0 := by
      simp [partialLagrangian,shiftedBoundModel,cModel,ModelData.objective,LinearForm,linearResidual,Fin.sum_univ_succ]
      all_goals ring
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · rintro v ⟨x,rfl⟩; simp only [hL,le_refl]
    · intro b hb
      have h := hb (show partialLagrangian shiftedBoundModel 0 ![1,0] (0,y) ∈
        gbdInnerRange shiftedBoundModel 0 ![1,0] y from ⟨0,rfl⟩)
      simpa only [hL] using h
    · simp [anchoredOptimalityCut,shiftedBoundModel,cModel,ModelData.objective,LinearForm,bPoint,Fin.sum_univ_succ]
    · intro x
      simp [shiftedBoundModel,cModel,ModelData.objective,LinearForm,Fin.sum_univ_succ]

end Chapter02GBDInnerValueExamples

#print axioms Chapter02GBDInnerValueExamples.a_linear
#print axioms Chapter02GBDInnerValueExamples.a_objective
#print axioms Chapter02GBDInnerValueExamples.a_convex
#print axioms Chapter02GBDInnerValueExamples.a_derivative
#print axioms Chapter02GBDInnerValueExamples.a_kkt
#print axioms Chapter02GBDInnerValueExamples.a_fixed_minimum
#print axioms Chapter02GBDInnerValueExamples.a_slater
#print axioms Chapter02GBDInnerValueExamples.b_linear
#print axioms Chapter02GBDInnerValueExamples.b_objective
#print axioms Chapter02GBDInnerValueExamples.b_convex
#print axioms Chapter02GBDInnerValueExamples.b_derivative
#print axioms Chapter02GBDInnerValueExamples.b_kkt
#print axioms Chapter02GBDInnerValueExamples.b_fixed_minimum
#print axioms Chapter02GBDInnerValueExamples.b_slater
#print axioms Chapter02GBDInnerValueExamples.zero_minimum
#print axioms Chapter02GBDInnerValueExamples.zero_slater
#print axioms Chapter02GBDInnerValueExamples.zero_kkt
#print axioms Chapter02GBDInnerValueExamples.zero_source_multipliers
#print axioms Chapter02GBDInnerValueExamples.c_linear
#print axioms Chapter02GBDInnerValueExamples.c_kkt
#print axioms Chapter02GBDInnerValueExamples.c_source_data
#print axioms Chapter02GBDInnerValueExamples.h_derivative
#print axioms Chapter02GBDInnerValueExamples.h_kkt
#print axioms Chapter02GBDInnerValueExamples.h_not_jointly_convex
#print axioms Chapter02GBDInnerValueExamples.h_fixed_minimum
#print axioms Chapter02GBDInnerValueExamples.h_slater
#print axioms Chapter02GBDInnerValueExamples.a_inner_value
#print axioms Chapter02GBDInnerValueExamples.b_inner_value
#print axioms Chapter02GBDInnerValueExamples.finite_value_formulas
#print axioms Chapter02GBDInnerValueExamples.b_strict_away_from_anchor
#print axioms Chapter02GBDInnerValueExamples.b_actual_off_anchor_control
#print axioms Chapter02GBDInnerValueExamples.ab_feasible_objective_comparison
#print axioms Chapter02GBDInnerValueExamples.zero_inner_and_anchor
#print axioms Chapter02GBDInnerValueExamples.c_dualized_bound_value
#print axioms Chapter02GBDInnerValueExamples.c_dropped_bound_weight_unbounded
#print axioms Chapter02GBDInnerValueExamples.h_inner_value
#print axioms Chapter02GBDInnerValueExamples.h_missing_joint_convexity_control
#print axioms Chapter02GBDInnerValueExamples.linked_offset_inner_value
#print axioms Chapter02GBDInnerValueExamples.linked_offset_excludes_true_optimum
#print axioms Chapter02GBDInnerValueExamples.zero_source_wrappers_nonvacuous
#print axioms Chapter02GBDInnerValueExamples.nonzero_rhs_control
