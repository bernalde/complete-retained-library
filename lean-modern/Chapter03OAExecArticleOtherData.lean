module

public import Chapter03OAExecArticleData

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open scoped BigOperators
namespace Chapter03.OAExec.Article

def T := boxModel 0 1 (xSquareRow 2)
def Tf := linearQuadratic (1/4)
def Tdf := linearQuadraticD (1/4)
def Tdg (p : P) (_ : Fin 1) := xSquareD p

theorem T_rows_exact : {j | ¬ AffineRow (T.g j)} = Set.univ := by
  ext j
  simp [T,boxModel,xSquareRow_nonaffine]

theorem T_relaxation (p : P) : p ∈ T.relaxationOn Set.univ ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  rw [T,box_relaxation]
  constructor
  · tauto
  · rintro ⟨hl,hu,hyl,hyu⟩
    refine ⟨hl,hu,hyl,hyu,?_⟩
    dsimp [xSquareRow]
    nlinarith [square_le_one (show -1 ≤ p.1 0 by linarith) hu]

theorem T_initial_minimum : IsMinimizer (T.relaxationOn Set.univ) Tf (pt 0 (1/4)) := by
  refine ⟨(T_relaxation _).mpr (by norm_num [pt,scalar]),?_⟩
  intro p hp
  have hx := ((T_relaxation p).mp hp).1
  norm_num [Tf,linearQuadratic,pt,scalar]
  exact add_nonneg hx (sq_nonneg _)

theorem T_fiber (y : V) (x : V) : x ∈ fiber T y ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
  constructor
  · intro h; exact (box_hard 0 1 _ _).mp h.1
  · rintro ⟨hl,hu⟩
    refine ⟨(box_hard 0 1 _ _).mpr ⟨hl,hu⟩,?_⟩
    intro j
    change (x 0)^2-2 ≤ 0
    nlinarith [square_le_one (show -1 ≤ x 0 by linarith) hu]

theorem T_fiber_minimum (y : V) :
    IsMinimizer (fiber T y) (fiberObjective Tf y) (scalar 0) := by
  refine ⟨(T_fiber _ _).mpr (by norm_num [scalar]),?_⟩
  intro x hx
  have hl := ((T_fiber _ _).mp hx).1
  simp only [fiberObjective,Tf,linearQuadratic,scalar,zero_add]
  linarith

def T_fixed (y : V) : FixedKKT T Tf (scalar 0) y where
  Df := Tdf (scalar 0,y)
  Dg := Tdg (scalar 0,y)
  lambda := scalar 0
  mu := ![1,0]
  primal := (T_fiber_minimum y).1
  derivative_f := linearQuadratic_derivative _ _
  derivative_g _ := xSquareRow_derivative _ _
  lambda_nonneg := by simp [scalar]
  mu_nonneg := by intro i; fin_cases i <;> norm_num
  soft_compl := by simp [scalar]
  hard_compl := by
    intro i; fin_cases i <;>
      norm_num [hard,linearResidual,T,boxModel,LinearForm,scalar,Fin.sum_univ_one]
  stationarity := by
    ext v
    norm_num [Tdf,linearQuadraticD,restrict_apply,scalar,Fin.sum_univ_two,
      Fin.sum_univ_one,fiberLinearRow_apply,LinearForm,T,boxModel]

theorem T_value_gap : Tf (pt 0 1)=9/16 ∧ Tf (pt 0 0)=1/16 ∧
    Tf (pt 0 1)-0=9/16 ∧ Tf (pt 0 0)<Tf (pt 0 1) := by
  norm_num [Tf,linearQuadratic,pt,scalar]

def A := boxModel (-1) 1 (fun p => quadratic (1/2) p-1/16)
def Af := quadratic (1/2)
def Adf := quadraticD (1/2)
def Adg (p : P) (_ : Fin 1) := quadraticD (1/2) p

theorem A_rows_exact : {j | ¬ AffineRow (A.g j)} = Set.univ := by
  ext j
  simp [A,boxModel,quadraticRow_nonaffine]

theorem A_initial_minimum : IsMinimizer (A.relaxationOn Set.univ) Af (pt 0 (1/2)) := by
  refine ⟨(box_relaxation _ _ _ _).mpr (by norm_num [quadratic,pt,scalar]),?_⟩
  intro p hp
  norm_num [Af,quadratic,pt,scalar]
  positivity

theorem binary_square (y : IntVector 1)
    (hy : y ∈ IntegerBox A.lo A.hi) : ((y 0 : ℝ)-1/2)^2=1/4 := by
  rcases (binary_box (-1) 1 _ y).mp hy with h | h <;> norm_num [h]

theorem A_fiber_empty (y : IntVector 1) (hy : y ∈ IntegerBox A.lo A.hi) :
    ¬ (fiber A (intCast y)).Nonempty := by
  rintro ⟨x,hx⟩
  have hg := hx.2 0
  change (x 0)^2+((y 0:ℝ)-1/2)^2-1/16 ≤ 0 at hg
  rw [binary_square y hy] at hg
  nlinarith [sq_nonneg (x 0)]

theorem A_original_empty : ¬ (A.feasibleOn Set.univ).Nonempty := by
  rintro ⟨p,hp⟩
  rcases (source_feasible_iff A _ p).mp hp with ⟨_,hg,hh,y,hy,he⟩
  apply A_fiber_empty y hy
  refine ⟨p.1,?_⟩
  change p.2=intCast y at he
  rw [← he]
  exact ⟨hh,hg⟩

theorem A_restoration_minimum (y : IntVector 1)
    (hy : y ∈ IntegerBox A.lo A.hi) :
    IsMinimizer (restSet A (intCast y)) (restCost (n:=1) (l:=1))
      (weightedInsert (scalar 0) (scalar (3/16))) := by
  have hb := binary_square y hy
  refine ⟨?_,?_⟩
  · rw [restSet_insert_iff]
    refine ⟨?_,?_,by norm_num [scalar]⟩
    · intro i
      fin_cases i <;>
        norm_num [hard,linearResidual,A,boxModel,LinearForm,scalar,Fin.sum_univ_one]
    · intro j
      change (0:ℝ)^2+((y 0:ℝ)-1/2)^2-1/16 ≤ 3/16
      rw [hb]
      norm_num
  · intro q hq
    have hq' : weightedInsert (weightedX (n:=1) (s:=1) q)
        (weightedV (n:=1) (s:=1) q) ∈ restSet A (intCast y) := by
      rw [weightedInsert_project (n:=1) (s:=1)]
      exact hq
    have hg := ((restSet_insert_iff A (intCast y) _ _).mp hq').2.1 0
    change (weightedX (n:=1) (s:=1) q 0)^2+((y 0:ℝ)-1/2)^2-1/16 ≤
      weightedV (n:=1) (s:=1) q 0 at hg
    rw [hb] at hg
    change weightedLiftObjective (n:=1) (fun _ : Fin 1 => 1) _ ≤
      weightedLiftObjective (n:=1) (fun _ : Fin 1 => 1) q
    simp only [weightedLiftObjective_apply,Fin.sum_univ_one,weightedV_insert,
      scalar,one_mul]
    nlinarith [sq_nonneg (weightedX (n:=1) (s:=1) q 0)]

/-- Actual empty joint relaxation on the ordinary nonempty hard interval
[-1,1]: the nonlinear source row x²+1 is impossible. -/
def EmptyInitial := boxModel (-1) 1 (xSquareRow (-1))

theorem empty_initializer_relaxation :
    ¬ (EmptyInitial.relaxationOn Set.univ).Nonempty := by
  rintro ⟨p,hp⟩
  have h := (box_relaxation (-1) 1 _ p).mp hp
  have hg := h.2.2.2.2
  change (p.1 0)^2-(-1)≤0 at hg
  nlinarith [sq_nonneg (p.1 0)]

/-- Actual integral initializer: this nonlinear objective attains its minimum
at the explicitly defined original feasible point (0,0). -/
def IntegralF := quadratic 0

theorem integral_initializer_minimum :
    IsMinimizer (G.relaxationOn Set.univ) IntegralF (pt 0 0) := by
  refine ⟨(G_relaxation _).mpr (by norm_num [pt,scalar]),?_⟩
  intro p hp
  norm_num [IntegralF,quadratic,pt,scalar]
  positivity

end Chapter03.OAExec.Article
