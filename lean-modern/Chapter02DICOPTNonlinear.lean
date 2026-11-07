module

public import Chapter02DICOPTModel
public import Chapter02DICOPTExampleData

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
open scoped BigOperators
namespace Chapter02DICOPTExamples

def nonlinearData : Data 1 1 1 0 0 where
  f x := -x 0
  h _ x := (x 0)^2 + x 0
  g := Fin.elim0
  A _ := scalar (-2)
  B := Fin.elim0
  C := Fin.elim0
  D := Fin.elim0
  rhs := Fin.elim0
  xL := scalar 0
  xU := scalar 1
  c := scalar (3/4)

@[simp] theorem dot_scalar (a : ℝ) (x : V) : dot (scalar a) x = a*x 0 := by
  simp [dot, Fin.sum_univ_one]

@[simp] theorem nonlinear_objective (x y : V) :
    nonlinearData.objective x y = -x 0 + (3/4:ℝ)*y 0 := by
  simp [Data.objective, nonlinearData]
  ring

@[simp] theorem nonlinear_feasible (x y : V) :
    nonlinearData.Feasible x y ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ (x 0)^2+x 0-2*y 0=0 := by
  simp [Data.Feasible, Data.Hard, Data.xBox, nonlinearData, scalar_Icc,
    Data.eqRow, Fin.forall_fin_one, and_assoc, Pi.le_def]
  ring_nf
  simp

def nonlinearJet (a : ℝ) : Jet nonlinearData (scalar a) where
  Df := -coord
  Dh _ := (2*a+1) • coord
  Dg := Fin.elim0
  fderiv := derivative_neg_coord _
  hderiv _ := by simpa [nonlinearData] using derivative_square_add (scalar a)
  gderiv := by intro i; exact Fin.elim0 i

def nonlinearKKT (a b lam : ℝ) (ha : 0 ≤ a ∧ a ≤ 1)
    (he : a^2+a-2*b=0) (hs : -1+lam*(2*a+1)=0) :
    FixedKKT nonlinearData (scalar a) (scalar b) where
  jet := nonlinearJet a
  alpha := -a
  sigma := 1
  lambda := scalar lam
  mu := Fin.elim0
  nu := Fin.elim0
  xLower := scalar 0
  xUpper := scalar 0
  feasible := (nonlinear_feasible _ _).mpr ⟨ha.1,ha.2,he⟩
  alphaFeasible := le_rfl
  sigmaNonneg := by norm_num
  muNonneg := by intro i; exact Fin.elim0 i
  nuNonneg := by intro i; exact Fin.elim0 i
  lowerNonneg := by intro i; norm_num
  upperNonneg := by intro i; norm_num
  alphaComp := by simp [nonlinearData]
  ineqComp := by intro i; exact Fin.elim0 i
  affineComp := by intro i; exact Fin.elim0 i
  lowerComp := by simp
  upperComp := by simp
  alphaStationarity := by norm_num
  stationarity := by
    intro v
    simp [nonlinearJet, Fin.sum_univ_one]
    nlinarith [mul_eq_zero_of_left hs (v 0)]

theorem nonlinear_signed (a b lam : ℝ) (ha : 0 ≤ a ∧ a ≤ 1)
    (he : a^2+a-2*b=0) (hs : -1+lam*(2*a+1)=0) (hl : 0 < lam) :
    SignedConvex nonlinearData (nonlinearKKT a b lam ha he hs) := by
  constructor
  · simpa [nonlinearData, Data.xBox] using
      convex_affine_on (convex_Icc (scalar (0:ℝ)) (scalar (1:ℝ))) (-1) 0
  · intro i; exact Fin.elim0 i
  · intro i
    have hs : signReal lam = 1 := by simp [signReal, sign_pos hl]
    simpa [nonlinearData, Data.xBox, nonlinearKKT, hs] using
      convex_square_add_on (convex_Icc (scalar (0:ℝ)) (scalar (1:ℝ)))

def nonlinearAnchor (a b lam w : ℝ) (ha : 0 ≤ a ∧ a ≤ 1)
    (he : a^2+a-2*b=0) (hs : -1+lam*(2*a+1)=0) (hl : 0 < lam)
    (hw : |lam| < w) : Anchor nonlinearData where
  x := scalar a
  y := scalar b
  kkt := nonlinearKKT a b lam ha he hs
  convex := nonlinear_signed a b lam ha he hs hl
  weights := {
    obj := 2
    eq := scalar w
    ineq := Fin.elim0
    obj_gt := by norm_num [nonlinearKKT]
    eq_gt := by simpa [nonlinearKKT] using (fun _ : Fin 1 => hw)
    ineq_gt := by intro i; exact Fin.elim0 i }

def nonlinearInitial : Anchor nonlinearData :=
  nonlinearAnchor (5/6) (55/72) (3/8) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
def nonlinearZero : Anchor nonlinearData :=
  nonlinearAnchor 0 0 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
def nonlinearOne : Anchor nonlinearData :=
  nonlinearAnchor 1 1 (1/3) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [abs_of_pos])

def nonlinearJoint : JointKKT nonlinearData (scalar (5/6)) (scalar (55/72)) where
  toFixedKKT := nonlinearInitial.kkt
  yFeasible := by
    constructor <;> intro i <;> norm_num [Data.yBox, nonlinearData, scalar]
  yLower := scalar 0
  yUpper := scalar 0
  yLowerNonneg := by simp
  yUpperNonneg := by simp
  yLowerComp := by simp
  yUpperComp := by simp
  yStationarity := by
    intro v
    simp [nonlinearInitial, nonlinearAnchor, nonlinearKKT, nonlinearData,
      Fin.sum_univ_one]
    ring

theorem nonlinear_relaxed_minimum :
    IsMinimizer nonlinearData.relaxed (fun z => nonlinearData.objective z.1 z.2)
      (scalar (5/6),scalar (55/72)) := by
  constructor
  · exact ⟨nonlinearJoint.feasible, nonlinearJoint.yFeasible⟩
  · intro z hz
    have he := ((nonlinear_feasible _ _).mp hz.1).2.2
    have hh := nonlinear_relaxed_square (z.1 0) (z.2 0) he
    simp only [nonlinear_objective, scalar_apply]
    nlinarith [sq_nonneg (z.1 0-5/6)]

theorem nonlinear_original_points (x y : V) :
    (x,y) ∈ nonlinearData.original ↔
      (x=scalar 0 ∧ y=scalar 0) ∨ (x=scalar 1 ∧ y=scalar 1) := by
  constructor
  · intro h
    have hf := (nonlinear_feasible _ _).mp h.1
    rcases nonlinear_binary_fiber ⟨hf.1,hf.2.1⟩ (h.2 0) hf.2.2 with h0|h1
    · exact Or.inl ⟨scalar_ext h0.2,scalar_ext h0.1⟩
    · exact Or.inr ⟨scalar_ext h1.2,scalar_ext h1.1⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;>
      norm_num [Data.original, nonlinear_feasible, Binary]

theorem nonlinear_original_minimum :
    IsMinimizer nonlinearData.original (fun z => nonlinearData.objective z.1 z.2)
      (scalar 1,scalar 1) := by
  constructor
  · exact (nonlinear_original_points _ _).mpr (Or.inr ⟨rfl,rfl⟩)
  · intro z hz
    rcases (nonlinear_original_points _ _).mp hz with ⟨hx,hy⟩|⟨hx,hy⟩ <;>
      norm_num [hx,hy]

end Chapter02DICOPTExamples
