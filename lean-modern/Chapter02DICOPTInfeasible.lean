module

public import Chapter02DICOPTNonlinear

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
open scoped BigOperators
namespace Chapter02DICOPTExamples

def infeasibleData : Data 1 1 1 0 0 where
  f _ := 0
  h _ x := x 0 + 1/2
  g := Fin.elim0
  A _ := scalar (-1)
  B := Fin.elim0
  C := Fin.elim0
  D := Fin.elim0
  rhs := Fin.elim0
  xL := scalar (-1/4)
  xU := scalar (1/4)
  c := scalar 0

@[simp] theorem infeasible_feasible (x y : V) :
    infeasibleData.Feasible x y ↔
      -(1/4:ℝ) ≤ x 0 ∧ x 0 ≤ 1/4 ∧ x 0 + 1/2 - y 0 = 0 := by
  simp [Data.Feasible, Data.Hard, Data.xBox, infeasibleData, scalar_Icc,
    Data.eqRow, Fin.forall_fin_one, and_assoc, Pi.le_def]
  all_goals ring_nf

def infeasibleJet : Jet infeasibleData (scalar 0) where
  Df := 0
  Dh _ := coord
  Dg := Fin.elim0
  fderiv := hasFDerivAt_const _ _
  hderiv _ := derivative_coord_add _ _
  gderiv := by intro i; exact Fin.elim0 i

def infeasibleKKT : FixedKKT infeasibleData (scalar 0) (scalar (1/2)) where
  jet := infeasibleJet
  alpha := 0
  sigma := 1
  lambda := scalar 0
  mu := Fin.elim0
  nu := Fin.elim0
  xLower := scalar 0
  xUpper := scalar 0
  feasible := (infeasible_feasible _ _).mpr (by norm_num)
  alphaFeasible := le_rfl
  sigmaNonneg := by norm_num
  muNonneg := by intro i; exact Fin.elim0 i
  nuNonneg := by intro i; exact Fin.elim0 i
  lowerNonneg := by simp
  upperNonneg := by simp
  alphaComp := by simp [infeasibleData]
  ineqComp := by intro i; exact Fin.elim0 i
  affineComp := by intro i; exact Fin.elim0 i
  lowerComp := by simp
  upperComp := by simp
  alphaStationarity := by norm_num
  stationarity := by simp [infeasibleJet]

def infeasibleInitial : Anchor infeasibleData where
  x := scalar 0
  y := scalar (1/2)
  kkt := infeasibleKKT
  convex := by
    constructor
    · simpa [infeasibleData,Data.xBox,infeasibleKKT,signReal,neg_div] using
        convex_affine_on (convex_Icc (scalar (-(1/4):ℝ)) (scalar (1/4:ℝ))) 0 0
    · intro i; exact Fin.elim0 i
    · intro i
      simpa [infeasibleData,Data.xBox,infeasibleKKT,signReal,neg_div] using
        convex_affine_on (convex_Icc (scalar (-(1/4):ℝ)) (scalar (1/4:ℝ))) 0 0
  weights := {
    obj := 2
    eq := scalar 1
    ineq := Fin.elim0
    obj_gt := by norm_num [infeasibleKKT]
    eq_gt := by simp [infeasibleKKT]
    ineq_gt := by intro i; exact Fin.elim0 i }

def infeasibleJoint : JointKKT infeasibleData (scalar 0) (scalar (1/2)) where
  toFixedKKT := infeasibleKKT
  yFeasible := by constructor <;> intro i <;> norm_num [Data.yBox, scalar]
  yLower := scalar 0
  yUpper := scalar 0
  yLowerNonneg := by simp
  yUpperNonneg := by simp
  yLowerComp := by simp
  yUpperComp := by simp
  yStationarity := by simp [infeasibleData,infeasibleKKT]

theorem infeasible_original_empty : infeasibleData.original = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := (infeasible_feasible _ _).mp hz.1
  exact affine_infeasible_binary ⟨hh.1,hh.2.1⟩ (hz.2 0) hh.2.2

theorem infeasible_binary_fiber_empty (y : V) (hy : Binary y) :
    ¬ (infeasibleData.fiber y).Nonempty := by
  rintro ⟨x,hx⟩
  have h : (x,y) ∈ infeasibleData.original := ⟨hx,hy⟩
  simp [infeasible_original_empty] at h

theorem infeasible_relaxed_nonempty : infeasibleData.relaxed.Nonempty :=
  ⟨(scalar 0,scalar (1/2)),infeasibleJoint.feasible,infeasibleJoint.yFeasible⟩

end Chapter02DICOPTExamples
