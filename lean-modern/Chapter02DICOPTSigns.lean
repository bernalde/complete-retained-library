module

public import Chapter02DICOPTKKT
public import Chapter02DICOPTInfeasible

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
open scoped BigOperators
namespace Chapter02DICOPTExamples

def signData (o t : ℝ) : Data 1 1 1 0 0 where
  f x := -t*x 0
  h _ x := o*((x 0)^2-1)
  g := Fin.elim0
  A _ := scalar 0
  B := Fin.elim0
  C := Fin.elim0
  D := Fin.elim0
  rhs := Fin.elim0
  xL := scalar 0
  xU := scalar 2
  c := scalar 0

def signJet (o t : ℝ) : Jet (signData o t) (scalar 1) where
  Df := (-t) • coord
  Dh _ := (2*o) • coord
  Dg := Fin.elim0
  fderiv := by
    convert (derivative_coord (scalar 1)).const_mul (-t) using 1 <;>
      (try ext v) <;> simp [signData, coord, Function.comp_def] <;> ring
  hderiv := by
    intro i
    convert ((derivative_square (scalar 1)).sub_const 1).const_mul o using 1 <;>
      (try ext v) <;> simp [signData, coord, Function.comp_def] <;> ring
  gderiv := by intro i; exact Fin.elim0 i

def signKKT (o t lam : ℝ) (hs : -t+lam*(2*o)=0) :
    FixedKKT (signData o t) (scalar 1) (scalar 0) where
  jet := signJet o t
  alpha := -t
  sigma := 1
  lambda := scalar lam
  mu := Fin.elim0
  nu := Fin.elim0
  xLower := scalar 0
  xUpper := scalar 0
  feasible := by
    norm_num [Data.Feasible,Data.Hard,Data.xBox,Data.eqRow,signData,Pi.le_def,
      Fin.forall_fin_one]
  alphaFeasible := by simp [signData]
  sigmaNonneg := by norm_num
  muNonneg := by intro i; exact Fin.elim0 i
  nuNonneg := by intro i; exact Fin.elim0 i
  lowerNonneg := by simp
  upperNonneg := by simp
  alphaComp := by simp [signData]
  ineqComp := by intro i; exact Fin.elim0 i
  affineComp := by intro i; exact Fin.elim0 i
  lowerComp := by simp
  upperComp := by simp
  alphaStationarity := by norm_num
  stationarity := by
    intro v
    simp [signJet,Fin.sum_univ_succ]
    nlinarith [mul_eq_zero_of_left hs (v 0)]

def positiveKKT := signKKT 1 1 (1/2) (by norm_num)
def negativeKKT := signKKT (-1) 1 (-(1/2)) (by norm_num)
def zeroKKT := signKKT 1 0 0 (by norm_num)

def signWeights (o t lam : ℝ) (hs : -t+lam*(2*o)=0) (hl : |lam|<1) :
    Weights (signKKT o t lam hs) where
  obj := 2
  eq := scalar 1
  ineq := Fin.elim0
  obj_gt := by norm_num [signKKT]
  eq_gt := by simpa [signKKT] using (fun _ : Fin 1 => hl)
  ineq_gt := by intro i; exact Fin.elim0 i

def positiveWeights : Weights positiveKKT := signWeights 1 1 (1/2) (by norm_num) (by norm_num [abs_of_pos])
def negativeWeights : Weights negativeKKT := signWeights (-1) 1 (-(1/2)) (by norm_num) (by norm_num [abs_of_pos])
def zeroWeights : Weights zeroKKT := signWeights 1 0 0 (by norm_num) (by norm_num)

theorem sign_source_convex (o t lam : ℝ) (hs : -t+lam*(2*o)=0)
    (hc : 0 ≤ signReal lam*o) : SignedConvex (signData o t) (signKKT o t lam hs) := by
  constructor
  · exact convex_affine_on (convex_Icc _ _) (-t) 0 |>.congr
      (by intro x hx; simp [signData])
  · intro i; exact Fin.elim0 i
  · intro i
    have hh := (convex_square_on (convex_Icc (scalar (0:ℝ)) (scalar (2:ℝ)))).add
      (convex_affine_on (convex_Icc (scalar (0:ℝ)) (scalar (2:ℝ))) 0 (-1))
    have hmul := hh.smul hc
    convert hmul using 1 <;> ext z <;>
      simp [Data.xBox, signData, signKKT, sub_eq_add_neg, Pi.le_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem positive_convex : SignedConvex (signData 1 1) positiveKKT :=
  sign_source_convex _ _ _ _ (by norm_num [signReal,sign_apply])
theorem negative_convex : SignedConvex (signData (-1) 1) negativeKKT :=
  sign_source_convex _ _ _ _ (by norm_num [signReal,sign_apply])
theorem zero_convex : SignedConvex (signData 1 0) zeroKKT :=
  sign_source_convex _ _ _ _ (by norm_num [signReal,sign_apply])

theorem sign_tangent_controls (x : V) :
    eqTangent (signData 1 1) positiveKKT.jet positiveKKT.lambda 0 x (scalar 0)=2*(x 0-1) ∧
    eqTangent (signData (-1) 1) negativeKKT.jet negativeKKT.lambda 0 x (scalar 0)=2*(x 0-1) ∧
    eqTangent (signData 1 0) zeroKKT.jet zeroKKT.lambda 0 x (scalar 0)=0 := by
  norm_num [eqTangent,positiveKKT,negativeKKT,zeroKKT,signKKT,signJet,signData,
    signReal,sign_apply]

/-- A genuine feasible signed hard-master point need not satisfy an equality whose multiplier is zero. -/
theorem zero_sign_drops_original_equality :
    (scalar 0,0) ∈ hardFeasible zeroKKT ∧
    ¬ (signData 1 0).Feasible (scalar 0) (scalar 0) := by
  constructor
  · norm_num [hardFeasible,Data.Hard,Data.xBox,signData,zeroKKT,signKKT,signJet,
      objTangent,eqTangent,signReal,sign_apply,Pi.le_def,Fin.forall_fin_one]
  · norm_num [Data.Feasible,Data.Hard,Data.xBox,Data.eqRow,signData,
      Pi.le_def,Fin.forall_fin_one]

/-- Boundary weights are evaluated on the SAME literal AP feasible set; they deliberately
    cannot be packaged as the strict `Weights` type. The equality weight remains one. -/
def boundaryObjective (w : ℝ) (z : SlicePoint 1 1 0) : ℝ :=
  dot infeasibleData.c (scalar (1/2)) + z.alpha+w*z.s+∑ i, z.p i
def boundaryPoint (t : ℝ) : SlicePoint 1 1 0 :=
  ⟨scalar 0,-t,t,scalar 0,Fin.elim0⟩

theorem boundary_point_feasible (t : ℝ) (ht : 0≤t) :
    boundaryPoint t ∈ apFeasible infeasibleKKT := by
  norm_num [apFeasible,boundaryPoint,infeasibleKKT,infeasibleJet,Data.Hard,Data.xBox,
    infeasibleData,Pi.le_def,Fin.forall_fin_one,objTangent,eqTangent,signReal,ht]

theorem boundary_point_value (w t : ℝ) :
    boundaryObjective w (boundaryPoint t)=(w-1)*t := by
  simp [boundaryObjective,boundaryPoint,infeasibleData,Fin.sum_univ_one]
  ring

theorem weight_one_nonzero_minimum :
    IsMinimizer (apFeasible infeasibleKKT) (boundaryObjective 1) (boundaryPoint 1) ∧
    (boundaryPoint 1).s≠0 := by
  refine ⟨⟨boundary_point_feasible 1 (by norm_num),?_⟩,by norm_num [boundaryPoint]⟩
  intro z hz
  have hc := hz.2.2.2.2.1
  have hp := hz.2.2.1 0
  simp [objTangent,infeasibleKKT,infeasibleJet,infeasibleData] at hc
  rw [boundary_point_value]
  simp [boundaryObjective,infeasibleData,Fin.sum_univ_one]
  linarith

theorem weight_half_unbounded (M : ℝ) :
    ∃ z ∈ apFeasible infeasibleKKT, boundaryObjective (1/2) z < M := by
  refine ⟨boundaryPoint (2*(|M|+1)),boundary_point_feasible _ (by positivity),?_⟩
  rw [boundary_point_value]
  have h := neg_abs_le M
  linarith

theorem weight_below_one_unbounded (w M : ℝ) (hw : w<1) :
    ∃ z ∈ apFeasible infeasibleKKT, boundaryObjective w z < M := by
  have hp : 0 < 1-w := by linarith
  refine ⟨boundaryPoint ((|M|+1)/(1-w)),boundary_point_feasible _ (by positivity),?_⟩
  rw [boundary_point_value]
  have he : (w-1)*((|M|+1)/(1-w))=-(|M|+1) := by
    field_simp
    ring
  rw [he]
  linarith [neg_abs_le M]

end Chapter02DICOPTExamples
