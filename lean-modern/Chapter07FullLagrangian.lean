module

public import Chapter06QuadraticRanking
public import Chapter06LevelFiber

@[expose] public section

/-! Chapter 7's actual full Lagrangian. Original affine rows, including bound
rows encoded in the source data, are retained. Supplied weights do not imply
KKT provenance; the continuous stationarity theorem requires an actual witness. -/
noncomputable section
open Set
open scoped BigOperators
open Chapter02 Chapter03.OAKKT Chapter06.Level
namespace Chapter07.FullLagrangian
variable {n m l r : ℕ}

def hardRow (d : Data n m l r) (i : Fin r) (z : Point n m) : ℝ :=
  LinearForm (d.A i) (d.B i) z - d.b i

def rows (d : Data n m l r) : Fin (l+r) → Point n m → ℝ :=
  Fin.addCases d.g (hardRow d)

def weights (lambda : Fin l → ℝ) (mu : Fin r → ℝ) : Fin (l+r) → ℝ :=
  Fin.addCases lambda mu

def lagrangian (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (z : Point n m) : ℝ :=
  d.f z + (∑ j, lambda j * d.g j z) + ∑ i, mu i * hardRow d i z

/-- Exact bridge to the accepted generic finite-row Lagrangian. -/
theorem concatenated_eq (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ) :
    Chapter06.QuadraticRanking.lagrangian d.f (rows d) (weights lambda mu) =
      lagrangian d lambda mu := by
  funext z
  simp [Chapter06.QuadraticRanking.lagrangian,rows,weights,lagrangian,Fin.sum_univ_add,
    add_assoc]

theorem hardRow_hasFDerivAt (d : Data n m l r) (i : Fin r) (a : Point n m) :
    HasFDerivAt (hardRow d i) (linearFormCLM (d.A i) (d.B i)) a :=
  (linearFormCLM (d.A i) (d.B i)).hasFDerivAt.sub_const _

theorem hardRow_contDiff (d : Data n m l r) (i : Fin r) :
    ContDiff ℝ 2 (hardRow d i) :=
  (linearFormCLM (d.A i) (d.B i)).contDiff.sub contDiff_const

theorem hardRow_convex (d : Data n m l r) (i : Fin r) :
    ConvexOn ℝ univ (hardRow d i) := by
  exact (((linearFormCLM (d.A i) (d.B i)).toLinearMap.convexOn convex_univ).add_const
    (-d.b i)).congr (fun x _ => by
      change LinearForm (d.A i) (d.B i) x + -d.b i = LinearForm (d.A i) (d.B i) x - d.b i
      ring)

theorem rows_convex (d : Data n m l r)
    (hg : ∀ j, ConvexOn ℝ univ (d.g j)) :
    ∀ i, ConvexOn ℝ univ (rows d i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j; simpa [rows] using hg j
  · intro j; simpa [rows] using hardRow_convex d j

theorem rows_contDiff (d : Data n m l r) (hg : ∀ j, ContDiff ℝ 2 (d.g j)) :
    ∀ i, ContDiff ℝ 2 (rows d i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j; simpa [rows] using hg j
  · intro j; simpa [rows] using hardRow_contDiff d j

theorem weights_nonneg (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hl : ∀ j, 0 ≤ lambda j) (hm : ∀ i, 0 ≤ mu i) :
    ∀ i, 0 ≤ weights lambda mu i := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j; simpa [weights] using hl j
  · intro j; simpa [weights] using hm j

theorem lagrangian_convex (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hf : ConvexOn ℝ univ d.f) (hg : ∀ j, ConvexOn ℝ univ (d.g j))
    (hl : ∀ j, 0 ≤ lambda j) (hm : ∀ i, 0 ≤ mu i) :
    ConvexOn ℝ univ (lagrangian d lambda mu) := by
  rw [← concatenated_eq]
  exact Chapter06.QuadraticRanking.lagrangian_convex d.f (rows d) (weights lambda mu)
    hf (rows_convex d hg) (weights_nonneg lambda mu hl hm)

theorem lagrangian_contDiff (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hf : ContDiff ℝ 2 d.f) (hg : ∀ j, ContDiff ℝ 2 (d.g j)) :
    ContDiff ℝ 2 (lagrangian d lambda mu) := by
  rw [← concatenated_eq]
  exact Chapter06.QuadraticRanking.lagrangian_contDiff d.f (rows d) (weights lambda mu)
    hf (rows_contDiff d hg)

def derivative (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) : Point n m →L[ℝ] ℝ :=
  fderiv ℝ d.f a + (∑ j, lambda j • fderiv ℝ (d.g j) a) +
    ∑ i, mu i • linearFormCLM (d.A i) (d.B i)

theorem lagrangian_hasFDerivAt (d : Data n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (a : Point n m)
    (hf : DifferentiableAt ℝ d.f a) (hg : ∀ j, DifferentiableAt ℝ (d.g j) a) :
    HasFDerivAt (lagrangian d lambda mu) (derivative d lambda mu a) a := by
  unfold lagrangian derivative
  exact (hf.hasFDerivAt.fun_add
    (HasFDerivAt.fun_sum fun j _ => (hg j).hasFDerivAt.const_mul (lambda j))).fun_add
      (HasFDerivAt.fun_sum fun i _ => (hardRow_hasFDerivAt d i a).const_mul (mu i))

theorem lagrangian_fderiv (d : Data n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (a : Point n m)
    (hf : DifferentiableAt ℝ d.f a) (hg : ∀ j, DifferentiableAt ℝ (d.g j) a) :
    fderiv ℝ (lagrangian d lambda mu) a = derivative d lambda mu a :=
  (lagrangian_hasFDerivAt d lambda mu a hf hg).fderiv

/-- Physical displacement only; epigraph height is absent. -/
def linear (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a z : Point n m) : ℝ := fderiv ℝ (lagrangian d lambda mu) a (z-a)

def hessian (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a z : Point n m) : ℝ :=
  fderiv ℝ (fderiv ℝ (lagrangian d lambda mu)) a (z-a) (z-a)

theorem hessian_nonneg (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hf : ConvexOn ℝ univ d.f) (hg : ∀ j, ConvexOn ℝ univ (d.g j))
    (hl : ∀ j, 0 ≤ lambda j) (hm : ∀ i, 0 ≤ mu i)
    (hf2 : ContDiff ℝ 2 d.f) (hg2 : ∀ j, ContDiff ℝ 2 (d.g j)) (a z : Point n m) :
    0 ≤ hessian d lambda mu a z :=
  Chapter05.Quadratic.hessian_nonneg (lagrangian_convex d lambda mu hf hg hl hm)
    (lagrangian_contDiff d lambda mu hf2 hg2) a (z-a)

/-- Actual full KKT stationarity, including all affine normals. -/
theorem continuous_stationarity (d : Data n m l r) (hr : Regularity d)
    (a : Point n m) (K : FeasibleKKT d hr a) (v : RealVector n) :
    fderiv ℝ (lagrangian d K.lambda K.mu) a (v,0) = 0 := by
  rw [lagrangian_fderiv d K.lambda K.mu a
    ((hr.objective_C1.differentiable (by norm_num)) a)
    (fun j => ((hr.constraint_C1 j).differentiable (by norm_num)) a)]
  have hk := congrArg (fun T : RealVector n →L[ℝ] ℝ => T v) K.stationarity
  simpa only [derivative,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,Chapter03.OAKKT.restrict_apply,fiberLinearRow_apply,
    boxedModel,ContinuousLinearMap.zero_apply,linearFormCLM_apply] using hk

/-- At a polished anchor the linear term depends only on integer displacement. -/
theorem linear_only_integer (d : Data n m l r) (hr : Regularity d)
    (a : Point n m) (K : FeasibleKKT d hr a) (z : Point n m) :
    linear d K.lambda K.mu a z =
      fderiv ℝ (lagrangian d K.lambda K.mu) a (0,z.2-a.2) := by
  have he : z-a = (z.1-a.1,0) + (0,z.2-a.2) := by ext <;> simp
  unfold linear
  rw [he,map_add,continuous_stationarity d hr a K,zero_add]

/-- Source-facing existence: a true polished fixed-fiber minimum supplies the
full KKT weights whose continuous derivative vanishes. -/
theorem polished_stationarity (d : Data n m l r) (hr : Regularity d)
    (y : IntVector m) (a : Point n m)
    (ha : IsMinimizer (d.feasibleFiber y) d.f a) :
    ∃ K : FeasibleKKT d hr a, ∀ v : RealVector n,
      fderiv ℝ (lagrangian d K.lambda K.mu) a (v,0) = 0 := by
  obtain ⟨K⟩ := feasibleKKT_exists d hr y ha
  exact ⟨K,continuous_stationarity d hr a K⟩

end Chapter07.FullLagrangian

#print axioms Chapter07.FullLagrangian.concatenated_eq
#print axioms Chapter07.FullLagrangian.lagrangian_fderiv
#print axioms Chapter07.FullLagrangian.lagrangian_convex
#print axioms Chapter07.FullLagrangian.lagrangian_contDiff
#print axioms Chapter07.FullLagrangian.hessian_nonneg
#print axioms Chapter07.FullLagrangian.continuous_stationarity
#print axioms Chapter07.FullLagrangian.linear_only_integer

#print axioms Chapter07.FullLagrangian.polished_stationarity
