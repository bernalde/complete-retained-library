module

public import Chapter02LiftingSource
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! Actual mixed finite model I. Original integer y remains integer; appended
normalization u=x+y and height v are continuous. The source adapter uses zero
budgets, so the displayed physical height is z=v+1: v≥u²−1,v≤0 is exactly
z≥u²,z≤1. This coordinate translation has zero objective coefficient. -/
noncomputable section
open scoped BigOperators
namespace Chapter02.LiftingMixedExamples

def original : ModelData 1 1 1 2 where
  g := fun _ p => (p.1 0+p.2 0)^2-1
  A := fun i _ => if i=0 then 1 else -1
  B := fun _ _ => 0
  rhs := fun _ => 1
  c1 := fun _ => 1
  c2 := fun _ => 1
  lo := fun _ => 0
  hi := fun _ => 1

def argA : Fin 1 → RealVector 1 := fun _ _ => 1
def argB : Fin 1 → RealVector 1 := fun _ _ => 1
def offset : RealVector 1 := fun _ => 0
def phi : Fin 1 → ℝ → ℝ := fun _ u => u^2-1
def weight : Fin 1 → RealVector 1 := fun _ _ => 1
def normalized := original.normalizedLift argA argB offset phi weight
def normProject : Point 2 1 → Point 1 1 := liftingSourceProject (n := 1) (q := 1)
def normHeight : Point 2 1 → RealVector 1 := liftingSourceHeight (n := 1) (q := 1)
def liftProject : Point 3 1 → Point 2 1 := liftingSourceProject (n := 2) (q := 1)
def liftHeight : Point 3 1 → RealVector 1 := liftingSourceHeight (n := 2) (q := 1)
def component : Fin 1 → Point 2 1 → ℝ := fun _ p => phi 0 (normHeight p 0)
def lifted := normalized.separableLift component weight
def originalPoint (x y : ℝ) : Point 1 1 := (fun _ => x,fun _ => y)
def normalizedPoint (x y : ℝ) : Point 2 1 := liftingSourceInsert (q := 1) (originalPoint x y) (fun _ => x+y)
def liftedPoint (x y : ℝ) : Point 3 1 := liftingSourceInsert (q := 1) (normalizedPoint x y) (fun _ => (x+y)^2-1)

theorem decomposition (i : Fin 1) (p : Point 1 1) :
    original.g i p = ∑ j, weight i j * phi j
      (liftingAffineArgument (argA j) (argB j) (offset j) p) := by
  simp [original,weight,phi,liftingAffineArgument,argA,argB,offset,LinearForm,Fin.sum_univ_one]

theorem normalized_decomposition (i : Fin 1) (p : Point 2 1) :
    normalized.g i p = ∑ j, weight i j * component j p := by
  simp [normalized,ModelData.normalizedLift,component,normHeight,Fin.sum_univ_one]

theorem original_rows (p : Point 1 1) :
    p ∈ original.feasibleOn Set.univ ↔
      -1 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ (p.1 0+p.2 0)^2 ≤ 1 ∧
      p ∈ IntegerCylinder original.lo original.hi := by
  change (((True ∧ ∀ i, (p.1 0+p.2 0)^2-1 ≤ 0) ∧ _) ∧ _) ↔ _
  have hl : p ∈ original.linearRegion ↔ -1 ≤ p.1 0 ∧ p.1 0 ≤ 1 := by
    simp [ModelData.linearRegion,original,LinearForm,Fin.sum_univ_one,Fin.forall_fin_two]
    constructor <;> intro h <;> constructor <;> linarith
  rw [hl]
  simp only [forall_const,sub_nonpos,true_and]
  tauto

theorem original_point_feasible (x : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) :
    originalPoint x 0 ∈ original.feasibleOn Set.univ := by
  apply (original_rows _).mpr
  refine ⟨hx,hx',?_,?_⟩
  · change (x+0)^2 ≤ 1
    nlinarith [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hx)]
  · refine ⟨fun _ => 0,?_,by ext i; norm_num [originalPoint]⟩
    intro i; norm_num [original]

theorem normalized_rows (p : Point 2 1) :
    p ∈ normalized.feasibleOn Set.univ ↔
      normProject p ∈ original.feasibleOn Set.univ ∧
      normHeight p 0 = (normProject p).1 0+p.2 0 := by
  simpa [normalized,argA,argB,offset,liftingAffineArgument,LinearForm,Fin.sum_univ_one,
    Fin.forall_fin_one,liftingSourceProject,normProject,normHeight] using
    lifting_normalization_feasible_iff original Set.univ argA argB offset phi weight decomposition p

theorem normalized_mixed_projection :
    normProject '' normalized.feasibleOn Set.univ = original.feasibleOn Set.univ := by
  simpa [normalized,normProject] using lifting_normalization_projection original Set.univ
    argA argB offset phi weight decomposition

theorem normalized_relaxed_projection :
    normProject '' normalized.relaxationOn Set.univ = original.relaxationOn Set.univ := by
  simpa [normalized,normProject] using lifting_normalization_relaxation_projection original Set.univ
    argA argB offset phi weight decomposition

theorem lifted_mixed_projection :
    liftProject '' lifted.feasibleOn Set.univ = normalized.feasibleOn Set.univ := by
  simpa [lifted,liftProject] using lifting_source_mixed_projection normalized Set.univ component weight
    (by intro i j; norm_num [weight]) normalized_decomposition

theorem lifted_relaxed_projection :
    liftProject '' lifted.relaxationOn Set.univ = normalized.relaxationOn Set.univ := by
  simpa [lifted,liftProject] using lifting_source_relaxation_projection normalized Set.univ component weight
    (by intro i j; norm_num [weight]) normalized_decomposition

theorem normalized_point_feasible (x : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) :
    normalizedPoint x 0 ∈ normalized.feasibleOn Set.univ := by
  apply (normalized_rows _).mpr
  constructor
  · simpa only [normProject,normalizedPoint,lifting_source_project_insert] using original_point_feasible x hx hx'
  · simp [normHeight,normProject,normalizedPoint,liftingSourceHeight,liftingSourceProject,
      liftingSourceInsert,originalPoint,weightedX,weightedV,weightedInsert]
    rfl

theorem lifted_point_feasible (x : ℝ) (hx : -1 ≤ x) (hx' : x ≤ 1) :
    liftedPoint x 0 ∈ lifted.feasibleOn Set.univ := by
  simpa [lifted,liftedPoint,component,phi,normalizedPoint,originalPoint,normHeight] using
    lifting_source_graph_feasible normalized Set.univ component weight normalized_decomposition
      (normalized_point_feasible x hx hx')

theorem original_minimum : IsMinimizer (original.feasibleOn Set.univ) original.objective
    (originalPoint (-1) 0) := by
  refine ⟨original_point_feasible (-1) (by norm_num) (by norm_num),?_⟩
  intro p hp
  have hb := ((original_rows p).mp hp).2.2.1
  simp only [original,ModelData.objective,LinearForm,Fin.sum_univ_one,originalPoint]
  norm_num
  nlinarith [sq_nonneg (p.1 0+p.2 0+1)]

theorem normalized_minimum : IsMinimizer (normalized.feasibleOn Set.univ) normalized.objective
    (normalizedPoint (-1) 0) := by
  have h := (lifting_normalization_minimizer_iff original Set.univ argA argB offset phi weight
    decomposition (normalizedPoint (-1) 0)).mpr
  apply h
  constructor
  · simpa [normalized] using normalized_point_feasible (-1) (by norm_num) (by norm_num)
  · simpa [normalizedPoint] using original_minimum

theorem lifted_minimum : IsMinimizer (lifted.feasibleOn Set.univ) lifted.objective
    (liftedPoint (-1) 0) := by
  have h := (lifting_source_minimizer_iff normalized Set.univ component weight
    (by intro i j; norm_num [weight]) normalized_decomposition (liftedPoint (-1) 0)).mpr
  apply h
  constructor
  · simpa [lifted] using lifted_point_feasible (-1) (by norm_num) (by norm_num)
  · simpa [liftedPoint] using normalized_minimum

theorem fractional_normalization_witness :
    normalizedPoint (1/2) 0 ∈ normalized.feasibleOn Set.univ ∧
    liftedPoint (1/2) 0 ∈ lifted.feasibleOn Set.univ ∧
    normHeight (normalizedPoint (1/2) 0) 0 = (1/2:ℝ) ∧
    ¬ ∃ z : ℤ, (z:ℝ) = normHeight (normalizedPoint (1/2) 0) 0 := by
  refine ⟨normalized_point_feasible (1/2) (by norm_num) (by norm_num),
    lifted_point_feasible (1/2) (by norm_num) (by norm_num),?_,?_⟩
  · norm_num [normalizedPoint,normHeight]
  · rintro ⟨z,hz⟩
    norm_num [normalizedPoint,normHeight] at hz
    have hpos : 0 < z := by exact_mod_cast (show (0:ℝ)<(z:ℝ) by linarith)
    have hlt : z < 1 := by exact_mod_cast (show (z:ℝ)<1 by linarith)
    omega

theorem normalized_auxiliary_objective_zero (p : Point 2 1) :
    normalized.objective p = original.objective (normProject p) :=
  lifting_normalization_objective original argA argB offset phi weight p

theorem lifted_auxiliary_objective_zero (p : Point 3 1) :
    lifted.objective p = original.objective (normProject (liftProject p)) := by
  rw [show lifted = normalized.separableLift component weight from rfl,
    lifting_source_objective,normalized_auxiliary_objective_zero]
  rfl

theorem total_mixed_projection :
    (normProject ∘ liftProject) '' lifted.feasibleOn Set.univ = original.feasibleOn Set.univ := by
  change (fun x => normProject (liftProject x)) '' lifted.feasibleOn Set.univ = _
  rw [← Set.image_image normProject liftProject,lifted_mixed_projection,normalized_mixed_projection]

theorem total_relaxed_projection :
    (normProject ∘ liftProject) '' lifted.relaxationOn Set.univ = original.relaxationOn Set.univ := by
  change (fun x => normProject (liftProject x)) '' lifted.relaxationOn Set.univ = _
  rw [← Set.image_image normProject liftProject,lifted_relaxed_projection,normalized_relaxed_projection]

theorem physical_height_rows (p : Point 3 1) :
    p ∈ lifted.feasibleOn Set.univ ↔
      liftProject p ∈ normalized.linearRegion ∧
      liftProject p ∈ IntegerCylinder original.lo original.hi ∧
      (normHeight (liftProject p) 0)^2 ≤ liftHeight p 0 + 1 ∧
      liftHeight p 0 + 1 ≤ 1 := by
  have he := lifting_source_feasible_rows normalized Set.univ component weight p
  simp only [Set.preimage_univ] at he
  rw [show lifted = normalized.separableLift component weight from rfl,he]
  change (True ∧ (∀ j : Fin 1, phi 0 (normHeight (liftProject p) 0) ≤ liftHeight p j) ∧
      liftProject p ∈ normalized.linearRegion ∧
      (∀ i : Fin 1, (∑ j, weight i j * liftHeight p j) ≤ 0) ∧
      liftProject p ∈ IntegerCylinder original.lo original.hi) ↔ _
  simp only [Fin.forall_fin_one,Fin.sum_univ_one,weight,one_mul,phi,true_and]
  constructor
  · rintro ⟨hc,hl,hb,hi⟩
    exact ⟨hl,hi,by linarith,by linarith⟩
  · rintro ⟨hl,hi,hc,hb⟩
    exact ⟨by linarith,hl,by linarith,hi⟩

theorem attained_values :
    original.objective (originalPoint (-1) 0) = -1 ∧
    normalized.objective (normalizedPoint (-1) 0) = -1 ∧
    lifted.objective (liftedPoint (-1) 0) = -1 := by
  rw [normalized_auxiliary_objective_zero,lifted_auxiliary_objective_zero]
  simp only [normProject,liftProject,normalizedPoint,liftedPoint,lifting_source_project_insert]
  norm_num [original,ModelData.objective,LinearForm,Fin.sum_univ_one,originalPoint]

theorem component_derivative (u : ℝ) : HasDerivAt (phi 0) (2*u) u := by
  change HasDerivAt (fun z : ℝ => z^2-1) (2*u) u
  convert (hasDerivAt_pow 2 u).sub_const 1 using 1
  norm_num

theorem original_derivative (p : Point 1 1) :
    HasFDerivAt (original.g 0)
      ((2*(p.1 0+p.2 0)) • linearFormCLM (argA 0) (argB 0)) p := by
  have h := lifting_affine_component_derivative (argA 0) (argB 0) (offset 0)
    (phi 0) (2*liftingAffineArgument (argA 0) (argB 0) (offset 0) p) p
    (component_derivative _)
  simpa only [original,phi,argA,argB,offset,liftingAffineArgument,LinearForm,
    Fin.sum_univ_one,one_mul,add_zero] using h

theorem component_convex : ConvexOn ℝ Set.univ (phi 0) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ s t hs ht hst
  have hp := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x-y))
  have he : t = 1-s := by linarith
  simp only [phi,smul_eq_mul]
  rw [he] at hp ⊢
  nlinarith

end Chapter02.LiftingMixedExamples

#print axioms Chapter02.LiftingMixedExamples.decomposition
#print axioms Chapter02.LiftingMixedExamples.normalized_decomposition
#print axioms Chapter02.LiftingMixedExamples.original_rows
#print axioms Chapter02.LiftingMixedExamples.original_point_feasible
#print axioms Chapter02.LiftingMixedExamples.normalized_rows
#print axioms Chapter02.LiftingMixedExamples.normalized_mixed_projection
#print axioms Chapter02.LiftingMixedExamples.normalized_relaxed_projection
#print axioms Chapter02.LiftingMixedExamples.lifted_mixed_projection
#print axioms Chapter02.LiftingMixedExamples.lifted_relaxed_projection
#print axioms Chapter02.LiftingMixedExamples.normalized_point_feasible
#print axioms Chapter02.LiftingMixedExamples.lifted_point_feasible
#print axioms Chapter02.LiftingMixedExamples.original_minimum
#print axioms Chapter02.LiftingMixedExamples.normalized_minimum
#print axioms Chapter02.LiftingMixedExamples.lifted_minimum
#print axioms Chapter02.LiftingMixedExamples.fractional_normalization_witness
#print axioms Chapter02.LiftingMixedExamples.normalized_auxiliary_objective_zero
#print axioms Chapter02.LiftingMixedExamples.lifted_auxiliary_objective_zero
#print axioms Chapter02.LiftingMixedExamples.total_mixed_projection
#print axioms Chapter02.LiftingMixedExamples.total_relaxed_projection
#print axioms Chapter02.LiftingMixedExamples.physical_height_rows
#print axioms Chapter02.LiftingMixedExamples.attained_values
#print axioms Chapter02.LiftingMixedExamples.component_derivative
#print axioms Chapter02.LiftingMixedExamples.original_derivative
#print axioms Chapter02.LiftingMixedExamples.component_convex
