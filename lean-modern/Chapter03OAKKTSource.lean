module

public import Chapter02WeightedRestoration
public import Chapter06

@[expose] public section

/-! Qualified source adapters for Chapter 3. Every original g row is retained,
including source-softened affine and bound rows. The objective is supplied
separately. These finite histories are not executions of Algorithm 1. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter03.OAKKT

variable {n m l r k : ℕ}

def intCast (y : IntVector m) : RealVector m := fun i => (y i : ℝ)

def hard (d : ModelData n m l r) (y : RealVector m) (i : Fin r)
    (x : RealVector n) : ℝ := linearResidual d i (x,y)

def soft (d : ModelData n m l r) (y : RealVector m) (j : Fin l)
    (x : RealVector n) : ℝ := d.g j (x,y)

def fiber (d : ModelData n m l r) (y : RealVector m) : Set (RealVector n) :=
  {x | (x,y) ∈ d.linearRegion ∧ ∀ j, d.g j (x,y) ≤ 0}

def fiberObjective (f : Point n m → ℝ) (y : RealVector m) (x : RealVector n) : ℝ :=
  f (x,y)

def restrict (D : Point n m →L[ℝ] ℝ) : RealVector n →L[ℝ] ℝ :=
  D.comp (fiberInclusionDerivative n m)

@[simp] theorem restrict_apply (D : Point n m →L[ℝ] ℝ) (v : RealVector n) :
    restrict D v = D (v,0) := rfl

theorem fiber_derivative {g : Point n m → ℝ} {D : Point n m →L[ℝ] ℝ}
    {x : RealVector n} {y : RealVector m} (hg : HasFDerivAt g D (x,y)) :
    HasFDerivAt (fun z => g (z,y)) (restrict D) x :=
  hg.comp x (fiberInclusion_hasFDerivAt y x)

theorem derivative_fiber_action (D : Point n m →L[ℝ] ℝ)
    (x a : RealVector n) (y : RealVector m) :
    D ((x,y)-(a,y)) = restrict D (x-a) := by simp

theorem derivative_fiber_coordinates (D : Point n m →L[ℝ] ℝ)
    (x a : RealVector n) (y : RealVector m) :
    D ((x,y)-(a,y)) = ∑ i, restrict D (Pi.single i 1) * (x-a) i := by
  rw [derivative_fiber_action, coneFunctional_coordinates]

theorem hard_derivative (d : ModelData n m l r) (y : RealVector m)
    (i : Fin r) (x : RealVector n) :
    HasFDerivAt (hard d y i) (fiberLinearRow d i) x :=
  (linearResidual_hasFDerivAt d i (x,y)).comp x (fiberInclusion_hasFDerivAt y x)

theorem hard_tangent (d : ModelData n m l r) (y : RealVector m)
    (i : Fin r) (a x : RealVector n) :
    hard d y i a + fiberLinearRow d i (x-a) = hard d y i x := by
  simp only [hard, ← fiberLinearResidual_eq d y, map_sub]
  ring

theorem fiber_iff (d : ModelData n m l r) (y : RealVector m) (x : RealVector n) :
    x ∈ fiber d y ↔ (∀ i, hard d y i x ≤ 0) ∧ ∀ j, soft d y j x ≤ 0 := by
  simp only [fiber, Set.mem_setOf_eq, hard, soft, ModelData.linearRegion,
    linearResidual, sub_nonpos]

theorem fiber_original_iff (d : ModelData n m l r) (y : IntVector m)
    (hy : y ∈ IntegerBox d.lo d.hi) (x : RealVector n) :
    x ∈ fiber d (intCast y) ↔ (x,intCast y) ∈ d.feasibleOn Set.univ := by
  rw [source_feasible_iff]
  constructor
  · rintro ⟨hh,hg⟩
    exact ⟨Set.mem_univ _,hg,hh,⟨y,hy,rfl⟩⟩
  · rintro ⟨_,hg,hh,_⟩
    exact ⟨hh,hg⟩

theorem fiber_minimizer_original_iff (d : ModelData n m l r)
    (f : Point n m → ℝ) (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (x : RealVector n) :
    IsMinimizer (fiber d (intCast y)) (fiberObjective f (intCast y)) x ↔
      IsMinimizer {p ∈ d.feasibleOn Set.univ | p.2 = intCast y} f (x,intCast y) := by
  constructor
  · rintro ⟨hx,hm⟩
    refine ⟨⟨(fiber_original_iff d y hy x).mp hx,rfl⟩,?_⟩
    rintro ⟨z,w⟩ ⟨hz,hw⟩
    change w = intCast y at hw
    subst w
    exact hm z ((fiber_original_iff d y hy z).mpr hz)
  · rintro ⟨hx,hm⟩
    refine ⟨(fiber_original_iff d y hy x).mpr hx.1,?_⟩
    intro z hz
    exact hm (z,intCast y) ⟨(fiber_original_iff d y hy z).mp hz,rfl⟩

/-- Exact source-row reindexing; no scaling, deletion, or merging of duplicates. -/
structure RowReindexing {s : ℕ} (g : Fin s → Point n m → ℝ)
    (d : ModelData n m l r) where
  index : Fin s ≃ Fin l
  row_eq : ∀ j, d.g (index j) = g j

/-- Actual global affine extension, required to identify its ambient derivative. -/
def AffineRow (g : Point n m → ℝ) : Prop :=
  ∃ ax : RealVector n, ∃ ay : RealVector m, ∃ b : ℝ,
    ∀ p, g p = LinearForm ax ay p - b

theorem affine_derivative_identity {g : Point n m → ℝ}
    {D : Point n m →L[ℝ] ℝ} {a : Point n m}
    (ax : RealVector n) (ay : RealVector m) (b : ℝ)
    (he : ∀ p, g p = LinearForm ax ay p-b) (hd : HasFDerivAt g D a) :
    D = linearFormCLM ax ay := by
  have hfun : g = fun p => LinearForm ax ay p-b := funext he
  rw [hfun] at hd
  exact hd.unique ((linearFormCLM ax ay).hasFDerivAt.sub_const b)

theorem affine_tangent {g : Point n m → ℝ} {D : Point n m →L[ℝ] ℝ}
    {a : Point n m} (hg : AffineRow g) (hd : HasFDerivAt g D a)
    (q : Point n m) : g a + D (q-a) = g q := by
  rcases hg with ⟨ax,ay,b,he⟩
  rw [affine_derivative_identity ax ay b he hd, map_sub]
  simp only [linearFormCLM_apply,he]
  ring

/-- Algorithm 1's all-row initial slot and a distinct source-selected current
slot. No seed feasibility, seed optimizer, or execution is assumed. -/
structure History (d : ModelData n m l r) (f : Point n m → ℝ)
    (N : Set (Fin l)) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (x : RealVector n) (y : RealVector m) where
  seed : Fin k
  current : Fin k
  distinct : seed ≠ current
  initial_all : c.selected seed = Set.univ
  current_origin : c.origin current = (x,y)
  current_selected : c.selected current = {j | j ∈ N ∧ 0 ≤ d.g j (x,y)}
  affine : ∀ j, j ∉ N → AffineRow (d.g j)
  g_derivative : ∀ i j, HasFDerivAt (d.g j) (c.derivative i j) (c.origin i)
  f_derivative : ∀ i, HasFDerivAt f (df i) (c.origin i)

def restSet (d : ModelData n m l r) (y : RealVector m) : Set (RealVector (n+l)) :=
  {q ∈ weightedX ⁻¹' (Set.univ : Set (RealVector n)) |
    ∀ i, weightedLiftRows (hard d y) (soft d y) i q ≤ 0}

def restCost : RealVector (n+l) →L[ℝ] ℝ :=
  weightedLiftObjective (fun _ : Fin l => 1)

@[simp] theorem restCost_insert (x : RealVector n) (s : RealVector l) :
    restCost (weightedInsert x s) = ∑ j, s j := by simp [restCost]

theorem restSet_insert_iff (d : ModelData n m l r) (y : RealVector m)
    (x : RealVector n) (s : RealVector l) :
    weightedInsert x s ∈ restSet d y ↔
      (∀ i, hard d y i x ≤ 0) ∧ (∀ j, soft d y j x ≤ s j) ∧ (∀ j, 0 ≤ s j) := by
  simp only [restSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, true_and,
    weighted_lift_rows_iff, weightedX_insert, weightedV_insert]

/-- Actual nonlinear-objective, continuous-coordinate KKT certificate. -/
structure FixedKKT (d : ModelData n m l r) (f : Point n m → ℝ)
    (x : RealVector n) (y : RealVector m) where
  Df : Point n m →L[ℝ] ℝ
  Dg : Fin l → Point n m →L[ℝ] ℝ
  lambda : Fin l → ℝ
  mu : Fin r → ℝ
  primal : x ∈ fiber d y
  derivative_f : HasFDerivAt f Df (x,y)
  derivative_g : ∀ j, HasFDerivAt (d.g j) (Dg j) (x,y)
  lambda_nonneg : ∀ j, 0 ≤ lambda j
  mu_nonneg : ∀ i, 0 ≤ mu i
  soft_compl : ∀ j, lambda j * soft d y j x = 0
  hard_compl : ∀ i, mu i * hard d y i x = 0
  stationarity : restrict Df + (∑ j, lambda j • restrict (Dg j)) +
    (∑ i, mu i • fiberLinearRow d i) = 0

/-- Raw KKT equations for the displayed sum of individual nonnegative slacks.
Every source g derivative is supplied; no minimum or CQ is hidden here. -/
structure SumKKT (d : ModelData n m l r) (x : RealVector n)
    (y : RealVector m) (s : RealVector l) where
  Dg : Fin l → Point n m →L[ℝ] ℝ
  lambda : Fin l → ℝ
  nu : Fin l → ℝ
  mu : Fin r → ℝ
  primal : weightedInsert x s ∈ restSet d y
  derivative_g : ∀ j, HasFDerivAt (d.g j) (Dg j) (x,y)
  lambda_nonneg : ∀ j, 0 ≤ lambda j
  nu_nonneg : ∀ j, 0 ≤ nu j
  mu_nonneg : ∀ i, 0 ≤ mu i
  soft_compl : ∀ j, lambda j * (soft d y j x-s j) = 0
  slack_compl : ∀ j, nu j * s j = 0
  slack_stationarity : ∀ j, 1-lambda j-nu j = 0
  hard_compl : ∀ i, mu i * hard d y i x = 0
  stationarity : (∑ j, lambda j • restrict (Dg j)) +
    (∑ i, mu i • fiberLinearRow d i) = 0

end Chapter03.OAKKT
