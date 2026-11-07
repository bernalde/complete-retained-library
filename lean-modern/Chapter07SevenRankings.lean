module

public import Chapter07FullLagrangian
public import Chapter07
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-! Seven literal physical rankings. Coordinate sums of squares are Euclidean;
only the infinity ranking uses the default finite Pi/product maximum norm.
No epigraph height, ambient center existence, or seed KKT provenance is assumed. -/
noncomputable section
open Set
open scoped BigOperators
open Chapter02 Chapter06.Level
namespace Chapter07.SevenRankings
variable {n m l r : ℕ}

def l1 (a z : Point n m) : ℝ :=
  (∑ i, |z.1 i-a.1 i|) + ∑ j, |z.2 j-a.2 j|

def linf (a z : Point n m) : ℝ := max ‖z.1-a.1‖ ‖z.2-a.2‖

def squared (a z : Point n m) : ℝ :=
  (∑ i, (z.1 i-a.1 i)^2) + ∑ j, (z.2 j-a.2 j)^2

def taylor (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a z : Point n m) : ℝ :=
  FullLagrangian.linear d lambda mu a z + FullLagrangian.hessian d lambda mu a z / 2

def scaled (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) (rho : ℝ) (z : Point n m) : ℝ :=
  FullLagrangian.linear d lambda mu a z + rho * squared a z

inductive Kind
  | l1 | linf | squared | taylor | hessian | scaled | linear
  deriving DecidableEq, Repr

def ranking (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) (rho : ℝ) (kind : Kind) : Point n m → ℝ :=
  match kind with
  | .l1 => l1 a
  | .linf => linf a
  | .squared => squared a
  | .taylor => taylor d lambda mu a
  | .hessian => FullLagrangian.hessian d lambda mu a
  | .scaled => scaled d lambda mu a rho
  | .linear => FullLagrangian.linear d lambda mu a

/-- Exact finite-coordinate adapter for the earlier global norm lifts. -/
def coordinates (a z : Point n m) : Fin (n+m) → ℝ :=
  Fin.append (z.1-a.1) (z.2-a.2)

theorem l1_eq_coordinates (a z : Point n m) :
    l1 a z = Chapter07.l1 (coordinates a z) := by
  simp [l1,Chapter07.l1,coordinates,Fin.sum_univ_add]

theorem linf_eq_norm (a z : Point n m) : linf a z = ‖z-a‖ := rfl

/-- Including zero makes the empty-coordinate convention explicit. -/
theorem linf_le_iff (a z : Point n m) (s : ℝ) :
    linf a z ≤ s ↔ 0 ≤ s ∧ (∀ i, |z.1 i-a.1 i| ≤ s) ∧
      (∀ j, |z.2 j-a.2 j| ≤ s) := by
  constructor
  · intro h
    have hs : 0 ≤ s := (norm_nonneg (z-a)).trans (by simpa [linf_eq_norm] using h)
    refine ⟨hs,?_,?_⟩
    · simpa only [Pi.sub_apply,Real.norm_eq_abs] using
        (pi_norm_le_iff_of_nonneg hs).mp ((le_max_left _ _).trans h)
    · simpa only [Pi.sub_apply,Real.norm_eq_abs] using
        (pi_norm_le_iff_of_nonneg hs).mp ((le_max_right _ _).trans h)
  · rintro ⟨hs,hx,hy⟩
    exact max_le ((pi_norm_le_iff_of_nonneg hs).mpr (by simpa using hx))
      ((pi_norm_le_iff_of_nonneg hs).mpr (by simpa using hy))

theorem linf_eq_coordinates [Nonempty (Fin (n+m))] (a z : Point n m) :
    linf a z = Chapter07.linf (coordinates a z) := by
  apply le_antisymm
  · apply (linf_le_iff a z _).mpr
    have hc := (Chapter07.linf_le_iff (coordinates a z) _).mp (le_refl _)
    refine ⟨Chapter07.linf_nonneg _,?_,?_⟩
    · intro i; simpa [coordinates] using hc (Fin.castAdd m i)
    · intro j; simpa [coordinates] using hc (Fin.natAdd n j)
  · apply (Chapter07.linf_le_iff (coordinates a z) _).mpr
    have hc := (linf_le_iff a z _).mp (le_refl _)
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i; simpa [coordinates] using hc.2.1 i
    · intro j; simpa [coordinates] using hc.2.2 j

@[simp] theorem l1_zero_dimensions (a z : Point 0 0) : l1 a z = 0 := by simp [l1]
@[simp] theorem squared_zero_dimensions (a z : Point 0 0) : squared a z = 0 := by
  simp [squared]
@[simp] theorem linf_zero_dimensions (a z : Point 0 0) : linf a z = 0 := by
  have h : z = a := Subsingleton.elim _ _
  simp [h,linf]

@[simp] theorem scaled_zero (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a z : Point n m) : scaled d lambda mu a 0 z = FullLagrangian.linear d lambda mu a z := by
  simp [scaled]

@[simp] theorem ranking_at_anchor (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) (rho : ℝ) (kind : Kind) : ranking d lambda mu a rho kind a = 0 := by
  cases kind <;> simp [ranking,l1,linf,squared,taylor,scaled,
    FullLagrangian.linear,FullLagrangian.hessian]

theorem l1_continuous (a : Point n m) : Continuous (l1 a) := by
  unfold l1
  fun_prop

theorem linf_continuous (a : Point n m) : Continuous (linf a) := by
  unfold linf
  fun_prop

theorem squared_continuous (a : Point n m) : Continuous (squared a) := by
  unfold squared
  fun_prop

theorem linear_continuous (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) : Continuous (FullLagrangian.linear d lambda mu a) := by
  unfold FullLagrangian.linear
  fun_prop

theorem hessian_continuous (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) : Continuous (FullLagrangian.hessian d lambda mu a) := by
  unfold FullLagrangian.hessian
  fun_prop

/-- Once derivatives at a fixed anchor are formed, all seven displayed functions
are continuous even without convexity or KKT assumptions. -/
theorem ranking_continuous (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) (rho : ℝ) (kind : Kind) : Continuous (ranking d lambda mu a rho kind) := by
  cases kind with
  | l1 => exact l1_continuous a
  | linf => exact linf_continuous a
  | squared => exact squared_continuous a
  | taylor =>
      exact (linear_continuous d lambda mu a).add
        ((hessian_continuous d lambda mu a).div_const 2)
  | hessian => exact hessian_continuous d lambda mu a
  | scaled =>
      exact (linear_continuous d lambda mu a).add
        (continuous_const.mul (squared_continuous a))
  | linear => exact linear_continuous d lambda mu a

theorem sum_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (hf : ∀ i, ConvexOn ℝ univ (f i)) :
    ConvexOn ℝ univ (fun z => ∑ i, f i z) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy s t hs ht hst
  simp only [smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => (hf i).2 hx hy hs ht hst

theorem abs_affine_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] ℝ) (c : ℝ) : ConvexOn ℝ univ (fun z => |T z-c|) := by
  have h := (convexOn_univ_dist c).comp_linearMap T.toLinearMap
  have hh := h.congr (g := fun z => |T z-c|) (fun z _ => by
    change dist (T z) c = |T z-c|
    exact Real.dist_eq _ _)
  simpa only [Set.preimage_univ] using hh

theorem square_affine_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] ℝ) (c : ℝ) : ConvexOn ℝ univ (fun z => (T z-c)^2) := by
  let A : E →ᵃ[ℝ] ℝ := T.toLinearMap.toAffineMap - AffineMap.const ℝ E c
  simpa [A,Function.comp_def] using
    ((show Even (2 : ℕ) by decide).convexOn_pow (𝕜 := ℝ)).comp_affineMap A

def xCoord (i : Fin n) : Point n m →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (RealVector n) (RealVector m))
def yCoord (j : Fin m) : Point n m →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (RealVector n) (RealVector m))

theorem l1_convex (a : Point n m) : ConvexOn ℝ univ (l1 a) := by
  exact (sum_convex (fun i (z : Point n m) => |z.1 i-a.1 i|)
    (fun i => abs_affine_convex (xCoord i) (a.1 i))).add
      (sum_convex (fun j (z : Point n m) => |z.2 j-a.2 j|)
        (fun j => abs_affine_convex (yCoord j) (a.2 j)))

theorem linf_convex (a : Point n m) : ConvexOn ℝ univ (linf a) := by
  change ConvexOn ℝ univ (fun z : Point n m => ‖z-a‖)
  simpa only [dist_eq_norm] using convexOn_univ_dist a

theorem squared_convex (a : Point n m) : ConvexOn ℝ univ (squared a) := by
  exact (sum_convex (fun i (z : Point n m) => (z.1 i-a.1 i)^2)
    (fun i => square_affine_convex (xCoord i) (a.1 i))).add
      (sum_convex (fun j (z : Point n m) => (z.2 j-a.2 j)^2)
        (fun j => square_affine_convex (yCoord j) (a.2 j)))

theorem linear_convex (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) : ConvexOn ℝ univ (FullLagrangian.linear d lambda mu a) := by
  unfold FullLagrangian.linear
  let T := fderiv ℝ (FullLagrangian.lagrangian d lambda mu) a
  simpa [T,Function.comp_def] using
    (T.toLinearMap.convexOn convex_univ).comp_affineMap
      (AffineMap.id ℝ (Point n m) - AffineMap.const ℝ (Point n m) a)

theorem linear_concave (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) : ConcaveOn ℝ univ (FullLagrangian.linear d lambda mu a) := by
  unfold FullLagrangian.linear
  let T := fderiv ℝ (FullLagrangian.lagrangian d lambda mu) a
  simpa [T,Function.comp_def] using
    (T.toLinearMap.concaveOn convex_univ).comp_affineMap
      (AffineMap.id ℝ (Point n m) - AffineMap.const ℝ (Point n m) a)

theorem taylor_eq_generic (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (a : Point n m) : taylor d lambda mu a =
      Chapter06.QuadraticRanking.ranking d.f (FullLagrangian.rows d)
        (FullLagrangian.weights lambda mu) a := by
  unfold taylor FullLagrangian.linear FullLagrangian.hessian Chapter06.QuadraticRanking.ranking
  rw [FullLagrangian.concatenated_eq]

theorem taylor_convex (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hf : ConvexOn ℝ univ d.f) (hg : ∀ j, ConvexOn ℝ univ (d.g j))
    (hl : ∀ j, 0 ≤ lambda j) (hm : ∀ i, 0 ≤ mu i)
    (hf2 : ContDiff ℝ 2 d.f) (hg2 : ∀ j, ContDiff ℝ 2 (d.g j)) (a : Point n m) :
    ConvexOn ℝ univ (taylor d lambda mu a) := by
  rw [taylor_eq_generic]
  exact Chapter06.QuadraticRanking.ranking_convex d.f (FullLagrangian.rows d)
    (FullLagrangian.weights lambda mu) hf (FullLagrangian.rows_convex d hg)
    (FullLagrangian.weights_nonneg lambda mu hl hm) hf2
    (FullLagrangian.rows_contDiff d hg2) a

theorem hessian_convex (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hf : ConvexOn ℝ univ d.f) (hg : ∀ j, ConvexOn ℝ univ (d.g j))
    (hl : ∀ j, 0 ≤ lambda j) (hm : ∀ i, 0 ≤ mu i)
    (hf2 : ContDiff ℝ 2 d.f) (hg2 : ∀ j, ContDiff ℝ 2 (d.g j)) (a : Point n m) :
    ConvexOn ℝ univ (FullLagrangian.hessian d lambda mu a) := by
  have h := (taylor_convex d lambda mu hf hg hl hm hf2 hg2 a).sub
    (linear_concave d lambda mu a)
  have he : FullLagrangian.hessian d lambda mu a =
      fun z => (2 : ℝ) • (taylor d lambda mu a z - FullLagrangian.linear d lambda mu a z) := by
    funext z; simp only [smul_eq_mul,taylor]; ring
  rw [he]
  exact h.smul (by norm_num)

theorem ranking_convex (d : Data n m l r) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
    (hf : ConvexOn ℝ univ d.f) (hg : ∀ j, ConvexOn ℝ univ (d.g j))
    (hl : ∀ j, 0 ≤ lambda j) (hm : ∀ i, 0 ≤ mu i)
    (hf2 : ContDiff ℝ 2 d.f) (hg2 : ∀ j, ContDiff ℝ 2 (d.g j))
    (a : Point n m) (rho : ℝ) (hrho : 0 ≤ rho) (kind : Kind) :
    ConvexOn ℝ univ (ranking d lambda mu a rho kind) := by
  cases kind with
  | l1 => exact l1_convex a
  | linf => exact linf_convex a
  | squared => exact squared_convex a
  | taylor => exact taylor_convex d lambda mu hf hg hl hm hf2 hg2 a
  | hessian => exact hessian_convex d lambda mu hf hg hl hm hf2 hg2 a
  | scaled => exact (linear_convex d lambda mu a).add ((squared_convex a).smul hrho)
  | linear => exact linear_convex d lambda mu a

end Chapter07.SevenRankings

#print axioms Chapter07.SevenRankings.l1_eq_coordinates
#print axioms Chapter07.SevenRankings.linf_le_iff
#print axioms Chapter07.SevenRankings.linf_eq_coordinates
#print axioms Chapter07.SevenRankings.ranking_at_anchor
#print axioms Chapter07.SevenRankings.ranking_continuous
#print axioms Chapter07.SevenRankings.taylor_eq_generic
#print axioms Chapter07.SevenRankings.hessian_convex
#print axioms Chapter07.SevenRankings.ranking_convex
