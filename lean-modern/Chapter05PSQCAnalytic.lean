module

public import Chapter02PSCOrder
public import Chapter05QuadraticScale
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! The literal restricted Lagrangian for the qualified separable PSC model.
Only this derivative function fixes w/y at the anchor; the master row retains
free w/y. Global regularity is explicit and no cut-validity oracle is assumed. -/
noncomputable section
open Set
open scoped BigOperators
open Chapter02
namespace Chapter05.PSQC
variable {p q m l s nw nv : ℕ}

def lagrangian (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (v : RealVector q) : ℝ :=
  d.objective e.w v e.y +
    (∑ j, e.lambda j * d.nonlinear j e.w v e.y) +
    ∑ i, e.mu i * d.coupling i e.w v e.y

def remainder (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (v : RealVector q) : ℝ :=
  lagrangian d e v - lagrangian d e e.v -
    fderiv ℝ (lagrangian d e) e.v (v-e.v)

def psqcRow (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (α : ℝ) (w : RealVector p) (v : RealVector q) (y : RealVector m) : ℝ :=
  pscRow d e w v y + (α/2) * Quadratic.curvature (lagrangian d e) e.v v

def fullCut (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (α : ℝ) (w : RealVector p) (v : RealVector q) (y : RealVector m) : ℝ :=
  d.a w + d.c y + psqcRow d e α w v y

theorem lagrangian_hasFDerivAt (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e) :
    HasFDerivAt (lagrangian d e)
      (e.Dr + (∑ j, e.lambda j • e.Dt j) + ∑ i, e.mu i • d.G i) e.v := by
  have ho : HasFDerivAt (fun v => d.objective e.w v e.y) e.Dr e.v :=
    (hk.derivative_r.const_add (d.a e.w)).add_const (d.c e.y)
  have hn (j : Fin l) : HasFDerivAt (fun v => d.nonlinear j e.w v e.y)
      (e.Dt j) e.v :=
    (hk.derivative_t j).const_add (d.C j e.y + d.D j e.w)
  have hc (i : Fin s) : HasFDerivAt (fun v => d.coupling i e.w v e.y)
      (d.G i) e.v :=
    ((d.G i).hasFDerivAt.const_add (d.E i e.y + d.F i e.w)).sub_const (d.b i)
  unfold lagrangian
  exact (ho.fun_add (HasFDerivAt.fun_sum fun j _ => (hn j).const_mul (e.lambda j))).fun_add
    (HasFDerivAt.fun_sum fun i _ => (hc i).const_mul (e.mu i))

theorem lagrangian_fderiv (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e) :
    fderiv ℝ (lagrangian d e) e.v =
      e.Dr + (∑ j, e.lambda j • e.Dt j) + ∑ i, e.mu i • d.G i :=
  (lagrangian_hasFDerivAt d e hk).fderiv

theorem lagrangian_contDiff (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hr : ContDiff ℝ 2 d.r)
    (ht : ∀ j, ContDiff ℝ 2 (d.t j)) : ContDiff ℝ 2 (lagrangian d e) := by
  have ho : ContDiff ℝ 2 (fun v => d.objective e.w v e.y) :=
    (contDiff_const.add hr).add contDiff_const
  have hn (j : Fin l) : ContDiff ℝ 2 (fun v => d.nonlinear j e.w v e.y) :=
    contDiff_const.add (ht j)
  have hc (i : Fin s) : ContDiff ℝ 2 (fun v => d.coupling i e.w v e.y) :=
    (contDiff_const.add (d.G i).contDiff).sub contDiff_const
  exact (ho.add (ContDiff.sum fun j _ => contDiff_const.mul (hn j))).add
    (ContDiff.sum fun i _ => contDiff_const.mul (hc i))

theorem lagrangian_convex (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j)) :
    ConvexOn ℝ univ (lagrangian d e) := by
  have ho : ConvexOn ℝ univ (fun v => d.objective e.w v e.y) :=
    ((convexOn_const (d.a e.w) convex_univ).add hr).add_const (d.c e.y)
  have hn (j : Fin l) : ConvexOn ℝ univ
      (fun v => e.lambda j * d.nonlinear j e.w v e.y) := by
    have hh := ((convexOn_const (d.C j e.y + d.D j e.w) convex_univ).add (ht j)).smul
      (hk.lambda_nonneg j)
    exact hh.congr (fun _ _ => rfl)
  have hc (i : Fin s) : ConvexOn ℝ univ
      (fun v => e.mu i * d.coupling i e.w v e.y) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    apply le_of_eq
    simp only [PSCData.coupling, map_add, map_smul, smul_eq_mul]
    rw [show b = 1-a by linarith]
    ring
  have hns : ConvexOn ℝ univ
      (fun v => ∑ j, e.lambda j * d.nonlinear j e.w v e.y) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hn j).2 hx hy ha hb hab)
    simpa only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] using hh
  have hcs : ConvexOn ℝ univ
      (fun v => ∑ i, e.mu i * d.coupling i e.w v e.y) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hc i).2 hx hy ha hb hab)
    simpa only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] using hh
  exact (ho.add hns).add hcs

end Chapter05.PSQC
