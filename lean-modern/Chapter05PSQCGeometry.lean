module

public import Chapter05PSQCAnalytic
public import Chapter02PSCAttainment

@[expose] public section

/-! Geometry of the literal structured quadratic PSC row.
The Hessian is the actual frozen derivative of the restricted Lagrangian.
The difference from the accepted quadratic tangent is explicitly affine;
no subtraction rule for arbitrary convex functions is used. Ambient convexity
does not assert convexity of the retained integer set or master domain. -/
noncomputable section
open Set
open scoped BigOperators
open Chapter02 Chapter05.Quadratic

namespace Chapter05.PSQC
variable {p q m l s nw nv : ℕ}

/-- The literal nonlinear-coordinate projection from retained coordinates. -/
def vProjection : PSCCoordinates p q m →L[ℝ] RealVector q :=
  (ContinuousLinearMap.snd ℝ (RealVector p) (RealVector q)).comp
    (ContinuousLinearMap.fst ℝ (RealVector p × RealVector q) (RealVector m))

/-- Linear part of the unchanged PSC row, including free w/y dependence. -/
def rowLinear (d : PSCData p q m l s nw nv) (e : PSCAnchor d) :
    PSCCoordinates p q m →L[ℝ] ℝ :=
  (∑ j, e.lambda j • ((d.C j).comp (ContinuousLinearMap.snd ℝ _ _) +
    (d.D j).comp ((ContinuousLinearMap.fst ℝ _ _).comp
      (ContinuousLinearMap.fst ℝ _ _)))) -
  ∑ i, e.mu i • (d.G i).comp vProjection

def rowAffineMap (d : PSCData p q m l s nw nv) (e : PSCAnchor d) :
    PSCCoordinates p q m →ᵃ[ℝ] ℝ :=
  (rowLinear d e).toLinearMap.toAffineMap +
    AffineMap.const ℝ _ (d.r e.v + (∑ j, e.lambda j * d.t j e.v) +
      ∑ i, e.mu i * d.G i e.v)

@[simp] theorem rowAffineMap_apply (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (z : PSCCoordinates p q m) : rowAffineMap d e z = pscRow d e z.1.1 z.1.2 z.2 := by
  simp [rowAffineMap, rowLinear, vProjection, pscRow, PSCData.nonlinear,
    map_sub, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Frozen tangent, transported by the actual v projection, as an affine map. -/
def tangentAffineMap (d : PSCData p q m l s nw nv) (e : PSCAnchor d) :
    PSCCoordinates p q m →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ _ (lagrangian d e e.v) +
    ((fderiv ℝ (lagrangian d e) e.v).comp vProjection).toLinearMap.toAffineMap -
    AffineMap.const ℝ _ (fderiv ℝ (lagrangian d e) e.v e.v)

@[simp] theorem tangentAffineMap_apply (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (z : PSCCoordinates p q m) :
    tangentAffineMap d e z = tangent (lagrangian d e) e.v z.1.2 := by
  simp [tangentAffineMap, vProjection, tangent, map_sub]
  ring

/-- This difference is affine by construction, independently of convexity. -/
def affineCorrection (d : PSCData p q m l s nw nv) (e : PSCAnchor d) :
    PSCCoordinates p q m →ᵃ[ℝ] ℝ := rowAffineMap d e - tangentAffineMap d e

theorem row_eq_cut_add_affine (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (alpha : ℝ) (z : PSCCoordinates p q m) :
    psqcRow d e alpha z.1.1 z.1.2 z.2 =
      cut (lagrangian d e) e.v alpha z.1.2 + affineCorrection d e z := by
  simp [affineCorrection, psqcRow, cut]
  ring

/-- The actual frozen bilinear Hessian is continuous even without a regularity
assumption on the underlying scalar function. -/
theorem row_continuous (d : PSCData p q m l s nw nv) (e : PSCAnchor d) (alpha : ℝ) :
    Continuous (fun z : PSCCoordinates p q m => psqcRow d e alpha z.1.1 z.1.2 z.2) := by
  unfold psqcRow
  apply Continuous.add
  · unfold pscRow PSCData.nonlinear
    apply Continuous.sub
    · apply continuous_const.add
      apply continuous_finset_sum
      intro j _
      apply continuous_const.mul
      exact (((d.C j).continuous.comp continuous_snd).add
        ((d.D j).continuous.comp (continuous_fst.comp continuous_fst))).add continuous_const
    · apply continuous_finset_sum
      intro i _
      exact continuous_const.mul ((d.G i).continuous.comp
        ((continuous_snd.comp continuous_fst).sub continuous_const))
  · apply continuous_const.mul
    unfold curvature
    have hv : Continuous (fun z : PSCCoordinates p q m => z.1.2 - e.v) :=
      (continuous_snd.comp continuous_fst).sub continuous_const
    exact (continuous_const.clm_apply hv).clm_apply hv

theorem row_convex (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (hconv : ConvexOn ℝ univ (lagrangian d e)) (hC2 : ContDiff ℝ 2 (lagrangian d e))
    {alpha : ℝ} (hscale : 0 ≤ alpha) :
    ConvexOn ℝ univ
      (fun z : PSCCoordinates p q m => psqcRow d e alpha z.1.1 z.1.2 z.2) := by
  have hquad : ConvexOn ℝ univ
      (fun z : PSCCoordinates p q m => cut (lagrangian d e) e.v alpha z.1.2) := by
    simpa [vProjection, Function.comp_def] using
      (cut_convex hconv hC2 e.v hscale).comp_affineMap
        (vProjection (p := p) (q := q) (m := m)).toLinearMap.toAffineMap
  have haff : ConvexOn ℝ univ (fun z => affineCorrection d e z) := by
    simpa [Function.comp_def] using
      (convexOn_id (𝕜 := ℝ) (s := (univ : Set ℝ)) convex_univ).comp_affineMap
        (affineCorrection d e)
  have hsum := hquad.add haff
  convert hsum using 1
  funext z
  exact row_eq_cut_add_affine d e alpha z

theorem fullCut_convex (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (hconv : ConvexOn ℝ univ (lagrangian d e)) (hC2 : ContDiff ℝ 2 (lagrangian d e))
    {alpha : ℝ} (hscale : 0 ≤ alpha) :
    ConvexOn ℝ univ
      (fun z : PSCCoordinates p q m => fullCut d e alpha z.1.1 z.1.2 z.2) := by
  let offset : PSCCoordinates p q m →L[ℝ] ℝ :=
    d.a.comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)) +
      d.c.comp (ContinuousLinearMap.snd ℝ _ _)
  have hoff : ConvexOn ℝ univ (fun z : PSCCoordinates p q m => d.a z.1.1 + d.c z.2) := by
    have h := (convexOn_id (𝕜 := ℝ) (s := (univ : Set ℝ)) convex_univ).comp_affineMap
      offset.toLinearMap.toAffineMap
    exact h.congr (fun _ _ => rfl)
  exact (hoff.add (row_convex d e hconv hC2 hscale)).congr (fun _ _ => rfl)

end Chapter05.PSQC
