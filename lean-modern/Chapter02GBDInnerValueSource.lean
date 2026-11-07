module

public import Chapter02GBDInnerValue
public import Chapter02MultiplierExistence
public import Chapter02MultiplierExamples

@[expose] public section

/-! Source-existence wrappers for the all-row inner-value bridge.
The source minimum and strict nonlinear Slater point belong to the same affine
fiber. Affine rows need not be strictly feasible. Compact attainment is exposed
separately and retains the literal allowed integer parameter and joint base.
These are qualified repaired-cut correspondences, not a classical procedure. -/

noncomputable section
namespace Chapter02

/-- Actual fixed-fiber minimization and refined Slater construct the multipliers;
the finite inner values and equality at the anchor are conclusions. -/
theorem gbd_inner_family_of_minimum {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hd : ∀ j, HasFDerivAt (d.g j) (D j) p)
    (hmin : IsMinimizer (d.fixedNonlinearFiber p.2) d.objective p)
    (hslater : ∃ z ∈ d.fixedLinearFiber p.2, ∀ j, d.g j z < 0) :
    ∃ lambda mu, FixedNLPKKT d p D lambda mu ∧
      IsGLB (gbdInnerRange d lambda mu p.2) (d.objective p) ∧
      ∀ y : RealVector m, ∃ v : ℝ, IsGLB (gbdInnerRange d lambda mu y) v ∧
        anchoredOptimalityCut d p D lambda mu y ≤ v ∧
        ∀ x : RealVector n, (x,y) ∈ d.linearRegion →
          (∀ j, d.g j (x,y) ≤ 0) → v ≤ d.objective (x,y) := by
  obtain ⟨lambda, mu, hkkt⟩ := exists_fixedNLPKKT d p D hconv hd hmin hslater
  obtain ⟨v, hv, _, _⟩ := gbd_inner_exists_of_kkt hkkt hconv p.2
  have heq := gbd_inner_isGLB_anchor hkkt hconv hv
  refine ⟨lambda, mu, hkkt, ?_, fun y => gbd_inner_exists_of_kkt hkkt hconv y⟩
  simpa only [heq] using hv

/-- Compactness of the literal joint affine/integer base gives an actual
minimum at an allowed integer parameter; its same-fiber Slater premise derives
nonemptiness as well as multipliers. No free epigraph is assumed compact. -/
theorem source_gbd_inner_family_attained {n m l r : ℕ} (d : ModelData n m l r)
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hslater : ∃ z ∈ d.fixedLinearFiber (fun i => (y i : ℝ)), ∀ j, d.g j z < 0) :
    ∃ p lambda mu, p.2 = (fun i => (y i : ℝ)) ∧
      IsMinimizer (d.fixedNonlinearFiber (fun i => (y i : ℝ))) d.objective p ∧
      FixedNLPKKT d p (fun j => fderiv ℝ (d.g j) p) lambda mu ∧
      IsGLB (gbdInnerRange d lambda mu (fun i => (y i : ℝ))) (d.objective p) ∧
      ∀ z : RealVector m, ∃ v : ℝ, IsGLB (gbdInnerRange d lambda mu z) v ∧
        anchoredOptimalityCut d p (fun j => fderiv ℝ (d.g j) p) lambda mu z ≤ v ∧
        ∀ x : RealVector n, (x,z) ∈ d.linearRegion →
          (∀ j, d.g j (x,z) ≤ 0) → v ≤ d.objective (x,z) := by
  obtain ⟨p, lambda, mu, hpy, hmin, hkkt⟩ :=
    source_fixedNLP_KKT_attained d y hy hbase hconv hdiff hslater
  obtain ⟨v, hv, _, _⟩ := gbd_inner_exists_of_kkt hkkt hconv p.2
  have heq := gbd_inner_isGLB_anchor hkkt hconv hv
  refine ⟨p, lambda, mu, hpy, hmin, hkkt, ?_,
    fun z => gbd_inner_exists_of_kkt hkkt hconv z⟩
  simpa only [heq, hpy] using hv

end Chapter02

namespace Chapter02GBDInnerSourceExamples
open Chapter02 Chapter02MultiplierExamples

/-- A nonlinear unit disk pinned to x=0 by two opposed affine rows has no
strict affine point. Its actual minimum and nonlinear Slater point nonetheless
produce genuine all-row inner infima -1 through the source wrapper. -/
theorem pinnedDisk_source_inner_with_no_strict_affine :
    (¬ ∃ p : Point 2 0, ∀ row,
      LinearForm (pinnedDisk.A row) (pinnedDisk.B row) p < pinnedDisk.rhs row) ∧
    ∃ lambda mu, ∀ y : RealVector 0,
      IsGLB (gbdInnerRange pinnedDisk lambda mu y) (-1) := by
  refine ⟨pinnedDisk_no_strict_affine, ?_⟩
  obtain ⟨lambda, mu, _, hv, _⟩ := gbd_inner_family_of_minimum pinnedDisk
    (pt2 0 (-1)) (fun _ => -((2 : ℝ) • diskCoord 1)) pinnedDisk_convex
    pinnedDisk_derivative pinnedDisk_minimum pinnedDisk_slater
  refine ⟨lambda, mu, fun y => ?_⟩
  have hy : y = (pt2 0 (-1)).2 := Subsingleton.elim _ _
  rw [hy]
  convert hv using 1
  norm_num [ModelData.objective, pinnedDisk, LinearForm, pt2, Fin.sum_univ_succ]

end Chapter02GBDInnerSourceExamples

#print axioms Chapter02.gbd_inner_family_of_minimum
#print axioms Chapter02.source_gbd_inner_family_attained
#print axioms Chapter02GBDInnerSourceExamples.pinnedDisk_source_inner_with_no_strict_affine
