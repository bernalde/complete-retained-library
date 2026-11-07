module

public import Chapter02Model
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Analytic ESH root and supporting-cut construction from Chapter 2,
`convexminlpreview.tex`, Extended supporting hyperplane subsection (lines 76–104).
The source's lambda is `1-t`: `AffineMap.lineMap a b t = (1-t) • a + t • b`.
Strict feasibility, a violated trial point, finite nonempty constraints, and
actual Fréchet differentiability are explicit. No root-search termination,
existence of an interior NLP optimizer, or whole ESH convergence is asserted. -/

noncomputable section
namespace Chapter02

variable {E J : Type*}

/-- The finite maximum used by the source ESH line search. -/
def eshMaximum [Fintype J] [Nonempty J] (g : J → E → ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => g j x)

theorem eshMaximum_continuous [TopologicalSpace E] [Fintype J] [Nonempty J] {g : J → E → ℝ}
    (hg : ∀ j, Continuous (g j)) : Continuous (eshMaximum g) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun j _ => hg j)

theorem eshMaximum_le_iff [Fintype J] [Nonempty J] (g : J → E → ℝ) (x : E) (r : ℝ) :
    eshMaximum g x ≤ r ↔ ∀ j, g j x ≤ r := by
  simp [eshMaximum, Finset.sup'_le_iff]

theorem eshMaximum_attained [Fintype J] [Nonempty J] (g : J → E → ℝ) (x : E) :
    ∃ j, eshMaximum g x = g j x := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => g j x)
  exact ⟨j, hj⟩

/-- The analytic strict-feasibility premise really gives a topological interior
point of the simultaneous nonlinear feasible set. -/
theorem esh_strictFeasible_mem_interior [TopologicalSpace E] [Fintype J] [Nonempty J]
    {g : J → E → ℝ} {a : E} (hg : ∀ j, Continuous (g j)) (ha : ∀ j, g j a < 0) :
    a ∈ interior {x | ∀ j, g j x ≤ 0} := by
  obtain ⟨j, hj⟩ := eshMaximum_attained g a
  have hnegative : eshMaximum g a < 0 := by rw [hj]; exact ha j
  have hopen : IsOpen {x | eshMaximum g x < 0} :=
    isOpen_lt (eshMaximum_continuous hg) continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (hopen.mem_nhds hnegative)
    (fun x hx => (eshMaximum_le_iff g x 0).mp hx.le)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- IVT establishes an interior segment parameter with every constraint feasible
and at least one active. Convexity is unnecessary for this existence step. -/
theorem esh_boundary_exists [Fintype J] [Nonempty J] {g : J → E → ℝ} {a b : E}
    (hg : ∀ j, Continuous (g j)) (ha : ∀ j, g j a < 0) (hb : ∃ j, 0 < g j b) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      (∀ j, g j (AffineMap.lineMap a b t) ≤ 0) ∧
      ∃ j, g j (AffineMap.lineMap a b t) = 0 := by
  let F : ℝ → ℝ := fun t => eshMaximum g (AffineMap.lineMap a b t)
  have hF : Continuous F := (eshMaximum_continuous hg).comp AffineMap.lineMap_continuous
  have hFa : F 0 < 0 := by
    obtain ⟨j, hj⟩ := eshMaximum_attained g a
    simpa [F, hj] using ha j
  have hFb : 0 < F 1 := by
    obtain ⟨j, hj⟩ := hb
    have hle : g j b ≤ eshMaximum g b :=
      (eshMaximum_le_iff g b (eshMaximum g b)).mp le_rfl j
    simpa [F] using hj.trans_le hle
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hF.continuousOn (show 0 ∈ Set.Icc (F 0) (F 1) from ⟨hFa.le, hFb.le⟩)
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    subst t
    exact (ne_of_lt hFa) hzero)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
    intro heq
    subst t
    exact (ne_of_gt hFb) hzero)
  refine ⟨t, ⟨ht0, ht1⟩, (eshMaximum_le_iff _ _ _).mp hzero.le, ?_⟩
  obtain ⟨j, hj⟩ := eshMaximum_attained g (AffineMap.lineMap a b t)
  exact ⟨j, hj.symm.trans hzero⟩

/-- Strict feasibility forces every active supporting normal to be nonzero and
to strictly separate the exterior trial point. The derivative is an actual
Fréchet derivative, not an assumed subgradient or arbitrary cut oracle. -/
theorem esh_active_cut_separates {g : E → ℝ} {a b : E} {t : ℝ} {D : E →L[ℝ] ℝ}
    (hconv : ConvexOn ℝ Set.univ g)
    (hderiv : HasFDerivAt g D (AffineMap.lineMap a b t))
    (ha : g a < 0) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hz : g (AffineMap.lineMap a b t) = 0) :
    D ≠ 0 ∧
      (∀ x, g x ≤ 0 → g (AffineMap.lineMap a b t) +
        D (x - AffineMap.lineMap a b t) ≤ 0) ∧
      0 < g (AffineMap.lineMap a b t) + D (b - AffineMap.lineMap a b t) := by
  let z := AffineMap.lineMap a b t
  have hDz : D (a - z) < 0 := by
    have hsupport := tangent_underestimator hconv hderiv (b := a)
    rw [hz, zero_add] at hsupport
    exact hsupport.trans_lt ha
  have hleft : a - z = t • (a - b) := AffineMap.left_vsub_lineMap a b t
  have hright : b - z = (1 - t) • (b - a) := AffineMap.right_vsub_lineMap a b t
  have hnegative : D (a - b) < 0 := by
    rw [hleft, map_smul, smul_eq_mul] at hDz
    nlinarith [ht.1]
  have hpositive : 0 < D (b - a) := by
    have heq : D (b - a) = -D (a - b) := by rw [← map_neg, neg_sub]
    rw [heq]
    linarith
  have hDb : 0 < D (b - z) := by
    rw [hright, map_smul, smul_eq_mul]
    exact mul_pos (sub_pos.mpr ht.2) hpositive
  refine ⟨?_, ?_, ?_⟩
  · intro hD
    simp [hD] at hpositive
  · intro x hx
    exact tangent_cut_valid hconv hderiv hx
  · simpa only [hz, zero_add] using hDb

/-- A feasible point at which an active differentiable constraint has nonzero
derivative is on the topological frontier of the simultaneous feasible set. -/
theorem active_constraint_mem_frontier {g : J → E → ℝ} {z : E} {j : J}
    {D : E →L[ℝ] ℝ} (hz : ∀ k, g k z ≤ 0) (hactive : g j z = 0)
    (hderiv : HasFDerivAt (g j) D z) (hD : D ≠ 0) :
    z ∈ frontier {x | ∀ k, g k x ≤ 0} := by
  refine ⟨subset_closure hz, ?_⟩
  intro hinterior
  have hlocal : IsLocalMax (g j) z := by
    have hnhds := mem_interior_iff_mem_nhds.mp hinterior
    filter_upwards [hnhds] with x hx
    simpa only [hactive] using hx j
  exact hD (hlocal.hasFDerivAt_eq_zero hderiv)

/-- The complete analytic ESH construction: an interior segment parameter gives
a nonlinear-feasible boundary point and an actual, nonzero Fréchet tangent
supporting all feasible points while strictly excluding the violated trial.
All analytic conclusions are derived from the listed source hypotheses. -/
theorem esh_supporting_cut_exists [Fintype J] [Nonempty J] {g : J → E → ℝ} {a b : E}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (g j)) (hdiff : ∀ j, Differentiable ℝ (g j))
    (ha : ∀ j, g j a < 0) (hb : ∃ j, 0 < g j b) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      (∀ j, g j (AffineMap.lineMap a b t) ≤ 0) ∧
      AffineMap.lineMap a b t ∈ frontier {x | ∀ j, g j x ≤ 0} ∧
      ∃ j, g j (AffineMap.lineMap a b t) = 0 ∧
        fderiv ℝ (g j) (AffineMap.lineMap a b t) ≠ 0 ∧
        (∀ x, (∀ k, g k x ≤ 0) → g j (AffineMap.lineMap a b t) +
          fderiv ℝ (g j) (AffineMap.lineMap a b t) (x - AffineMap.lineMap a b t) ≤ 0) ∧
        0 < g j (AffineMap.lineMap a b t) +
          fderiv ℝ (g j) (AffineMap.lineMap a b t) (b - AffineMap.lineMap a b t) := by
  obtain ⟨t, ht, hfeas, j, hj⟩ := esh_boundary_exists (fun j => (hdiff j).continuous) ha hb
  have hderiv := (hdiff j (AffineMap.lineMap a b t)).hasFDerivAt
  obtain ⟨hne, hvalid, hsep⟩ := esh_active_cut_separates (hconv j) hderiv (ha j) ht hj
  exact ⟨t, ht, hfeas, active_constraint_mem_frontier hfeas hj hderiv hne,
    j, hj, hne, fun x hx => hvalid x (hx j), hsep⟩

/-- Source-model wiring for ESH: interpolation preserves every literal affine
row when both endpoints satisfy those rows. The generated point lies on the
nonlinear region's frontier and supplies a supporting cut for that entire
region. Integer membership is not asserted: the supporting point may have
fractional relaxed-integer coordinates, as in the source construction. -/
theorem source_esh_supporting_cut_exists {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) {a b : Point n m}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (haL : a ∈ d.linearRegion) (hbL : b ∈ d.linearRegion)
    (ha : ∀ j, d.g j a < 0) (hb : ∃ j, 0 < d.g j b) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      AffineMap.lineMap a b t ∈ d.nonlinearRegion ∩ d.linearRegion ∧
      AffineMap.lineMap a b t ∈ frontier d.nonlinearRegion ∧
      ∃ j, d.g j (AffineMap.lineMap a b t) = 0 ∧
        fderiv ℝ (d.g j) (AffineMap.lineMap a b t) ≠ 0 ∧
        (∀ x ∈ d.nonlinearRegion, d.g j (AffineMap.lineMap a b t) +
          fderiv ℝ (d.g j) (AffineMap.lineMap a b t) (x - AffineMap.lineMap a b t) ≤ 0) ∧
        0 < d.g j (AffineMap.lineMap a b t) +
          fderiv ℝ (d.g j) (AffineMap.lineMap a b t) (b - AffineMap.lineMap a b t) := by
  obtain ⟨t, ht, hfeas, hfrontier, j, hj, hne, hvalid, hsep⟩ :=
    esh_supporting_cut_exists hconv hdiff ha hb
  have hL : AffineMap.lineMap a b t ∈ d.linearRegion := by
    rw [AffineMap.lineMap_apply_module]
    exact (source_linearRegion_convex d) haL hbL (sub_nonneg.mpr ht.2.le) ht.1.le
      (sub_add_cancel 1 t)
  exact ⟨t, ht, ⟨hfeas, hL⟩, hfrontier, j, hj, hne, hvalid, hsep⟩

end Chapter02

#print axioms Chapter02.eshMaximum_continuous
#print axioms Chapter02.eshMaximum_le_iff
#print axioms Chapter02.eshMaximum_attained
#print axioms Chapter02.esh_strictFeasible_mem_interior
#print axioms Chapter02.esh_boundary_exists
#print axioms Chapter02.esh_active_cut_separates
#print axioms Chapter02.active_constraint_mem_frontier
#print axioms Chapter02.esh_supporting_cut_exists
#print axioms Chapter02.source_esh_supporting_cut_exists
