module

public import Chapter02OAHistory
public import Chapter04
public import Chapter04Euclidean

@[expose] public section

/-! The corrected Chapter4 Slater-ball lemma. The objective is the model's
`c1 · x + c2 · y`, repairing the swapped coordinates in the displayed source
set. The center obeys all original constraints; the ambient ball is required
to obey only the nonlinear rows and the epsilon objective cutoff. -/

noncomputable section
namespace Chapter04.CenterCut
open Chapter02

/-- Same-fiber interpolation gives an original feasible center with strict
nonlinear rows and a strict objective cutoff relative to a fixed optimizer. -/
theorem optimizer_strict_center {n m l k : ℕ} (d : ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hSlater : OAFiberSlater d) (pStar : Point n m)
    (hmin : IsMinimizer (d.feasibleOn Set.univ) d.objective pStar)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ center : Point n m, center.2 = pStar.2 ∧
      center ∈ d.feasibleOn Set.univ ∧
      d.objective center < d.objective pStar + ε ∧ ∀ j, d.g j center < 0 := by
  obtain ⟨_, hpG, hpL, y, hy, hpY⟩ := (source_feasible_iff d Set.univ pStar).mp hmin.1
  have hpY' : pStar.2 = oaIntCast y := hpY
  have hpFiber : pStar ∈ d.fixedNonlinearFiber (oaIntCast y) :=
    (mem_fixedNonlinearFiber d _ _).mpr ⟨hpL, hpY', hpG⟩
  obtain ⟨z, hzFiber, hzG⟩ := hSlater y hy ⟨pStar, hpFiber⟩
  obtain ⟨hzL, hzY⟩ := (mem_fixedLinearFiber d _ _).mp hzFiber
  by_cases hgap : d.objective z - d.objective pStar < ε
  · refine ⟨z, hzY.trans hpY'.symm, ?_, by linarith, hzG⟩
    exact (source_feasible_iff d Set.univ z).mpr
      ⟨Set.mem_univ _, fun j => (hzG j).le, hzL, y, hy, hzY⟩
  · let a : ℝ := 1 - ε / (2 * (d.objective z - d.objective pStar))
    obtain ⟨ha, ha1, hstep⟩ :=
      Chapter04.epsilon_interpolation ε (d.objective z - d.objective pStar)
        hε (le_of_not_gt hgap)
    change 0 ≤ a at ha
    change a < 1 at ha1
    change (1 - a) * (d.objective z - d.objective pStar) = ε / 2 at hstep
    have h1a : 0 ≤ 1 - a := sub_nonneg.mpr ha1.le
    have hsum : a + (1 - a) = 1 := by ring
    let center : Point n m := (a • pStar.1 + (1 - a) • z.1, oaIntCast y)
    have hpEq : (pStar.1, oaIntCast y) = pStar := Prod.ext rfl hpY'.symm
    have hzEq : (z.1, oaIntCast y) = z := Prod.ext rfl hzY.symm
    have hmix : center = a • pStar + (1 - a) • z := by
      dsimp only [center]
      rw [fiber_mix _ _ _ _ _ hsum, hpEq, hzEq]
    have hcG : ∀ j, d.g j center < 0 := by
      intro j
      apply Chapter04.strict_interpolation a (d.g j pStar) (d.g j z)
        (d.g j center) ha ha1 (hpG j) (hzG j)
      rw [hmix]
      exact (hconv j).2 (Set.mem_univ _) (Set.mem_univ _) ha h1a hsum
    have hcL : center ∈ d.linearRegion := by
      rw [hmix]
      exact source_linearRegion_convex d hpL hzL ha h1a hsum
    have hcObj : d.objective center = d.objective pStar + ε / 2 := by
      change LinearForm d.c1 d.c2 center = _
      rw [hmix, linearForm_affine]
      change a * d.objective pStar + (1 - a) * d.objective z = _
      nlinarith [hstep]
    refine ⟨center, hpY'.symm, ?_, ?_, hcG⟩
    · exact (source_feasible_iff d Set.univ center).mpr
        ⟨Set.mem_univ _, fun j => (hcG j).le, hcL, y, hy, rfl⟩
    · rw [hcObj]
      linarith

/-- A fixed actual optimizer determines a same-integer feasible center for
every positive epsilon. The closed ball is measured in the full concatenated
Euclidean space; only its center is required to satisfy affine/integer rows. -/
theorem optimizer_epsilon_slater_ball {n m l k : ℕ} (d : ModelData n m l k)
    (hg : ∀ j, Continuous (d.g j))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hSlater : OAFiberSlater d) (pStar : Point n m)
    (hmin : IsMinimizer (d.feasibleOn Set.univ) d.objective pStar)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ center radius, center.2 = pStar.2 ∧
      center ∈ d.feasibleOn Set.univ ∧ 0 < radius ∧
      ∀ q, ‖coordinates n m q - coordinates n m center‖ ≤ radius →
        d.objective q ≤ d.objective pStar + ε ∧ ∀ j, d.g j q ≤ 0 := by
  obtain ⟨center, hcY, hcF, hcObj, hcG⟩ :=
    optimizer_strict_center d hconv hSlater pStar hmin ε hε
  let rows : Option (Fin l) → EuclideanPoint n m → ℝ
    | none => fun u => d.objective ((coordinates n m).symm u) - (d.objective pStar + ε)
    | some j => fun u => d.g j ((coordinates n m).symm u)
  have hrows : ∀ j, Continuous (rows j) := by
    intro j
    cases j with
    | none => exact ((linearForm_continuous d.c1 d.c2).comp
        (coordinates n m).symm.continuous).sub continuous_const
    | some j => exact (hg j).comp (coordinates n m).symm.continuous
  have hstrict : ∀ j, rows j (coordinates n m center) < 0 := by
    intro j
    cases j with
    | none => simpa only [rows, ContinuousLinearEquiv.symm_apply_apply] using sub_neg.mpr hcObj
    | some j => simpa only [rows, ContinuousLinearEquiv.symm_apply_apply] using hcG j
  have hinterior := esh_strictFeasible_mem_interior hrows hstrict
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hinterior)
  refine ⟨center, δ / 2, hcY, hcF, half_pos hδ, ?_⟩
  intro q hq
  have hmem : coordinates n m q ∈ Metric.ball (coordinates n m center) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hq.trans_lt (half_lt_self hδ)
  have hall := hball hmem
  constructor
  · have h := hall none
    change d.objective ((coordinates n m).symm (coordinates n m q)) -
      (d.objective pStar + ε) ≤ 0 at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using sub_nonpos.mp h
  · intro j
    have h := hall (some j)
    simpa only [rows, ContinuousLinearEquiv.symm_apply_apply] using h

/-- Corrected full source wrapper: the original feasible problem attains a
single optimum, fixed before quantifying over epsilon. Compactness is imposed
on the source mixed linear base and full feasibility is explicitly nonempty. -/
theorem source_epsilon_slater_ball {n m l k : ℕ} (d : ModelData n m l k)
    (hg : ∀ j, Continuous (d.g j))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hne : (d.feasibleOn Set.univ).Nonempty) (hSlater : OAFiberSlater d) :
    ∃ pStar, IsMinimizer (d.feasibleOn Set.univ) d.objective pStar ∧
      ∀ ε, 0 < ε → ∃ center radius, center ∈ d.feasibleOn Set.univ ∧
        0 < radius ∧ ∀ q, ‖coordinates n m q - coordinates n m center‖ ≤ radius →
          d.objective q ≤ d.objective pStar + ε ∧ ∀ j, d.g j q ≤ 0 := by
  obtain ⟨pStar, hmin⟩ := source_minimum_attained d hcompact hg hne
  refine ⟨pStar, hmin, ?_⟩
  intro ε hε
  obtain ⟨center, radius, _, hcF, hr, hball⟩ :=
    optimizer_epsilon_slater_ball d hg hconv hSlater pStar hmin ε hε
  exact ⟨center, radius, hcF, hr, hball⟩

end Chapter04.CenterCut
