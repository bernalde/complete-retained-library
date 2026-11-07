module

public import Chapter04TrialHistory
public import Chapter04SlaterBall
public import Chapter04FiberGap

@[expose] public section

/-! One fixed positive near-optimal ambient ball survives every finite actual
trial history before a globally optimal polish is stored. Empty seed is
explicit: optimizer preservation at radius zero alone is insufficient. Only
the center satisfies affine/integer constraints. This is a necessary support
for finite discovery, not a master-existence or finite-return theorem. -/

noncomputable section
namespace Chapter04.CenterCut
open Chapter02

/-- An ambient ball obeying the nonlinear rows and an objective cutoff obeys
all actual normalized event rows whose stored polish is above that cutoff.
This includes zero normals and zero objective; no event validity is needed. -/
theorem eventRows_of_ambient_ball {n m l k : ℕ} (d : ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (e : TrialEvent n m) (center : Point n m) (ρ cutoff : ℝ) (hρ : 0 ≤ ρ)
    (hball : ∀ q, ‖coordinates n m q - coordinates n m center‖ ≤ ρ →
      d.objective q ≤ cutoff ∧ ∀ j, d.g j q ≤ 0)
    (hcutoff : ∀ p, e.polished = some p → cutoff ≤ d.objective p) :
    eventRows d e center ρ := by
  have hrow : ∀ (a : Point n m) j,
      d.g j a + inner ℝ (euclideanGradient (d.g j) a)
        (coordinates n m center - coordinates n m a) +
        ρ * ‖euclideanGradient (d.g j) a‖ ≤ 0 := by
    intro a j
    apply (normalized_halfspace_ball_iff (euclideanGradient (d.g j) a)
      (coordinates n m center) (coordinates n m a) (d.g j a) ρ hρ).mpr
    intro z hz
    have hq : ‖coordinates n m ((coordinates n m).symm z) -
        coordinates n m center‖ ≤ ρ := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
    have h := euclideanGradient_tangent_valid (hconv j) (hdiff j a) ((hball _ hq).2 j)
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h
  cases hp : e.polished with
  | none =>
      simp only [eventRows, hp]
      intro j _
      exact hrow e.trial j
  | some p =>
      simp only [eventRows, hp]
      refine ⟨fun j _ => hrow p j, ?_⟩
      have hobjective : -cutoff + inner ℝ (coordinates n m (d.c1, d.c2))
          (coordinates n m center - 0) +
          ρ * ‖coordinates n m (d.c1, d.c2)‖ ≤ 0 := by
        apply (normalized_halfspace_ball_iff (coordinates n m (d.c1, d.c2))
          (coordinates n m center) 0 (-cutoff) ρ hρ).mpr
        intro z hz
        have hq : ‖coordinates n m ((coordinates n m).symm z) -
            coordinates n m center‖ ≤ ρ := by
          simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
        have h := (hball _ hq).1
        rw [objective_eq_inner_coordinates] at h
        simp only [ContinuousLinearEquiv.apply_symm_apply] at h
        simp only [sub_zero]
        linarith
      rw [sub_zero, ← objective_eq_inner_coordinates] at hobjective
      have hpbound := hcutoff p hp
      linarith

/-- The same originally feasible center and strictly positive radius belong
to every finite empty-seed master before any globally optimal polish is stored.
One attained optimizer is fixed before the gap, ball and history. There is no
nonzero-objective, exact-master, radius bound or separation premise. -/
theorem source_pre_discovery_ball {n m l k : ℕ} (d : ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hfeas : (d.feasibleOn Set.univ).Nonempty) (hSlater : OAFiberSlater d) :
    ∃ (center : Point n m) (ρ : ℝ), center ∈ d.feasibleOn Set.univ ∧ 0 < ρ ∧
      ∀ H : List (TrialEvent n m),
        (∀ e ∈ H, eventValid d e) →
        (∀ e ∈ H, ∀ p, e.polished = some p →
          ¬ IsMinimizer (d.feasibleOn Set.univ) d.objective p) →
        (center, ρ) ∈ sourceMaster d [] H := by
  have hg : ∀ j, Continuous (d.g j) := fun j => (hdiff j).continuous
  obtain ⟨pStar, hmin⟩ := source_minimum_attained d hcompact hg hfeas
  obtain ⟨ε, hε, hgap⟩ := source_attained_fiber_value_gap d hg hcompact pStar hmin
  obtain ⟨center, ρ, _, hcF, hρ, hball⟩ :=
    optimizer_epsilon_slater_ball d hg hconv hSlater pStar hmin ε hε
  refine ⟨center, ρ, hcF, hρ, ?_⟩
  intro H hvalid hnot
  have hc := (source_feasible_iff d Set.univ center).mp hcF
  refine ⟨⟨hc.2.2.1, hc.2.2.2⟩, ?_, ?_⟩
  · simp
  · intro e he
    apply eventRows_of_ambient_ball d hconv hdiff e center ρ
      (d.objective pStar + ε) hρ.le hball
    intro p hp
    have hv := hvalid e he
    have hpolish : IsMinimizer (d.fixedNonlinearFiber e.trial.2) d.objective p := by
      have hb : e.trial ∈ d.nonlinearRegion ∧
          IsMinimizer (d.fixedNonlinearFiber e.trial.2) d.objective p := by
        simpa only [hp] using hv.2
      exact hb.2
    obtain ⟨y, hy, htrialY⟩ := hv.1.2
    have hpolishY : IsMinimizer (d.fixedNonlinearFiber (oaIntCast y)) d.objective p := by
      change IsMinimizer (d.fixedNonlinearFiber (fun i => (y i : ℝ))) d.objective p
      simpa only [htrialY] using hpolish
    rcases hgap y hy p hpolishY with heq | hgt
    · exfalso
      apply hnot e he p hp
      refine ⟨event_polished_feasible d e hv p hp, ?_⟩
      intro q hq
      rw [heq]
      exact hmin.2 q hq
    · exact hgt.le

end Chapter04.CenterCut
