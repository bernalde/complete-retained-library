module

public import Chapter05QuadraticControlData
public import Chapter05QuadraticAnalytic
public import Chapter05QuadraticMaster

@[expose] public section

/-! Four analytic nonvacuity controls for the source-used quadratic family.
Rank-one coordinates are the joint two-coordinate real vector, with the literal
box retained. Scalar quartics test positive-curvature infimum and empty branches.
These are static cut/master controls, not a numerical experiment or trace. -/
noncomputable section
namespace Chapter05.Quadratic.Control

theorem rank_tangent (x : Chapter02.RealVector 2) : tangent rankSquare 0 x = 0 := by
  simp [tangent, rankSquare_fderiv_zero, rankSquare]

theorem rank_curvature (x : Chapter02.RealVector 2) :
    curvature rankSquare 0 x = 2*(x 0+x 1)^2 := by
  simp only [curvature, sub_zero, rankSquare_hessian]
  ring

theorem rank_cut (α : ℝ) (x : Chapter02.RealVector 2) :
    cut rankSquare 0 α x = α * rankSquare x := by
  rw [cut, rank_tangent, rank_curvature]
  dsimp [rankSquare]
  ring

theorem rank_hessian_entries (i j : Fin 2) :
    fderiv ℝ (fderiv ℝ rankSquare) 0 (Pi.single i 1) (Pi.single j 1) = 2 := by
  rw [rankSquare_hessian]
  fin_cases i <;> fin_cases j <;> norm_num [Pi.single_apply]

theorem rank_null_direction : nullDirection ∈ rankBox ∧ nullDirection ≠ 0 ∧
    curvature rankSquare 0 nullDirection = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [nullDirection]
  · intro h
    have he := congrFun h (0 : Fin 2)
    norm_num [nullDirection] at he
  · norm_num [rank_curvature, nullDirection]

theorem rank_positive_direction : positiveDirection ∈ rankBox ∧
    curvature rankSquare 0 positiveDirection = 2 := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [positiveDirection]
  · norm_num [rank_curvature, positiveDirection]

theorem quartic_tangent (x : ℝ) : tangent Chapter05.quartic 0 x = 0 := by
  simp [tangent, quartic_fderiv_zero, Chapter05.quartic]

theorem quartic_curvature (x : ℝ) : curvature Chapter05.quartic 0 x = 2*x^2 := by
  simp only [curvature, sub_zero, quartic_hessian]
  ring

theorem quartic_cut (α x : ℝ) : cut Chapter05.quartic 0 α x = α*x^2 := by
  rw [cut, quartic_tangent, quartic_curvature]
  ring

theorem quartic_ratio (x : ℝ) (hx : x ≠ 0) :
    (Chapter05.quartic x - tangent Chapter05.quartic 0 x) /
      curvature Chapter05.quartic 0 x = (1+x^2)/2 := by
  rw [quartic_tangent, quartic_curvature, sub_zero]
  apply (div_eq_iff (by positivity : 2*x^2 ≠ 0)).2
  rw [Chapter05.quartic_remainder_factor]
  ring

theorem fourth_tangent (x : ℝ) : tangent fourth 0 x = 0 := by
  simp [tangent, fourth_fderiv_zero, fourth]

theorem fourth_curvature (x : ℝ) : curvature fourth 0 x = 0 := by
  simp only [curvature, sub_zero, fourth_hessian]

theorem fourth_cut (α x : ℝ) : cut fourth 0 α x = 0 := by
  simp [cut, fourth_tangent, fourth_curvature]

theorem rank_domain_nonempty :
    (positiveCurvatureDomain rankSquare 0 rankBox).Nonempty := by
  refine ⟨positiveDirection, rank_positive_direction.1, ?_⟩
  rw [rank_positive_direction.2]
  norm_num

theorem rank_ratioSet : ratioSet rankSquare 0 rankBox = {1/2} := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply Set.mem_singleton_iff.mpr
    have hp : 0 < 2*(x 0+x 1)^2 := by simpa [rank_curvature] using hx.2
    dsimp only
    rw [rank_tangent, rank_curvature, sub_zero]
    apply (div_eq_iff (ne_of_gt hp)).2
    dsimp [rankSquare]
    ring
  · intro hr
    have hr' : r = 1/2 := Set.mem_singleton_iff.mp hr
    subst r
    refine ⟨positiveDirection, ⟨rank_positive_direction.1, ?_⟩, ?_⟩
    · rw [rank_positive_direction.2]
      norm_num
    · norm_num [rankSquare, positiveDirection, rank_tangent, rank_curvature]

theorem rank_safeScale : safeScale rankSquare 0 rankBox = 1 := by
  rw [safeScale_of_nonempty rank_domain_nonempty, rank_ratioSet]
  norm_num

/-- Actual joint-coordinate control, invoking the source-facing analytic scale
endpoint with n=p=1, not an arbitrary supplied matrix. -/
theorem rank_analytic_control :
    safeScale rankSquare 0 rankBox = 1 ∧
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ x ∈ rankBox,
      tangent rankSquare 0 x ≤ cut rankSquare 0 α x ∧
      cut rankSquare 0 α x ≤ rankSquare x ∧
      cut rankSquare 0 α x ≤ cut rankSquare 0 1 x) ∧
    ConvexOn ℝ Set.univ (cut rankSquare 0 1) := by
  refine ⟨rank_safeScale, ?_, cut_convex rankSquare_convex rankSquare_contDiff 0 (by norm_num)⟩
  intro α hα0 hα1 x hx
  have hs : α ≤ safeScale rankSquare 0 rankBox := by
    rw [rank_safeScale]
    exact hα1
  exact (source_joint_safeScale (n := 1) (p := 1) rankSquare_convex
    rankSquare_contDiff 0 rankBox).2 α hα0 hs x hx

theorem quartic_domain : positiveCurvatureDomain Chapter05.quartic 0 scalarBox =
    {x ∈ scalarBox | x ≠ 0} := by
  ext x
  simp only [positiveCurvatureDomain, Set.mem_setOf_eq, quartic_curvature]
  constructor
  · rintro ⟨hx, hp⟩
    refine ⟨hx, ?_⟩
    intro hzero
    simp [hzero] at hp
  · rintro ⟨hx, hn⟩
    exact ⟨hx, by positivity⟩

theorem quartic_domain_nonempty :
    (positiveCurvatureDomain Chapter05.quartic 0 scalarBox).Nonempty := by
  rw [quartic_domain]
  exact ⟨1, by norm_num [scalarBox]⟩

theorem quartic_ratioSet : ratioSet Chapter05.quartic 0 scalarBox = quarticRatios := by
  rw [ratioSet, quartic_domain]
  apply Set.image_congr
  exact fun x hx => quartic_ratio x hx.2

theorem quartic_actual_inf : sInf (ratioSet Chapter05.quartic 0 scalarBox) = 1/2 := by
  rw [quartic_ratioSet, quarticRatios_inf]

theorem quartic_actual_nonattainment :
    ∀ x ∈ positiveCurvatureDomain Chapter05.quartic 0 scalarBox,
      (Chapter05.quartic x-tangent Chapter05.quartic 0 x)/curvature Chapter05.quartic 0 x ≠
        sInf (ratioSet Chapter05.quartic 0 scalarBox) := by
  intro x hx heq
  have hmem : sInf (ratioSet Chapter05.quartic 0 scalarBox) ∈
      ratioSet Chapter05.quartic 0 scalarBox := ⟨x, hx, heq⟩
  rw [quartic_ratioSet] at hmem
  exact quarticRatios_inf_not_mem hmem

theorem quartic_safeScale : safeScale Chapter05.quartic 0 scalarBox = 1 := by
  rw [safeScale_of_nonempty quartic_domain_nonempty, quartic_actual_inf]
  norm_num

theorem quartic_analytic_control (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (x : ℝ) (hx : x ∈ scalarBox) :
    tangent Chapter05.quartic 0 x ≤ cut Chapter05.quartic 0 α x ∧
    cut Chapter05.quartic 0 α x ≤ Chapter05.quartic x ∧
    cut Chapter05.quartic 0 α x ≤ cut Chapter05.quartic 0 1 x :=
  cut_bounds_of_safeScale quartic_convex quartic_contDiff 0 scalarBox hα0
    (by simpa only [quartic_safeScale] using hα1) x hx

theorem fourth_domain_empty : positiveCurvatureDomain fourth 0 scalarBox = ∅ := by
  ext x
  simp [positiveCurvatureDomain, fourth_curvature]

theorem fourth_safeScale : safeScale fourth 0 scalarBox = 1 := by
  apply safeScale_of_empty
  rw [fourth_domain_empty]
  exact Set.not_nonempty_empty

theorem fourth_analytic_control : scalarBox.Nonempty ∧
    positiveCurvatureDomain fourth 0 scalarBox = ∅ ∧
    safeScale fourth 0 scalarBox = 1 ∧
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ x ∈ scalarBox,
      tangent fourth 0 x ≤ cut fourth 0 α x ∧ cut fourth 0 α x ≤ fourth x ∧
      cut fourth 0 α x ≤ cut fourth 0 1 x := by
  refine ⟨⟨0, by norm_num [scalarBox]⟩, fourth_domain_empty, fourth_safeScale, ?_⟩
  intro α hα0 hα1 x hx
  exact cut_bounds_of_safeScale fourth_convex fourth_contDiff 0 scalarBox hα0
    (by simpa only [fourth_safeScale] using hα1) x hx

/-- A single exact quadratic objective and the same quadratic as a constraint.
The feasible set contains the null line. No Slater or algorithm hypothesis is
needed or claimed by this static master control. -/
def oneAnchorData : MasterData (Chapter02.RealVector 2) (Fin 1) (Fin 1) where
  f := rankSquare
  g := fun _ => rankSquare
  anchor := fun _ => 0
  objectiveScale := fun _ => 1
  constraintScale := fun _ _ => 1
  base := rankBox

def oneAnchorHistory : Finset (Fin 1) := {0}

theorem oneAnchor_regular : MasterRegularity oneAnchorData :=
  ⟨rankSquare_convex, rankSquare_contDiff, fun _ => rankSquare_convex,
    fun _ => rankSquare_contDiff⟩

theorem oneAnchor_safe : SafeHistory oneAnchorData oneAnchorHistory := by
  simp [SafeHistory, oneAnchorData, rank_safeScale]

theorem oneAnchor_true_iff (p : Chapter02.RealVector 2 × ℝ) :
    p ∈ trueEpigraph oneAnchorData ↔
      p.1 ∈ rankBox ∧ rankSquare p.1 ≤ 0 ∧ rankSquare p.1 ≤ p.2 := by
  simp [trueEpigraph, oneAnchorData]

theorem oneAnchor_quadratic_iff (p : Chapter02.RealVector 2 × ℝ) :
    p ∈ quadraticMaster oneAnchorData oneAnchorHistory ↔
      p.1 ∈ rankBox ∧ rankSquare p.1 ≤ p.2 ∧ rankSquare p.1 ≤ 0 := by
  simp [quadraticMaster, oneAnchorHistory, oneAnchorData, rank_cut]

theorem oneAnchor_linear_iff (p : Chapter02.RealVector 2 × ℝ) :
    p ∈ linearMaster oneAnchorData oneAnchorHistory ↔ p.1 ∈ rankBox ∧ 0 ≤ p.2 := by
  simp [linearMaster, oneAnchorHistory, oneAnchorData, rank_tangent]

theorem oneAnchor_true_minimum :
    Chapter02.IsMinimizer (trueEpigraph oneAnchorData) Prod.snd (0, 0) := by
  refine ⟨?_, ?_⟩
  · rw [oneAnchor_true_iff]
    norm_num [rankBox, rankSquare]
  · intro p hp
    have h := (oneAnchor_true_iff p).mp hp
    exact (sq_nonneg (p.1 0+p.1 1)).trans h.2.2

theorem oneAnchor_quadratic_minimum :
    Chapter02.IsMinimizer (quadraticMaster oneAnchorData oneAnchorHistory)
      Prod.snd (0, 0) := by
  refine ⟨?_, ?_⟩
  · rw [oneAnchor_quadratic_iff]
    norm_num [rankBox, rankSquare]
  · intro p hp
    have h := (oneAnchor_quadratic_iff p).mp hp
    exact (sq_nonneg (p.1 0+p.1 1)).trans h.2.1

theorem oneAnchor_linear_minimum :
    Chapter02.IsMinimizer (linearMaster oneAnchorData oneAnchorHistory)
      Prod.snd (0, 0) := by
  refine ⟨?_, ?_⟩
  · rw [oneAnchor_linear_iff]
    norm_num [rankBox]
  · intro p hp
    exact ((oneAnchor_linear_iff p).mp hp).2

/-- The quadratic master excludes a point admitted by the matched linear one. -/
theorem oneAnchor_strict_distinction :
    (positiveDirection, 0) ∈ linearMaster oneAnchorData oneAnchorHistory ∧
    (positiveDirection, 0) ∉ quadraticMaster oneAnchorData oneAnchorHistory := by
  constructor
  · rw [oneAnchor_linear_iff]
    exact ⟨rank_positive_direction.1, le_rfl⟩
  · rw [oneAnchor_quadratic_iff]
    norm_num [rankSquare, positiveDirection]

/-- The control invokes the joint-coordinate source master consumer and its
attained-minimum transfer, with all minima supplied by the explicit model. -/
theorem oneAnchor_analytic_control :
    (trueEpigraph oneAnchorData ⊆ quadraticMaster oneAnchorData oneAnchorHistory) ∧
    (quadraticMaster oneAnchorData oneAnchorHistory ⊆ linearMaster oneAnchorData oneAnchorHistory) ∧
    ((0 : Chapter02.RealVector 2), (0 : ℝ)) ∈ trueEpigraph oneAnchorData ∧
    ∃ l q, Chapter02.IsMinimizer (linearMaster oneAnchorData oneAnchorHistory) Prod.snd l ∧
      Chapter02.IsMinimizer (quadraticMaster oneAnchorData oneAnchorHistory) Prod.snd q ∧
      l.2 ≤ q.2 ∧ Chapter02.IsLowerBound (trueEpigraph oneAnchorData) Prod.snd q.2 := by
  have hi := source_joint_master_inclusions (n := 1) (p := 1) (m := 1)
    oneAnchor_regular oneAnchor_safe
  exact ⟨hi.1, hi.2, oneAnchor_true_minimum.1, (0, 0), (0, 0),
    oneAnchor_linear_minimum, oneAnchor_quadratic_minimum,
    quadratic_linear_minima_order oneAnchor_regular oneAnchor_safe
      oneAnchor_linear_minimum oneAnchor_quadratic_minimum,
    quadratic_master_lower_bound oneAnchor_regular oneAnchor_safe oneAnchor_quadratic_minimum⟩

end Chapter05.Quadratic.Control
