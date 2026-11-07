module

public import Chapter02KKTExamples
public import Chapter02MultiplierExistence
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Edge controls for multiplier existence. Original accepted examples are
imported unchanged. Global nonlinear strictness is separated from strictness
on the chosen fiber, and an unbounded source fiber has no attained restoration
minimum despite globally smooth convex nonlinear data. -/
noncomputable section
open Chapter02 Chapter02Examples Chapter02KKTExamples
namespace Chapter02MultiplierEdgeExamples

/-- A strict point elsewhere in continuous L cannot supply the missing
fiberwise Slater hypothesis at y=0. The accepted universal no-KKT witness is
reused at identical bytes. -/
theorem global_strict_point_does_not_give_fiber_slater :
    (∃ z ∈ zeroMarginModel.linearRegion, ∀ j, zeroMarginModel.g j z < 0) ∧
    (¬ ∃ z ∈ zeroMarginModel.fixedLinearFiber (pt 0 0).2,
      ∀ j, zeroMarginModel.g j z < 0) ∧
    (¬ ∃ (D : Fin 1 → Point 1 1 →L[ℝ] ℝ) (lambda : Fin 1 → ℝ) (mu : Fin 2 → ℝ),
      FixedNLPKKT zeroMarginModel (pt 0 0) D lambda mu) := by
  refine ⟨?_, ?_, zeroMargin_no_kkt⟩
  · refine ⟨pt 0 1, (zeroMargin_linear_iff _).mpr (by norm_num [pt]), ?_⟩
    intro j
    norm_num [zeroMarginModel, pt]
  · rintro ⟨z, hz, hg⟩
    have hy : z.2 0 = 0 := by simpa [pt] using congrFun hz.2 0
    have hg0 := hg 0
    change (z.1 0)^2 - z.2 0 < 0 at hg0
    rw [hy] at hg0
    nlinarith [sq_nonneg (z.1 0)]

def expModel : ModelData 1 1 1 1 where
  g := fun _ p => Real.exp (-p.1 0)
  A := fun _ _ => -1
  B := fun _ _ => 0
  rhs := fun _ => 0
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0

theorem exp_linear_iff (p : Point 1 1) :
    p ∈ expModel.linearRegion ↔ 0 ≤ p.1 0 := by
  simp [ModelData.linearRegion, expModel, LinearForm, Fin.sum_univ_one]

theorem exp_rows_convex : ∀ j, ConvexOn ℝ Set.univ (expModel.g j) := by
  intro j
  simpa [expModel, coordX, Function.comp_def] using
    convexOn_exp.comp_linearMap (-coordX).toLinearMap

theorem exp_rows_smooth : ∀ j, ContDiff ℝ 1 (expModel.g j) := by
  intro j
  exact Real.contDiff_exp.comp (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).neg)

theorem exp_rows_positive : ∀ p j, 0 < expModel.g j p := by
  intro p j
  exact Real.exp_pos _

theorem exp_fixed_fiber_nonempty : (expModel.fixedLinearFiber (pt 0 0).2).Nonempty :=
  ⟨pt 0 0, ⟨(exp_linear_iff _).mpr le_rfl, rfl⟩⟩

/-- Every proposed attained restoration point has a better feasible point at
x+1. No optimizer or totalized real infimum is assumed. -/
theorem exp_restoration_no_minimizer :
    ¬ ∃ q, IsMinimizer (RestorationPairs (expModel.fixedLinearFiber (pt 0 0).2)
      expModel.g) Prod.snd q := by
  rintro ⟨q, hq, hmin⟩
  let z := pt (q.1.1 0 + 1) 0
  have hz : z ∈ expModel.fixedLinearFiber (pt 0 0).2 := by
    refine ⟨(exp_linear_iff _).mpr ?_, rfl⟩
    have hx := (exp_linear_iff _).mp hq.1.1
    change 0 ≤ q.1.1 0 + 1
    linarith
  have hzpair : (z, Real.exp (-(q.1.1 0 + 1))) ∈
      RestorationPairs (expModel.fixedLinearFiber (pt 0 0).2) expModel.g :=
    ⟨hz, fun _ => le_rfl⟩
  have hlt : Real.exp (-(q.1.1 0 + 1)) < Real.exp (-q.1.1 0) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hs := hq.2 (0 : Fin 1)
  change Real.exp (-q.1.1 0) ≤ q.2 at hs
  exact (not_le_of_gt (hlt.trans_le hs)) (hmin _ hzpair)

theorem exp_source_base_not_compact :
    ¬ IsCompact (expModel.linearRegion ∩ IntegerCylinder (n := 1) expModel.lo expModel.hi) := by
  intro hcompact
  apply exp_restoration_no_minimizer
  have hfcompact := source_fixedLinearFiber_compact expModel (fun _ => (0 : ℤ))
    (by intro i; norm_num [IntegerBox, expModel]) hcompact
  have hfcompact' : IsCompact (expModel.fixedLinearFiber (pt 0 0).2) := by
    simpa [pt] using hfcompact
  exact restorationPairs_minimum_attained hfcompact' exp_fixed_fiber_nonempty
    (fun j => (exp_rows_smooth j).continuous)

/-- Zero is the greatest lower bound of attainable slack values here, but is
never attained. This records the finite limit without a totalized sInf. -/
theorem exp_arbitrarily_small_positive_slack (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ q ∈ RestorationPairs (expModel.fixedLinearFiber (pt 0 0).2) expModel.g,
      0 < q.2 ∧ q.2 < epsilon := by
  let x : ℝ := max 0 (-Real.log epsilon) + 1
  have hx0 : 0 ≤ x := by dsimp [x]; linarith [le_max_left (0 : ℝ) (-Real.log epsilon)]
  have hxlog : -x < Real.log epsilon := by
    dsimp [x]
    linarith [le_max_right (0 : ℝ) (-Real.log epsilon)]
  refine ⟨(pt x 0, Real.exp (-x)), ?_, Real.exp_pos _, ?_⟩
  · exact ⟨⟨(exp_linear_iff _).mpr hx0, rfl⟩, fun _ => le_rfl⟩
  · calc
      Real.exp (-x) < Real.exp (Real.log epsilon) := Real.exp_lt_exp.mpr hxlog
      _ = epsilon := Real.exp_log he

theorem exp_attainment_ablation :
    (∀ j, ConvexOn ℝ Set.univ (expModel.g j)) ∧
    (∀ j, ContDiff ℝ 1 (expModel.g j)) ∧
    (expModel.fixedLinearFiber (pt 0 0).2).Nonempty ∧
    (∀ q ∈ RestorationPairs (expModel.fixedLinearFiber (pt 0 0).2) expModel.g, 0 < q.2) ∧
    (∀ epsilon > (0 : ℝ),
      ∃ q ∈ RestorationPairs (expModel.fixedLinearFiber (pt 0 0).2) expModel.g,
        0 < q.2 ∧ q.2 < epsilon) ∧
    ¬ ∃ q, IsMinimizer (RestorationPairs (expModel.fixedLinearFiber (pt 0 0).2)
      expModel.g) Prod.snd q := by
  refine ⟨exp_rows_convex, exp_rows_smooth, exp_fixed_fiber_nonempty, ?_,
    exp_arbitrarily_small_positive_slack, exp_restoration_no_minimizer⟩
  intro q hq
  exact (exp_rows_positive q.1 0).trans_le (hq.2 0)

/-- A designated nonlinear row can have zero margin without strict feasibility,
yet admit multipliers. The original objective is identically zero. -/
def zeroSuccessModel : ModelData 1 1 1 1 :=
  { expModel with g := fun _ p => p.1 0 }

theorem zeroSuccess_convex : ∀ j, ConvexOn ℝ Set.univ (zeroSuccessModel.g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t _ _ _
  simp [zeroSuccessModel, smul_eq_mul]

theorem zeroSuccess_derivative : ∀ j,
    HasFDerivAt (zeroSuccessModel.g j) coordX (pt 0 0) := by
  intro j
  exact coordX.hasFDerivAt

theorem zeroSuccess_restoration_minimum :
    IsMinimizer (RestorationPairs (zeroSuccessModel.fixedLinearFiber (pt 0 0).2)
      zeroSuccessModel.g) Prod.snd (pt 0 0, 0) := by
  refine ⟨⟨⟨(exp_linear_iff _).mpr le_rfl, rfl⟩, fun _ => le_rfl⟩, ?_⟩
  intro q hq
  have hx := (exp_linear_iff _).mp hq.1.1
  exact hx.trans (hq.2 0)

theorem zeroSuccess_no_fiber_slater :
    ¬ ∃ p ∈ zeroSuccessModel.fixedLinearFiber (pt 0 0).2,
      ∀ j, zeroSuccessModel.g j p < 0 := by
  rintro ⟨p, hp, hg⟩
  exact (not_lt_of_ge ((exp_linear_iff p).mp hp.1)) (hg 0)

def emptyNonlinearModel : ModelData 1 1 0 1 where
  g := Fin.elim0
  A := fun _ _ => -1
  B := fun _ _ => 0
  rhs := fun _ => 0
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0

theorem emptyNonlinear_minimum :
    IsMinimizer (emptyNonlinearModel.fixedNonlinearFiber (pt 0 0).2)
      emptyNonlinearModel.objective (pt 0 0) := by
  refine ⟨⟨⟨(exp_linear_iff _).mpr le_rfl, rfl⟩, fun j => Fin.elim0 j⟩, ?_⟩
  intro p hp
  have hx := (exp_linear_iff _).mp hp.1.1
  simpa [emptyNonlinearModel, ModelData.objective, LinearForm, pt, Fin.sum_univ_one] using hx

theorem emptyNonlinear_slater :
    ∃ p ∈ emptyNonlinearModel.fixedLinearFiber (pt 0 0).2,
      ∀ j, emptyNonlinearModel.g j p < 0 :=
  ⟨pt 0 0, ⟨(exp_linear_iff _).mpr le_rfl, rfl⟩, fun j => Fin.elim0 j⟩

theorem emptyNonlinear_restoration_no_minimum :
    ¬ ∃ q, IsMinimizer (RestorationPairs (emptyNonlinearModel.fixedLinearFiber (pt 0 0).2)
      emptyNonlinearModel.g) Prod.snd q :=
  restorationPairs_no_minimizer_empty_rows _ _

def zeroDimensionModel : ModelData 0 0 1 0 where
  g := fun _ _ => 1
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0

theorem zeroDimension_restoration_minimum :
    IsMinimizer (RestorationPairs (zeroDimensionModel.fixedLinearFiber (0 : RealVector 0))
      zeroDimensionModel.g) Prod.snd ((0 : Point 0 0), 1) := by
  refine ⟨⟨⟨(fun row => Fin.elim0 row), rfl⟩, fun _ => le_rfl⟩, ?_⟩
  intro q hq
  exact hq.2 0

theorem zeroMargin_restoration_minimum :
    IsMinimizer (RestorationPairs (zeroMarginModel.fixedLinearFiber (pt 0 0).2)
      zeroMarginModel.g) Prod.snd (pt 0 0, 0) := by
  refine ⟨⟨⟨(zeroMargin_linear_iff _).mpr (by norm_num [pt]), rfl⟩,
    fun _ => by norm_num [zeroMarginModel, pt]⟩, ?_⟩
  intro q hq
  have hy : q.1.2 0 = 0 := by simpa [pt] using congrFun hq.1.2 0
  have hr := hq.2 (0 : Fin 1)
  change (q.1.1 0)^2 - q.1.2 0 ≤ q.2 at hr
  rw [hy] at hr
  change 0 ≤ q.2
  nlinarith [sq_nonneg (q.1.1 0)]

def noAffineModel : ModelData 1 1 1 0 where
  g := fun _ p => (p.1 0)^2 - 1
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0

theorem noAffine_convex : ∀ j, ConvexOn ℝ Set.univ (noAffineModel.g j) := by
  intro j
  simpa [noAffineModel, sample] using sample_convex (0 : Fin 2)

theorem noAffine_derivative : ∀ j,
    HasFDerivAt (noAffineModel.g j) ((-2 : ℝ) • coordX) (pt (-1) 0) := by
  intro j
  have h := ((hasDerivAt_pow 2 (-1 : ℝ)).comp_hasFDerivAt (pt (-1) 0)
    coordX.hasFDerivAt).sub_const 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_neg, mul_one] at h
  exact h

theorem noAffine_minimum :
    IsMinimizer (noAffineModel.fixedNonlinearFiber (pt (-1) 0).2)
      noAffineModel.objective (pt (-1) 0) := by
  refine ⟨⟨⟨(fun i => Fin.elim0 i), rfl⟩,
    fun _ => by norm_num [noAffineModel, pt]⟩, ?_⟩
  intro p hp
  have hg := hp.2 0
  change (p.1 0)^2 - 1 ≤ 0 at hg
  simp only [ModelData.objective, noAffineModel, LinearForm, Fin.sum_univ_one,
    pt, one_mul, zero_mul, add_zero]
  nlinarith [sq_nonneg (p.1 0 + 1)]

theorem noAffine_slater : ∃ p ∈ noAffineModel.fixedLinearFiber (pt (-1) 0).2,
    ∀ j, noAffineModel.g j p < 0 :=
  ⟨pt 0 0, ⟨(fun i => Fin.elim0 i), rfl⟩, fun _ => by norm_num [noAffineModel, pt]⟩

/-- The existing zero-margin failure concerns the original objective, while
free-slack restoration at the same point does have theorem-derived multipliers. -/
theorem zeroMargin_restoration_exists_despite_original_failure :
    (¬ ∃ (D : Fin 1 → Point 1 1 →L[ℝ] ℝ) (lambda : Fin 1 → ℝ) (mu : Fin 2 → ℝ),
      FixedNLPKKT zeroMarginModel (pt 0 0) D lambda mu) ∧
    ∃ lambda mu, RestorationKKT zeroMarginModel (pt 0 0) 0 (fun _ => -coordY) lambda mu := by
  refine ⟨zeroMargin_no_kkt, ?_⟩
  apply exists_restorationKKT zeroMarginModel (pt 0 0) 0 (fun _ => -coordY)
    zeroMargin_convex
  · intro j
    simpa [pt] using zeroMargin_derivative (pt 0 0) j
  · exact zeroMargin_restoration_minimum

/-- Nonlinear Slater is sufficient, not necessary. Here it fails, but a
zero-margin restoration certificate obtained from the existence theorem is
also an original fixed-NLP certificate because its objective is zero. -/
theorem zero_margin_fixed_kkt_without_slater :
    (¬ ∃ p ∈ zeroSuccessModel.fixedLinearFiber (pt 0 0).2,
      ∀ j, zeroSuccessModel.g j p < 0) ∧
    ∃ lambda mu, lambda 0 = 1 ∧
      FixedNLPKKT zeroSuccessModel (pt 0 0) (fun _ => coordX) lambda mu := by
  obtain ⟨lambda, mu, hk⟩ := exists_restorationKKT zeroSuccessModel (pt 0 0) 0
    (fun _ => coordX) zeroSuccess_convex zeroSuccess_derivative zeroSuccess_restoration_minimum
  refine ⟨zeroSuccess_no_fiber_slater, lambda, mu, ?_, ?_⟩
  · simpa [Fin.sum_univ_one] using hk.normalization
  · refine ⟨hk.linear_feasible, hk.slack_feasible, hk.derivatives, hk.lambda_nonneg,
      hk.mu_nonneg, ?_, hk.linear_complementarity, ?_⟩
    · intro j
      simpa using hk.nonlinear_complementarity j
    · intro dx
      simpa [ModelData.objective, zeroSuccessModel, expModel, LinearForm] using hk.stationarity dx

/-- With no nonlinear rows, the fixed-NLP existence theorem gives LP
multipliers. Its affine coefficient is nonzero and derived, not inserted. -/
theorem empty_nonlinear_fixed_kkt :
    ∃ lambda mu, mu 0 = 1 ∧
      FixedNLPKKT emptyNonlinearModel (pt 0 0) (fun j => Fin.elim0 j) lambda mu := by
  obtain ⟨lambda, mu, hk⟩ := exists_fixedNLPKKT emptyNonlinearModel (pt 0 0)
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    emptyNonlinear_minimum emptyNonlinear_slater
  refine ⟨lambda, mu, ?_, hk⟩
  have hs := hk.stationarity (fun _ => 1)
  norm_num [ModelData.objective, emptyNonlinearModel, LinearForm, Fin.sum_univ_one] at hs
  linarith

/-- With no original continuous or integer coordinates, restoration still
introduces its one continuous slack. The theorem derives normalization. -/
theorem zero_dimension_restoration_kkt :
    ∃ lambda mu, lambda 0 = 1 ∧
      RestorationKKT zeroDimensionModel (0 : Point 0 0) 1 (fun _ => 0) lambda mu := by
  have hc : ∀ j, ConvexOn ℝ Set.univ (zeroDimensionModel.g j) := by
    intro j
    refine ⟨convex_univ, ?_⟩
    intro p _ q _ s t _ _ hst
    simpa [zeroDimensionModel, smul_eq_mul] using le_of_eq hst.symm
  obtain ⟨lambda, mu, hk⟩ := exists_restorationKKT zeroDimensionModel (0 : Point 0 0) 1
    (fun _ => 0) hc (fun j => hasFDerivAt_const _ _) zeroDimension_restoration_minimum
  exact ⟨lambda, mu, by simpa [Fin.sum_univ_one] using hk.normalization, hk⟩

/-- With no affine rows, fixed-NLP existence yields nonlinear stationarity;
the derived coefficient 1/2 gives the one-dimensional sign control. -/
theorem no_affine_fixed_kkt :
    ∃ lambda mu, lambda 0 = 1/2 ∧
      FixedNLPKKT noAffineModel (pt (-1) 0) (fun _ => (-2 : ℝ) • coordX) lambda mu := by
  obtain ⟨lambda, mu, hk⟩ := exists_fixedNLPKKT noAffineModel (pt (-1) 0)
    (fun _ => (-2 : ℝ) • coordX) noAffine_convex noAffine_derivative noAffine_minimum noAffine_slater
  refine ⟨lambda, mu, ?_, hk⟩
  have hs := hk.stationarity (fun _ => 1)
  norm_num [ModelData.objective, noAffineModel, LinearForm, Fin.sum_univ_one, coordX] at hs
  linarith

end Chapter02MultiplierEdgeExamples

#print axioms Chapter02MultiplierEdgeExamples.global_strict_point_does_not_give_fiber_slater
#print axioms Chapter02MultiplierEdgeExamples.exp_attainment_ablation
#print axioms Chapter02MultiplierEdgeExamples.exp_source_base_not_compact
#print axioms Chapter02MultiplierEdgeExamples.emptyNonlinear_restoration_no_minimum
#print axioms Chapter02MultiplierEdgeExamples.zeroMargin_restoration_exists_despite_original_failure
#print axioms Chapter02MultiplierEdgeExamples.zero_margin_fixed_kkt_without_slater
#print axioms Chapter02MultiplierEdgeExamples.empty_nonlinear_fixed_kkt
#print axioms Chapter02MultiplierEdgeExamples.zero_dimension_restoration_kkt
#print axioms Chapter02MultiplierEdgeExamples.no_affine_fixed_kkt
