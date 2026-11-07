module

public import Chapter02ModelExamples
public import Chapter02Epigraph
public import Chapter02ESH
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Nonvacuity cases for the full Chapter 2 foundation continuation.
The nonlinear objective is distinct from the original example's linear one.
Additional examples below will exercise the actual new model and ESH interfaces.
-/
noncomputable section
open Chapter02 Chapter02Examples
namespace Chapter02CompletionExamples

def nonlinearObjective (p : Point 1 1) : ℝ := (p.1 0)^2 + (p.2 0)^2
def zeroPoint : Point 1 1 := (fun _ => 0, fun _ => 0)

theorem zero_feasible : zeroPoint ∈ sample.feasibleOn Set.univ := by
  rw [source_feasible_iff]
  refine ⟨Set.mem_univ _, ?_, ?_, fun _ => (0:ℤ), ?_, by simp [zeroPoint]⟩
  · intro j
    fin_cases j <;> norm_num [sample, zeroPoint]
  · intro row
    fin_cases row <;> norm_num [sample, zeroPoint, LinearForm, Fin.sum_univ_one]
  · intro i
    norm_num [sample]

theorem nonlinearObjective_minimizer :
    IsMinimizer (sample.feasibleOn Set.univ) nonlinearObjective zeroPoint := by
  refine ⟨zero_feasible, ?_⟩
  intro p _
  change 0^2 + 0^2 ≤ (p.1 0)^2 + (p.2 0)^2
  nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.2 0)]

theorem nonlinearObjective_bounds : ∀ p ∈ sample.feasibleOn Set.univ,
    0 ≤ nonlinearObjective p ∧ nonlinearObjective p ≤ 2 := by
  intro p hp
  have h := (source_feasible_iff sample Set.univ p).mp hp
  have hx := h.2.1 0
  have hy := h.2.1 1
  change (p.1 0)^2 - 1 ≤ 0 at hx
  change (p.2 0)^2 - 1 ≤ 0 at hy
  dsimp [nonlinearObjective]
  constructor <;> nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.2 0)]

theorem nonlinearObjective_convex : ConvexOn ℝ Set.univ nonlinearObjective := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t hs ht hst
  have hx : 0 ≤ s*t*(p.1 0-q.1 0)^2 := mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
  have hy : 0 ≤ s*t*(p.2 0-q.2 0)^2 := mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
  simp only [nonlinearObjective, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [sq_nonneg (p.1 0-q.1 0), sq_nonneg (p.2 0-q.2 0)]

theorem nonlinearObjective_smooth : ContDiff ℝ 1 nonlinearObjective := by
  unfold nonlinearObjective
  fun_prop

theorem sample_rows_smooth : ∀ j, ContDiff ℝ 1 (sample.g j) := by
  intro j
  fin_cases j <;> simp [sample] <;> fun_prop

theorem sample_base_compact :
    IsCompact (sample.linearRegion ∩ IntegerCylinder (n := 1) sample.lo sample.hi) := by
  have hL : IsClosed sample.linearRegion := by
    have heq : sample.linearRegion =
        ⋂ row, {p | LinearForm (sample.A row) (sample.B row) p ≤ sample.rhs row} := by
      ext p
      simp [ModelData.linearRegion]
    rw [heq]
    exact isClosed_iInter fun row => isClosed_le (linearForm_continuous _ _) continuous_const
  have hY : IsClosed (IntegerCylinder (n := 1) sample.lo sample.hi) := by
    have hfin := (integerBox_finite sample.lo sample.hi).image
      (fun y : IntVector 1 => fun i => (y i : ℝ))
    have heq : IntegerCylinder (n := 1) sample.lo sample.hi =
        Prod.snd ⁻¹' ((fun y : IntVector 1 => fun i => (y i : ℝ)) ''
          IntegerBox sample.lo sample.hi) := by
      ext p
      simp [IntegerCylinder, eq_comm]
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  apply (isCompact_Icc : IsCompact (Set.Icc
    ((fun _ : Fin 1 => (-2 : ℝ)), (fun _ : Fin 1 => (0 : ℝ)))
    ((fun _ : Fin 1 => (2 : ℝ)), (fun _ : Fin 1 => (1 : ℝ))))).of_isClosed_subset
    (hL.inter hY)
  rintro p ⟨hL, y, hy, hp⟩
  have hxlo := hL (1 : Fin 2)
  have hxhi := hL (0 : Fin 2)
  norm_num [sample, LinearForm, Fin.sum_univ_one] at hxlo hxhi
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i
    fin_cases i
    change -2 ≤ p.1 0
    linarith
  · intro i
    rw [hp]
    exact (hy i).1
  · intro i
    fin_cases i
    exact hxhi
  · intro i
    rw [hp]
    exact (hy i).2

private noncomputable def __migrationExample_Chapter02CompletionExamples_L106_N001 : IsCompact ((sample.boundedEpigraphModel nonlinearObjective 0 2).linearRegion ∩
    IntegerCylinder (n := 2) sample.lo sample.hi) :=
  boundedEpigraphModel_base_compact sample nonlinearObjective 0 2 sample_base_compact

private noncomputable def __migrationExample_Chapter02CompletionExamples_L110_N002 : ∀ j, ContDiff ℝ 1 ((sample.boundedEpigraphModel nonlinearObjective 0 2).g j) :=
  boundedEpigraphModel_rows_contDiff sample nonlinearObjective 0 2 1
    nonlinearObjective_smooth sample_rows_smooth

private noncomputable def __migrationExample_Chapter02CompletionExamples_L114_N003 : epiInsert zeroPoint 2 ∈
    (sample.boundedEpigraphModel nonlinearObjective 0 2).linearRegion ∧
    ∀ j, (sample.boundedEpigraphModel nonlinearObjective 0 2).g j
      (epiInsert zeroPoint 2) < 0 := by
  apply boundedEpigraphModel_strict_start sample nonlinearObjective 0 2 zeroPoint
  · intro row
    fin_cases row <;> norm_num [sample, zeroPoint, LinearForm, Fin.sum_univ_one]
  · intro j
    fin_cases j <;> norm_num [sample, zeroPoint]
  · norm_num
  · norm_num [nonlinearObjective, zeroPoint]

private noncomputable def __migrationExample_Chapter02CompletionExamples_L126_N004 : ¬ IsCompact ((sample.epigraphModel nonlinearObjective).linearRegion ∩
    IntegerCylinder (n := 2) sample.lo sample.hi) := by
  apply epigraphModel_base_not_compact
  have hz := (source_feasible_iff sample Set.univ zeroPoint).mp zero_feasible
  exact ⟨zeroPoint, hz.2.2.1, hz.2.2.2⟩

private noncomputable def __migrationExample_Chapter02CompletionExamples_L132_N005 : epigraphDerivative (0 : Point 1 1 →L[ℝ] ℝ) (epiInsert zeroPoint 1) = -1 := by
  simp [epigraphDerivative_insert]

private noncomputable def __migrationExample_Chapter02CompletionExamples_L135_N006 : IsMinimizer
    ((sample.epigraphModel nonlinearObjective).feasibleOn (epiProject ⁻¹' Set.univ))
    (sample.epigraphModel nonlinearObjective).objective (epiInsert zeroPoint 0) := by
  rw [epigraphModel_minimizer_iff]
  exact ⟨by simpa using nonlinearObjective_minimizer,
    by norm_num [nonlinearObjective, zeroPoint]⟩

private noncomputable def __migrationExample_Chapter02CompletionExamples_L142_N007 : IsMinimizer
    ((sample.boundedEpigraphModel nonlinearObjective 0 2).feasibleOn (epiProject ⁻¹' Set.univ))
    (sample.boundedEpigraphModel nonlinearObjective 0 2).objective (epiInsert zeroPoint 0) := by
  rw [boundedEpigraphModel_minimizer_iff sample nonlinearObjective Set.univ 0 2
    nonlinearObjective_bounds]
  exact ⟨by simpa using nonlinearObjective_minimizer,
    by norm_num [nonlinearObjective, zeroPoint]⟩

/-- The concrete added nonlinear row excludes an invalid epigraph height. -/
private noncomputable def __migrationExample_Chapter02CompletionExamples_L151_N008 : epiInsert zeroPoint (-1) ∉
    (sample.epigraphModel nonlinearObjective).feasibleOn (epiProject ⁻¹' Set.univ) := by
  rw [epigraphModel_feasible_iff]
  simp [nonlinearObjective, zeroPoint]

private noncomputable def __migrationExample_Chapter02CompletionExamples_L156_N009 : (sample.epigraphModel nonlinearObjective).objective
    (epiInsert (fun _ => 1, fun _ => 1) 3) = 3 := by
  simp

/-- A wrong cap excludes an otherwise feasible graph point. -/
private noncomputable def __migrationExample_Chapter02CompletionExamples_L161_N010 : epiInsert (fun _ => 1, fun _ => 1) 2 ∉
    (sample.boundedEpigraphModel nonlinearObjective 0 1).feasibleOn
      (epiProject ⁻¹' Set.univ) := by
  rw [boundedEpigraphModel_feasible_iff]
  simp

def quadraticConstraint (_ : Fin 1) (x : ℝ) := x^2 - 1

theorem quadraticConstraint_convex :
    ∀ j, ConvexOn ℝ Set.univ (quadraticConstraint j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have h : 0 ≤ s*t*(x-y)^2 := mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
  change (s*x+t*y)^2-1 ≤ s*(x^2-1)+t*(y^2-1)
  nlinarith [sq_nonneg (x-y)]

theorem quadraticConstraint_differentiable :
    ∀ j, Differentiable ℝ (quadraticConstraint j) := by
  intro j
  exact (differentiable_id.pow 2).sub_const 1

/-- A nontrivial actual ESH instance, with a violated trial at 2. -/
private noncomputable def __migrationExample_Chapter02CompletionExamples_L184_N011 : ∃ t ∈ Set.Ioo (0:ℝ) 1,
    AffineMap.lineMap (0:ℝ) 2 t ∈ frontier {x : ℝ | x^2-1 ≤ 0} ∧
    ∃ j : Fin 1,
      fderiv ℝ (quadraticConstraint j) (AffineMap.lineMap (0:ℝ) 2 t) ≠ 0 ∧
      0 < fderiv ℝ (quadraticConstraint j) (AffineMap.lineMap (0:ℝ) 2 t)
        (2-AffineMap.lineMap (0:ℝ) 2 t) := by
  obtain ⟨t, ht, _, hfront, j, hj, hD, _, hsep⟩ := esh_supporting_cut_exists
    quadraticConstraint_convex quadraticConstraint_differentiable
    (a := (0:ℝ)) (b := (2:ℝ)) (by intro j; norm_num [quadraticConstraint])
    (by exact ⟨0, by norm_num [quadraticConstraint]⟩)
  refine ⟨t, ht, ?_, j, hD, ?_⟩
  · simpa [quadraticConstraint] using hfront
  · simpa only [hj, zero_add] using hsep

/-- Feasible alone does not supply the strict starting point required by ESH. -/
private noncomputable def __migrationExample_Chapter02CompletionExamples_L199_N012 : ¬ ∃ a : ℝ, a^2 < 0 := by
  rintro ⟨a, ha⟩
  exact (not_lt.mpr (sq_nonneg a)) ha

/-- A root outside the interpolation segment does not give the promised separation. -/
private noncomputable def __migrationExample_Chapter02CompletionExamples_L204_N013 : quadraticConstraint 0 (-1) = 0 ∧
    HasDerivAt (quadraticConstraint 0) (-2) (-1) ∧ (-2:ℝ)*(2-(-1)) ≤ 0 := by
  refine ⟨by norm_num [quadraticConstraint], ?_, by norm_num⟩
  convert (hasDerivAt_pow 2 (-1:ℝ)).sub_const 1 using 1 <;>
    (try ext x) <;> norm_num [quadraticConstraint]

private noncomputable def __migrationExample_Chapter02CompletionExamples_L210_N014 : ∃ t ∈ Set.Ioo (0:ℝ) 1,
    AffineMap.lineMap zeroPoint (fun _ => 2, fun _ => 1) t ∈
      sample.nonlinearRegion ∩ sample.linearRegion ∧
    AffineMap.lineMap zeroPoint (fun _ => 2, fun _ => 1) t ∈ frontier sample.nonlinearRegion := by
  obtain ⟨t, ht, hfeas, hfront, _⟩ := source_esh_supporting_cut_exists sample sample_convex
    (fun j => (sample_rows_smooth j).differentiable (by norm_num))
    (a := zeroPoint) (b := (fun _ => 2, fun _ => 1))
    (by intro row; fin_cases row <;> norm_num [sample, zeroPoint, LinearForm, Fin.sum_univ_one])
    (by intro row; fin_cases row <;> norm_num [sample, LinearForm, Fin.sum_univ_one])
    (by intro j; fin_cases j <;> norm_num [sample, zeroPoint])
    (by exact ⟨0, by norm_num [sample]⟩)
  exact ⟨t, ht, hfeas, hfront⟩

end Chapter02CompletionExamples
