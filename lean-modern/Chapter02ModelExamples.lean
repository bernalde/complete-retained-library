module

public import Chapter02Model
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! Executable nonvacuity checks, not additional certificate targets. The nonlinear
model has x in [-2,2], integer y in [0,1], objective x+y, and two constraints.
Only the first constraint is selected for the tangent at x=2,y=0. -/
noncomputable section
open Chapter02
namespace Chapter02Examples

def coordX : Point 1 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector 1))

def sample : ModelData 1 1 2 2 where
  g := fun j p => if j = 0 then (p.1 0)^2 - 1 else (p.2 0)^2 - 1
  A := fun row _ => if row = 0 then 1 else -1
  B := fun _ _ => 0
  rhs := fun _ => 2
  c1 := fun _ => 1
  c2 := fun _ => 1
  lo := fun _ => 0
  hi := fun _ => 1

def cuts : TangentFamily 1 1 2 1 where
  origin := fun _ => (fun _ => 2, fun _ => 0)
  selected := fun _ => {0}
  derivative := fun _ _ => (4 : ℝ) • coordX

private noncomputable def __migrationExample_Chapter02ModelExamples_L29_N001 : (fun _ => 0, fun _ => 1) ∈ sample.feasibleOn Set.univ := by
  rw [source_feasible_iff]
  refine ⟨Set.mem_univ _, ?_, ?_, fun _ => (1:ℤ), ?_, by norm_num⟩
  · intro j
    fin_cases j <;> norm_num [sample]
  · intro row
    fin_cases row <;> norm_num [sample, LinearForm, Fin.sum_univ_one]
  · intro i
    norm_num [sample]

private noncomputable def __migrationExample_Chapter02ModelExamples_L39_N002 : sample.objective (fun _ => 1/2, fun _ => 1) = 3/2 := by
  norm_num [ModelData.objective, sample, LinearForm, Fin.sum_univ_one]

theorem sample_convex : ∀ j, ConvexOn ℝ Set.univ (sample.g j) := by
  intro j
  constructor
  · exact convex_univ
  · intro p _ q _ s t hs ht hst
    have hs1 : s ≤ 1 := by linarith
    have htpq : 0 ≤ s*t*((p.1 0)-(q.1 0))^2 :=
      mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
    have hty : 0 ≤ s*t*((p.2 0)-(q.2 0))^2 :=
      mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
    fin_cases j <;> simp [sample, smul_eq_mul] <;> nlinarith [sq_nonneg (p.1 0-q.1 0), sq_nonneg (p.2 0-q.2 0)]

theorem sample_derivative : ∀ i j, j ∈ cuts.selected i →
    HasFDerivAt (sample.g j) (cuts.derivative i j) (cuts.origin i) := by
  intro i j hj
  have hj0 : j = 0 := by simpa [cuts] using hj
  subst j
  have h := ((hasDerivAt_pow 2 (2:ℝ)).comp_hasFDerivAt (cuts.origin i)
    coordX.hasFDerivAt).sub_const 1
  convert h using 1 <;> norm_num [sample, cuts, coordX, Function.comp_def]

private noncomputable def __migrationExample_Chapter02ModelExamples_L63_N003 : sample.feasibleOn Set.univ ⊆ sample.masterOn cuts Set.univ :=
  source_feasible_subset_master sample cuts Set.univ sample_convex
    (fun _ => Set.mem_univ _) sample_derivative

private noncomputable def __migrationExample_Chapter02ModelExamples_L67_N004 : cuts.cutRegion sample = {p | 4 * p.1 0 - 5 ≤ 0} := by
  ext p
  simp [TangentFamily.cutRegion, sample, cuts, coordX, smul_eq_mul]
  constructor <;> intro h <;> linarith

private noncomputable def __migrationExample_Chapter02ModelExamples_L72_N005 : cuts.origin 0 ∉ cuts.cutRegion sample := by
  intro h
  have hcut := h 0 0 (by simp [cuts])
  norm_num [cuts, sample, coordX] at hcut

private noncomputable def __migrationExample_Chapter02ModelExamples_L77_N006 : (fun _ => 0, fun _ => 1) ∈ cuts.cutRegion sample := by
  intro i j hj
  have hj0 : j = 0 := by simpa [cuts] using hj
  subst j
  norm_num [cuts, sample, coordX]

private noncomputable def __migrationExample_Chapter02ModelExamples_L83_N007 : IsCompact (BoundedEpigraph (Set.Icc (-1:ℝ) 1) (fun x => x^2) 0 1) :=
  bounded_epigraph_compact isCompact_Icc (by fun_prop) 0 1

private noncomputable def __migrationExample_Chapter02ModelExamples_L86_N008 : ∀ p : ℝ × ℝ,
    IsMinimizer (BoundedEpigraph (Set.Icc (-1:ℝ) 1) (fun x => x^2) 0 1) Prod.snd p ↔
    IsMinimizer (Set.Icc (-1:ℝ) 1) (fun x => x^2) p.1 ∧ p.2 = p.1^2 := by
  intro p
  apply bounded_epigraph_minimizer_iff
  intro x hx
  exact ⟨sq_nonneg _, by nlinarith [hx.1, hx.2]⟩

private noncomputable def __migrationExample_Chapter02ModelExamples_L94_N009 : ¬ IsCompact (EpigraphLift ({0} : Set ℝ) (fun _ => (0:ℝ))) :=
  nonempty_epigraph_not_compact (Set.singleton_nonempty 0)

/-- A height cap that is too low can destroy every feasible lifted point. -/
private noncomputable def __migrationExample_Chapter02ModelExamples_L98_N010 : BoundedEpigraph (Set.Icc (-1:ℝ) 1) (fun x => x^2+1) 0 (1/2) = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have h := hp.2.1.trans hp.2.2.2
  nlinarith [sq_nonneg p.1]

end Chapter02Examples
