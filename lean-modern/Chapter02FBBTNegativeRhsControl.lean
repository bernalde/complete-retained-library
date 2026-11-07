module

public import Chapter02FBBTSourceControl
public import Chapter02FBBTBoundaryControls

@[expose] public section

/-! Additive, uncounted source-adapter boundary control. The only changed field
of the retained source data is rhs = -1. This empty run uses the unconditional
infeasibility endpoint; it asserts no source-limit or minimizer conclusion.
Candidate source: compilation and independent frozen review remain pending. -/
noncomputable section
open Chapter02 Chapter02FBBT Chapter02FBBTBoundary
namespace Chapter02FBBTControls

/-- The original full control data with only its affine right-hand side changed. -/
def Dneg : BBPolyData 2 1 1 :=
  { data with rhs := fun _ => -1 }

lemma negative_rhs_source_lower (i : Fin 1) :
    sourceLower Dneg initialX i = -1 := by
  fin_cases i
  norm_num [sourceLower, Dneg, data, initialX, point, affineProductLo,
    Fin.sum_univ_succ]

lemma negative_rhs_initial_ordered : Ordered (sourceInitial Dneg initialX) :=
  source_initial_ordered Dneg initialX initialX_ordered

/-- Evaluate the actual initial product's signed image, including the strict
image-lower-bound/right-hand-side branch of the source adapter. -/
lemma negative_rhs_initial_image (i : Fin 1) :
    imageLo Dneg.coefficient (sourceInitial Dneg initialX) i = 0 ∧
    imageHi Dneg.coefficient (sourceInitial Dneg initialX) i = 2 ∧
    Dneg.rhs i < imageLo Dneg.coefficient (sourceInitial Dneg initialX) i := by
  fin_cases i
  norm_num [imageLo, imageHi, productLo, productHi, sourceInitial, Dneg, data,
    initialX, point, affineProductLo, affineProductHi, Fin.sum_univ_succ]

/-- The upward row is [0,-1], and downward preserves its endpoints. -/
lemma negative_rhs_first_raw_row (i : Fin 1) :
    (rawF Dneg.coefficient (sourceInitial Dneg initialX)
      (sourceInitial Dneg initialX)).1 (.inr i) = 0 ∧
    (rawF Dneg.coefficient (sourceInitial Dneg initialX)
      (sourceInitial Dneg initialX)).2 (.inr i) = -1 := by
  fin_cases i
  norm_num [rawF, downward, upward, clip, sourceInitial, sourceLower, Dneg,
    data, initialX, point, imageLo, imageHi, productLo, productHi,
    affineProductLo, affineProductHi, Fin.sum_univ_succ]

lemma negative_rhs_first_raw_invalid :
    ¬ Ordered (rawF Dneg.coefficient (sourceInitial Dneg initialX)
      (sourceInitial Dneg initialX)) := by
  intro h
  have hr := h (.inr (0 : Fin 1))
  rw [(negative_rhs_first_raw_row 0).1, (negative_rhs_first_raw_row 0).2] at hr
  norm_num at hr

/-- This is the existing full empty-run interface, applied to sourceInitial. -/
theorem negative_rhs_empty_control :
    EmptyAfterOneControl Dneg.coefficient (sourceInitial Dneg initialX) :=
  empty_after_one_control Dneg.coefficient (sourceInitial Dneg initialX)
    negative_rhs_initial_ordered negative_rhs_first_raw_invalid

lemma negative_rhs_run_not_nonempty :
    ¬ RunNonempty Dneg.coefficient (sourceInitial Dneg initialX) := by
  intro h
  have h1 := h 1
  rw [negative_rhs_empty_control.firstEmpty] at h1
  exact Set.not_nonempty_empty h1

/-- Invoke the actual source theorem's unconditional branch using its actual
scalar-LP infeasibility certificate. No SourceConclusion is asserted. -/
theorem negative_rhs_source_infeasible :
    Dneg.feasible integerCoordinates ∩ members initialX = ∅ :=
  (qualified_source_fbbt Dneg integerCoordinates initialX initialX_ordered).unconditionalSourceInfeasibility
    negative_rhs_empty_control.LPEmpty

/-- The first retained-source witness satisfies the box, affine and integer
restrictions, and violates the nonlinear restriction alone. -/
lemma retained_nonlinear_isolation :
    point 0 2 ∈ members tightenedX ∧
    point 0 2 ∈ data.polyhedron ∧
    (∀ i : {i : Fin 2 // i ∈ integerCoordinates},
      ∃ k : ℤ, (k : ℝ) = point 0 2 i) ∧
    ¬ (∀ j, data.c (point 0 2) j ≤ 0) := by
  refine ⟨retained_nonlinear_effective.1, ?_, ?_, retained_nonlinear_effective.2⟩
  · intro i
    fin_cases i
    norm_num [data, point, Fin.sum_univ_succ]
  · rintro ⟨i, hi⟩
    have hi' : i = 1 := by simpa [integerCoordinates] using hi
    subst i
    exact ⟨2, by norm_num [point]⟩

/-- The second retained-source witness satisfies the box, affine and nonlinear
restrictions, and fails integrality. -/
lemma retained_integrality_isolation :
    point 0 (1/2) ∈ members tightenedX ∧
    point 0 (1/2) ∈ data.polyhedron ∧
    (∀ j, data.c (point 0 (1/2)) j ≤ 0) ∧
    ¬ (∀ i : {i : Fin 2 // i ∈ integerCoordinates},
      ∃ k : ℤ, (k : ℝ) = point 0 (1/2) i) := by
  refine ⟨retained_integrality_effective.1, ?_,
    retained_integrality_effective.2.1, retained_integrality_effective.2.2⟩
  intro i
  fin_cases i
  norm_num [data, point, Fin.sum_univ_succ]

end Chapter02FBBTControls
