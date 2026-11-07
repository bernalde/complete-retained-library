module

public import Chapter02FBBTSourceTheorem
public import Chapter02FBBTControlData
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Chapter02 Chapter02FBBT Filter
namespace Chapter02FBBTControls

private lemma seededMax_one (s : ℝ) (v : Fin 1 → ℝ) :
    seededMax s v = max s (v 0) := by
  have h : (Finset.univ : Finset (Option (Fin 1))) = {none, some 0} := by decide
  simp [seededMax, h, Finset.sup'_insert, Finset.sup'_singleton]

private lemma seededMin_one (s : ℝ) (v : Fin 1 → ℝ) :
    seededMin s v = min s (v 0) := by
  have h : (Finset.univ : Finset (Option (Fin 1))) = {none, some 0} := by decide
  simp [seededMin, h, Finset.inf'_insert, Finset.inf'_singleton]

def controlBox (t : ℝ) : JointBounds 2 1 :=
  (Sum.elim (point 0 (-2)) (fun _ => 0), Sum.elim (point t 2) (fun _ => 1))

lemma control_initial_eq : sourceInitial data initialX = controlBox 2 := by
  apply Prod.ext <;> funext i <;> cases i with
  | inl j => rfl
  | inr i =>
    fin_cases i;
      norm_num [sourceInitial, sourceLower, data, initialX, point, controlBox,
        affineProductLo, Fin.sum_univ_succ]

lemma control_tightened_eq : sourceInitial data tightenedX = controlBox 1 := by
  apply Prod.ext <;> funext i <;> cases i with
  | inl j => rfl
  | inr i =>
    fin_cases i;
      norm_num [sourceInitial, sourceLower, data, tightenedX, point, controlBox,
        affineProductLo, Fin.sum_univ_succ]

lemma control_step (t : ℝ) (ht : 1 ≤ t) (ht2 : t ≤ 2) :
    rawF data.coefficient (controlBox 2) (controlBox t) = controlBox 1 := by
  have hc : clip (controlBox t) (controlBox 2) = controlBox t := by
    apply Prod.ext <;> funext s <;> cases s with
    | inl j => fin_cases j <;> simp [clip, controlBox, point, min_eq_left ht2]
    | inr i => simp [clip, controlBox]
  have hu : upward data.coefficient (controlBox t) = controlBox t := by
    apply Prod.ext <;> funext s <;> cases s with
    | inl j => rfl
    | inr i =>
      fin_cases i; simp [upward, imageLo, imageHi, productLo, productHi,
        data, controlBox, point, affineProductLo, affineProductHi,
        Fin.sum_univ_succ, min_eq_left ht]
  rw [rawF, hc, hu]
  apply Prod.ext <;> funext s <;> cases s with
  | inr i => rfl
  | inl j =>
    fin_cases j <;>
      norm_num [downward, seededMax_one, seededMin_one, inverseLo, inverseHi,
        restLo, restHi, productLo, productHi, data, controlBox, point,
        affineProductLo, affineProductHi, Finset.univ_fin2, min_eq_right ht]

lemma control_run_successor (k : ℕ) :
    rawRun data.coefficient (controlBox 2) (k+1) = controlBox 1 := by
  induction k with
  | zero =>
    simpa [rawRun] using control_step 2 (by norm_num) le_rfl
  | succ k ih =>
    rw [rawRun, Function.iterate_succ_apply']
    change rawF data.coefficient (controlBox 2)
      (rawRun data.coefficient (controlBox 2) (k+1)) = _
    rw [ih]
    exact control_step 1 le_rfl (by norm_num)

lemma control_nonempty_run : RunNonempty data.coefficient (sourceInitial data initialX) := by
  apply fixed_implies_nonempty_run
  refine ⟨(graph data.coefficient optimum, graph data.coefficient optimum), fun _ => le_rfl, ?_⟩
  exact graph_singleton_fixed _ _ _
    ((source_feasible_graph_iff data integerCoordinates initialX optimum).1 actual_source_optimum.1).2

lemma control_limit : limitBounds data.coefficient (sourceInitial data initialX) = controlBox 1 := by
  have ht : Filter.Tendsto (rawRun data.coefficient (controlBox 2))
      Filter.atTop (nhds (controlBox 1)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [control_run_successor] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => controlBox 1) Filter.atTop (nhds (controlBox 1)))
  rw [← control_initial_eq] at ht
  exact tendsto_nhds_unique (actual_limit _ _ control_nonempty_run).2.2.1 ht

lemma control_source_limit : sourceLimitX data initialX = tightenedX := by
  unfold sourceLimitX
  rw [control_limit]
  rfl

lemma retained_source_actual_application :
    SourceTheory data integerCoordinates initialX ∧
    SourceConclusion data integerCoordinates initialX ∧
    sourceLimitX data initialX = tightenedX ∧
    IsMinimizer (data.feasible integerCoordinates ∩ members (sourceLimitX data initialX)) data.f optimum ∧
    data.f optimum = -1 ∧
    rawF data.coefficient (sourceInitial data initialX) (sourceInitial data initialX) = controlBox 1 ∧
    LPFeasible data.coefficient (sourceInitial data initialX)
      (canonicalAssignment data.coefficient (controlBox 1)) ∧
    (∀ i, (canonicalAssignment data.coefficient (controlBox 1)).zLo i 1 = 0 ∧
      (canonicalAssignment data.coefficient (controlBox 1)).zHi i 1 = 0) := by
  have hs := qualified_source_fbbt data integerCoordinates initialX initialX_ordered
  have hc := hs.conditionalSourceConclusion control_nonempty_run
  have hlp := (hs.core.conditionalConclusion control_nonempty_run).attainedLP
  rw [control_limit] at hlp
  refine ⟨hs, hc, control_source_limit,
    (hc.originalObjectiveMinimizerEquivalence optimum).2 actual_source_optimum,
    by norm_num [data, optimum, point], ?_, hlp, ?_⟩
  · rw [control_initial_eq]
    exact control_step 2 (by norm_num) le_rfl
  · intro i
    exact zero_product_equalities _ _ _ hlp i 1 (by simp [data])

end Chapter02FBBTControls
