module

public import Chapter02PresolveRedundancy
public import Mathlib.Tactic

@[expose] public section

/-! Exact full-model and boundary controls. No numerical solver is used. -/
noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02PresolveBoundsExamples

def point (x : ℝ) : RealVector 1 := fun _ => x

def intervalData (u : ℝ) : BBPolyData 1 1 2 where
  coefficient := ![![-1], ![1]]
  rhs := ![0, u]
  c := fun _ _ => -1
  f := fun z => z 0

theorem interval_feasible_iff (u : ℝ) (z : RealVector 1) :
    z ∈ (intervalData u).feasible ∅ ↔ 0 ≤ z 0 ∧ z 0 ≤ u := by
  simp [BBPolyData.feasible, BBPolyData.polyhedron, intervalData,
    Fin.forall_fin_succ, Fin.sum_univ_succ]

theorem relaxed_interval_control :
    (intervalData 1).feasible ∅ ⊆ (intervalData 2).feasible ∅ ∧
    IsMinimizer ((intervalData 2).feasible ∅) (fun z => z 0) (point 0) ∧
    IsMinimizer ((intervalData 2).feasible ∅) (fun z => -z 0) (point 2) ∧
    point 2 ∉ (intervalData 1).feasible ∅ := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨hl, hu⟩ := (interval_feasible_iff 1 z).mp hz
    exact (interval_feasible_iff 2 z).mpr ⟨hl, by linarith⟩
  · exact (interval_feasible_iff 2 _).mpr (by norm_num [point])
  · intro z hz
    exact (interval_feasible_iff 2 z).mp hz |>.1
  · exact (interval_feasible_iff 2 _).mpr (by norm_num [point])
  · intro z hz
    have hu := ((interval_feasible_iff 2 z).mp hz).2
    dsimp [point]
    linarith
  · simp [interval_feasible_iff, point]

theorem half_iterate_is_not_coordinate_bound :
    point (1/2) ∈ (intervalData 2).feasible ∅ ∧
    ¬ IsLowerBound ((intervalData 2).feasible ∅) (fun z => z 0) (1/2) ∧
    point 0 ∈ (intervalData 1).feasible ∅ ∧
    point 0 ∉ coordinateEnclosure (fun (_ : Fin 1) z => z 0)
      (fun _ => 1/2) (fun _ => 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (interval_feasible_iff 2 _).mpr (by norm_num [point])
  · intro h
    have hbad := h (point 0) ((interval_feasible_iff 2 _).mpr (by norm_num [point]))
    norm_num [point] at hbad
  · exact (interval_feasible_iff 1 _).mpr (by norm_num [point])
  · intro h
    have hbad := (h 0).1
    norm_num [point] at hbad

theorem compact_interval_extrema_control :
    ∃ lower upper : Fin 1 → RealVector 1,
      (∀ i, IsMinimizer ((intervalData 2).feasible ∅) (fun z => z i) (lower i)) ∧
      (∀ i, IsMinimizer ((intervalData 2).feasible ∅) (fun z => -z i) (upper i)) := by
  have hset : (intervalData 2).feasible ∅ =
      Set.Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 2) := by
    ext z
    simp [interval_feasible_iff, Set.mem_Icc, Pi.le_def, Fin.forall_fin_succ]
  apply compact_coordinate_extrema
  · rw [hset]
    exact isCompact_Icc
  · exact ⟨point 0, relaxed_interval_control.2.1.1⟩
  · intro i
    exact (continuous_apply i).continuousOn

theorem interval_closed_cutoff_control :
    HasUpperBoundWitness ((intervalData 2).feasible ∅) (intervalData 2).f 1 ∧
    IsMinimizer (cutoffSet ((intervalData 2).feasible ∅) (intervalData 2).f 1)
      (intervalData 2).f (point 0) ∧
    point 2 ∈ (intervalData 2).feasible ∅ ∧
    point 2 ∉ cutoffSet ((intervalData 2).feasible ∅) (intervalData 2).f 1 := by
  have hinc : HasUpperBoundWitness ((intervalData 2).feasible ∅) (intervalData 2).f 1 :=
    ⟨point 1, (interval_feasible_iff 2 _).mpr (by norm_num [point]), by norm_num [intervalData, point]⟩
  refine ⟨hinc, ?_, ?_, ?_⟩
  · apply (cutoff_minimizer_iff hinc (Set.Subset.refl _)
      (fun _ hx => hx.1) (point 0)).mp
    exact relaxed_interval_control.2.1
  · exact relaxed_interval_control.2.2.1.1
  · intro h
    norm_num [intervalData, point] at h
    exact (by norm_num : ¬(2 : ℝ) ≤ 1) h.2

theorem interval_invalid_cutoff_control :
    ((intervalData 2).feasible ∅).Nonempty ∧
    cutoffSet ((intervalData 2).feasible ∅) (intervalData 2).f (-1) = ∅ ∧
    ¬ HasUpperBoundWitness ((intervalData 2).feasible ∅) (intervalData 2).f (-1) := by
  have hempty : cutoffSet ((intervalData 2).feasible ∅) (intervalData 2).f (-1) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hlo := ((interval_feasible_iff 2 z).mp hz.1).1
    have hhi : z 0 ≤ -1 := hz.2
    linarith
  refine ⟨⟨point 0, relaxed_interval_control.2.1.1⟩, hempty, ?_⟩
  intro h
  have hn := cutoff_nonempty_of_incumbent h
  rw [hempty] at hn
  exact Set.not_nonempty_empty hn

theorem strict_cutoff_loses_tied_minimizers :
    HasUpperBoundWitness (Set.Icc (0 : ℝ) 2) (fun _ => 0) 0 ∧
    IsMinimizer (Set.Icc (0 : ℝ) 2) (fun _ => 0) 0 ∧
    IsMinimizer (Set.Icc (0 : ℝ) 2) (fun _ => 0) 2 ∧
    cutoffSet (Set.Icc (0 : ℝ) 2) (fun _ => 0) 0 = Set.Icc 0 2 ∧
    {x ∈ Set.Icc (0 : ℝ) 2 | (0 : ℝ) < 0} = ∅ := by
  refine ⟨⟨0, by norm_num, le_rfl⟩, ⟨by norm_num, fun _ _ => le_rfl⟩,
    ⟨by norm_num, fun _ _ => le_rfl⟩, ?_, ?_⟩
  · ext x; simp [cutoffSet]
  · simp

theorem empty_relaxation_has_no_attained_endpoint :
    IsLowerBound (∅ : Set ℝ) id 17 ∧ ¬ ∃ x, IsMinimizer (∅ : Set ℝ) id x := by
  simp [IsLowerBound, IsMinimizer]

theorem unbounded_relaxation_has_no_finite_endpoints :
    (∀ L : ℝ, ¬ IsLowerBound Set.univ id L) ∧
    (∀ U : ℝ, ¬ IsLowerBound Set.univ (fun x : ℝ => -x) (-U)) := by
  constructor
  · intro L h
    have hbad := h (L-1) (Set.mem_univ _)
    dsimp at hbad
    linarith
  · intro U h
    have hbad := h (U+1) (Set.mem_univ _)
    dsimp at hbad
    linarith

theorem open_relaxation_bound_is_unattained :
    IsLowerBound (Set.Ioo (0 : ℝ) 1) id 0 ∧
    ¬ ∃ x, IsMinimizer (Set.Ioo (0 : ℝ) 1) id x := by
  refine ⟨fun _ hx => le_of_lt hx.1, ?_⟩
  rintro ⟨x, hx, hmin⟩
  have hhalf : x/2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hbad := hmin (x/2) hhalf
  dsimp at hbad
  linarith [hx.1]

theorem zero_coordinate_enclosure_control :
    coordinateEnclosure (fun (i : Fin 0) (z : RealVector 0) => z i)
      (fun _ => 0) (fun _ => 0) = {fun i => Fin.elim0 i} := by
  rw [coordinateEnclosure_zero]
  ext z
  simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
  funext i
  exact Fin.elim0 i

theorem coordinate_enclosure_is_not_projection_equality :
    IsMinimizer ({0, 1} : Set ℝ) id 0 ∧
    IsMinimizer ({0, 1} : Set ℝ) (fun x => -x) 1 ∧
    (1/2 : ℝ) ∈ coordinateEnclosure (fun (_ : Fin 1) x => x) (fun _ => 0) (fun _ => 1) ∧
    (1/2 : ℝ) ∉ ({0, 1} : Set ℝ) := by
  refine ⟨⟨by simp, ?_⟩, ⟨by simp, ?_⟩, ?_, by norm_num⟩
  · intro y hy
    rcases hy with rfl | hy
    · norm_num
    · have hy' : y = 1 := hy; subst y; norm_num
  · intro y hy
    rcases hy with rfl | hy
    · norm_num
    · have hy' : y = 1 := hy; subst y; norm_num
  · intro i; norm_num

def duplicateData : BBPolyData 1 1 2 where
  coefficient := fun _ _ => 1
  rhs := fun _ => 0
  c := fun z _ => (z 0)^2 - 1
  f := fun z => z 0

def duplicateBase : Set (RealVector 1) := {z | -1 ≤ z 0 ∧ z 0 ≤ 1}

def duplicateCertificate (kept deleted : Fin 2) :
    duplicateData.RetainedRowCertificate {kept} deleted where
  weight := fun _ => 1
  nonneg := by intro k hk; norm_num
  coefficient_eq := by intro i; simp [duplicateData]
  rhs_le := by simp [duplicateData]

theorem duplicate_single_deletion_exact (kept : Fin 2) :
    duplicateData.retainedFeasible ∅ duplicateBase {kept} = duplicateBase ∩ duplicateData.feasible ∅ := by
  apply duplicateData.retained_feasible_eq_of_certificates
  intro j _
  exact duplicateCertificate kept j

theorem duplicate_invalid_double_deletion :
    point 1 ∈ duplicateData.retainedFeasible ∅ duplicateBase ∅ ∧
    point 1 ∉ duplicateBase ∩ duplicateData.feasible ∅ := by
  constructor
  · simp [BBPolyData.retainedFeasible, BBPolyData.retainedContinuous,
      BBPolyData.retainedPolyhedron, duplicateBase, duplicateData, point]
  · intro h
    have hbad := h.2.1 0
    norm_num [duplicateData, point, Fin.sum_univ_succ] at hbad

def integerData : BBPolyData 1 1 4 where
  coefficient := fun j _ => if j.val = 0 then -1 else 1
  rhs := fun j => if j.val = 1 then 1 else if j.val = 2 then 1/2 else 0
  c := fun z _ => (z 0)^2 - 1
  f := fun z => z 0

def integerKept : Finset (Fin 4) := Finset.univ.filter (fun j => j.val < 3)

theorem integer_only_redundancy_exact :
    integerData.retainedFeasible {0} Set.univ integerKept =
      Set.univ ∩ integerData.feasible {0} := by
  apply integerData.retained_feasible_eq_of_implication
  intro z hz j hj
  have hhalf := hz.1.2.1 2 (by simp [integerKept])
  have hnonneg := hz.1.2.1 0 (by simp [integerKept])
  change (1 : ℝ) * z 0 + 0 ≤ (1/2 : ℝ) at hhalf
  change -1 * z 0 + 0 ≤ 0 at hnonneg
  obtain ⟨k, hk⟩ := hz.2 ⟨0, by simp⟩
  change (k : ℝ) = z 0 at hk
  have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast (show (0 : ℝ) ≤ (k : ℝ) by linarith)
  have hk1 : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < (1 : ℝ) by linarith)
  have hkz : k = 0 := by omega
  have hz0 : z 0 = 0 := by simpa [hkz] using hk.symm
  fin_cases j <;> norm_num [integerData, Fin.sum_univ_succ, hz0]

theorem integer_only_redundancy_changes_continuous_model :
    point (1/2) ∈ integerData.retainedContinuous Set.univ integerKept ∧
    point (1/2) ∉ integerData.polyhedron ∧
    point 0 ∈ integerData.feasible {0} := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Set.mem_univ _, ?_, ?_⟩
    · intro j hj
      have he : integerKept = ({0, 1, 2} : Finset (Fin 4)) := by decide
      have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by
        simpa only [he, Finset.mem_insert, Finset.mem_singleton] using hj
      rcases hjcases with rfl | rfl | rfl <;>
        norm_num [integerData, point, Fin.sum_univ_succ]
    · intro j
      norm_num [integerData, point]
  · intro h
    have hbad := h 3
    change (1 : ℝ) * (1/2) + 0 ≤ 0 at hbad
    norm_num at hbad
  · refine ⟨?_, ?_, ?_⟩
    · intro j
      fin_cases j <;> norm_num [integerData, point, Fin.sum_univ_succ]
    · intro j
      norm_num [integerData, point]
    · intro i
      exact ⟨0, by simp [point]⟩

end Chapter02PresolveBoundsExamples

#print axioms Chapter02PresolveBoundsExamples.interval_feasible_iff
#print axioms Chapter02PresolveBoundsExamples.relaxed_interval_control
#print axioms Chapter02PresolveBoundsExamples.half_iterate_is_not_coordinate_bound
#print axioms Chapter02PresolveBoundsExamples.compact_interval_extrema_control
#print axioms Chapter02PresolveBoundsExamples.interval_closed_cutoff_control
#print axioms Chapter02PresolveBoundsExamples.interval_invalid_cutoff_control
#print axioms Chapter02PresolveBoundsExamples.strict_cutoff_loses_tied_minimizers
#print axioms Chapter02PresolveBoundsExamples.empty_relaxation_has_no_attained_endpoint
#print axioms Chapter02PresolveBoundsExamples.unbounded_relaxation_has_no_finite_endpoints
#print axioms Chapter02PresolveBoundsExamples.open_relaxation_bound_is_unattained
#print axioms Chapter02PresolveBoundsExamples.zero_coordinate_enclosure_control
#print axioms Chapter02PresolveBoundsExamples.coordinate_enclosure_is_not_projection_equality
#print axioms Chapter02PresolveBoundsExamples.duplicate_single_deletion_exact
#print axioms Chapter02PresolveBoundsExamples.duplicate_invalid_double_deletion
#print axioms Chapter02PresolveBoundsExamples.integer_only_redundancy_exact
#print axioms Chapter02PresolveBoundsExamples.integer_only_redundancy_changes_continuous_model
