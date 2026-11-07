module

public import Chapter03OAKKTControlMaps
public import Chapter03OAKKTControlHistory
public import Chapter03OAKKTControlConvexity

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples
open scoped BigOperators
namespace Chapter03.OAKKT.Controls

/-- Full source feasible-branch consumer, with attained fiber minimum. -/
theorem final_master_lower {z : P × ℝ}
    (hz : z∈Chapter06.EpigraphMaster finalModel positiveF (finalFamily 1)
      (positiveHistoryDf 1) Set.univ) (hy : z.1.2=scalar 1) : (5/4:ℝ)≤z.2 := by
  have hh := fixed_solution_master_lower (finalHistory 1) final_fiber_minimum finalFixed hz hy
  norm_num [positiveF,scalar] at hh
  exact hh

theorem thesis_master_lower {z : P × ℝ}
    (hz : z∈Chapter06.EpigraphMaster thesisModel positiveF (thesisFamily 1)
      (positiveHistoryDf 1) Set.univ) (hy : z.1.2=scalar 1) : (5/4:ℝ)≤z.2 := by
  have hh := fixed_solution_master_lower (thesisHistory 1) thesis_fiber_minimum thesisFixed hz hy
  norm_num [positiveF,scalar] at hh
  exact hh

/-- STATIC infeasible-fiber consumer: the genuine seed already excludes y=0.
This theorem makes no claim that an OA execution visits the fiber. -/
theorem final_static_restoration_exclusion :
    ¬∃z∈Chapter06.EpigraphMaster finalModel positiveF (finalFamily 0)
      (positiveHistoryDf 0) Set.univ,z.1.2=scalar 0 :=
  infeasible_restoration_master_exclusion (finalHistory 0) final_zero_fiber_empty
    final_restoration_minimum finalRestoration

/-- STATIC all-original-g restoration consumer; objective is sum of five slacks. -/
theorem thesis_static_restoration_exclusion :
    ¬∃z∈Chapter06.EpigraphMaster thesisModel positiveF (thesisFamily 0)
      (positiveHistoryDf 0) Set.univ,z.1.2=scalar 0 :=
  infeasible_restoration_master_exclusion (thesisHistory 0) thesis_zero_fiber_empty
    thesis_restoration_minimum thesisRestoration

theorem active_master_lower {z : P × ℝ}
    (hz : z∈Chapter06.EpigraphMaster activeModel activeF activeFamily
      activeHistoryDf Set.univ) (hy : z.1.2=scalar 1) : 0≤z.2 := by
  have hh := fixed_solution_master_lower activeHistory active_fiber_minimum activeFixed hz hy
  simpa [activeF,scalar] using hh

theorem final_source_containment (b : ℝ) {q : P}
    (hq : q∈finalModel.feasibleOn Set.univ) :
    (q,positiveF q)∈Chapter06.EpigraphMaster finalModel positiveF (finalFamily b)
      (positiveHistoryDf b) Set.univ :=
  Chapter06.source_feasible_epigraph_in_master finalModel positiveF (finalFamily b)
    (positiveHistoryDf b) Set.univ (fun _ => positiveG_convex) positiveF_convex
    (fun _ => Set.mem_univ _) (fun i j _ => (finalHistory b).g_derivative i j)
    (finalHistory b).f_derivative hq

theorem thesis_source_containment (b : ℝ) {q : P}
    (hq : q∈thesisModel.feasibleOn Set.univ) :
    (q,positiveF q)∈Chapter06.EpigraphMaster thesisModel positiveF (thesisFamily b)
      (positiveHistoryDf b) Set.univ :=
  Chapter06.source_feasible_epigraph_in_master thesisModel positiveF (thesisFamily b)
    (positiveHistoryDf b) Set.univ thesis_convex positiveF_convex
    (fun _ => Set.mem_univ _) (fun i j _ => (thesisHistory b).g_derivative i j)
    (thesisHistory b).f_derivative hq

theorem active_source_containment {q : P}
    (hq : q∈activeModel.feasibleOn Set.univ) :
    (q,activeF q)∈Chapter06.EpigraphMaster activeModel activeF activeFamily
      activeHistoryDf Set.univ :=
  Chapter06.source_feasible_epigraph_in_master activeModel activeF activeFamily
    activeHistoryDf Set.univ active_convex activeF_convex
    (fun _ => Set.mem_univ _) (fun i j _ => activeHistory.g_derivative i j)
    activeHistory.f_derivative hq

theorem final_master_nonvacuity (b : ℝ) :
    (pt (1/2) 1,(5/4:ℝ))∈Chapter06.EpigraphMaster finalModel positiveF (finalFamily b)
      (positiveHistoryDf b) Set.univ := by
  have hh := final_source_containment b final_original_minimum.1
  norm_num [positiveF,pt,scalar] at hh ⊢
  exact hh

theorem thesis_master_nonvacuity (b : ℝ) :
    (pt (1/2) 1,(5/4:ℝ))∈Chapter06.EpigraphMaster thesisModel positiveF (thesisFamily b)
      (positiveHistoryDf b) Set.univ := by
  have hh := thesis_source_containment b thesis_original_minimum.1
  norm_num [positiveF,pt,scalar] at hh ⊢
  exact hh

theorem active_original_feasible : pt 1 1∈activeModel.feasibleOn Set.univ := by
  refine ⟨⟨⟨Set.mem_univ _,activeFixed.primal.2⟩,activeFixed.primal.1⟩,?_⟩
  exact ⟨fun _ => 1,by norm_num [IntegerBox,activeModel,scalar],by ext i; norm_num [pt,scalar]⟩

theorem active_master_nonvacuity :
    (pt 1 1,(0:ℝ))∈Chapter06.EpigraphMaster activeModel activeF activeFamily
      activeHistoryDf Set.univ := by
  simpa [activeF,pt,scalar] using active_source_containment active_original_feasible

theorem restoration_values :
    restCost (n:=1) (l:=1) (weightedInsert (scalar (1/2)) (scalar (1/4)))=(1/4:ℝ) ∧
    restCost (n:=1) (l:=5) (weightedInsert (scalar (1/2)) thesisSlack)=(1/4:ℝ) ∧
    (∑j,thesisRestoration.lambda j)=2 := by
  norm_num [restCost_insert,scalar,Fin.sum_univ_one,thesisSlack,thesisRestoration,
    thesisLambda,Fin.sum_univ_succ]

theorem thesis_literal_master_lower {z : P × ℝ}
    (hz : z∈sourceMaster thesisModel positiveF (thesisFamily 1) (positiveHistoryDf 1))
    (hy : z.1.2=scalar 1) : (5/4:ℝ)≤z.2 := by
  rw [thesis_source_master_identity] at hz
  exact thesis_master_lower hz hy

theorem thesis_literal_static_exclusion :
    ¬∃z∈sourceMaster thesisModel positiveF (thesisFamily 0) (positiveHistoryDf 0),
      z.1.2=scalar 0 := by
  rw [thesis_source_master_identity]
  exact thesis_static_restoration_exclusion

theorem active_literal_master_lower {z : P × ℝ}
    (hz : z∈sourceMaster activeModel activeF activeFamily activeHistoryDf)
    (hy : z.1.2=scalar 1) : 0≤z.2 := by
  rw [active_source_master_identity] at hz
  exact active_master_lower hz hy

end Chapter03.OAKKT.Controls
