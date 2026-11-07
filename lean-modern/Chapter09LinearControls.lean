module

public import Chapter09Linear
public import Chapter09NonlinearControls
public import Chapter09SequentialControls

@[expose] public section

/-! Exact boundary controls; no experiment or source-wide acceptance. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Source

theorem zero_row_residual_control :
    ((0 : ℝ) + rowSlack 0 - 1) ^ 2 = 0 := by norm_num [rowSlack]

theorem one_row_residual_control :
    ((1 : ℝ) + rowSlack 1 - 1) ^ 2 = 0 := by norm_num [rowSlack]

theorem two_row_residual_control :
    ((2 : ℝ) + rowSlack 2 - 1) ^ 2 = 1 := by norm_num [rowSlack]

theorem noncanonical_row_slack_control :
    ((1 : ℝ) + 1 - 1) ^ 2 > ((1 : ℝ) + rowSlack 1 - 1) ^ 2 := by
  norm_num [rowSlack]

/-- The natural-count hypothesis in the row bound cannot be silently dropped. -/
theorem real_count_pair_bound_fails :
    ((3 / 2 : ℝ) - 1) ^ 2 < (3 / 2 : ℝ) * ((3 / 2 : ℝ) - 1) / 2 := by
  norm_num

end Chapter09.Source

namespace Chapter09.Source.LinearControls
open Chapter09.Source

theorem zero_vertices (G : Graph 0) (k : ℕ) (c1 c2 : ℝ) :
    qLinear G k c1 c2 = 0 := by
  obtain ⟨z, hz⟩ := qLinear_attained G k c1 c2
  simpa [lScore, edgePenalty, vertexPenalty] using hz.symm

theorem enough_colors (n k : ℕ) (G : Graph n) (hnk : n ≤ k)
    (c1 c2 : ℝ) (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) : qLinear G k c1 c2 = n := by
  rw [qLinear_eq_alpha G k c1 c2 hc1 hc2, Controls.enough_colors_alpha G hnk]

theorem edge_unit_joint_maximum :
    IsLMax Chapter09.SequentialControls.edgeGraph 1 1
      (canonicalLift Chapter09.SequentialControls.edgeGraph Chapter09.SequentialControls.edgeTie) := by
  intro z
  exact (lScore_le_uScore _ 1 1 (by norm_num) (by norm_num) z).trans
    ((Chapter09.SequentialControls.edge_tie_maximum z.1).trans_eq
      (lScore_canonical_rowCount_le_two _ 1 1 _ (by decide)).symm)

/-- The source linear corollary is instantiated with an actual globally
maximizing infeasible x projection and its complete, concrete scan lists. -/
theorem source_unit_corollary :
    let G := Chapter09.SequentialControls.edgeGraph
    let S := Chapter09.SequentialControls.edgeTie
    let LE := Chapter09.SequentialControls.edgeList1
    let LV := Chapter09.SequentialControls.slotList1
    qLinear G 1 1 1 = alpha G 1 ∧ Feasible G (Chapter09.Sequential.algorithm LE LV S) ∧
      ((Chapter09.Sequential.algorithm LE LV S).card : ℝ) = alpha G 1 := by
  exact corollary_9_3_2 _ (by decide) 1 1 le_rfl le_rfl (Or.inl rfl)
    _ _ (by decide) (by decide) (by decide) _ edge_unit_joint_maximum

theorem unit_projection_infeasible :
    ¬ Feasible Chapter09.SequentialControls.edgeGraph
      (canonicalLift Chapter09.SequentialControls.edgeGraph Chapter09.SequentialControls.edgeTie).1 :=
  Chapter09.SequentialControls.edge_tie_infeasible

theorem k1_zero_color_penalty (G : Graph 2) : qLinear G 1 2 0 = alpha G 1 :=
  qLinear_one_color G 2 0 (by norm_num) le_rfl

theorem strict_optimizer_exists :
    ∃ z : LState Controls.twoVertexEdge 1, IsLMax Controls.twoVertexEdge 2 0 z ∧
      Feasible Controls.twoVertexEdge z.1 ∧ z.1.card = 1 := by
  obtain ⟨z,hz⟩ := qLinear_attained Controls.twoVertexEdge 1 2 0
  have hm := (isLMax_iff_value _ 2 0 z).mpr hz
  obtain ⟨hf,hc⟩ := linear_one_color_strict _ 2 0 (by norm_num) le_rfl z hm
  rw [Controls.edge_one_color_alpha] at hc
  exact ⟨z,hm,hf,by exact_mod_cast hc⟩

def badSlackState : LState (Controls.emptyGraph 1) 1 :=
  (Finset.univ, fun _ => false, fun _ => true)

theorem badSlackState_value (c1 c2 : ℝ) :
    lScore (Controls.emptyGraph 1) c1 c2 badSlackState = 1 - c2 := by
  have he : edgePenalty (Controls.emptyGraph 1) badSlackState.1 badSlackState.2.1 = 0 := by
    change (∑ er : EdgeIndex (Controls.emptyGraph 1) 1,
      edgeResidual (Controls.emptyGraph 1) badSlackState.1 badSlackState.2.1 er ^ 2) = 0
    apply Finset.sum_eq_zero
    intro er _
    exact False.elim (Finset.notMem_empty _ er.1.property)
  unfold lScore
  rw [he]
  norm_num [badSlackState, vertexPenalty, flag, boolValue, Fin.sum_univ_one]

/-- Unlike the nonlinear k=1 model, negative linear row-slack weights can
reward a deliberately noncanonical slack and destroy value equivalence. -/
theorem negative_k1_color_penalty_fails :
    alpha (Controls.emptyGraph 1) 1 < qLinear (Controls.emptyGraph 1) 1 2 (-1) := by
  have h := le_qLinear (Controls.emptyGraph 1) 2 (-1) badSlackState
  rw [badSlackState_value] at h
  rw [Controls.empty_graph_alpha 1 1 (by decide)]
  norm_num at *
  linarith

theorem positive_noncanonical_slack_is_suboptimal :
    lScore (Controls.emptyGraph 1) 2 2 badSlackState < qLinear (Controls.emptyGraph 1) 1 2 2 := by
  rw [badSlackState_value, qLinear_eq_alpha _ 1 2 2 (by norm_num) (by norm_num),
    Controls.empty_graph_alpha 1 1 (by decide)]
  norm_num

def pathGraph : Graph 3 := ⟨{(0,1),(1,2)}, by
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl <;> decide⟩

/-- Edges are stored with i<j, but the middle vertex has incident neighbors
in both directions. The full penalty sums both source constraints. -/
theorem both_incident_orientations :
    Adj pathGraph 1 0 ∧ Adj pathGraph 1 2 ∧
    edgePenalty pathGraph (Finset.univ : Finset (Slot 3 1))
      (canonicalEdgeSlack pathGraph Finset.univ) = 2 := by
  refine ⟨by simp [Adj,pathGraph], by simp [Adj,pathGraph], ?_⟩
  rw [edgePenalty_canonical]
  norm_num [edgeProducts,pathGraph,flag,Fin.sum_univ_one]

theorem middle_deletion_canonical_penalty :
    edgePenalty pathGraph ((Finset.univ : Finset (Slot 3 1)).erase (1,0))
      (canonicalEdgeSlack pathGraph (Finset.univ.erase (1,0))) = 0 := by
  rw [edgePenalty_canonical]
  norm_num [edgeProducts,pathGraph,flag,Fin.sum_univ_one]

end Chapter09.Source.LinearControls

#print axioms Chapter09.Source.zero_row_residual_control
#print axioms Chapter09.Source.one_row_residual_control
#print axioms Chapter09.Source.two_row_residual_control
#print axioms Chapter09.Source.noncanonical_row_slack_control
#print axioms Chapter09.Source.real_count_pair_bound_fails
#print axioms Chapter09.Source.LinearControls.zero_vertices
#print axioms Chapter09.Source.LinearControls.enough_colors
#print axioms Chapter09.Source.LinearControls.edge_unit_joint_maximum
#print axioms Chapter09.Source.LinearControls.source_unit_corollary
#print axioms Chapter09.Source.LinearControls.unit_projection_infeasible
#print axioms Chapter09.Source.LinearControls.k1_zero_color_penalty
#print axioms Chapter09.Source.LinearControls.strict_optimizer_exists
#print axioms Chapter09.Source.LinearControls.negative_k1_color_penalty_fails
#print axioms Chapter09.Source.LinearControls.positive_noncanonical_slack_is_suboptimal
#print axioms Chapter09.Source.LinearControls.both_incident_orientations
#print axioms Chapter09.Source.LinearControls.middle_deletion_canonical_penalty
