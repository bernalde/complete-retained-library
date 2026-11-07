module

public import Chapter09Sharpness
public import Chapter09Nonlinear
public import Chapter09Linear

@[expose] public section

/-! Literal-objective sharpness consequences and boundary controls.
The universal quantifiers vary the number of vertices; no individual graph is
claimed to require each threshold. These repair the ordered-factor and k=1
necessity defects and do not certify the source's false wider propositions. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Source

/-- The literal ordered nonlinear objective of the parametric clique witness. -/
theorem nScore_cliqueBad (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ) :
    nScore (cliqueGraph (k+1)) c1 c2 (cliqueBad k hk) = (k : ℝ) + 1 - c1 := by
  rw [nScore_eq_uScore, uScore_cliqueBad]

/-- For each k≥1, the complete graph on k+1 vertices defeats every c1<1.
The full feasible optimum is the proved value k, not a supplied hypothesis. -/
theorem nonlinear_clique_counterfamily (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ) (hc1 : c1 < 1) :
    alpha (cliqueGraph (k+1)) k < nScore (cliqueGraph (k+1)) c1 c2 (cliqueBad k hk) := by
  rw [nScore_eq_uScore]
  exact cliqueBad_uScore_overshoot k hk c1 (2*c2) hc1

/-- The factor two follows from the proved literal ordered objective bridge. -/
theorem nScore_doubleColors (k : ℕ) (hk : 2 ≤ k) (c1 c2 : ℝ) :
    nScore (emptyGraph 1) c1 c2 (doubleColors k hk) = 2 - 2*c2 := by
  rw [nScore_eq_uScore, uScore_doubleColors]

theorem nonlinear_color_counterfamily (k : ℕ) (hk : 2 ≤ k) (c1 c2 : ℝ)
    (hc2 : c2 < 1/2) :
    alpha (emptyGraph 1) k < nScore (emptyGraph 1) c1 c2 (doubleColors k hk) := by
  rw [nScore_eq_uScore]
  exact doubleColors_uScore_overshoot k hk c1 (2*c2) (by linarith)

/-- The unit edge boundary has an infeasible globally maximizing literal assignment. -/
theorem cliqueBad_nonlinear_global_tie (k : ℕ) (hk : 0 < k) (c2 : ℝ) (hc2 : 1 ≤ 2*c2) :
    ¬ Feasible (cliqueGraph (k+1)) (cliqueBad k hk) ∧
    nScore (cliqueGraph (k+1)) 1 c2 (cliqueBad k hk) = alpha (cliqueGraph (k+1)) k ∧
    ∀ T : Finset (Slot (k+1) k),
      nScore (cliqueGraph (k+1)) 1 c2 T ≤ nScore (cliqueGraph (k+1)) 1 c2 (cliqueBad k hk) := by
  simpa only [nScore_eq_uScore] using cliqueBad_uScore_global_tie k hk (2*c2) hc2

/-- The ordered color boundary c2=1/2 gives a global infeasible optimum tie. -/
theorem doubleColors_nonlinear_global_tie (k : ℕ) (hk : 2 ≤ k) (c1 : ℝ) :
    ¬ Feasible (emptyGraph 1) (doubleColors k hk) ∧
    nScore (emptyGraph 1) c1 (1/2) (doubleColors k hk) = alpha (emptyGraph 1) k ∧
    ∀ T : Finset (Slot 1 k),
      nScore (emptyGraph 1) c1 (1/2) T ≤ nScore (emptyGraph 1) c1 (1/2) (doubleColors k hk) := by
  have he : (2 : ℝ) * (1/2) = 1 := by norm_num
  simpa only [nScore_eq_uScore, he] using doubleColors_uScore_global_tie k hk c1

/-- A concrete two-color, one-vertex global boundary example. -/
theorem nonlinear_two_color_boundary_control :
    ¬ Feasible (emptyGraph 1) (doubleColors 2 (by decide)) ∧
    nScore (emptyGraph 1) 2 (1/2) (doubleColors 2 (by decide)) = 1 ∧
    ∀ T : Finset (Slot 1 2), nScore (emptyGraph 1) 2 (1/2) T ≤ 1 := by
  obtain ⟨hbad,hvalue,hglobal⟩ := doubleColors_nonlinear_global_tie 2 (by decide) 2
  have hv : nScore (emptyGraph 1) 2 (1/2) (doubleColors 2 (by decide)) = 1 := by
    simpa [alpha_one_vertex] using hvalue
  exact ⟨hbad,hv,fun T => (hglobal T).trans_eq hv⟩


/-- A strict counterexample for the actual attained nonlinear maximum. -/
theorem nonlinear_clique_value_failure (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ) (hc1 : c1 < 1) :
    alpha (cliqueGraph (k+1)) k < qNonlinear (cliqueGraph (k+1)) k c1 c2 :=
  (nonlinear_clique_counterfamily k hk c1 c2 hc1).trans_le
    (nScore_le_qNonlinear _ c1 c2 (cliqueBad k hk))

theorem nonlinear_color_value_failure (k : ℕ) (hk : 2 ≤ k) (c1 c2 : ℝ) (hc2 : c2 < 1/2) :
    alpha (emptyGraph 1) k < qNonlinear (emptyGraph 1) k c1 c2 :=
  (nonlinear_color_counterfamily k hk c1 c2 hc2).trans_le
    (nScore_le_qNonlinear _ c1 c2 (doubleColors k hk))

/-- Corrected universal value threshold: n and the graph vary, with k fixed.
This does not assert necessity on each individual graph or fixed small n. -/
theorem nonlinear_universal_value_iff (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ)
    (_hc1 : 0 < c1) (_hc2 : 0 < c2) :
    (∀ (n : ℕ) (G : Graph n), qNonlinear G k c1 c2 = alpha G k) ↔
      1 ≤ c1 ∧ (k = 1 ∨ 1/2 ≤ c2) := by
  constructor
  · intro h
    have h1 : 1 ≤ c1 := by
      by_contra hn
      have hf := nonlinear_clique_value_failure k hk c1 c2 (lt_of_not_ge hn)
      rw [h (k+1) (cliqueGraph (k+1))] at hf
      exact (lt_irrefl _) hf
    refine ⟨h1,?_⟩
    by_cases hk1 : k = 1
    · exact Or.inl hk1
    · right
      by_contra hn
      have hk2 : 2 ≤ k := by omega
      have hf := nonlinear_color_value_failure k hk2 c1 c2 (lt_of_not_ge hn)
      rw [h 1 (emptyGraph 1)] at hf
      exact (lt_irrefl _) hf
  · rintro ⟨h1,h2⟩ n G
    rcases h2 with hk1 | h2
    · subst k
      exact qNonlinear_one_color G c1 c2 h1
    · exact qNonlinear_eq_alpha G k c1 c2 h1 (by linarith)

theorem cliqueBad_nonlinear_attained_tie (k : ℕ) (hk : 0 < k) (c2 : ℝ) (hc2 : 1 ≤ 2*c2) :
    ¬ Feasible (cliqueGraph (k+1)) (cliqueBad k hk) ∧
    nScore (cliqueGraph (k+1)) 1 c2 (cliqueBad k hk) = qNonlinear (cliqueGraph (k+1)) k 1 c2 ∧
    qNonlinear (cliqueGraph (k+1)) k 1 c2 = alpha (cliqueGraph (k+1)) k := by
  obtain ⟨hbad,hvalue,hmax⟩ := cliqueBad_nonlinear_global_tie k hk c2 hc2
  have hq := (isNMax_iff _ 1 c2 (cliqueBad k hk)).mp hmax
  exact ⟨hbad,hq,hq.symm.trans hvalue⟩

theorem doubleColors_nonlinear_attained_tie (k : ℕ) (hk : 2 ≤ k) (c1 : ℝ) :
    ¬ Feasible (emptyGraph 1) (doubleColors k hk) ∧
    nScore (emptyGraph 1) c1 (1/2) (doubleColors k hk) = qNonlinear (emptyGraph 1) k c1 (1/2) ∧
    qNonlinear (emptyGraph 1) k c1 (1/2) = alpha (emptyGraph 1) k := by
  obtain ⟨hbad,hvalue,hmax⟩ := doubleColors_nonlinear_global_tie k hk c1
  have hq := (isNMax_iff _ c1 (1/2) (doubleColors k hk)).mp hmax
  exact ⟨hbad,hq,hq.symm.trans hvalue⟩

/-- c2=3/4 is below the source's claimed unit cutoff but universally sufficient. -/
theorem nonlinear_three_quarters_all_graphs (n : ℕ) (G : Graph n) :
    qNonlinear G 2 2 (3/4) = alpha G 2 :=
  qNonlinear_eq_alpha G 2 2 (3/4) (by norm_num) (by norm_num)

/-- k=1 admits positive color penalties below both printed and corrected k≥2 cutoffs. -/
theorem nonlinear_one_color_small_penalty (n : ℕ) (G : Graph n) :
    qNonlinear G 1 2 (1/10) = alpha G 1 := qNonlinear_one_color G 2 (1/10) (by norm_num)


/-- Explicit canonical Boolean slacks realize the clique linear witness. -/
theorem lScore_cliqueBad (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ) :
    lScore (cliqueGraph (k+1)) c1 c2 (canonicalLift (cliqueGraph (k+1)) (cliqueBad k hk)) =
      (k : ℝ) + 1 - c1 := by
  rw [lScore_canonical_rowCount_le_two _ c1 c2 (cliqueBad k hk)
    (fun i => (rowCount_cliqueBad_le_one k hk i).trans (by decide)), uScore_cliqueBad]

/-- The isolated-vertex witness has its actual linear residual, not an assumed score. -/
theorem lScore_doubleColors (k : ℕ) (hk : 2 ≤ k) (c1 c2 : ℝ) :
    lScore (emptyGraph 1) c1 c2 (canonicalLift (emptyGraph 1) (doubleColors k hk)) = 2 - c2 := by
  rw [lScore_canonical_rowCount_le_two _ c1 c2 (doubleColors k hk) (by intro i; simp),
    uScore_doubleColors]

/-- The displayed two-color linear witness uses t=0 at the actual vertex. -/
theorem doubleColors_canonical_t_zero (k : ℕ) (hk : 2 ≤ k) (i : Fin 1) :
    boolValue ((canonicalLift (emptyGraph 1) (doubleColors k hk)).2.2 i) = 0 := by
  simp [canonicalLift, canonicalVertexSlack, boolValue]

/-- No edge-slack coordinates exist on this graph. -/
theorem doubleColors_no_edge_index (k : ℕ) (er : EdgeIndex (emptyGraph 1) k) : False := by
  exact Finset.notMem_empty er.1.val er.1.property

theorem linear_clique_counterfamily (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ) (hc1 : c1 < 1) :
    alpha (cliqueGraph (k+1)) k <
      lScore (cliqueGraph (k+1)) c1 c2 (canonicalLift (cliqueGraph (k+1)) (cliqueBad k hk)) := by
  rw [alpha_clique, lScore_cliqueBad]
  linarith

theorem linear_color_counterfamily (k : ℕ) (hk : 2 ≤ k) (c1 c2 : ℝ) (hc2 : c2 < 1) :
    alpha (emptyGraph 1) k < lScore (emptyGraph 1) c1 c2 (canonicalLift (emptyGraph 1) (doubleColors k hk)) := by
  rw [alpha_one_vertex k (by omega), lScore_doubleColors]
  linarith

theorem linear_clique_value_failure (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ) (hc1 : c1 < 1) :
    alpha (cliqueGraph (k+1)) k < qLinear (cliqueGraph (k+1)) k c1 c2 :=
  (linear_clique_counterfamily k hk c1 c2 hc1).trans_le
    (le_qLinear _ c1 c2 (canonicalLift _ (cliqueBad k hk)))

theorem linear_color_value_failure (k : ℕ) (hk : 2 ≤ k) (c1 c2 : ℝ) (hc2 : c2 < 1) :
    alpha (emptyGraph 1) k < qLinear (emptyGraph 1) k c1 c2 :=
  (linear_color_counterfamily k hk c1 c2 hc2).trans_le
    (le_qLinear _ c1 c2 (canonicalLift _ (doubleColors k hk)))

/-- Corrected universal linear value thresholds on the actual x,s,t domain.
The number of vertices varies; k is fixed and positive. -/
theorem linear_universal_value_iff (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ)
    (_hc1 : 0 < c1) (hc2 : 0 < c2) :
    (∀ (n : ℕ) (G : Graph n), qLinear G k c1 c2 = alpha G k) ↔
      1 ≤ c1 ∧ (k = 1 ∨ 1 ≤ c2) := by
  constructor
  · intro h
    have h1 : 1 ≤ c1 := by
      by_contra hn
      have hf := linear_clique_value_failure k hk c1 c2 (lt_of_not_ge hn)
      rw [h (k+1) (cliqueGraph (k+1))] at hf
      exact (lt_irrefl _) hf
    refine ⟨h1,?_⟩
    by_cases hk1 : k = 1
    · exact Or.inl hk1
    · right
      by_contra hn
      have hk2 : 2 ≤ k := by omega
      have hf := linear_color_value_failure k hk2 c1 c2 (lt_of_not_ge hn)
      rw [h 1 (emptyGraph 1)] at hf
      exact (lt_irrefl _) hf
  · rintro ⟨h1,h2⟩ n G
    rcases h2 with hk1 | h2
    · subst k
      exact qLinear_one_color G c1 c2 h1 hc2.le
    · exact qLinear_eq_alpha G k c1 c2 h1 h2

/-- An actual globally maximizing infeasible triple at the unit edge boundary. -/
theorem cliqueBad_linear_attained_tie (k : ℕ) (hk : 0 < k) (c2 : ℝ) (hc2 : 1 ≤ c2) :
    ¬ Feasible (cliqueGraph (k+1)) (cliqueBad k hk) ∧
    lScore (cliqueGraph (k+1)) 1 c2 (canonicalLift (cliqueGraph (k+1)) (cliqueBad k hk)) =
      qLinear (cliqueGraph (k+1)) k 1 c2 ∧
    qLinear (cliqueGraph (k+1)) k 1 c2 = alpha (cliqueGraph (k+1)) k := by
  have hv : lScore (cliqueGraph (k+1)) 1 c2
      (canonicalLift (cliqueGraph (k+1)) (cliqueBad k hk)) = alpha (cliqueGraph (k+1)) k := by
    rw [lScore_cliqueBad, alpha_clique]; ring
  have hq := qLinear_eq_alpha (cliqueGraph (k+1)) k 1 c2 (by norm_num) hc2
  exact ⟨cliqueBad_not_feasible k hk, hv.trans hq.symm, hq⟩

/-- The color boundary c2=1 has an infeasible globally maximizing actual triple. -/
theorem doubleColors_linear_attained_tie (k : ℕ) (hk : 2 ≤ k) (c1 : ℝ) (hc1 : 0 ≤ c1) :
    ¬ Feasible (emptyGraph 1) (doubleColors k hk) ∧
    lScore (emptyGraph 1) c1 1 (canonicalLift (emptyGraph 1) (doubleColors k hk)) =
      qLinear (emptyGraph 1) k c1 1 ∧
    qLinear (emptyGraph 1) k c1 1 = alpha (emptyGraph 1) k := by
  obtain ⟨hbad,hvalue,hglobal⟩ := doubleColors_uScore_global_tie k hk c1
  have hmax : IsLMax (emptyGraph 1) c1 1 (canonicalLift (emptyGraph 1) (doubleColors k hk)) := by
    intro z
    calc
      lScore (emptyGraph 1) c1 1 z ≤ uScore (emptyGraph 1) c1 1 z.1 :=
        lScore_le_uScore _ c1 1 hc1 (by norm_num) z
      _ ≤ uScore (emptyGraph 1) c1 1 (doubleColors k hk) := hglobal z.1
      _ = lScore (emptyGraph 1) c1 1 (canonicalLift (emptyGraph 1) (doubleColors k hk)) := by
        rw [uScore_doubleColors, lScore_doubleColors]
  have hq := (isLMax_iff_value _ c1 1 (canonicalLift _ (doubleColors k hk))).mp hmax
  have hv : lScore (emptyGraph 1) c1 1 (canonicalLift (emptyGraph 1) (doubleColors k hk)) =
      alpha (emptyGraph 1) k := by
    rw [lScore_doubleColors, alpha_one_vertex k (by omega)]; norm_num
  exact ⟨hbad,hq,hq.symm.trans hv⟩

theorem linear_one_color_small_penalty (n : ℕ) (G : Graph n) :
    qLinear G 1 2 (1/10) = alpha G 1 :=
  qLinear_one_color G 2 (1/10) (by norm_num) (by norm_num)

theorem linear_two_color_boundary_control :
    qLinear (emptyGraph 1) 2 2 1 = 1 ∧
    lScore (emptyGraph 1) 2 1 (canonicalLift (emptyGraph 1) (doubleColors 2 (by decide))) = 1 ∧
    ¬ Feasible (emptyGraph 1) (doubleColors 2 (by decide)) := by
  obtain ⟨hbad,hscore,hq⟩ := doubleColors_linear_attained_tie 2 (by decide) 2 (by norm_num)
  have hv : qLinear (emptyGraph 1) 2 2 1 = 1 := by simpa [alpha_one_vertex] using hq
  exact ⟨hv,hscore.trans hv,hbad⟩

end Chapter09.Source
#print axioms Chapter09.Source.nonlinear_clique_counterfamily
#print axioms Chapter09.Source.nonlinear_color_counterfamily
#print axioms Chapter09.Source.cliqueBad_nonlinear_global_tie
#print axioms Chapter09.Source.doubleColors_nonlinear_global_tie
#print axioms Chapter09.Source.nonlinear_two_color_boundary_control

#print axioms Chapter09.Source.nonlinear_universal_value_iff
#print axioms Chapter09.Source.cliqueBad_nonlinear_attained_tie
#print axioms Chapter09.Source.doubleColors_nonlinear_attained_tie
#print axioms Chapter09.Source.nonlinear_three_quarters_all_graphs
#print axioms Chapter09.Source.nonlinear_one_color_small_penalty

#print axioms Chapter09.Source.linear_clique_counterfamily
#print axioms Chapter09.Source.linear_color_counterfamily
#print axioms Chapter09.Source.linear_universal_value_iff
#print axioms Chapter09.Source.cliqueBad_linear_attained_tie
#print axioms Chapter09.Source.doubleColors_linear_attained_tie
#print axioms Chapter09.Source.doubleColors_canonical_t_zero
#print axioms Chapter09.Source.doubleColors_no_edge_index
#print axioms Chapter09.Source.linear_one_color_small_penalty
#print axioms Chapter09.Source.linear_two_color_boundary_control
