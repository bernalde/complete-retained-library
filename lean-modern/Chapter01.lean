module

public import Chapter03

@[expose] public section
/-! Two narrowly scoped context counterexamples: convex constraints do not
suffice for convex minimization, and smaller expected cost does not imply greater
probability of sampling a ground-cost outcome. No complexity/quantum-state theorem. -/
noncomputable section
namespace Chapter01

theorem constraints_alone_not_convex_objective :
    ¬ ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun x => -x^2) := by
  intro h
  have hh := h.2 (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  norm_num at hh

/-- Costs 0,1,1000,1001 occur in the two-bit linear QUBO y₁+1000y₂.
Distribution A has mass .99 at cost0 and .01 at cost1000, B has mass1 at cost1.
Both are probability distributions. The result is only this finite arithmetic. -/
theorem lower_expectation_not_higher_success :
    (0:ℝ) ≤ 99/100 ∧ (0:ℝ) ≤ 1/100 ∧ (99/100:ℝ)+1/100=1 ∧
    ((0:ℝ)*0+1*1+0*1000+0*1001) <
      ((99/100:ℝ)*0+0*1+(1/100)*1000+0*1001) ∧
    (0:ℝ) < 99/100 := by norm_num

/-- Two independent affine disjunctions: convexifying each separately leaves a
point excluded by the original intersection. This is the exact scalar witness. -/
theorem local_hulls_not_global_hull :
    ({(0:ℝ),2} : Set ℝ) ∩ {0,1} = {0} ∧
    (1:ℝ) ∈ convexHull ℝ ({0,2} : Set ℝ) ∩ convexHull ℝ ({0,1} : Set ℝ) ∧
    (1:ℝ) ∉ convexHull ℝ (({0,2} : Set ℝ) ∩ {0,1}) := by
  have hi : ({(0:ℝ),2} : Set ℝ) ∩ {0,1} = {0} := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0|h2,h0'|h1⟩
      · exact h0
      · exact h0
      · exact h0'
      · have h := h2.symm.trans h1; norm_num at h
    · intro h; exact ⟨Or.inl h,Or.inl h⟩
  refine ⟨hi,?_,?_⟩
  · constructor
    · have h0 : (0:ℝ) ∈ convexHull ℝ ({0,2} : Set ℝ) :=
        subset_convexHull ℝ _ (by simp)
      have h2 : (2:ℝ) ∈ convexHull ℝ ({0,2} : Set ℝ) :=
        subset_convexHull ℝ _ (by simp)
      have h := (convex_convexHull ℝ ({0,2} : Set ℝ)) h0 h2
        (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
        (show (1/2:ℝ)+1/2=1 by norm_num)
      simpa [smul_eq_mul] using h
    · exact subset_convexHull ℝ _ (by simp)
  · rw [hi,convexHull_singleton]; norm_num

end Chapter01
#print axioms Chapter01.constraints_alone_not_convex_objective
#print axioms Chapter01.lower_expectation_not_higher_success

#print axioms Chapter01.local_hulls_not_global_hull
