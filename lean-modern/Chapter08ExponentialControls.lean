module

public import Chapter08ExponentialRows

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter08.Exponential.Controls

/-- A positive point and a nontrivial zero-face point exercise the actual geometric set. -/
theorem positive_and_boundary :
    ((1,1,0) : Space) ∈ positive ∧ ((2,0,-1) : Space) ∈ cone ∧
      ((2,0,-1) : Space) ∈ closure positive := by
  have hz : ((2,0,-1) : Space) ∈ cone := by
    change ExpCone 2 0 (-1)
    norm_num [exp_cone_zero]
  refine ⟨?_, hz, ?_⟩
  · norm_num [positive]
  · rwa [closure_positive]

/-- Exact distinct auxiliary values for nonzero softplus input. -/
theorem softplus_auxiliaries :
    (3/4 : ℝ)+(1/4 : ℝ) ≤ 1 ∧
      ExpCone (3/4) 1 (Real.log 3-Real.log 4) ∧
      ExpCone (1/4) 1 (-Real.log 4) := by
  norm_num [exp_cone_epigraph, Real.exp_sub, Real.exp_neg,
    Real.exp_log (by norm_num : 0 < (3:ℝ)), Real.exp_log (by norm_num : 0 < (4:ℝ))]

theorem softplus_nonzero : Real.log (1+Real.exp (Real.log 3)) ≤ Real.log 4 := by
  apply (softplus_iff _ _).mpr
  exact ⟨3/4,1/4,softplus_auxiliaries⟩

/-- Fractional perspective scale, with both auxiliaries explicitly scaled. -/
theorem softplus_fractional :
    (1/2:ℝ)*Real.log (1+Real.exp (((1/2:ℝ)*Real.log 3)/(1/2))) ≤
      (1/2)*Real.log 4 := by
  apply (softplus_perspective_iff _ _ _ (by norm_num)).mpr
  refine ⟨3/8,1/8,by norm_num,?_,?_⟩
  · convert exp_cone_scaling _ _ _ (1/2) softplus_auxiliaries.2.1
      (by norm_num : 0 ≤ (1/2:ℝ)) using 1 <;> ring
  · convert exp_cone_scaling _ _ _ (1/2) softplus_auxiliaries.2.2
      (by norm_num : 0 ≤ (1/2:ℝ)) using 1 <;> ring

/-- The zero face accepts its exact bound and rejects a strictly smaller height. -/
theorem softplus_zero_boundary :
    softplusSystem 2 2 0 ∧ ¬softplusSystem 2 1 0 ∧ softplusSystem (-2) 0 0 := by
  norm_num [softplus_zero_iff]

/-- Nonzero scale, input, weight, affine right side and exact process auxiliary. -/
theorem process_nonzero :
    (∑ _j : Fin 1, (3:ℝ)*(Real.exp ((2*Real.log 2)/2)-1)) -
      (∑ _j : Fin 1, (3/(2*Real.log 2))*(2*Real.log 2)) ≤ 0 := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  apply (source_process_iff (fun _ : Fin 1 => 3) (fun _ => 2)
    (fun _ => 3/(2*Real.log 2)) (fun _ => 2*Real.log 2)
    (by intro j; norm_num) (by intro j; norm_num)).mpr
  refine ⟨fun _ => 1, ?_, ?_⟩
  · simp only [Fin.sum_univ_one]
    field_simp <;> norm_num
  · intro j
    apply (process_cone_iff _ _ _ (by norm_num)).mpr
    norm_num [Real.exp_log (by norm_num : 0 < (2:ℝ))]

/-- Negative arguments need genuinely free auxiliaries; nonnegativity would change this row. -/
theorem process_negative_auxiliary :
    Real.exp (-1)-1 < 0 ∧
      ExpCone (1*((Real.exp (-1)-1)+1)) 1 (-1) := by
  constructor
  · have h : Real.exp (-1) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    linarith
  · exact (process_cone_iff _ _ _ (by norm_num)).mpr (by simp)

/-- Zero weights and the empty row family are valid edge cases of the actual process bridge. -/
theorem process_zero_and_empty :
    (∃ u : Fin 1 → ℝ, (∑ j, (0:ℝ)*u j) ≤ 0 ∧
      ∀ j, ExpCone (1*(u j+1)) 1 (-1)) ∧
    (∃ u : Fin 0 → ℝ, (∑ j, (1:ℝ)*u j) ≤ 0 ∧
      ∀ j, ExpCone (1*(u j+1)) 1 1) := by
  constructor
  · apply (weighted_process_iff (fun _ : Fin 1 => 0) (fun _ => 1)
      (fun _ => -1) 0 (by intro j; norm_num) (by intro j; norm_num)).mp
    simp
  · apply (weighted_process_iff (fun _ : Fin 0 => 1) (fun _ => 1)
      (fun _ => 1) 0 (by intro j; norm_num) (by intro j; norm_num)).mp
    simp

/-- The random-row logarithmic domain is forced even with a negative affine slope. -/
theorem random_affine_nonzero :
    0 < (-1:ℝ)*(-3)+3 ∧
      Real.log 2+(∑ _j : Fin 1, (1:ℝ)*Real.log 3) ≤ Real.log ((-1)*(-3)+3) := by
  apply (source_random_log_iff 2 (-1) 3 (-3)
    (fun _ : Fin 1 => 1) (fun _ => Real.log 3) (by norm_num)).mp
  norm_num [Real.exp_log (by norm_num : 0 < (3:ℝ))]

/-- A nonpositive right side is excluded by the same primary random-log equivalence. -/
theorem random_zero_rhs_rejected : ¬ ((2:ℝ)*Real.exp 1 ≤ 0) := by
  rw [random_exponential_log_iff _ _ _ (by norm_num)]
  simp

end Chapter08.Exponential.Controls
