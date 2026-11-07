module

public import Chapter04

@[expose] public section

private noncomputable def __migrationExample_Chapter04Examples_L3_N001 : Chapter04.OverwriteMaster 1 (5 / 4) :=
  Chapter04.overwrite_trial_master_optimal.1

private noncomputable def __migrationExample_Chapter04Examples_L6_N002 : Chapter02.IsMinimizer
    {x : ℝ | -3 ≤ x ∧ x ≤ 3 ∧ (x - 1)^2 - 1 ≤ 0} (fun x => x) 0 :=
  Chapter04.quadratic_fixed_minimizer

private noncomputable def __migrationExample_Chapter04Examples_L10_N003 : (1 + Chapter04.PositiveStep (1 / 2))^2 - 1 > 0 :=
  Chapter04.positive_step_stays_infeasible _ (by norm_num)

private noncomputable def __migrationExample_Chapter04Examples_L13_N004 : ((1 : ℝ) - 1)^2 - 1 < 0 ∧ -3 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 3 := by norm_num

private noncomputable def __migrationExample_Chapter04Examples_L15_N005 : 0 ≤ 1 - (1 : ℝ) / (2 * 2) ∧ 1 - (1 : ℝ) / (2 * 2) < 1 ∧
    (1 - (1 - (1 : ℝ) / (2 * 2))) * 2 = (1 : ℝ) / 2 :=
  Chapter04.epsilon_interpolation 1 2 (by norm_num) (by norm_num)
