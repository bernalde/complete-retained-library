module

public import Chapter02DICOPTProcedureExamples
public import Chapter02DICOPTMixedExactness
public import Chapter02DICOPTSupplementalControls

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
namespace Chapter02DICOPTExamples

/-- Concrete applications retain primal/dual KKT data, global fixed-slice minima,
    every-minimizer slack exactness, and the separately justified nonlinear minimum. -/
def AnalyticTransfer {n m e l r : ℕ} {d : Data n m e l r}
    {x : RealVector n} {y : RealVector m} (k : FixedKKT d x y) (w : Weights k) : Prop :=
  Nonempty (HardKKT k (x,k.alpha)) ∧
  IsMinimizer (hardFeasible k) (hardObjective k) (x,k.alpha) ∧
  Nonempty (APKKT k w (apAnchor k)) ∧
  IsMinimizer (apFeasible k) (apObjective k w) (apAnchor k) ∧
  (∀ z, IsMinimizer (apFeasible k) (apObjective k w) z →
    z.s=0 ∧ (∀ i,z.p i=0) ∧ ∀ i,z.q i=0) ∧
  IsMinimizer (d.fiber y) (fun z => d.objective z y) x

theorem analyticTransfer_of {n m e l r : ℕ} {d : Data n m e l r}
    {x : RealVector n} {y : RealVector m} (k : FixedKKT d x y) (w : Weights k)
    (hc : SignedConvex d k) : AnalyticTransfer k w := by
  have hh := source_signed_hard_transfer k
  have ha := source_separate_slack_transfer k w
  exact ⟨hh.1,hh.2,ha.1,ha.2.1,ha.2.2.2,k.global_min hc⟩

structure NonlinearDriverAndLimits : Prop where
  nonlinear_relaxed : IsMinimizer nonlinearData.relaxed
    (fun z => nonlinearData.objective z.1 z.2) (scalar (5/6),scalar (55/72))
  nonlinear_selector : Nonempty (Selector nonlinearData)
  nonlinear_run : ∀ choose : Selector nonlinearData, ∃ output,
    procedure nonlinearData nonlinearInitialization choose=some output ∧
    output.result=.solution (scalar 1,scalar 1) ∧
    output.binarySolves≤2 ∧ output.masterDecisions≤3 ∧
    ReturnCertificate nonlinearData output.result
  infeasible_relaxation : infeasibleData.relaxed.Nonempty
  infeasible_original : infeasibleData.original=∅
  infeasible_selector : Nonempty (Selector infeasibleData)
  infeasible_run : ∀ choose : Selector infeasibleData, ∃ output,
    procedure infeasibleData infeasibleInitialization choose=some output ∧
    output.result=.infeasible ∧ output.binarySolves≤2 ∧ output.masterDecisions≤3 ∧
    ReturnCertificate infeasibleData output.result
  actual_empty_step : ∀ b : BVector 1,
    Continue infeasibleData (initialState infeasibleInitial)
      (append infeasibleData (initialState infeasibleInitial) (infeasibleReply b)) ∧
    (append infeasibleData (initialState infeasibleInitial) (infeasibleReply b)).incumbent=none ∧
    b ∈ (append infeasibleData (initialState infeasibleInitial) (infeasibleReply b)).seen
  fractional_history_link : infeasibleRelaxedAnchor.toAnchor=infeasibleInitial
  actual_recursive_empty_branch : ∀ b : BVector 1,
    ∃ choose : Selector infeasibleData,
      run infeasibleData choose 3 (initialState infeasibleInitial)
        (initial_invariant infeasibleInitial) =
      (run infeasibleData choose 2
        (append infeasibleData (initialState infeasibleInitial) (infeasibleReply b))
        (continue_invariant infeasibleData (initial_invariant infeasibleInitial)
          (infeasible_actual_first_step b).1)).map (fun out => (out.1,out.2+1))
  positive_transfer : AnalyticTransfer positiveKKT positiveWeights
  negative_transfer : AnalyticTransfer negativeKKT negativeWeights
  zero_transfer : AnalyticTransfer zeroKKT zeroWeights
  signed_rows : ∀ x : V,
    eqTangent (signData 1 1) positiveKKT.jet positiveKKT.lambda 0 x (scalar 0)=2*(x 0-1) ∧
    eqTangent (signData (-1) 1) negativeKKT.jet negativeKKT.lambda 0 x (scalar 0)=2*(x 0-1) ∧
    eqTangent (signData 1 0) zeroKKT.jet zeroKKT.lambda 0 x (scalar 0)=0
  zero_row_limit : (scalar 0,0) ∈ hardFeasible zeroKKT ∧
    ¬ (signData 1 0).Feasible (scalar 0) (scalar 0)
  boundary_nonzero :
    IsMinimizer (apFeasible infeasibleKKT) (boundaryObjective 1) (boundaryPoint 1) ∧
    (boundaryPoint 1).s≠0
  below_boundary : ∀ w M : ℝ, w<1 →
    ∃ z ∈ apFeasible infeasibleKKT, boundaryObjective w z < M
  mixed_fixed_transfer : AnalyticTransfer mixedKKT mixedAnchor.weights
  mixed_original_min :
    IsMinimizer mixedData.original (fun z => mixedData.objective z.1 z.2)
      (scalar 0,scalar 0)
  mixed_master_min : IsMinimizer (masterFeasible mixedData [mixedAnchor] ∅)
    (masterObjective mixedData [mixedAnchor]) mixedPoint
  mixed_limit : mixedPoint.q (0:Fin 1) 0=1 ∧
    masterObjective mixedData [mixedAnchor] mixedPoint = -1 ∧
    mixedData.objective (scalar 0) (scalar 0)=0 ∧
    mixedAnchor.weights.ineq 0 > |mixedAnchor.kkt.mu 0|
  substantiveSupplementalControls : Chapter02DICOPTSupplemental.SupplementalControls

/-- Fully instantiated nonlinear and infeasible procedures, plus genuine source
    sign/weight/mixed-assignment controls. No numerical solver is represented. -/
theorem nonlinear_driver_and_limits : NonlinearDriverAndLimits where
  nonlinear_relaxed := nonlinear_relaxed_minimum
  nonlinear_selector := nonlinear_procedure_all_choices.1
  nonlinear_run := nonlinear_procedure_all_choices.2
  infeasible_relaxation := infeasible_relaxed_nonempty
  infeasible_original := infeasible_original_empty
  infeasible_selector := infeasible_procedure_all_choices.1
  infeasible_run := infeasible_procedure_all_choices.2
  actual_empty_step := infeasible_actual_first_step
  fractional_history_link := rfl
  actual_recursive_empty_branch := infeasible_actual_first_run
  positive_transfer := analyticTransfer_of _ _ positive_convex
  negative_transfer := analyticTransfer_of _ _ negative_convex
  zero_transfer := analyticTransfer_of _ _ zero_convex
  signed_rows := sign_tangent_controls
  zero_row_limit := zero_sign_drops_original_equality
  boundary_nonzero := weight_one_nonzero_minimum
  below_boundary := weight_below_one_unbounded
  mixed_fixed_transfer := analyticTransfer_of _ _ mixedAnchor.convex
  mixed_original_min := mixed_original_minimum
  mixed_master_min := mixed_point_minimum
  mixed_limit := mixed_positive_slack_and_gap
  substantiveSupplementalControls := Chapter02DICOPTSupplemental.supplemental_controls

end Chapter02DICOPTExamples
#print axioms Chapter02DICOPTExamples.nonlinear_driver_and_limits
