module

public import Chapter04FiberGap
public import Chapter04SlaterBallControl

@[expose] public section

/-! Applications of both attained-fiber endpoints to the accepted S005 control.
The existing model has x ∈ [0,1], integer y = 0, nonlinear row x²+y² ≤ 4,
objective x and the exact optimizer (0,0). Its only feasible integer fiber is
y = 0, so these applications cover the empty-suboptimal branch and trivial
polishing case. They do not instantiate the nonempty-suboptimal branch or an
algorithm execution. No new model or uniqueness assertion is introduced. -/

noncomputable section
open Chapter02
namespace Chapter04.CenterCut.Control

/-- The attained-value window specialized to the existing accepted model. -/
theorem attained_fiber_value_gap_control :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ IntegerBox model.lo model.hi,
      ∀ p : P,
        IsMinimizer (model.fixedNonlinearFiber (oaIntCast y)) model.objective p →
        model.objective p = model.objective (pt 0 0) ∨
          model.objective (pt 0 0) + ε < model.objective p := by
  exact source_attained_fiber_value_gap model rows_continuous compact_base
    (pt 0 0) zero_minimizer

/-- The existence and every-exact-choice polishing conclusion on the same model. -/
theorem near_optimal_fiber_polishing_control :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : P, q ∈ model.feasibleOn Set.univ →
        model.objective q ≤ model.objective (pt 0 0) + ε →
        (∃ p : P,
          IsMinimizer (model.fixedNonlinearFiber q.2) model.objective p) ∧
        ∀ p : P,
          IsMinimizer (model.fixedNonlinearFiber q.2) model.objective p →
          IsMinimizer (model.feasibleOn Set.univ) model.objective p ∧
          model.objective p = model.objective (pt 0 0) := by
  exact source_near_optimal_fiber_polishing model rows_continuous compact_base
    (pt 0 0) zero_minimizer

end Chapter04.CenterCut.Control
