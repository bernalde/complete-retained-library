module

public import Chapter02FBBTContractionApplication
public import Chapter02FBBTSourceControl
public import Chapter02FBBTBoundaryControls

@[expose] public section

/-! One bundled control endpoint. Each field exposes actual model/operator/LP
or retained-original predicates; helper lemma counts are not certificate counts. -/
noncomputable section
open Chapter02 Chapter02FBBT
namespace Chapter02FBBTControls

structure QualifiedControls : Prop where
  auxiliaryIntervalsOrdered : ∀ {n m} (A : Chapter02FBBT.Matrix n m) (q0 : JointBounds n m)
    (p : LPAssignment n m), LPFeasible A q0 p → ∀ i j, p.zLo i j ≤ p.zHi i j
  boundary : Chapter02FBBTBoundary.BoundaryControls
  infiniteContraction : ∀ a : ℝ, 1 < a →
    SimultaneousConclusion (contractionMatrix a) (contractionBox 1) ∧
    limitBounds (contractionMatrix a) (contractionBox 1) = contractionBox 0 ∧
    (∀ k, 0 < width (rawRun (contractionMatrix a) (contractionBox 1) k)) ∧
    (∀ k, rawRun (contractionMatrix a) (contractionBox 1) (k+1) ≠
      rawRun (contractionMatrix a) (contractionBox 1) k) ∧
    LPFeasible (contractionMatrix a) (contractionBox 1)
      (canonicalAssignment (contractionMatrix a) (contractionBox 0))
  retainedSource : SourceTheory data integerCoordinates initialX ∧
    SourceConclusion data integerCoordinates initialX ∧
    sourceLimitX data initialX = tightenedX ∧
    IsMinimizer (data.feasible integerCoordinates ∩ members (sourceLimitX data initialX)) data.f optimum ∧
    data.f optimum = -1 ∧
    rawF data.coefficient (sourceInitial data initialX) (sourceInitial data initialX) = controlBox 1 ∧
    LPFeasible data.coefficient (sourceInitial data initialX)
      (canonicalAssignment data.coefficient (controlBox 1)) ∧
    (∀ i, (canonicalAssignment data.coefficient (controlBox 1)).zLo i 1 = 0 ∧
      (canonicalAssignment data.coefficient (controlBox 1)).zHi i 1 = 0)
  nonlinearEffective : point 0 2 ∈ members tightenedX ∧
    ¬ (∀ j, data.c (point 0 2) j ≤ 0)
  integerEffective : point 0 (1/2) ∈ members tightenedX ∧
    (∀ j, data.c (point 0 (1/2)) j ≤ 0) ∧
    ¬ (∀ i : {i : Fin 2 // i ∈ integerCoordinates}, ∃ k : ℤ, (k : ℝ) = point 0 (1/2) i)

/-- Proposed counted bundled applications, not additional independent research
claims and not a numerical solver/finite-termination certificate. -/
theorem qualified_fbbt_controls : QualifiedControls :=
  ⟨lp_auxiliary_ordered, Chapter02FBBTBoundary.boundary_controls, contraction_actual_theory_application,
   retained_source_actual_application, retained_nonlinear_effective, retained_integrality_effective⟩

end Chapter02FBBTControls
#print axioms Chapter02FBBTControls.qualified_fbbt_controls
