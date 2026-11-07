module

public import Chapter02FBBTContractionControl
public import Chapter02FBBTTheorem

@[expose] public section

noncomputable section
open Chapter02FBBT
namespace Chapter02FBBTControls

lemma contraction_limit_eq_zero (a : ℝ) (ha : 1 < a) :
    limitBounds (contractionMatrix a) (contractionBox 1) = contractionBox 0 := by
  exact tendsto_nhds_unique
    ((qualified_simultaneous_fbbt (contractionMatrix a) (contractionBox 1)
      (contraction_box_ordered zero_le_one)).conditionalConclusion
        (contraction_every_public_nonempty a ha)).actualEndpointConvergence
    (contraction_raw_tends_zero a ha)

lemma contraction_never_stabilizes (a : ℝ) (ha : 1 < a) (k : ℕ) :
    rawRun (contractionMatrix a) (contractionBox 1) (k+1) ≠
      rawRun (contractionMatrix a) (contractionBox 1) k := by
  intro he
  have heq := congrArg (fun q : JointBounds 2 2 => q.2 (.inl 0)) he
  rw [contraction_raw_run a ha (k+1), contraction_raw_run a ha k] at heq
  change (a⁻¹)^(k+1) = (a⁻¹)^k at heq
  rw [pow_succ] at heq
  have hp : 0 < (a⁻¹)^k := pow_pos (inv_pos.mpr (by linarith)) k
  have hi : a⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < a)).mpr ha
  nlinarith

lemma contraction_actual_theory_application (a : ℝ) (ha : 1 < a) :
    SimultaneousConclusion (contractionMatrix a) (contractionBox 1) ∧
    limitBounds (contractionMatrix a) (contractionBox 1) = contractionBox 0 ∧
    (∀ k, 0 < width (rawRun (contractionMatrix a) (contractionBox 1) k)) ∧
    (∀ k, rawRun (contractionMatrix a) (contractionBox 1) (k+1) ≠
      rawRun (contractionMatrix a) (contractionBox 1) k) ∧
    LPFeasible (contractionMatrix a) (contractionBox 1)
      (canonicalAssignment (contractionMatrix a) (contractionBox 0)) := by
  have hc := (qualified_simultaneous_fbbt (contractionMatrix a) (contractionBox 1)
    (contraction_box_ordered zero_le_one)).conditionalConclusion
      (contraction_every_public_nonempty a ha)
  have he := contraction_limit_eq_zero a ha
  exact ⟨hc, he, contraction_finite_positive_width a ha,
    contraction_never_stabilizes a ha, he ▸ hc.attainedLP⟩

end Chapter02FBBTControls
