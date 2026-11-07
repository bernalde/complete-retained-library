module

public import Chapter03PumpSoftComposition
public import Chapter03PumpOAIntegratedWarmComposed

@[expose] public section

/-! One bounded nonvacuity specialization: the accepted actual cap-one pump
prefix, fixed W=0, and a proved exact warm-soft return. No optimizer, alpha,
continuation trace or exact continuation counts are inherited from hard OA. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OASoftMaster
open Chapter03.OASoftExecutionAvailability
namespace Chapter03.PumpSoft.IntegratedWarm

abbrev I := OAExec.Integrated.spec

theorem hard_affine : HardAffineEntailment I := by
  intro j hj
  exact False.elim (hj (by rw [OAExec.Integrated.nonlinear_exact]; exact Set.mem_univ j))

def zeroWeights (delta : ℝ) : PrefixWeights I delta := fun _ _ => 0

theorem zero_nonneg (delta : ℝ) : ∀ P o, 0 ≤ zeroWeights delta P o := fun _ _ => le_refl 0

/-- The one transferred pump seed/incumbent is used directly. There is no new
relaxation solve and the policy seed agrees with the zero prefix weight. -/
theorem actual_initial_state (delta : ℝ) :
    let s := initialState I delta PumpOA.IntegratedWarm.s1
      (zeroWeights delta PumpOA.IntegratedWarm.s1) (zero_nonneg delta _)
    s.history = [] ∧ s.incumbent = some OAExec.Integrated.solution ∧
      s.lower = I.f OAExec.Integrated.seed ∧
      SeedAgreement I delta PumpOA.IntegratedWarm.s1
        (zeroWeights delta PumpOA.IntegratedWarm.s1) s.policy :=
  ⟨rfl,rfl,rfl,initialPolicy_agreement I delta PumpOA.IntegratedWarm.s1
    (zeroWeights delta PumpOA.IntegratedWarm.s1) (zero_nonneg delta _)⟩

/-- The known cap-one pump prefix is the actual input to a nonvacuous warm-soft
execution. The returned optimum is existential; no hard-trace identity is used. -/
theorem actual_zero_composition (delta : ℝ) (hd : 0 ≤ delta) :
    FP.procedure (PumpOA.asFPDelta I delta) (PumpOA.IntegratedWarm.initialization delta)
      (PumpOA.IntegratedWarm.choose delta hd) = some (.loop (PumpOA.IntegratedWarm.output delta)) ∧
    Nonempty (Selectors I delta (zeroWeights delta) 0) ∧
    ∀ chooseOA : Selectors I delta (zeroWeights delta) 0,
      ∃ out p,
        execute PumpOA.IntegratedWarm.full_assumptions delta hd (zeroWeights delta) (zero_nonneg delta)
          0 (some 1) (PumpOA.IntegratedWarm.initialization delta)
          (PumpOA.IntegratedWarm.choose delta hd) chooseOA = some out ∧
        out.continuation.result = .solution p ∧ IsMinimizer I.original I.f p ∧
        PumpOA.CountBounds I (some 1) out := by
  have H := qualified_source_pump_soft PumpOA.IntegratedWarm.full_assumptions hard_affine
    delta hd (zeroWeights delta) (zero_nonneg delta) 0 (le_refl 0) (some 1)
  refine ⟨PumpOA.IntegratedWarm.actual_procedure delta hd,H.2.2.1,?_⟩
  intro chooseOA
  obtain ⟨out,he,hc,hb⟩ := H.2.2.2 (PumpOA.IntegratedWarm.initialization delta)
    (PumpOA.IntegratedWarm.choose delta hd) chooseOA
  cases hv : out.continuation.result with
  | infeasible =>
    have hi : ¬ I.original.Nonempty := by simpa [hv,OAExec.ReturnCertificate] using hc
    exact False.elim (hi ⟨OAExec.Integrated.solution,OAExec.Integrated.solution_minimum.1⟩)
  | solution p =>
    refine ⟨out,p,he,hv,?_,hb⟩
    simpa only [hv,OAExec.ReturnCertificate,add_zero,IsMinimizer] using hc

end Chapter03.PumpSoft.IntegratedWarm
