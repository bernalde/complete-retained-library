module

public import Chapter03PumpOAComposition

@[expose] public section

/-! Exact early-exit reductions of the composed procedure. No fractional state
or pump/OA solve is fabricated for an empty or integral relaxed initialization.
The general return certificate specializes to original exact optimality at zero
absolute OA tolerance; it does not identify the pump's relative delta with it. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

theorem execute_empty_initializer {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (epsilon : ℝ) (cap : Option ℕ)
    (he : ¬(asFPDelta d delta).relaxation.Nonempty)
    (choosePump : FP.Selector (asFPDelta d delta) cap)
    (chooseOA : Selectors d delta epsilon) :
    execute h delta hd epsilon cap (.empty he) choosePump chooseOA =
      some ⟨⟨1,0,0,0,0⟩,⟨.infeasible,0,0,0⟩⟩ :=
  execute_of_initialInfeasible h delta hd epsilon cap (.empty he)
    choosePump chooseOA rfl

theorem execute_integral_initializer {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (epsilon : ℝ) (cap : Option ℕ) (p : Point n m)
    (hp : IsMinimizer (asFPDelta d delta).relaxation (asFPDelta d delta).f p)
    (hi : integral p)
    (choosePump : FP.Selector (asFPDelta d delta) cap)
    (chooseOA : Selectors d delta epsilon) :
    execute h delta hd epsilon cap (.minimum p hp) choosePump chooseOA =
      some ⟨⟨1,0,0,0,0⟩,⟨.solution p,0,0,0⟩⟩ := by
  apply execute_of_initialOptimal h delta hd epsilon cap (.minimum p hp)
    choosePump chooseOA
  have horig : p ∈ (asFPDelta d delta).original :=
    OAExec.integral_relaxation_original hp.1 hi
  simp only [FP.procedure, if_pos horig]

theorem zero_result_exact {d : OAExec.Data n m l r} {p : Point n m}
    (hc : OAExec.ReturnCertificate d 0 (.solution p)) :
    IsMinimizer d.original d.f p := OAExec.zero_certificate_exact hc

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.execute_empty_initializer
#print axioms Chapter03.PumpOA.execute_integral_initializer
#print axioms Chapter03.PumpOA.zero_result_exact
