module

public import Chapter03PumpOAC2Execution
public import Chapter03PumpOAComposedControls
public import Chapter03PumpOACounts

@[expose] public section

/-! Each concrete source package invokes the qualified composed endpoint.
The exact execution equations identify its certified returned value and counts.
Selector existence is derived, including in the universal suffix controls. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA

namespace C2

theorem control_certificate :
    OAExec.ReturnCertificate spec 0 (.solution FPTrace.C2.one) ∧
    CountBounds spec (some 2) ⟨⟨1,2,2,3,1⟩,⟨.solution FPTrace.C2.one,3,3,0⟩⟩ := by
  obtain ⟨out,he,hc,hb⟩ :=
    (qualified_source_pump_oa source_package (37/81) (by norm_num) 0 (le_refl 0)
      (some 2)).2.2.2 pumpInitialization pumpChoose chooseOA
  rw [composed_execution] at he
  cases Option.some.inj he
  exact ⟨hc,hb⟩

theorem returned_original_minimum : IsMinimizer spec.original spec.f FPTrace.C2.one :=
  OAExec.zero_certificate_exact control_certificate.1

end C2

namespace Symmetric

theorem control_certificate (epsilon : ℝ) (heps : 0≤epsilon) (hsmall : epsilon<1/4) :
    Nonempty (Selectors spec 0 epsilon) ∧
    OAExec.ReturnCertificate spec epsilon (.solution (pt 0)) ∧
    CountBounds spec none ⟨⟨1,2,2,3,2⟩,⟨.solution (pt 0),1,0,0⟩⟩ := by
  have h := qualified_source_pump_oa source_package 0 (le_refl 0) epsilon heps none
  refine ⟨h.2.2.1,?_⟩
  obtain ⟨chooseOA⟩ := h.2.2.1
  obtain ⟨out,he,hc,hb⟩ := h.2.2.2 initialization choose chooseOA
  rw [composed_saved epsilon hsmall chooseOA] at he
  cases Option.some.inj he
  exact ⟨hc,hb⟩

theorem returned_original_minimum : IsMinimizer spec.original spec.f (pt 0) :=
  OAExec.zero_certificate_exact (control_certificate 0 (le_refl 0) (by norm_num)).2.1

end Symmetric

namespace Infeasible

theorem control_certificate (epsilon : ℝ) (heps : 0≤epsilon) :
    Nonempty (Selectors spec 0 epsilon) ∧
    OAExec.ReturnCertificate spec epsilon .infeasible ∧
    CountBounds spec none ⟨⟨1,0,0,1,0⟩,⟨.infeasible,1,0,0⟩⟩ := by
  have h := qualified_source_pump_oa source_package 0 (le_refl 0) epsilon heps none
  refine ⟨h.2.2.1,?_⟩
  obtain ⟨chooseOA⟩ := h.2.2.1
  obtain ⟨out,he,hc,hb⟩ := h.2.2.2 initialization choose chooseOA
  rw [composed_infeasible epsilon chooseOA] at he
  cases Option.some.inj he
  exact ⟨hc,hb⟩

end Infeasible

namespace Integrated

theorem control_certificate (epsilon : ℝ) (heps : 0≤epsilon) :
    Nonempty (Selectors I 0 epsilon) ∧
    OAExec.ReturnCertificate I epsilon (.solution OAExec.Integrated.solution) ∧
    CountBounds I (some 0)
      ⟨⟨1,0,0,1,0⟩,⟨.solution OAExec.Integrated.solution,2,2,1⟩⟩ := by
  have h := qualified_source_pump_oa full_assumptions 0 (le_refl 0) epsilon heps (some 0)
  refine ⟨h.2.2.1,?_⟩
  obtain ⟨chooseOA⟩ := h.2.2.1
  obtain ⟨out,he,hc,hb⟩ := h.2.2.2 initialization pumpChoose chooseOA
  rw [composed_restoration epsilon heps chooseOA] at he
  cases Option.some.inj he
  exact ⟨hc,hb⟩

theorem returned_original_minimum : IsMinimizer I.original I.f OAExec.Integrated.solution :=
  OAExec.zero_certificate_exact (control_certificate 0 (le_refl 0)).2.1

end Integrated
end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.C2.control_certificate
#print axioms Chapter03.PumpOA.Symmetric.control_certificate
#print axioms Chapter03.PumpOA.Infeasible.control_certificate
#print axioms Chapter03.PumpOA.Integrated.control_certificate
