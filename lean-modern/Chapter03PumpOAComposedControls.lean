module

public import Chapter03PumpOAEmptyResiduals
public import Chapter03PumpOAIntegrated
public import Chapter03PumpOAComposition

@[expose] public section

/-! Actual two-stage execution equations. Every record contains one real
continuous initializer, the actual pump counts, and the new continuation counts.
These are executions of PumpOA.execute, not merely safe-handoff memberships. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA

namespace Symmetric

theorem composed_saved (epsilon : ℝ) (heps : epsilon<1/4)
    (chooseOA : Selectors spec 0 epsilon) :
    execute source_package 0 (le_refl 0) epsilon none initialization choose chooseOA=
      some ⟨⟨1,2,2,3,2⟩,⟨.solution (pt 0),1,0,0⟩⟩ := by
  rw [execute_of_loop source_package 0 (le_refl 0) epsilon none initialization choose chooseOA
    actual_procedure]
  have hb : spec.box.card=2 := box_card
  simp only [output,hb]
  rw [suffix_returns_saved epsilon heps]
  rfl

end Symmetric

namespace Infeasible

theorem composed_infeasible (epsilon : ℝ) (chooseOA : Selectors spec 0 epsilon) :
    execute source_package 0 (le_refl 0) epsilon none initialization choose chooseOA=
      some ⟨⟨1,0,0,1,0⟩,⟨.infeasible,1,0,0⟩⟩ := by
  rw [execute_of_loop source_package 0 (le_refl 0) epsilon none initialization choose chooseOA
    actual_procedure]
  have hb : spec.box.card=2 := Symmetric.box_card
  simp only [output,hb]
  rw [suffix_returns_infeasible epsilon]
  rfl

end Infeasible

namespace Integrated

theorem composed_restoration (epsilon : ℝ) (heps : 0≤epsilon)
    (chooseOA : Selectors I 0 epsilon) :
    execute full_assumptions 0 (le_refl 0) epsilon (some 0) initialization pumpChoose chooseOA=
      some ⟨⟨1,0,0,1,0⟩,⟨.solution OAExec.Integrated.solution,2,2,1⟩⟩ := by
  rw [execute_of_loop full_assumptions 0 (le_refl 0) epsilon (some 0) initialization
    pumpChoose chooseOA pump_procedure]
  have hb : I.box.card=2 := OAExec.Integrated.box_card
  simp only [pumpOutput,hb]
  rw [every_suffix epsilon heps]
  rfl

end Integrated
end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.Symmetric.composed_saved
#print axioms Chapter03.PumpOA.Infeasible.composed_infeasible
#print axioms Chapter03.PumpOA.Integrated.composed_restoration
