module

public import Chapter03PumpOAIntegratedWarmContinuation
public import Chapter03PumpOACounts

@[expose] public section

/-! Full-hypothesis R1 control: actual cap-one success history, both pump stop
branches, and every admitted continuation selector. Pump choices are selected;
the first projection's x coordinate is not claimed unique. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA.IntegratedWarm

theorem composed_restoration (delta : ℝ) (hd : 0≤delta) (epsilon : ℝ)
    (heps : epsilon<5/16) (chooseOA : Selectors I delta epsilon) :
    execute full_assumptions delta hd epsilon (some 1) (initialization delta)
      (choose delta hd) chooseOA=
        some ⟨⟨1,1,1,2,1⟩,⟨.solution OAExec.Integrated.solution,2,1,1⟩⟩ := by
  rw [execute_of_loop full_assumptions delta hd epsilon (some 1) (initialization delta)
    (choose delta hd) chooseOA (actual_procedure delta hd)]
  have hb : I.box.card=2 := OAExec.Integrated.box_card
  simp only [output,hb]
  have ht := every_suffix delta epsilon heps (chooseOA s1 OAExec.Integrated.seed_valid)
  change runFuel I delta s1 epsilon (chooseOA s1 OAExec.Integrated.seed_valid)
    3 (initialState I s1) .initial = _ at ht
  rw [ht]
  rfl

theorem composed_closed (delta : ℝ) (hd : 0≤delta) (epsilon : ℝ)
    (heps : 5/16≤epsilon) (chooseOA : Selectors I delta epsilon) :
    execute full_assumptions delta hd epsilon (some 1) (initialization delta)
      (choose delta hd) chooseOA=
        some ⟨⟨1,1,1,2,1⟩,⟨.solution OAExec.Integrated.solution,0,0,0⟩⟩ := by
  rw [execute_of_loop full_assumptions delta hd epsilon (some 1) (initialization delta)
    (choose delta hd) chooseOA (actual_procedure delta hd)]
  have hb : I.box.card=2 := OAExec.Integrated.box_card
  simp only [output,hb]
  have ht := every_closed_suffix delta epsilon heps (chooseOA s1 OAExec.Integrated.seed_valid)
  change runFuel I delta s1 epsilon (chooseOA s1 OAExec.Integrated.seed_valid)
    3 (initialState I s1) .initial = _ at ht
  rw [ht]
  rfl

theorem restoration_certificate (delta : ℝ) (hd : 0≤delta) (epsilon : ℝ)
    (heps : 0≤epsilon) (hsmall : epsilon<5/16) :
    Nonempty (Selectors I delta epsilon) ∧
    OAExec.ReturnCertificate I epsilon (.solution OAExec.Integrated.solution) ∧
    CountBounds I (some 1) ⟨⟨1,1,1,2,1⟩,⟨.solution OAExec.Integrated.solution,2,1,1⟩⟩ := by
  have h := qualified_source_pump_oa full_assumptions delta hd epsilon heps (some 1)
  refine ⟨h.2.2.1,?_⟩
  obtain ⟨chooseOA⟩ := h.2.2.1
  obtain ⟨out,he,hc,hb⟩ := h.2.2.2 (initialization delta) (choose delta hd) chooseOA
  rw [composed_restoration delta hd epsilon hsmall chooseOA] at he
  cases Option.some.inj he
  exact ⟨hc,hb⟩

theorem closed_certificate (delta : ℝ) (hd : 0≤delta) (epsilon : ℝ)
    (heps : 5/16≤epsilon) :
    Nonempty (Selectors I delta epsilon) ∧
    OAExec.ReturnCertificate I epsilon (.solution OAExec.Integrated.solution) ∧
    CountBounds I (some 1) ⟨⟨1,1,1,2,1⟩,⟨.solution OAExec.Integrated.solution,0,0,0⟩⟩ := by
  have h := qualified_source_pump_oa full_assumptions delta hd epsilon (by linarith) (some 1)
  refine ⟨h.2.2.1,?_⟩
  obtain ⟨chooseOA⟩ := h.2.2.1
  obtain ⟨out,he,hc,hb⟩ := h.2.2.2 (initialization delta) (choose delta hd) chooseOA
  rw [composed_closed delta hd epsilon heps chooseOA] at he
  cases Option.some.inj he
  exact ⟨hc,hb⟩

theorem returned_original_minimum (delta : ℝ) (hd : 0≤delta) :
    IsMinimizer I.original I.f OAExec.Integrated.solution :=
  OAExec.zero_certificate_exact (restoration_certificate delta hd 0 (le_refl 0) (by norm_num)).2.1

end Chapter03.PumpOA.IntegratedWarm

#print axioms Chapter03.PumpOA.IntegratedWarm.composed_restoration
#print axioms Chapter03.PumpOA.IntegratedWarm.composed_closed
#print axioms Chapter03.PumpOA.IntegratedWarm.restoration_certificate
#print axioms Chapter03.PumpOA.IntegratedWarm.closed_certificate
#print axioms Chapter03.PumpOA.IntegratedWarm.returned_original_minimum
