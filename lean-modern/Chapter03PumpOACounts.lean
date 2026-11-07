module

public import Chapter03PumpOAComposition

@[expose] public section

/-! Counts refer to actual calls in the composed recursion. Pump projection
inspections and polishing solves stay separate from OA fixed solves, including
the restoration solves used when a requested original fixed fiber is empty. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

structure CountBounds (d : OAExec.Data n m l r) (cap : Option ℕ)
    (out : Output n m) : Prop where
  relaxation_exact : out.pump.relaxations = 1
  pump_bodies : out.pump.bodies ≤ d.box.card
  pump_projections : out.pump.projections ≤ d.box.card
  pump_masters : out.pump.masters ≤ d.box.card+1
  pump_polishes : out.pump.polishes ≤ out.pump.bodies
  cap_bound : ∀ b, cap = some b → out.pump.bodies ≤ b ∧ out.pump.projections ≤ b
  continuation_masters : out.continuation.masters ≤ d.box.card+1
  continuation_fixed : out.continuation.fixed ≤ out.continuation.masters
  continuation_restorations : out.continuation.restorations ≤ d.box.card
  restoration_subset_fixed : out.continuation.restorations ≤ out.continuation.fixed
  total_masters : out.pump.masters + out.continuation.masters ≤ 2*d.box.card+2
  total_fixed : out.pump.polishes + out.continuation.fixed ≤ 2*d.box.card+1

theorem combine_count_bounds {d : OAExec.Data n m l r} {delta : ℝ}
    {cap : Option ℕ} {pump : FP.Outcome n m} {tail : OAExec.Output n m}
    (hp : FP.CountBounds (asFPDelta d delta) cap pump)
    (hm : tail.masters ≤ d.box.card+1) (hf : tail.fixed ≤ tail.masters)
    (hr : tail.restorations ≤ d.box.card) (hrf : tail.restorations ≤ tail.fixed) :
    CountBounds d cap ⟨pump.counts,tail⟩ := by
  have hb : pump.counts.bodies ≤ d.box.card := hp.bodies_bound
  have hpj : pump.counts.projections ≤ d.box.card := hp.projections_bound
  have hpm : pump.counts.masters ≤ d.box.card+1 := hp.masters_bound
  have hpp := hp.polishes_bound
  refine ⟨hp.relaxation_exact,hb,hpj,hpm,hpp,hp.cap_bound,hm,hf,hr,hrf,?_,?_⟩
  · dsimp
    omega
  · dsimp
    omega

theorem execute_returns {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (epsilon : ℝ) (heps : 0 ≤ epsilon) (cap : Option ℕ)
    (initial : FP.Initialization (asFPDelta d delta))
    (choosePump : FP.Selector (asFPDelta d delta) cap)
    (chooseOA : Selectors d delta epsilon) :
    ∃ out, execute h delta hd epsilon cap initial choosePump chooseOA = some out ∧
      OAExec.ReturnCertificate d epsilon out.continuation.result ∧
      CountBounds d cap out := by
  obtain ⟨pump,hp,hc,hb⟩ := FP.procedure_returns (asFPDelta d delta)
    (asFPDelta_analytic h hd) cap initial choosePump
  cases pump with
  | initialInfeasible =>
    refine ⟨_,execute_of_initialInfeasible h delta hd epsilon cap initial
      choosePump chooseOA hp,?_,combine_count_bounds hb (Nat.zero_le _) le_rfl
        (Nat.zero_le _) le_rfl⟩
    cases initial with
    | empty _ => exact hc
    | minimum _ _ => exact False.elim hc
  | initialOptimal p =>
    refine ⟨_,execute_of_initialOptimal h delta hd epsilon cap initial
      choosePump chooseOA hp,?_,combine_count_bounds hb (Nat.zero_le _) le_rfl
        (Nat.zero_le _) le_rfl⟩
    cases initial with
    | empty _ => exact False.elim hc
    | minimum _ _ =>
      exact ⟨hc.2.1,fun z hz => (hc.2.2 z hz).trans (le_add_of_nonneg_right heps)⟩
  | loop o =>
    have hs := pump_loop_seed_valid h hd initial choosePump hp
    have hi := pump_loop_invariant h hd initial choosePump hp
    obtain ⟨tail,ht,hcert,hm,_,hr⟩ := finite_return_with_counts h hd hi hs heps
      (chooseOA o.state hs)
    have hex := runFuel_execution d delta o.state epsilon (chooseOA o.state hs)
      (d.box.card+1) (initialState d o.state) .initial ht
    have hcounts := execution_counts hex
    refine ⟨⟨FP.Outcome.counts (.loop o),tail⟩,?_,hcert,
      combine_count_bounds hb hm hcounts.1 hr hcounts.2.2⟩
    rw [execute_of_loop h delta hd epsilon cap initial choosePump chooseOA hp,ht]
    rfl

/-- One substantive qualified composed endpoint. Every exact initializer and
both stages' admitted selectors execute; their existence is derived from the
explicit source package. No optimum, master-progress or final-return oracle is
assumed. Delta is the relative pump cutoff, epsilon the absolute OA gap.
This combines the explicit hard-domain availability package with corrected
hard-master OA and enabled pump success no-goods. It excludes the literal thesis
all-soft bound encoding, the final/author paper's soft-rMIP/DICOPT call, the
no-success-cut integer variant and numerical/commercial solver guarantees. -/
theorem qualified_source_pump_oa {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (epsilon : ℝ) (heps : 0 ≤ epsilon) (cap : Option ℕ) :
    Nonempty (FP.Initialization (asFPDelta d delta)) ∧
    Nonempty (FP.Selector (asFPDelta d delta) cap) ∧
    Nonempty (Selectors d delta epsilon) ∧
    ∀ (initial : FP.Initialization (asFPDelta d delta))
      (choosePump : FP.Selector (asFPDelta d delta) cap)
      (chooseOA : Selectors d delta epsilon),
      ∃ out, execute h delta hd epsilon cap initial choosePump chooseOA = some out ∧
        OAExec.ReturnCertificate d epsilon out.continuation.result ∧
        CountBounds d cap out :=
  ⟨FP.initialization_nonempty (asFPDelta d delta) (asFPDelta_analytic h hd),
    FP.selector_nonempty (asFPDelta d delta) (asFPDelta_analytic h hd) cap,
    selectors_nonempty h delta epsilon, execute_returns h delta hd epsilon heps cap⟩

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.combine_count_bounds
#print axioms Chapter03.PumpOA.execute_returns
#print axioms Chapter03.PumpOA.qualified_source_pump_oa
