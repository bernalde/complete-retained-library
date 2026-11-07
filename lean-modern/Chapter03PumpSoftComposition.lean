module

public import Chapter03PumpSoftReturn
public import Chapter03PumpSoftSelectors
public import Chapter03PumpOACounts

@[expose] public section

/-! Concrete sibling of PumpOA.execute. Both initialization exits are preserved;
every actual pump loop stop enters the all-soft-prefix continuation unchanged. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy Chapter03.OASoftExecutionAvailability
namespace Chapter03.PumpSoft
variable {n m l r : ℕ}

def execute {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    (delta : ℝ) (hd : 0 ≤ delta) (V : PrefixWeights d delta) (hV : ∀ P o, 0 ≤ V P o)
    (epsilon : ℝ) (cap : Option ℕ)
    (initial : FP.Initialization (PumpOA.asFPDelta d delta))
    (choosePump : FP.Selector (PumpOA.asFPDelta d delta) cap)
    (chooseOA : Selectors d delta V epsilon) : Option (PumpOA.Output n m) :=
  match hr : FP.procedure (PumpOA.asFPDelta d delta) initial choosePump with
  | none => none
  | some (.initialInfeasible) =>
    some ⟨FP.Outcome.counts (.initialInfeasible : FP.Outcome n m),⟨.infeasible,0,0,0⟩⟩
  | some (.initialOptimal p) =>
    some ⟨FP.Outcome.counts (.initialOptimal p),⟨.solution p,0,0,0⟩⟩
  | some (.loop o) =>
    (runFuel d delta o.state (V o.state) epsilon
      (chooseOA o.state (PumpOA.pump_loop_seed_valid h hd initial choosePump hr)
        (PumpOA.pump_loop_invariant h hd initial choosePump hr))
      (d.box.card+1) (initialState d delta o.state (V o.state) (hV o.state)) (.initial (hV o.state))).map
        (fun tail => ⟨FP.Outcome.counts (.loop o),tail⟩)

theorem execute_of_loop {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    (delta : ℝ) (hd : 0 ≤ delta) (V : PrefixWeights d delta) (hV : ∀ P o, 0 ≤ V P o)
    (epsilon : ℝ) (cap : Option ℕ)
    (initial : FP.Initialization (PumpOA.asFPDelta d delta))
    (choosePump : FP.Selector (PumpOA.asFPDelta d delta) cap)
    (chooseOA : Selectors d delta V epsilon) {o : FP.LoopOutput n m}
    (hr : FP.procedure (PumpOA.asFPDelta d delta) initial choosePump = some (.loop o)) :
    execute h delta hd V hV epsilon cap initial choosePump chooseOA =
      (runFuel d delta o.state (V o.state) epsilon
        (chooseOA o.state (PumpOA.pump_loop_seed_valid h hd initial choosePump hr)
          (PumpOA.pump_loop_invariant h hd initial choosePump hr))
        (d.box.card+1) (initialState d delta o.state (V o.state) (hV o.state)) (.initial (hV o.state))).map
          (fun tail => ⟨FP.Outcome.counts (.loop o),tail⟩) := by
  unfold execute
  split
  · simp_all
  · simp_all
  · simp_all
  · rename_i o' he
    have heq : o' = o := FP.Outcome.loop.inj (Option.some.inj (he.symm.trans hr))
    subst o'
    rfl

theorem execute_of_initialInfeasible {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (V : PrefixWeights d delta) (hV : ∀ P o, 0 ≤ V P o) (epsilon : ℝ) (cap : Option ℕ)
    (initial : FP.Initialization (PumpOA.asFPDelta d delta))
    (choosePump : FP.Selector (PumpOA.asFPDelta d delta) cap)
    (chooseOA : Selectors d delta V epsilon)
    (hr : FP.procedure (PumpOA.asFPDelta d delta) initial choosePump = some .initialInfeasible) :
    execute h delta hd V hV epsilon cap initial choosePump chooseOA =
      some ⟨FP.Outcome.counts (.initialInfeasible : FP.Outcome n m),⟨.infeasible,0,0,0⟩⟩ := by
  unfold execute
  split <;> rename_i he
  all_goals first | rfl | simp_all

theorem execute_of_initialOptimal {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (V : PrefixWeights d delta) (hV : ∀ P o, 0 ≤ V P o) (epsilon : ℝ) (cap : Option ℕ)
    (initial : FP.Initialization (PumpOA.asFPDelta d delta))
    (choosePump : FP.Selector (PumpOA.asFPDelta d delta) cap)
    (chooseOA : Selectors d delta V epsilon) {p : Point n m}
    (hr : FP.procedure (PumpOA.asFPDelta d delta) initial choosePump = some (.initialOptimal p)) :
    execute h delta hd V hV epsilon cap initial choosePump chooseOA =
      some ⟨FP.Outcome.counts (.initialOptimal p),⟨.solution p,0,0,0⟩⟩ := by
  unfold execute
  split <;> rename_i he
  all_goals first | rfl | simp_all

theorem execute_returns {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (V : PrefixWeights d delta) (hV : ∀ P o, 0 ≤ V P o)
    (epsilon : ℝ) (heps : 0 ≤ epsilon) (cap : Option ℕ)
    (initial : FP.Initialization (PumpOA.asFPDelta d delta))
    (choosePump : FP.Selector (PumpOA.asFPDelta d delta) cap)
    (chooseOA : Selectors d delta V epsilon) :
    ∃ out, execute h delta hd V hV epsilon cap initial choosePump chooseOA = some out ∧
      OAExec.ReturnCertificate d epsilon out.continuation.result ∧ PumpOA.CountBounds d cap out := by
  obtain ⟨pump,hp,hc,hb⟩ := FP.procedure_returns (PumpOA.asFPDelta d delta)
    (PumpOA.asFPDelta_analytic h hd) cap initial choosePump
  cases pump with
  | initialInfeasible =>
    refine ⟨_,execute_of_initialInfeasible h delta hd V hV epsilon cap initial
      choosePump chooseOA hp,?_,PumpOA.combine_count_bounds hb (Nat.zero_le _) le_rfl
        (Nat.zero_le _) le_rfl⟩
    cases initial with
    | empty _ => exact hc
    | minimum _ _ => exact False.elim hc
  | initialOptimal p =>
    refine ⟨_,execute_of_initialOptimal h delta hd V hV epsilon cap initial
      choosePump chooseOA hp,?_,PumpOA.combine_count_bounds hb (Nat.zero_le _) le_rfl
        (Nat.zero_le _) le_rfl⟩
    cases initial with
    | empty _ => exact False.elim hc
    | minimum _ _ =>
      exact ⟨hc.2.1,fun z hz => (hc.2.2 z hz).trans (le_add_of_nonneg_right heps)⟩
  | loop o =>
    have hs := PumpOA.pump_loop_seed_valid h hd initial choosePump hp
    have hi := PumpOA.pump_loop_invariant h hd initial choosePump hp
    obtain ⟨tail,ht,hcert,hm,_,hr⟩ := finite_return_with_counts h hd hi hs (hV o.state) heps
      (chooseOA o.state hs hi)
    have hex := runFuel_execution d delta o.state (V o.state) epsilon
      (chooseOA o.state hs hi) (d.box.card+1)
      (initialState d delta o.state (V o.state) (hV o.state)) (.initial (hV o.state)) ht
    have hcounts := execution_counts hex
    refine ⟨⟨FP.Outcome.counts (.loop o),tail⟩,?_,hcert,
      PumpOA.combine_count_bounds hb hm hcounts.1 hr hcounts.2.2⟩
    rw [execute_of_loop h delta hd V hV epsilon cap initial choosePump chooseOA hp,ht]
    rfl

/-- Qualified all-soft-prefix pump continuation. All local choices exist from
visible data hypotheses, and every admitted exact choice sequence returns.
This stored mathematical policy does not assert historical software behavior. -/
theorem qualified_source_pump_soft {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (hard : HardAffineEntailment d)
    (delta : ℝ) (hd : 0 ≤ delta) (V : PrefixWeights d delta) (hV : ∀ P o, 0 ≤ V P o)
    (epsilon : ℝ) (heps : 0 ≤ epsilon) (cap : Option ℕ) :
    Nonempty (FP.Initialization (PumpOA.asFPDelta d delta)) ∧
    Nonempty (FP.Selector (PumpOA.asFPDelta d delta) cap) ∧
    Nonempty (Selectors d delta V epsilon) ∧
    ∀ (initial : FP.Initialization (PumpOA.asFPDelta d delta))
      (choosePump : FP.Selector (PumpOA.asFPDelta d delta) cap)
      (chooseOA : Selectors d delta V epsilon),
      ∃ out, execute h delta hd V hV epsilon cap initial choosePump chooseOA = some out ∧
        OAExec.ReturnCertificate d epsilon out.continuation.result ∧ PumpOA.CountBounds d cap out :=
  ⟨FP.initialization_nonempty (PumpOA.asFPDelta d delta) (PumpOA.asFPDelta_analytic h hd),
    FP.selector_nonempty (PumpOA.asFPDelta d delta) (PumpOA.asFPDelta_analytic h hd) cap,
    selectors_nonempty h hard delta V epsilon,
    execute_returns h delta hd V hV epsilon heps cap⟩

end Chapter03.PumpSoft
