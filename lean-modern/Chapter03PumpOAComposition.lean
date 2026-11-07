module

public import Chapter03PumpOAReturnCounts

@[expose] public section

/-! The actual two-stage procedure. Every loop stop reason feeds the real pump
state into the retained-master continuation, including positive-delta empty
master/projection stops. Initial empty/integral exits incur no continuation.
The proved seed property only makes the dependent selector callable; it neither
chooses a solver answer nor supplies progress or a final optimum. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

theorem pump_chain_seed {d : FP.Data n m l r} {cap : Option ℕ}
    {s t : FP.State n m} {k q : ℕ} (hc : FP.Chain d cap s k q t) :
    t.seed = s.seed := by
  induction hc with
  | nil _ => rfl
  | cons _ _ ih => exact ih

theorem pump_return_claims {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} (hd : 0 ≤ delta)
    {cap : Option ℕ} (initial : FP.Initialization (asFPDelta d delta))
    (choose : FP.Selector (asFPDelta d delta) cap) {out : FP.Outcome n m}
    (hr : FP.procedure (asFPDelta d delta) initial choose = some out) :
    FP.ReturnClaims (asFPDelta d delta) cap initial out ∧
      FP.CountBounds (asFPDelta d delta) cap out := by
  obtain ⟨o,ho,hc,hb⟩ := FP.procedure_returns (asFPDelta d delta)
    (asFPDelta_analytic h hd) cap initial choose
  have he : o = out := Option.some.inj (ho.symm.trans hr)
  simpa only [he] using And.intro hc hb

theorem pump_loop_seed_valid {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} (hd : 0 ≤ delta)
    {cap : Option ℕ} (initial : FP.Initialization (asFPDelta d delta))
    (choose : FP.Selector (asFPDelta d delta) cap) {o : FP.LoopOutput n m}
    (hr : FP.procedure (asFPDelta d delta) initial choose = some (.loop o)) :
    OAExec.SeedValid d o.state.seed := by
  have hc := (pump_return_claims h hd initial choose hr).1
  cases initial with
  | empty _ => exact False.elim hc
  | minimum p hp =>
    have hs : o.state.seed = p := pump_chain_seed hc.2.1
    rw [hs]
    exact ⟨hp,h.every_exact_initialization p hp,
      fun hi => hc.1 (OAExec.integral_relaxation_original hp.1 hi)⟩

theorem pump_loop_invariant {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} (hd : 0 ≤ delta)
    {cap : Option ℕ} (initial : FP.Initialization (asFPDelta d delta))
    (choose : FP.Selector (asFPDelta d delta) cap) {o : FP.LoopOutput n m}
    (hr : FP.procedure (asFPDelta d delta) initial choose = some (.loop o)) :
    FP.Invariant (asFPDelta d delta) o.state := by
  have hc := (pump_return_claims h hd initial choose hr).1
  cases initial with
  | empty _ => exact False.elim hc
  | minimum _ _ => exact hc.2.2.2.1

structure Output (n m : ℕ) where
  pump : FP.Counts
  continuation : OAExec.Output n m

def execute {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    (delta : ℝ) (hd : 0 ≤ delta) (epsilon : ℝ) (cap : Option ℕ)
    (initial : FP.Initialization (asFPDelta d delta))
    (choosePump : FP.Selector (asFPDelta d delta) cap)
    (chooseOA : Selectors d delta epsilon) : Option (Output n m) :=
  match hr : FP.procedure (asFPDelta d delta) initial choosePump with
  | none => none
  | some (.initialInfeasible) =>
    some ⟨FP.Outcome.counts (.initialInfeasible : FP.Outcome n m),⟨.infeasible,0,0,0⟩⟩
  | some (.initialOptimal p) =>
    some ⟨FP.Outcome.counts (.initialOptimal p),⟨.solution p,0,0,0⟩⟩
  | some (.loop o) =>
    (runFuel d delta o.state epsilon
      (chooseOA o.state (pump_loop_seed_valid h hd initial choosePump hr))
      (d.box.card+1) (initialState d o.state) .initial).map
        (fun tail => ⟨FP.Outcome.counts (.loop o),tail⟩)

theorem execute_of_loop {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (epsilon : ℝ) (cap : Option ℕ)
    (initial : FP.Initialization (asFPDelta d delta))
    (choosePump : FP.Selector (asFPDelta d delta) cap)
    (chooseOA : Selectors d delta epsilon) {o : FP.LoopOutput n m}
    (hr : FP.procedure (asFPDelta d delta) initial choosePump = some (.loop o)) :
    execute h delta hd epsilon cap initial choosePump chooseOA =
      (runFuel d delta o.state epsilon
        (chooseOA o.state (pump_loop_seed_valid h hd initial choosePump hr))
        (d.box.card+1) (initialState d o.state) .initial).map
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
    (epsilon : ℝ) (cap : Option ℕ)
    (initial : FP.Initialization (asFPDelta d delta))
    (choosePump : FP.Selector (asFPDelta d delta) cap)
    (chooseOA : Selectors d delta epsilon)
    (hr : FP.procedure (asFPDelta d delta) initial choosePump = some .initialInfeasible) :
    execute h delta hd epsilon cap initial choosePump chooseOA =
      some ⟨FP.Outcome.counts (.initialInfeasible : FP.Outcome n m),
        ⟨.infeasible,0,0,0⟩⟩ := by
  unfold execute
  split <;> rename_i he
  all_goals first | rfl | simp_all

theorem execute_of_initialOptimal {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (hd : 0 ≤ delta)
    (epsilon : ℝ) (cap : Option ℕ)
    (initial : FP.Initialization (asFPDelta d delta))
    (choosePump : FP.Selector (asFPDelta d delta) cap)
    (chooseOA : Selectors d delta epsilon) {p : Point n m}
    (hr : FP.procedure (asFPDelta d delta) initial choosePump = some (.initialOptimal p)) :
    execute h delta hd epsilon cap initial choosePump chooseOA =
      some ⟨FP.Outcome.counts (.initialOptimal p),⟨.solution p,0,0,0⟩⟩ := by
  unfold execute
  split <;> rename_i he
  all_goals first | rfl | simp_all

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.pump_loop_seed_valid
#print axioms Chapter03.PumpOA.pump_loop_invariant
#print axioms Chapter03.PumpOA.execute_of_loop
