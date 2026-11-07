module

public import Chapter03PumpOAReturn
public import Chapter03PumpOARestoration
public import Chapter03PumpOAAvailability

@[expose] public section

/-! The restoration bound counts actual invoked individual-sum minimizations.
It is transported from the reached history of the same recursive execution. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

theorem execution_restoration_count {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ}
    {s : OAExec.State d} {out : OAExec.Output n m} (hr : Reachable d delta P epsilon s)
    (hex : Execution d delta P epsilon s out) :
    out.restorations + OAExec.restorationCount s ≤ d.box.card := by
  induction hex with
  | gap _ _ => simpa using reachable_restoration_length_le h hd hP hs hr
  | empty _ _ => simpa using reachable_restoration_length_le h hd hP hs hr
  | step ho q e hv hy _ ih =>
    have hb := ih (.next hr (.step ho q e hv hy))
    rw [restorationCount_advance_eq_event] at hb
    simp only [OAExec.countStep]
    omega

/-- Main fractional-loop endpoint: every admitted exact selector, actual
source order, finite return, original-objective guarantee and all solve counts. -/
theorem finite_return_with_counts {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d delta P epsilon) :
    ∃ out, runFuel d delta P epsilon choose (d.box.card+1) (initialState d P)
      .initial = some out ∧ OAExec.ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card := by
  obtain ⟨out,hout,hcert,hm,hf⟩ := finite_return h hd hP hs heps choose
  have hex := runFuel_execution d delta P epsilon choose _ _ .initial hout
  have hc := execution_restoration_count h hd hP hs .initial hex
  exact ⟨out,hout,hcert,hm,hf,by simpa [OAExec.restorationCount,OAExec.restorationEvents,initialState] using hc⟩

/-- Local availability inhabits the quantified selectors; finite return itself
does not assume a whole execution or a final result exists. -/
theorem locally_available_finite_return {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (available : LocalAvailability d delta P epsilon) :
    Nonempty (Selector d delta P epsilon) ∧
    ∀ choose : Selector d delta P epsilon, ∃ out,
      runFuel d delta P epsilon choose (d.box.card+1) (initialState d P)
        .initial = some out ∧ OAExec.ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card :=
  ⟨selector_inhabited available,fun choose => finite_return_with_counts h hd hP hs heps choose⟩

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.finite_return_with_counts
#print axioms Chapter03.PumpOA.locally_available_finite_return
