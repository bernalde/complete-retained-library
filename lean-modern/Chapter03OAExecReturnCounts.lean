module

public import Chapter03OAExecReturn
public import Chapter03OAExecCountBridge

@[expose] public section

/-! The restoration bound counts actual invoked individual-sum minimizations.
It is transported from the reached history of the same recursive execution. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

theorem execution_restoration_count {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ}
    {s : State d} {out : Output n m} (hr : Reachable d seed epsilon s)
    (h : Execution d seed epsilon s out) :
    out.restorations + restorationCount s ≤ d.box.card := by
  induction h with
  | gap _ _ => simpa using reachable_restoration_length_le a hs hr
  | empty _ _ => simpa using reachable_restoration_length_le a hs hr
  | step ho q e hv hy _ ih =>
    have hb := ih (.next hr (.step ho q e hv hy))
    rw [restorationCount_advance_eq_event] at hb
    simp only [countStep]
    omega

/-- Main fractional-loop endpoint: every admitted exact selector, actual
source order, finite return, original-objective guarantee and all solve counts. -/
theorem finite_return_with_counts {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d seed epsilon) :
    ∃ out, runFuel d seed epsilon choose (d.box.card+1) (initialState d seed)
      .initial = some out ∧ ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card := by
  obtain ⟨out,hout,hcert,hm,hf⟩ := finite_return a hs heps choose
  have hex := runFuel_execution d seed epsilon choose _ _ .initial hout
  have hc := execution_restoration_count a hs .initial hex
  exact ⟨out,hout,hcert,hm,hf,by simpa [restorationCount_initial] using hc⟩

/-- Local availability inhabits the quantified selectors; finite return itself
does not assume a whole execution or a final result exists. -/
theorem locally_available_finite_return {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (available : LocalAvailability d seed epsilon) :
    Nonempty (Selector d seed epsilon) ∧
    ∀ choose : Selector d seed epsilon, ∃ out,
      runFuel d seed epsilon choose (d.box.card+1) (initialState d seed)
        .initial = some out ∧ ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card :=
  ⟨selector_inhabited available,fun choose => finite_return_with_counts a hs heps choose⟩

end Chapter03.OAExec

#print axioms Chapter03.OAExec.finite_return_with_counts
#print axioms Chapter03.OAExec.locally_available_finite_return
