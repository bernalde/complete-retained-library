module

public import Chapter03PumpOARun
public import Chapter03PumpOAProgress

@[expose] public section

/-! Conditional soundness and finite return for every exact certificate-bearing
selector. Progress and local availability are separate: the former is derived
from the actual master/event geometry, not included in the selector's type. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

theorem execution_sound {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} (hd : 0 ≤ delta)
    {P : FP.State n m} (hP : FP.Invariant (asFPDelta d delta) P)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : OAExec.State d} {out : OAExec.Output n m}
    (hi : Invariant d P s) (hex : Execution d delta P epsilon s out) :
    OAExec.ReturnCertificate d epsilon out.result := by
  induction hex with
  | gap hu hg => exact gap_certificate hi heps hu hg
  | @empty s _ he =>
    cases hu : s.incumbent with
    | none =>
      simpa [emptyResult,hu,OAExec.ReturnCertificate] using
        empty_without_incumbent h hd hP hi he hu
    | some u =>
      have hm := empty_with_incumbent h hd hP hi he hu
      simp only [emptyResult,hu,OAExec.ReturnCertificate]
      exact ⟨hm.1,fun z hz => (hm.2 z hz).trans (le_add_of_nonneg_right heps)⟩
  | step _ q _ he _ _ ih => exact ih (advance_invariant h hd hP hi q he)

theorem execution_master_count {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : OAExec.State d} {out : OAExec.Output n m} (hr : Reachable d delta P epsilon s)
    (hex : Execution d delta P epsilon s out) :
    out.masters + s.history.length ≤ d.box.card+1 := by
  induction hex with
  | gap _ _ => simpa using reachable_length_le_succ h hd hP hs heps hr
  | empty ho _ =>
    have hb := reachable_open_length_le h hd hP hs heps hr ho
    simp only
    omega
  | step ho q e hv hy _ ih =>
    have hb := ih (.next hr (.step ho q e hv hy))
    simp only [OAExec.countStep,advance,List.length_append,List.length_singleton] at *
    omega

theorem runFuel_total {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d delta P epsilon) (fuel : ℕ) (s : OAExec.State d)
    (hr : Reachable d delta P epsilon s) (budget : d.box.card+1 ≤ fuel+s.history.length) :
    ∃ out, runFuel d delta P epsilon choose fuel s hr = some out := by
  classical
  induction fuel generalizing s with
  | zero =>
    by_cases ho : OAExec.loopOpen d epsilon s
    · have hb := reachable_open_length_le h hd hP hs heps hr ho
      omega
    · exact ⟨_,by rw [runFuel]; simp only [dif_neg ho]; rfl⟩
  | succ fuel ih =>
    by_cases ho : OAExec.loopOpen d epsilon s
    · cases hc : choose s hr ho with
      | empty he =>
        exact ⟨_,by rw [runFuel]; simp only [dif_pos ho,hc]; rfl⟩
      | next q e hv hy =>
        have hb : d.box.card+1 ≤ fuel+(advance s q e).history.length := by
          simp only [advance,List.length_append,List.length_singleton]
          omega
        obtain ⟨out,hout⟩ := ih (advance s q e) (.next hr (.step ho q e hv hy)) hb
        exact ⟨OAExec.countStep e out,by rw [runFuel]; simp only [dif_pos ho,hc,hout]; rfl⟩
    · exact ⟨_,by rw [runFuel]; simp only [dif_neg ho]; rfl⟩

/-- No original optimum is assumed. The actual recursion returns after at most
N+1 master decisions, even when a last repeated fiber incurs one final NLP. -/
theorem finite_return {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d delta P epsilon) :
    ∃ out, runFuel d delta P epsilon choose (d.box.card+1) (initialState d P)
      .initial = some out ∧ OAExec.ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 := by
  obtain ⟨out,hout⟩ := runFuel_total h hd hP hs heps choose (d.box.card+1)
    (initialState d P) .initial (by simp [initialState])
  have hex := runFuel_execution d delta P epsilon choose _ _ .initial hout
  have hc := execution_master_count h hd hP hs heps .initial hex
  have hf := (execution_counts hex).1
  refine ⟨out,hout,execution_sound h hd hP heps (initial_invariant hs hP) hex,?_,?_⟩
  · simpa [initialState] using hc
  · simpa [initialState] using hf.trans (by simpa [initialState] using hc)

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.finite_return
#print axioms Chapter03.PumpOA.execution_sound
