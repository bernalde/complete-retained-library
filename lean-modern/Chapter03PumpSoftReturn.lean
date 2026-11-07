module

public import Chapter03PumpSoftRun
public import Chapter03PumpSoftProgress

@[expose] public section

/-! Finite continuation and solve counts for every admitted exact selector.
The proof derives progress and soundness; the fuel bound is not an oracle field. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.PumpSoft
variable {n m l r : ℕ} {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
variable {W : Occurrence (prefixFamily d delta P) → ℝ}

theorem execution_sound (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hW : ∀ o, 0 ≤ W o)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State d delta P W} {out : OAExec.Output n m}
    (hi : Invariant d P s) (hex : Execution d delta P W epsilon s out) :
    OAExec.ReturnCertificate d epsilon out.result := by
  induction hex with
  | gap hu hg => exact PumpOA.gap_certificate hi heps hu hg
  | @empty s _ he =>
    cases hu : s.incumbent with
    | none =>
      simpa [PumpOA.emptyResult,hu,OAExec.ReturnCertificate] using
        empty_without_incumbent h hd hP hi he hu
    | some u =>
      have hm := empty_with_incumbent h hd hP hi he hu
      simp only [PumpOA.emptyResult,hu,OAExec.ReturnCertificate]
      exact ⟨hm.1,fun z hz => (hm.2 z hz).trans (le_add_of_nonneg_right heps)⟩
  | step _ q _ G _ _ ih => exact ih (advance_invariant h hd hP hW hi q G)

theorem execution_master_count (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d delta P W} {out : OAExec.Output n m} (hr : Reachable d delta P W epsilon s)
    (hex : Execution d delta P W epsilon s out) :
    out.masters + s.history.length ≤ d.box.card+1 := by
  induction hex with
  | gap _ _ => simpa using reachable_length_le_succ h hd hP hs hW heps hr
  | empty ho _ =>
    have hb := reachable_open_length_le h hd hP hs hW heps hr ho
    simp only
    omega
  | step ho q e G hy _ ih =>
    have hb := ih (.next hr (.step ho q e G hy))
    simp only [OAExec.countStep,advance,State.history,List.length_append,List.length_singleton] at *
    omega

theorem runFuel_total (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d delta P W epsilon) (fuel : ℕ) (s : State d delta P W)
    (hr : Reachable d delta P W epsilon s) (budget : d.box.card+1 ≤ fuel+s.history.length) :
    ∃ out, runFuel d delta P W epsilon choose fuel s hr = some out := by
  classical
  induction fuel generalizing s with
  | zero =>
    by_cases ho : loopOpen d epsilon s
    · have hb := reachable_open_length_le h hd hP hs hW heps hr ho
      omega
    · exact ⟨_,by rw [runFuel]; simp only [dif_neg ho]; rfl⟩
  | succ fuel ih =>
    by_cases ho : loopOpen d epsilon s
    · cases hc : choose s hr ho with
      | empty he =>
        exact ⟨_,by rw [runFuel]; simp only [dif_pos ho,hc]; rfl⟩
      | next q e G hy =>
        have hb : d.box.card+1 ≤ fuel+(advance s q e G).history.length := by
          change d.box.card+1 ≤ fuel+(s.history ++ [e]).length
          simp only [List.length_append,List.length_singleton]
          omega
        obtain ⟨out,hout⟩ := ih (advance s q e G) (.next hr (.step ho q e G hy)) hb
        exact ⟨OAExec.countStep e out,by rw [runFuel]; simp only [dif_pos ho,hc,hout]; rfl⟩
    · exact ⟨_,by rw [runFuel]; simp only [dif_neg ho]; rfl⟩

theorem finite_return (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d delta P W epsilon) :
    ∃ out, runFuel d delta P W epsilon choose (d.box.card+1) (initialState d delta P W hW)
      (.initial hW) = some out ∧ OAExec.ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 := by
  obtain ⟨out,hout⟩ := runFuel_total h hd hP hs hW heps choose (d.box.card+1)
    (initialState d delta P W hW) (.initial hW)
    (by simp [initialState,State.history,PumpOA.initialState])
  have hex := runFuel_execution d delta P W epsilon choose _ _ (.initial hW) hout
  have hc := execution_master_count h hd hP hs hW heps (.initial hW) hex
  have hf := (execution_counts hex).1
  have hm : out.masters ≤ d.box.card+1 := by
    simpa [initialState,State.history,PumpOA.initialState] using hc
  exact ⟨out,hout,execution_sound h hd hP hW heps (initial_invariant hs hP hW) hex,hm,hf.trans hm⟩

theorem restorationCount_advance_eq_event (s : State d delta P W)
    (q : MasterChoice d delta P W s) (e : OAExec.Event d) (G : Generation d e) :
    OAExec.restorationCount (advance s q e G).core =
      OAExec.restorationCount s.core + OAExec.eventRestorations e := by
  simp only [OAExec.restorationCount,advance,State.history,restorationEvents_append,List.length_append]
  cases h : e.restoration <;> simp [eventRestorations,h]

theorem execution_restoration_count (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} {s : State d delta P W} {out : OAExec.Output n m}
    (hr : Reachable d delta P W epsilon s) (hex : Execution d delta P W epsilon s out) :
    out.restorations + OAExec.restorationCount s.core ≤ d.box.card := by
  induction hex with
  | gap _ _ => simpa using reachable_restoration_length_le h hd hP hs hW hr
  | empty _ _ => simpa using reachable_restoration_length_le h hd hP hs hW hr
  | step ho q e G hy _ ih =>
    have hb := ih (.next hr (.step ho q e G hy))
    rw [restorationCount_advance_eq_event] at hb
    simp only [OAExec.countStep]
    omega

/-- At most N+1 masters and fixed solves and N restoration calls. Pump work
is counted separately at the concrete composition endpoint. -/
theorem finite_return_with_counts (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d delta P W epsilon) :
    ∃ out, runFuel d delta P W epsilon choose (d.box.card+1) (initialState d delta P W hW)
      (.initial hW) = some out ∧ OAExec.ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card := by
  obtain ⟨out,hout,hcert,hm,hf⟩ := finite_return h hd hP hs hW heps choose
  have hex := runFuel_execution d delta P W epsilon choose _ _ (.initial hW) hout
  have hc := execution_restoration_count h hd hP hs hW (.initial hW) hex
  exact ⟨out,hout,hcert,hm,hf,by
    simpa [initialState,OAExec.restorationCount,restorationEvents,PumpOA.initialState] using hc⟩

end Chapter03.PumpSoft
