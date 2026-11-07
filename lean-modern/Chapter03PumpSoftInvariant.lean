module

public import Chapter03PumpSoftState
public import Chapter03PumpSoftGeometry

@[expose] public section

/-! The residual lower bound is incumbent-relative. The actual warm prefix
may exclude its saved incumbent's fiber, so only min(incumbent,lower) is global. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.PumpSoft
variable {n m l r : ℕ} {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
variable {W : Occurrence (prefixFamily d delta P) → ℝ}

theorem state_improving_embed (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) {s : State d delta P W}
    (hi : Invariant d P s) {p : Point n m} (hp : p ∈ d.original)
    (himprove : PumpOA.Improves d s.core p) :
    embed d.f (family d delta P s.history) p ∈ warmMaster d delta P s.history := by
  exact improving_embed_mem h hd hP hi hp himprove

theorem master_lower_bound (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hW : ∀ o, 0 ≤ W o)
    {s : State d delta P W} (hi : Invariant d P s)
    {z : Candidate (family d delta P s.history)}
    (hm : IsMinimizer (warmMaster d delta P s.history) (cost (weight d delta P W s.policy)) z)
    {p : Point n m} (hp : p ∈ d.original) (himprove : PumpOA.Improves d s.core p) :
    z.2.1 ≤ d.f p := by
  have hn := penalty_nonneg (weight_nonneg d delta P W hW s.policy) hm.1
  have hb := hm.2 _ (state_improving_embed h hd hP hi hp himprove)
  rw [cost_embed] at hb
  exact (le_add_of_nonneg_right hn).trans hb

theorem advance_invariant (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hW : ∀ o, 0 ≤ W o)
    {s : State d delta P W} (hi : Invariant d P s) (q : MasterChoice d delta P W s)
    {e : OAExec.Event d} (G : Generation d e) : Invariant d P (advance s q e G) := by
  classical
  have hpersist : ∀ u, s.incumbent = some u →
      P.incumbent = some u ∨
        ∃ v ∈ s.history ++ [e], v.restoration = none ∧ v.anchor = u := by
    intro u hu
    rcases hi.provenance u hu with hp | ⟨v,hv,hn,ha⟩
    · exact Or.inl hp
    · exact Or.inr ⟨v,List.mem_append_left _ hv,hn,ha⟩
  refine ⟨OAExec.validHistory_append hi.history G.valid,?_,?_,?_,?_,?_⟩
  · intro u hu
    change OAExec.nextIncumbent s.core e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [OAExec.nextIncumbent,if_pos hn] at hu
      rcases OAExec.keepBest_cases hu with rfl | hu
      · exact OAExec.event_feasible G.valid hn
      · exact hi.feasible _ hu
    · exact hi.feasible _ (by simpa [OAExec.nextIncumbent,hn] using hu)
  · intro u hu
    change OAExec.nextIncumbent s.core e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [OAExec.nextIncumbent,if_pos hn] at hu
      rcases OAExec.keepBest_cases hu with rfl | hu
      · exact Or.inr ⟨e,List.mem_append_right _ (by simp),hn,rfl⟩
      · exact hpersist _ hu
    · exact hpersist _ (by simpa [OAExec.nextIncumbent,hn] using hu)
  · intro v hv hnv
    change v ∈ s.history ++ [e] at hv
    change ∃ u, OAExec.nextIncumbent s.core e = some u ∧ d.f u ≤ d.f v.anchor
    by_cases hn : e.restoration = none
    · obtain ⟨u,hu,hle⟩ := OAExec.keepBest_some d.f s.incumbent e.anchor
      refine ⟨u,by simpa [OAExec.nextIncumbent,hn] using hu,?_⟩
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨w,hw,hlew⟩ := hi.dominates v hv hnv
        change s.incumbent = some w at hw
        rw [hw] at hu
        exact (OAExec.keepBest_le_old hu).trans hlew
      · simpa only [List.mem_singleton.mp hv] using hle
    · rcases List.mem_append.mp hv with hv | hv
      · simpa [OAExec.nextIncumbent,hn] using hi.dominates v hv hnv
      · exact False.elim (hn ((List.mem_singleton.mp hv) ▸ hnv))
  · intro u hu
    obtain ⟨v,hv,hvu⟩ := hi.pump_dominates u hu
    obtain ⟨w,hw,hwv⟩ := PumpOA.nextIncumbent_le_old s.core e hv
    exact ⟨w,hw,hwv.trans hvu⟩
  · intro p hp hnew
    have hold := improves_before_advance q e G hnew
    change q.nextLower ≤ d.f p
    cases hq : q.attained with
    | false => simpa [MasterChoice.nextLower,hq] using hi.lower p hp hold
    | true =>
      have hv : IsMinimizer (warmMaster d delta P s.history)
          (cost (weight d delta P W s.policy)) q.point := by simpa [hq] using q.valid
      simpa [MasterChoice.nextLower,hq] using master_lower_bound h hd hP hW hi hv hp hold

theorem reachable_invariant (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} {s : State d delta P W}
    (hr : Reachable d delta P W epsilon s) : Invariant d P s := by
  induction hr with
  | initial hW' => exact initial_invariant hs hP hW'
  | next _ step ih =>
    cases step with
    | step _ q _ G _ => exact advance_invariant h hd hP hW ih q G

theorem empty_with_incumbent (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) {s : State d delta P W}
    (hi : Invariant d P s) (he : warmMaster d delta P s.history = ∅)
    {u : Point n m} (hu : s.incumbent = some u) : IsMinimizer d.original d.f u := by
  refine ⟨hi.feasible u hu,?_⟩
  intro p hp
  by_contra hn
  have hm := state_improving_embed h hd hP hi hp
    (show PumpOA.Improves d s.core p from by
      intro v hv
      have hvu : v = u := Option.some.inj (hv.symm.trans hu)
      simpa [hvu] using lt_of_not_ge hn)
  rw [he] at hm
  exact hm

theorem empty_without_incumbent (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) {s : State d delta P W}
    (hi : Invariant d P s) (he : warmMaster d delta P s.history = ∅)
    (hu : s.incumbent = none) : ¬ d.original.Nonempty := by
  rintro ⟨p,hp⟩
  have hm := state_improving_embed h hd hP hi hp (by simp [PumpOA.Improves,hu])
  rw [he] at hm
  exact hm

end Chapter03.PumpSoft
