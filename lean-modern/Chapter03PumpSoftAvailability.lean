module

public import Chapter03PumpSoftCoverage
public import Chapter03PumpSoftAttainment

@[expose] public section

noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy Chapter03.OASoftExecutionAvailability
namespace Chapter03.PumpSoft
variable {n m l r : ℕ}

theorem warm_master_attained_of_bddBelow (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) (H : List (OAExec.Event d))
    (w : Occurrence (family d delta P H) → ℝ)
    (hne : (warmMaster d delta P H).Nonempty)
    (hb : BddBelow (cost w '' warmMaster d delta P H)) :
    ∃ z, IsMinimizer (warmMaster d delta P H) (cost w) z := by
  exact PumpSoftAttainment.soft_master_attained_of_bddBelow d (family d delta P H)
    (familyDf d delta P H) (keep P H) (keep_same_y P H) w hne hb

theorem requested_generation_exists {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (hard : HardAffineEntailment d)
    (hne : d.relaxation.Nonempty) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) {z : Candidate (family d delta P H)}
    (hz : z ∈ warmMaster d delta P H) :
    ∃ e : OAExec.Event d, Nonempty (Generation d e) ∧ z.1.2 = intCast e.target := by
  classical
  obtain ⟨y,hy,hsame⟩ := hz.2.1
  by_cases hf : (fiber d.model (intCast y)).Nonempty
  · obtain ⟨x,hx⟩ := fixed_generation_exists h hard y hy hf
    exact ⟨⟨y,hy,x,none⟩,hx,hsame⟩
  · have hslice : (OAExec.hardSlice d y).Nonempty := by
      refine ⟨z.1,?_,hsame⟩
      apply (OAExec.asFP_base_iff d z.1).mpr
      exact ⟨hz.1,by rw [hsame]; exact hy⟩
    obtain ⟨x,s,hx⟩ := restoration_generation_exists h hard hne y hy hslice hf
    exact ⟨⟨y,hy,x,some s⟩,hx,hsame⟩

end Chapter03.PumpSoft
