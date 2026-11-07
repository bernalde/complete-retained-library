module

public import Chapter03PumpOAProgress

@[expose] public section

/-! Restoration counts use actual empty-fiber certificates. Every restoration
target is new even in a final round; hence any repeated terminal fiber is feasible. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

theorem restorationCount_advance_eq_event {d : OAExec.Data n m l r}
    {delta : ℝ} {P : FP.State n m} (s : OAExec.State d)
    (q : MasterChoice d delta P s) (e : OAExec.Event d) :
    OAExec.restorationCount (advance s q e) = OAExec.restorationCount s +
      OAExec.eventRestorations e := by
  simp only [OAExec.restorationCount, advance, OAExec.restorationEvents_append,
    List.length_append]
  cases he : e.restoration <;> simp [OAExec.eventRestorations, he]

theorem advance_restoration_target_fresh {d : OAExec.Data n m l r}
    {delta : ℝ} {P : FP.State n m} {s : OAExec.State d} (hi : Invariant d P s)
    (q : MasterChoice d delta P s) {e : OAExec.Event d} (he : OAExec.EventValid d e)
    (hn : e.restoration ≠ none) (hy : q.point.1.2 = intCast e.target) :
    e.target ∉ s.history.map OAExec.Event.target := by
  rintro hm
  obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
  have hyv : q.point.1.2 = intCast v.target := by rw [ht]; exact hy
  have hnone : v.restoration = none := by
    by_contra hnv
    exact q.mem.2.2 v hv hnv hyv
  have hmem := (OAExec.event_fixed_minimum (hi.history.2 v hv) hnone).1
  rw [ht] at hmem
  exact OAExec.event_empty he hn ⟨v.x,hmem⟩

theorem repeated_target_feasible {d : OAExec.Data n m l r}
    {delta : ℝ} {P : FP.State n m} {s : OAExec.State d} (hi : Invariant d P s)
    (q : MasterChoice d delta P s) {e : OAExec.Event d} (he : OAExec.EventValid d e)
    (hy : q.point.1.2 = intCast e.target)
    (hr : e.target ∈ s.history.map OAExec.Event.target) : e.restoration = none := by
  by_contra hn
  exact advance_restoration_target_fresh hi q he hn hy hr

theorem reachable_restoration_nodup {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ}
    {s : OAExec.State d} (hr : Reachable d delta P epsilon s) :
    ((OAExec.restorationEvents s.history).map OAExec.Event.target).Nodup := by
  classical
  induction hr with
  | initial => simp [initialState,OAExec.restorationEvents]
  | @next s t hr step ih =>
    cases step with
    | step hopen q e he hy =>
      change ((OAExec.restorationEvents (s.history ++ [e])).map OAExec.Event.target).Nodup
      rw [OAExec.restorationEvents_append]
      by_cases hn : e.restoration.isSome
      · rw [if_pos hn]
        have hf := advance_restoration_target_fresh
          (reachable_invariant h hd hs hP hr) q he (Option.isSome_iff_ne_none.mp hn) hy
        have hf' : e.target ∉ (OAExec.restorationEvents s.history).map OAExec.Event.target := by
          intro hm
          obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
          exact hf (List.mem_map.mpr ⟨v,(OAExec.restorationEvents_mem.mp hv).1,ht⟩)
        simp only [List.map_append,List.map_singleton,List.nodup_append,
          List.nodup_singleton,true_and]
        refine ⟨ih,?_⟩
        intro u hu v hv huv
        rw [List.mem_singleton.mp hv] at huv
        exact hf' (huv ▸ hu)
      · simpa only [if_neg hn,List.append_nil] using ih

theorem reachable_restoration_length_le {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ}
    {s : OAExec.State d} (hr : Reachable d delta P epsilon s) :
    OAExec.restorationCount s ≤ d.box.card :=
  target_nodup_length_le _ (reachable_restoration_nodup h hd hP hs hr)

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.advance_restoration_target_fresh
#print axioms Chapter03.PumpOA.repeated_target_feasible
#print axioms Chapter03.PumpOA.reachable_restoration_length_le
