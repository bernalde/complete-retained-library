module

public import Chapter03PumpSoftInvariant
public import Chapter03PumpSoftCoverage

@[expose] public section

/-! An open successor must use a new suffix target. A repeated success closes
the gap only after its actual fixed solve; failed fibers have actual no-goods. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.PumpSoft
variable {n m l r : ℕ} {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
variable {W : Occurrence (prefixFamily d delta P) → ℝ}

theorem advance_target_fresh_of_open (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hW : ∀ o, 0 ≤ W o)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) {s : State d delta P W}
    (hi : Invariant d P s) (q : MasterChoice d delta P W s)
    {e : OAExec.Event d} (G : Generation d e) (hy : q.point.1.2 = intCast e.target)
    (ho : loopOpen d epsilon (advance s q e G)) :
    e.target ∉ s.history.map OAExec.Event.target := by
  classical
  rintro hm
  obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hv
  have hyv : q.point.1.2 = intCast (s.history.get i).target := by rw [ht]; exact hy
  have hnone : (s.history.get i).restoration = none := by
    by_contra hn
    exact q.mem.2.2.1.2.2 _ (List.get_mem _ _) hn hyv
  cases hq : q.attained with
  | false =>
    have hu : ¬ BddBelow (cost (weight d delta P W s.policy) '' warmMaster d delta P s.history) := by
      have hh := q.valid
      simp only [hq,Bool.false_eq_true,↓reduceIte] at hh
      exact hh.2
    exact hu (warm_success_cost_bddBelow h hP hi.history W hW s.policy s.agreement i hnone)
  | true =>
    have hm : IsMinimizer (warmMaster d delta P s.history)
        (cost (weight d delta P W s.policy)) q.point := by simpa [hq] using q.valid
    have hlo : q.point.2.1 = d.f (s.history.get i).anchor :=
      warm_revisit_alpha h hP hi.history W hW s.policy s.agreement i hnone q.point hm hyv
    have hj := advance_invariant h hd hP hW hi q G
    obtain ⟨u,hu,hup⟩ := hj.dominates (s.history.get i)
      (List.mem_append_left _ (List.get_mem _ _)) hnone
    have hgap := ho u hu
    have hl : (advance s q e G).core.lower = q.point.2.1 := by
      simp [advance,MasterChoice.nextLower,hq]
    rw [hl,hlo] at hgap
    linarith

theorem reachable_open_nodup (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d delta P W} (hr : Reachable d delta P W epsilon s)
    (ho : loopOpen d epsilon s) : (s.history.map OAExec.Event.target).Nodup := by
  classical
  induction hr with
  | initial hW' => simp [initialState,State.history,PumpOA.initialState]
  | @next s t hr step ih =>
    cases step with
    | step hopen q e G hy =>
      have hf := advance_target_fresh_of_open h hd hP hW heps
        (reachable_invariant h hd hP hs hW hr) q G hy ho
      change ((s.history ++ [e]).map OAExec.Event.target).Nodup
      simp only [List.map_append,List.map_singleton,List.nodup_append,
        List.nodup_singleton,true_and]
      refine ⟨ih hopen,?_⟩
      intro u hu v hv huv
      rw [List.mem_singleton.mp hv] at huv
      exact hf (huv ▸ hu)

theorem reachable_open_length_le (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d delta P W} (hr : Reachable d delta P W epsilon s)
    (ho : loopOpen d epsilon s) : s.history.length ≤ d.box.card :=
  target_nodup_length_le s.history (reachable_open_nodup h hd hP hs hW heps hr ho)

theorem reachable_length_le_succ (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d delta P W} (hr : Reachable d delta P W epsilon s) :
    s.history.length ≤ d.box.card + 1 := by
  cases hr with
  | initial hW' => simp [initialState,State.history,PumpOA.initialState]
  | @next s t hr step =>
    cases step with
    | step hopen q e G hy =>
      have hb := reachable_open_length_le h hd hP hs hW heps hr hopen
      simpa only [advance,State.history,List.length_append,List.length_singleton] using
        Nat.add_le_add_right hb 1

theorem advance_restoration_target_fresh {s : State d delta P W} (hi : Invariant d P s)
    (q : MasterChoice d delta P W s) {e : OAExec.Event d} (G : Generation d e)
    (hn : e.restoration ≠ none) (hy : q.point.1.2 = intCast e.target) :
    e.target ∉ s.history.map OAExec.Event.target := by
  rintro hm
  obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
  have hyv : q.point.1.2 = intCast v.target := by rw [ht]; exact hy
  have hnone : v.restoration = none := by
    by_contra hnv
    exact q.mem.2.2.1.2.2 v hv hnv hyv
  have hmem := (event_fixed_minimum (hi.history.2 v hv) hnone).1
  rw [ht] at hmem
  exact event_empty G.valid hn ⟨v.x,hmem⟩

theorem repeated_target_feasible {s : State d delta P W} (hi : Invariant d P s)
    (q : MasterChoice d delta P W s) {e : OAExec.Event d} (G : Generation d e)
    (hy : q.point.1.2 = intCast e.target)
    (hr : e.target ∈ s.history.map OAExec.Event.target) : e.restoration = none := by
  by_contra hn
  exact advance_restoration_target_fresh hi q G hn hy hr

theorem reachable_restoration_nodup (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} {s : State d delta P W}
    (hr : Reachable d delta P W epsilon s) :
    ((restorationEvents s.history).map OAExec.Event.target).Nodup := by
  classical
  induction hr with
  | initial hW' => simp [initialState,State.history,PumpOA.initialState,restorationEvents]
  | @next s t hr step ih =>
    cases step with
    | step hopen q e G hy =>
      change ((restorationEvents (s.history ++ [e])).map OAExec.Event.target).Nodup
      rw [restorationEvents_append]
      by_cases hn : e.restoration.isSome
      · rw [if_pos hn]
        have hf := advance_restoration_target_fresh
          (reachable_invariant h hd hP hs hW hr) q G (Option.isSome_iff_ne_none.mp hn) hy
        have hf' : e.target ∉ (restorationEvents s.history).map OAExec.Event.target := by
          intro hm
          obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
          exact hf (List.mem_map.mpr ⟨v,(restorationEvents_mem.mp hv).1,ht⟩)
        simp only [List.map_append,List.map_singleton,List.nodup_append,
          List.nodup_singleton,true_and]
        refine ⟨ih,?_⟩
        intro u hu v hv huv
        rw [List.mem_singleton.mp hv] at huv
        exact hf' (huv ▸ hu)
      · simpa only [if_neg hn,List.append_nil] using ih

theorem reachable_restoration_length_le (h : OAExec.AvailabilityAssumptions d) (hd : 0 ≤ delta)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hs : OAExec.SeedValid d P.seed)
    (hW : ∀ o, 0 ≤ W o) {epsilon : ℝ} {s : State d delta P W}
    (hr : Reachable d delta P W epsilon s) : OAExec.restorationCount s.core ≤ d.box.card :=
  target_nodup_length_le _ (reachable_restoration_nodup h hd hP hs hW hr)

end Chapter03.PumpSoft
