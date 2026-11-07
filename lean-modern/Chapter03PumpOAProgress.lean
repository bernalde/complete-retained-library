module

public import Chapter03PumpOAInvariant

@[expose] public section

/-! Finite progress for every raw solve choice. The gap is inspected after
the appended fixed solve, so the last round may repeat one feasible fiber. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

theorem advance_target_fresh_of_open {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : OAExec.State d} (hi : Invariant d P s) (q : MasterChoice d delta P s)
    {e : OAExec.Event d} (he : OAExec.EventValid d e)
    (hy : q.point.1.2 = intCast e.target)
    (ho : OAExec.loopOpen d epsilon (advance s q e)) :
    e.target ∉ s.history.map OAExec.Event.target := by
  classical
  rintro hm
  obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
  have hyv : q.point.1.2 = intCast v.target := by rw [ht]; exact hy
  have hnone : v.restoration = none := by
    by_contra hn
    exact q.mem.2.2 v hv hn hyv
  cases hq : q.attained with
  | false =>
    have hu : ¬ BddBelow (Prod.snd '' master d delta P s.history) := by
      have h := q.valid
      simp only [hq,Bool.false_eq_true,↓reduceIte] at h
      exact h.2
    apply hu
    exact (OAExec.event_master_bddBelow h.analytic hi.history hv hnone).mono
      (Set.image_mono Set.inter_subset_right)
  | true =>
    have hlo := OAExec.event_master_lower h.analytic hi.history hv hnone q.mem.2 hyv
    have hj := advance_invariant h hd hP hi q he
    obtain ⟨u,hu,hup⟩ := hj.dominates v (List.mem_append_left _ hv) hnone
    have hgap := ho u hu
    have hl : (advance s q e).lower = q.point.2 := by
      simp [advance,MasterChoice.nextLower,hq]
    rw [hl] at hgap
    linarith

theorem target_nodup_length_le {d : OAExec.Data n m l r} (H : List (OAExec.Event d))
    (h : (H.map OAExec.Event.target).Nodup) : H.length ≤ d.box.card := by
  classical
  have hs : (H.map OAExec.Event.target).toFinset ⊆ d.box := by
    intro y hy
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact e.target_mem_box
  have hc := Finset.card_le_card hs
  simpa only [List.toFinset_card_of_nodup h,List.length_map] using hc

theorem reachable_open_nodup {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : OAExec.State d} (hr : Reachable d delta P epsilon s) (ho : OAExec.loopOpen d epsilon s) :
    (s.history.map OAExec.Event.target).Nodup := by
  classical
  induction hr with
  | initial => simp [initialState]
  | @next s t hr step ih =>
    cases step with
    | step hopen q e he hy =>
      have hf := advance_target_fresh_of_open h hd hP heps
        (reachable_invariant h hd hs hP hr) q he hy ho
      change ((s.history ++ [e]).map OAExec.Event.target).Nodup
      simp only [List.map_append,List.map_singleton,List.nodup_append,
        List.nodup_singleton,true_and]
      refine ⟨ih hopen,?_⟩
      intro u hu v hv huv
      rw [List.mem_singleton.mp hv] at huv
      exact hf (huv ▸ hu)

theorem reachable_open_length_le {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : OAExec.State d} (hr : Reachable d delta P epsilon s) (ho : OAExec.loopOpen d epsilon s) :
    s.history.length ≤ d.box.card :=
  target_nodup_length_le s.history (reachable_open_nodup h hd hP hs heps hr ho)

theorem reachable_length_le_succ {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P)
    (hs : OAExec.SeedValid d P.seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : OAExec.State d} (hr : Reachable d delta P epsilon s) :
    s.history.length ≤ d.box.card + 1 := by
  cases hr with
  | initial => simp [initialState]
  | @next s t hr step =>
    cases step with
    | step hopen q e he hy =>
      have hb := reachable_open_length_le h hd hP hs heps hr hopen
      simpa only [advance,List.length_append,List.length_singleton] using
        Nat.add_le_add_right hb 1

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.advance_target_fresh_of_open
#print axioms Chapter03.PumpOA.reachable_open_nodup
#print axioms Chapter03.PumpOA.reachable_length_le_succ
