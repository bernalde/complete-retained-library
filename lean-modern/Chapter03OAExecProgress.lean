module

public import Chapter03OAExecInvariant

@[expose] public section

/-! Finite progress for every raw solve choice. The gap is inspected after
the appended fixed solve, so the last round may repeat one feasible fiber. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

theorem advance_target_fresh_of_open {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d} (hi : Invariant d seed s) (q : MasterChoice d seed s)
    {e : Event d} (he : EventValid d e)
    (hy : q.point.1.2 = intCast e.target)
    (ho : loopOpen d epsilon (advance s q e)) :
    e.target ∉ s.history.map Event.target := by
  classical
  rintro hm
  obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
  have hyv : q.point.1.2 = intCast v.target := by rw [ht]; exact hy
  have hnone : v.restoration = none := by
    by_contra hn
    exact q.mem.2 v hv hn hyv
  cases hq : q.attained with
  | false =>
    have hu : ¬ BddBelow (Prod.snd '' master d seed s.history) := by
      have h := q.valid
      simp only [hq,Bool.false_eq_true,↓reduceIte] at h
      exact h.2
    exact hu (event_master_bddBelow a hi.history hv hnone)
  | true =>
    have hlo := event_master_lower a hi.history hv hnone q.mem hyv
    have hj := advance_invariant a hi q he
    obtain ⟨u,hu,hup⟩ := hj.dominates v (List.mem_append_left _ hv) hnone
    have hgap := ho u hu
    have hl : (advance s q e).lower = q.point.2 := by
      simp [advance,MasterChoice.nextLower,hq]
    rw [hl] at hgap
    linarith

theorem target_nodup_length_le {d : Data n m l r} (H : List (Event d))
    (h : (H.map Event.target).Nodup) : H.length ≤ d.box.card := by
  classical
  have hs : (H.map Event.target).toFinset ⊆ d.box := by
    intro y hy
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact e.target_mem_box
  have hc := Finset.card_le_card hs
  simpa only [List.toFinset_card_of_nodup h,List.length_map] using hc

theorem reachable_open_nodup {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d} (hr : Reachable d seed epsilon s) (ho : loopOpen d epsilon s) :
    (s.history.map Event.target).Nodup := by
  classical
  induction hr with
  | initial => simp [initialState]
  | @next s t hr step ih =>
    cases step with
    | step hopen q e he hy =>
      have hf := advance_target_fresh_of_open a heps
        (reachable_invariant a hs hr) q he hy ho
      change ((s.history ++ [e]).map Event.target).Nodup
      simp only [List.map_append,List.map_singleton,List.nodup_append,
        List.nodup_singleton,true_and]
      refine ⟨ih hopen,?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton.mp hb] at hab
      exact hf (hab ▸ ha)

theorem reachable_open_length_le {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d} (hr : Reachable d seed epsilon s) (ho : loopOpen d epsilon s) :
    s.history.length ≤ d.box.card :=
  target_nodup_length_le s.history (reachable_open_nodup a hs heps hr ho)

theorem reachable_length_le_succ {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d} (hr : Reachable d seed epsilon s) :
    s.history.length ≤ d.box.card + 1 := by
  cases hr with
  | initial => simp [initialState]
  | @next s t hr step =>
    cases step with
    | step hopen q e he hy =>
      have hb := reachable_open_length_le a hs heps hr hopen
      simpa only [advance,List.length_append,List.length_singleton] using
        Nat.add_le_add_right hb 1

end Chapter03.OAExec

#print axioms Chapter03.OAExec.advance_target_fresh_of_open
#print axioms Chapter03.OAExec.reachable_open_nodup
#print axioms Chapter03.OAExec.reachable_length_le_succ
