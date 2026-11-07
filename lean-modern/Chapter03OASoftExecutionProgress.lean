module

public import Chapter03OASoftExecutionState

@[expose] public section

/-! Derived soft progress. A repeated failed fiber is excluded by its actual
no-good; a retained success bounds the full cost globally and forces stripped
alpha equality on an attained same-fiber reply. The appended fixed solve occurs
before the next gap inspection. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.OASoftExec
variable {n m l r : ℕ}

theorem advance_target_fresh_of_open {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d} (hi : Invariant d seed s) (q : MasterChoice d seed s)
    {e : Event d} (G : Generation d e)
    (hy : q.point.1.2 = intCast e.target)
    (ho : loopOpen d epsilon (advance s q e G)) :
    e.target ∉ s.history.map Event.target := by
  classical
  rintro hm
  obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hv
  have hyv : q.point.1.2 = intCast (s.history.get i).target := by rw [ht]; exact hy
  have hnone : (s.history.get i).restoration = none := by
    by_contra hn
    exact q.mem.2.2.1.1 _ (List.get_mem _ _) hn hyv
  cases hq : q.attained with
  | false =>
    have hu : ¬ BddBelow (cost (s.policy.weight seed) '' historyMaster d seed s.history) := by
      have h := q.valid
      simp only [hq,Bool.false_eq_true,↓reduceIte] at h
      exact h.2
    exact hu (s.policy.successful_master_available a seed hi.history.1 i hnone).2.1
  | true =>
    have hm : IsMinimizer (historyMaster d seed s.history)
        (cost (s.policy.weight seed)) q.point := by simpa [hq] using q.valid
    have hc := s.policy.event_coverage a seed hi.history.1 i hnone
    have hr := supported_soft_revisit_closure d a seed s.history hi.history i hnone
      ((s.policy.generation i).certificate hnone) (fun _ => True) trivial
      (s.policy.weight seed) (s.policy.weight_nonneg seed) _ _ hc q.point hm hyv
    have hlo : q.point.2.1 = d.f (s.history.get i).anchor := hr.2.2.1
    have hj := advance_invariant a hi q G
    obtain ⟨u,hu,hup⟩ := hj.dominates (s.history.get i)
      (List.mem_append_left _ (List.get_mem _ _)) hnone
    have hgap := ho u hu
    have hl : (advance s q e G).core.lower = q.point.2.1 := by
      simp [advance,State.core,MasterChoice.nextLower,hq]
    rw [hl,hlo] at hgap
    linarith

theorem reachable_open_nodup {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d} (hr : Reachable d seed epsilon s) (ho : loopOpen d epsilon s) :
    (s.history.map Event.target).Nodup := by
  classical
  induction hr with
  | initial P0 => simp [initialState,State.history,State.core,OAExec.initialState]
  | @next s t hr step ih =>
    cases step with
    | step hopen q e G hy =>
      have hf := advance_target_fresh_of_open a heps
        (reachable_invariant a hs hr) q G hy ho
      change ((s.history ++ [e]).map Event.target).Nodup
      simp only [List.map_append,List.map_singleton,List.nodup_append,
        List.nodup_singleton,true_and]
      refine ⟨ih hopen,?_⟩
      intro u hu v hv huv
      rw [List.mem_singleton.mp hv] at huv
      exact hf (huv ▸ hu)

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
  | initial P0 => simp [initialState,State.history,State.core,OAExec.initialState]
  | @next s t hr step =>
    cases step with
    | step hopen q e G hy =>
      have hb := reachable_open_length_le a hs heps hr hopen
      simpa only [advance,State.history,State.core,List.length_append,List.length_singleton] using
        Nat.add_le_add_right hb 1

theorem advance_restoration_target_fresh {d : Data n m l r}
    {seed : Point n m} {s : State d} (hi : Invariant d seed s)
    (q : MasterChoice d seed s) {e : Event d} (G : Generation d e)
    (hn : e.restoration ≠ none) (hy : q.point.1.2 = intCast e.target) :
    e.target ∉ s.history.map Event.target := by
  rintro hm
  obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
  have hyv : q.point.1.2 = intCast v.target := by rw [ht]; exact hy
  have hnone : v.restoration = none := by
    by_contra hnv
    exact q.mem.2.2.1.1 v hv hnv hyv
  have hmem := (event_fixed_minimum (hi.history.2 v hv) hnone).1
  rw [ht] at hmem
  exact event_empty G.valid hn ⟨v.x,hmem⟩

theorem repeated_target_feasible {d : Data n m l r}
    {seed : Point n m} {s : State d} (hi : Invariant d seed s)
    (q : MasterChoice d seed s) {e : Event d} (G : Generation d e)
    (hy : q.point.1.2 = intCast e.target)
    (hr : e.target ∈ s.history.map Event.target) : e.restoration = none := by
  by_contra hn
  exact advance_restoration_target_fresh hi q G hn hy hr

theorem reachable_restoration_nodup {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ}
    {s : State d} (hr : Reachable d seed epsilon s) :
    ((restorationEvents s.history).map Event.target).Nodup := by
  classical
  induction hr with
  | initial P0 => simp [initialState,State.history,State.core,OAExec.initialState,restorationEvents]
  | @next s t hr step ih =>
    cases step with
    | step hopen q e G hy =>
      change ((restorationEvents (s.history ++ [e])).map Event.target).Nodup
      rw [restorationEvents_append]
      by_cases hn : e.restoration.isSome
      · rw [if_pos hn]
        have hf := advance_restoration_target_fresh
          (reachable_invariant a hs hr) q G (Option.isSome_iff_ne_none.mp hn) hy
        have hf' : e.target ∉ (restorationEvents s.history).map Event.target := by
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

theorem reachable_restoration_length_le {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ}
    {s : State d} (hr : Reachable d seed epsilon s) :
    OAExec.restorationCount s.core ≤ d.box.card :=
  target_nodup_length_le _ (reachable_restoration_nodup a hs hr)


end Chapter03.OASoftExec
