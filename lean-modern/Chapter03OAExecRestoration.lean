module

public import Chapter03OAExecProgress

@[expose] public section

/-! Restoration counts use actual empty-fiber certificates. Every restoration
target is new even in a final round; hence any repeated terminal fiber is feasible. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

def restorationEvents {d : Data n m l r} (H : List (Event d)) : List (Event d) :=
  H.filter (fun e => e.restoration.isSome)

def restorationCount {d : Data n m l r} (s : State d) : ℕ :=
  (restorationEvents s.history).length

theorem restorationEvents_mem {d : Data n m l r} {H : List (Event d)}
    {e : Event d} : e ∈ restorationEvents H ↔ e ∈ H ∧ e.restoration ≠ none := by
  simp only [restorationEvents,List.mem_filter,Option.isSome_iff_ne_none]

theorem restorationEvents_append {d : Data n m l r} (H : List (Event d))
    (e : Event d) : restorationEvents (H++[e]) = restorationEvents H ++
      if e.restoration.isSome then [e] else [] := by
  cases h : e.restoration <;> simp [restorationEvents,List.filter_append,h]

theorem restorationCount_advance {d : Data n m l r} {seed : Point n m}
    (s : State d) (q : MasterChoice d seed s) (e : Event d) :
    restorationCount (advance s q e) = restorationCount s +
      if e.restoration.isSome then 1 else 0 := by
  simp only [restorationCount,advance,restorationEvents_append,List.length_append]
  split <;> simp

theorem advance_restoration_target_fresh {d : Data n m l r}
    {seed : Point n m} {s : State d} (hi : Invariant d seed s)
    (q : MasterChoice d seed s) {e : Event d} (he : EventValid d e)
    (hn : e.restoration ≠ none) (hy : q.point.1.2 = intCast e.target) :
    e.target ∉ s.history.map Event.target := by
  rintro hm
  obtain ⟨v,hv,ht⟩ := List.mem_map.mp hm
  have hyv : q.point.1.2 = intCast v.target := by rw [ht]; exact hy
  have hnone : v.restoration = none := by
    by_contra hnv
    exact q.mem.2 v hv hnv hyv
  have hmem := (event_fixed_minimum (hi.history.2 v hv) hnone).1
  rw [ht] at hmem
  exact event_empty he hn ⟨v.x,hmem⟩

theorem repeated_target_feasible {d : Data n m l r}
    {seed : Point n m} {s : State d} (hi : Invariant d seed s)
    (q : MasterChoice d seed s) {e : Event d} (he : EventValid d e)
    (hy : q.point.1.2 = intCast e.target)
    (hr : e.target ∈ s.history.map Event.target) : e.restoration = none := by
  by_contra hn
  exact advance_restoration_target_fresh hi q he hn hy hr

theorem reachable_restoration_nodup {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ}
    {s : State d} (hr : Reachable d seed epsilon s) :
    ((restorationEvents s.history).map Event.target).Nodup := by
  classical
  induction hr with
  | initial => simp [initialState,restorationEvents]
  | @next s t hr step ih =>
    cases step with
    | step hopen q e he hy =>
      change ((restorationEvents (s.history ++ [e])).map Event.target).Nodup
      rw [restorationEvents_append]
      by_cases hn : e.restoration.isSome
      · rw [if_pos hn]
        have hf := advance_restoration_target_fresh
          (reachable_invariant a hs hr) q he (Option.isSome_iff_ne_none.mp hn) hy
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
    restorationCount s ≤ d.box.card :=
  target_nodup_length_le _ (reachable_restoration_nodup a hs hr)

end Chapter03.OAExec

#print axioms Chapter03.OAExec.advance_restoration_target_fresh
#print axioms Chapter03.OAExec.repeated_target_feasible
#print axioms Chapter03.OAExec.reachable_restoration_length_le
