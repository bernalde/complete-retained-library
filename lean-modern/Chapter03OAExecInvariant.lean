module

public import Chapter03OAExecState

@[expose] public section

/-! Invariants derived from the actual source-ordered update. No freshness,
termination or final-answer field is assumed. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

theorem advance_invariant {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {s : State d} (hi : Invariant d seed s)
    (q : MasterChoice d seed s) {e : Event d} (he : EventValid d e) :
    Invariant d seed (advance s q e) := by
  classical
  refine ⟨validHistory_append hi.history he,?_,?_,?_,?_⟩
  · change IsLowerBound d.original d.f q.nextLower
    cases hq : q.attained with
    | false => simpa [MasterChoice.nextLower,hq] using hi.lower
    | true =>
      have hv : IsMinimizer (master d seed s.history) Prod.snd q.point := by
        simpa [hq] using q.valid
      simpa [MasterChoice.nextLower,hq] using master_lower_bound a hi.history hv
  · intro u hu
    change nextIncumbent s e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [nextIncumbent,if_pos hn] at hu
      rcases keepBest_cases hu with rfl | hu
      · exact event_feasible he hn
      · exact hi.feasible _ hu
    · exact hi.feasible _ (by simpa [nextIncumbent,hn] using hu)
  · intro u hu
    change nextIncumbent s e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [nextIncumbent,if_pos hn] at hu
      rcases keepBest_cases hu with rfl | hu
      · exact ⟨e,List.mem_append_right _ (by simp),hn,rfl⟩
      · obtain ⟨v,hv,hnv,ha⟩ := hi.provenance u hu
        exact ⟨v,List.mem_append_left _ hv,hnv,ha⟩
    · obtain ⟨v,hv,hnv,ha⟩ := hi.provenance u
        (by simpa [nextIncumbent,hn] using hu)
      exact ⟨v,List.mem_append_left _ hv,hnv,ha⟩
  · intro v hv hnv
    change v ∈ s.history ++ [e] at hv
    change ∃ u, nextIncumbent s e = some u ∧ d.f u ≤ d.f v.anchor
    by_cases hn : e.restoration = none
    · obtain ⟨u,hu,hle⟩ := keepBest_some d.f s.incumbent e.anchor
      refine ⟨u,by simpa [nextIncumbent,hn] using hu,?_⟩
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨w,hw,hlew⟩ := hi.dominates v hv hnv
        rw [hw] at hu
        exact (keepBest_le_old hu).trans hlew
      · simpa only [List.mem_singleton.mp hv] using hle
    · rcases List.mem_append.mp hv with hv | hv
      · simpa [nextIncumbent,hn] using hi.dominates v hv hnv
      · exact False.elim (hn ((List.mem_singleton.mp hv) ▸ hnv))

theorem rawStep_invariant {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {epsilon : ℝ} {s t : State d}
    (hi : Invariant d seed s) (h : RawStep d seed epsilon s t) :
    Invariant d seed t := by
  cases h with
  | step _ q e he _ => exact advance_invariant a hi q he

theorem reachable_invariant {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} {s : State d}
    (h : Reachable d seed epsilon s) : Invariant d seed s := by
  induction h with
  | initial => exact initial_invariant hs
  | next _ h ih => exact rawStep_invariant a ih h

end Chapter03.OAExec

#print axioms Chapter03.OAExec.advance_invariant
#print axioms Chapter03.OAExec.reachable_invariant
