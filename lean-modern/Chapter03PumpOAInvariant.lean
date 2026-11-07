module

public import Chapter03PumpOAModel

@[expose] public section

/-! Incumbent-relative enclosure for the actual retained pump prefix and OA
suffix. Feasible pump no-goods need not preserve the incumbent's own fiber. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

theorem initial_invariant {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
    (hs : OAExec.SeedValid d P.seed) (hP : FP.Invariant (asFPDelta d delta) P) :
    Invariant d P (initialState d P) := by
  refine ⟨⟨hs.2.1,by simp [initialState]⟩,?_,?_,?_,?_,?_⟩
  · exact hP.incumbent
  · intro u hu
    exact Or.inl hu
  · simp [initialState]
  · intro u hu
    exact ⟨u,hu,le_rfl⟩
  · intro p hp _
    exact hs.1.2 p (OAExec.original_subset_relaxation d hp)

theorem nextIncumbent_le_old {d : OAExec.Data n m l r} (s : OAExec.State d)
    (e : OAExec.Event d) {u : Point n m} (hu : s.incumbent = some u) :
    ∃ v, OAExec.nextIncumbent s e = some v ∧ d.f v ≤ d.f u := by
  classical
  by_cases hn : e.restoration = none
  · obtain ⟨v,hv,_⟩ := OAExec.keepBest_some d.f s.incumbent e.anchor
    refine ⟨v,by simpa [OAExec.nextIncumbent,hn] using hv,?_⟩
    rw [hu] at hv
    exact OAExec.keepBest_le_old hv
  · exact ⟨u,by simpa [OAExec.nextIncumbent,hn] using hu,le_rfl⟩

theorem improves_before_advance {d : OAExec.Data n m l r} {delta : ℝ}
    {P : FP.State n m} {s : OAExec.State d} (q : MasterChoice d delta P s)
    (e : OAExec.Event d) {p : Point n m} (hi : Improves d (advance s q e) p) :
    Improves d s p := by
  intro u hu
  obtain ⟨v,hv,hle⟩ := nextIncumbent_le_old s e hu
  exact (hi v hv).trans_le hle

theorem improves_pump {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
    {s : OAExec.State d} (hs : Invariant d P s) {p : Point n m}
    (hi : Improves d s p) : FP.Improves (asFPDelta d delta) P p := by
  intro u hu
  obtain ⟨v,hv,hle⟩ := hs.pump_dominates u hu
  exact (hi v hv).trans_le hle

theorem improving_mem {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P) {s : OAExec.State d}
    (hs : Invariant d P s) {p : Point n m} (hp : p ∈ d.original)
    (hi : Improves d s p) : (p,d.f p) ∈ master d delta P s.history := by
  exact ⟨FP.handoff_contains_improving (asFPDelta d delta) (asFPDelta_analytic h hd)
    hP hp (improves_pump hs hi), OAExec.original_epigraph_mem h.analytic hs.history hp⟩

theorem advance_invariant {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hP : FP.Invariant (asFPDelta d delta) P) {s : OAExec.State d}
    (hi : Invariant d P s) (q : MasterChoice d delta P s)
    {e : OAExec.Event d} (he : OAExec.EventValid d e) :
    Invariant d P (advance s q e) := by
  classical
  have hpersist : ∀ u, s.incumbent = some u →
      P.incumbent = some u ∨
        ∃ v ∈ s.history ++ [e], v.restoration = none ∧ v.anchor = u := by
    intro u hu
    rcases hi.provenance u hu with hp | ⟨v,hv,hn,ha⟩
    · exact Or.inl hp
    · exact Or.inr ⟨v,List.mem_append_left _ hv,hn,ha⟩
  refine ⟨OAExec.validHistory_append hi.history he,?_,?_,?_,?_,?_⟩
  · intro u hu
    change OAExec.nextIncumbent s e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [OAExec.nextIncumbent,if_pos hn] at hu
      rcases OAExec.keepBest_cases hu with rfl | hu
      · exact OAExec.event_feasible he hn
      · exact hi.feasible _ hu
    · exact hi.feasible _ (by simpa [OAExec.nextIncumbent,hn] using hu)
  · intro u hu
    change OAExec.nextIncumbent s e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [OAExec.nextIncumbent,if_pos hn] at hu
      rcases OAExec.keepBest_cases hu with rfl | hu
      · exact Or.inr ⟨e,List.mem_append_right _ (by simp),hn,rfl⟩
      · exact hpersist _ hu
    · exact hpersist _ (by simpa [OAExec.nextIncumbent,hn] using hu)
  · intro v hv hnv
    change v ∈ s.history ++ [e] at hv
    change ∃ u, OAExec.nextIncumbent s e = some u ∧ d.f u ≤ d.f v.anchor
    by_cases hn : e.restoration = none
    · obtain ⟨u,hu,hle⟩ := OAExec.keepBest_some d.f s.incumbent e.anchor
      refine ⟨u,by simpa [OAExec.nextIncumbent,hn] using hu,?_⟩
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨w,hw,hlew⟩ := hi.dominates v hv hnv
        rw [hw] at hu
        exact (OAExec.keepBest_le_old hu).trans hlew
      · simpa only [List.mem_singleton.mp hv] using hle
    · rcases List.mem_append.mp hv with hv | hv
      · simpa [OAExec.nextIncumbent,hn] using hi.dominates v hv hnv
      · exact False.elim (hn ((List.mem_singleton.mp hv) ▸ hnv))
  · intro u hu
    obtain ⟨v,hv,hvu⟩ := hi.pump_dominates u hu
    obtain ⟨w,hw,hwv⟩ := nextIncumbent_le_old s e hv
    exact ⟨w,hw,hwv.trans hvu⟩
  · intro p hp hnew
    have hold := improves_before_advance q e hnew
    change q.nextLower ≤ d.f p
    cases hq : q.attained with
    | false => simpa [MasterChoice.nextLower,hq] using hi.lower p hp hold
    | true =>
      have hv : IsMinimizer (master d delta P s.history) Prod.snd q.point := by
        simpa [hq] using q.valid
      simpa [MasterChoice.nextLower,hq] using
        hv.2 (p,d.f p) (improving_mem h hd hP hi hp hold)

theorem reachable_invariant {d : OAExec.Data n m l r} (h : OAExec.AvailabilityAssumptions d)
    {delta : ℝ} (hd : 0 ≤ delta) {P : FP.State n m}
    (hs : OAExec.SeedValid d P.seed) (hP : FP.Invariant (asFPDelta d delta) P)
    {epsilon : ℝ} {s : OAExec.State d} (hr : Reachable d delta P epsilon s) :
    Invariant d P s := by
  induction hr with
  | initial => exact initial_invariant hs hP
  | next _ step ih =>
    cases step with
    | step _ q _ he _ => exact advance_invariant h hd hP ih q he

theorem merged_lower {d : OAExec.Data n m l r} {P : FP.State n m}
    {s : OAExec.State d} (hs : Invariant d P s) {u : Point n m}
    (hu : s.incumbent = some u) :
    IsLowerBound d.original d.f (min (d.f u) s.lower) := by
  intro p hp
  by_cases hi : d.f p < d.f u
  · apply (min_le_right _ _).trans (hs.lower p hp ?_)
    intro v hv
    have he : v=u := Option.some.inj (hv.symm.trans hu)
    simpa [he] using hi
  · exact (min_le_left _ _).trans (le_of_not_gt hi)

theorem gap_certificate {d : OAExec.Data n m l r} {P : FP.State n m}
    {s : OAExec.State d} (hs : Invariant d P s) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {u : Point n m} (hu : s.incumbent = some u) (hg : d.f u-s.lower ≤ epsilon) :
    OAExec.ReturnCertificate d epsilon (.solution u) := by
  refine ⟨hs.feasible u hu,?_⟩
  intro p hp
  have hl := merged_lower hs hu p hp
  rcases le_total (d.f u) s.lower with h | h
  · rw [min_eq_left h] at hl
    linarith
  · rw [min_eq_right h] at hl
    linarith

theorem empty_with_incumbent {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} (hd : 0 ≤ delta)
    {P : FP.State n m} (hP : FP.Invariant (asFPDelta d delta) P)
    {s : OAExec.State d} (hs : Invariant d P s)
    (he : master d delta P s.history = ∅) {u : Point n m}
    (hu : s.incumbent = some u) : IsMinimizer d.original d.f u := by
  refine ⟨hs.feasible u hu,?_⟩
  intro p hp
  by_contra hn
  have hm := improving_mem h hd hP hs hp (show Improves d s p from by
    intro v hv
    have hvu : v=u := Option.some.inj (hv.symm.trans hu)
    simpa [hvu] using lt_of_not_ge hn)
  rw [he] at hm
  exact hm

theorem empty_without_incumbent {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} (hd : 0 ≤ delta)
    {P : FP.State n m} (hP : FP.Invariant (asFPDelta d delta) P)
    {s : OAExec.State d} (hs : Invariant d P s)
    (he : master d delta P s.history = ∅) (hu : s.incumbent = none) :
    ¬ d.original.Nonempty := by
  rintro ⟨p,hp⟩
  have hm := improving_mem h hd hP hs hp (by simp [Improves,hu])
  rw [he] at hm
  exact hm

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.reachable_invariant
#print axioms Chapter03.PumpOA.empty_with_incumbent
#print axioms Chapter03.PumpOA.empty_without_incumbent
