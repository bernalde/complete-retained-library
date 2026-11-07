module

public import Chapter02GBDHistory
public import Chapter02OAState

@[expose] public section

/-! Retained state for the repaired, projected linearized GBD procedure.
The master has only an integer tuple and a height. Empty affine fibers receive
an integer exclusion, not an affine cut. Source-derived existence of legal
replies is separate from this raw transition relation. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

structure GBDState (n m l r : ℕ) where
  history : List (GBDBatch n m l r)
  incumbent : Option (Point n m)

def gbdInit (warm : Option (Point n m) := none) : GBDState n m l r := ⟨[],warm⟩

def gbdAppend (d : ModelData n m l r) (s : GBDState n m l r)
    (b : GBDBatch n m l r) : GBDState n m l r :=
  ⟨s.history ++ [b], match gbdBatchOptimalAnchor b with
    | some p => some (oaBest d s.incumbent p)
    | none => s.incumbent⟩

/-- The best-anchor field asserts existence of an incumbent for every optimal
record. It is not conditional on the incumbent already being present. -/
structure GBDInvariant (d : ModelData n m l r) (s : GBDState n m l r) : Prop where
  valid : ∀ b ∈ s.history, gbdBatchValid d b
  feasible : ∀ u, s.incumbent = some u → u ∈ d.feasibleOn Set.univ
  best : ∀ b ∈ s.history, ∀ p, gbdBatchOptimalAnchor b = some p →
    ∃ u, s.incumbent = some u ∧ d.objective u ≤ d.objective p

theorem gbd_init_invariant (d : ModelData n m l r)
    (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    GBDInvariant d (gbdInit warm) := by
  exact ⟨by simp [gbdInit], hwarm, by simp [gbdInit]⟩

theorem gbd_append_invariant (d : ModelData n m l r) {s : GBDState n m l r}
    (hs : GBDInvariant d s) (b : GBDBatch n m l r) (hb : gbdBatchValid d b) :
    GBDInvariant d (gbdAppend d s b) := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    simp only [gbdAppend, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hs.valid c hc
    · exact hb
  · intro u hu
    cases he : gbdBatchOptimalAnchor b with
    | none => exact hs.feasible u (by simpa only [gbdAppend,he] using hu)
    | some p =>
      have hu' : oaBest d s.incumbent p = u := by
        simpa only [gbdAppend,he,Option.some.injEq] using hu
      rw [← hu']
      exact oa_best_feasible d s.incumbent p
        (gbdBatch_optimal_original d b hb p he) hs.feasible
  · intro c hc a ha
    simp only [gbdAppend, List.mem_append, List.mem_singleton] at hc
    cases he : gbdBatchOptimalAnchor b with
    | none =>
      rcases hc with hc | rfl
      · simpa only [gbdAppend,he] using hs.best c hc a ha
      · simp [he] at ha
    | some p =>
      refine ⟨oaBest d s.incumbent p, by simp [gbdAppend,he], ?_⟩
      rcases hc with hc | rfl
      · obtain ⟨u,hu,hle⟩ := hs.best c hc a ha
        rw [hu]
        exact (oa_best_le_old d u p).trans hle
      · have hpa : p = a := Option.some.inj (he.symm.trans ha)
        subst a
        exact oa_best_le_new d s.incumbent p

def gbdCompetitive (d : ModelData n m l r) (epsilon : ℝ)
    (s : GBDState n m l r) (z : IntVector m × ℝ) : Prop :=
  ∀ u, s.incumbent = some u → z.2 + epsilon < d.objective u

/-- Raw transitions allow any real epsilon, so excluded policies can be
examined. Every certified progress/finite-return theorem requires epsilon≥0.
Freshness and progress are conclusions, not constructor fields. -/
inductive GBDContinue (d : ModelData n m l r) (floor epsilon : ℝ) :
    GBDState n m l r → GBDState n m l r → Prop
  | step {s : GBDState n m l r} {z : IntVector m × ℝ} {b : GBDBatch n m l r}
      (master : IsMinimizer (gbdMaster d floor s.history) Prod.snd z)
      (competitive : gbdCompetitive d epsilon s z)
      (batch : gbdBatchValid d b) (same_integer : z.1 = b.integer) :
      GBDContinue d floor epsilon s (gbdAppend d s b)

theorem gbd_continue_invariant (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} (hs : GBDInvariant d s)
    (h : GBDContinue d floor epsilon s t) : GBDInvariant d t := by
  cases h with
  | step _ _ hb _ => exact gbd_append_invariant d hs _ hb

def gbdSeen (s : GBDState n m l r) : Finset (IntVector m) := by
  classical
  exact (s.history.map GBDBatch.integer).toFinset

def gbdRemaining (d : ModelData n m l r) (s : GBDState n m l r) : ℕ := by
  classical
  exact (oaBox d \ gbdSeen s).card

theorem gbd_competitive_unseen (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s : GBDState n m l r} (hs : GBDInvariant d s)
    {z : IntVector m × ℝ} (hz : z ∈ gbdMaster d floor s.history)
    (hc : gbdCompetitive d epsilon s z) : z.1 ∉ gbdSeen s := by
  classical
  intro hseen
  obtain ⟨b,hb,hby⟩ := List.mem_map.mp (List.mem_toFinset.mp hseen)
  have hm := (gbd_master_mem_iff d floor s.history z).mp hz
  obtain ⟨a,ha,hle⟩ := gbdBatch_processed_lower d b (hs.valid b hb) z
    (hm.2.2 b hb) hby.symm
  obtain ⟨u,hu,hua⟩ := hs.best b hb a ha
  have hcomp := hc u hu
  linarith

theorem gbd_seen_append (d : ModelData n m l r) (s : GBDState n m l r)
    (b : GBDBatch n m l r) :
    gbdSeen (gbdAppend d s b) = insert b.integer (gbdSeen s) := by
  classical
  ext y
  simp [gbdSeen, gbdAppend, or_comm]

theorem gbd_continue_remaining_lt (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s t : GBDState n m l r} (hs : GBDInvariant d s)
    (h : GBDContinue d floor epsilon s t) : gbdRemaining d t < gbdRemaining d s := by
  classical
  cases h with
  | @step z b hm hc hb hy =>
    have hn : b.integer ∉ gbdSeen s := by
      simpa only [hy] using gbd_competitive_unseen d hepsilon hs hm.1 hc
    have hmem : b.integer ∈ oaBox d \ gbdSeen s :=
      Finset.mem_sdiff.mpr ⟨by simpa [oaBox] using hb.1, hn⟩
    have heq : oaBox d \ gbdSeen (gbdAppend d s b) =
        (oaBox d \ gbdSeen s).erase b.integer := by
      rw [gbd_seen_append]
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
      tauto
    unfold gbdRemaining
    rw [heq]
    exact Finset.card_erase_lt_of_mem hmem

theorem gbd_continue_history_retained (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} (h : GBDContinue d floor epsilon s t) :
    ∃ b, t.history = s.history ++ [b] := by
  cases h with
  | step _ _ _ _ => exact ⟨_,rfl⟩

theorem gbd_continue_master_subset (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} (h : GBDContinue d floor epsilon s t) :
    gbdMaster d floor t.history ⊆ gbdMaster d floor s.history := by
  obtain ⟨b,hb⟩ := gbd_continue_history_retained d h
  rw [hb,gbd_master_append]
  exact Set.inter_subset_left

theorem gbd_master_values_monotone (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} (h : GBDContinue d floor epsilon s t)
    {z w : IntVector m × ℝ}
    (hz : IsMinimizer (gbdMaster d floor s.history) Prod.snd z)
    (hw : IsMinimizer (gbdMaster d floor t.history) Prod.snd w) :
    z.2 ≤ w.2 := hz.2 w (gbd_continue_master_subset d h hw.1)

/-- Reuse only the model-level result/certificate types; this does not identify
GBD state, master, transition or decision counts with those of OA. -/
abbrev GBDResult := OAResult
abbrev GBDReturnCertificate := @OAReturnCertificate

inductive GBDStop (d : ModelData n m l r) (floor epsilon : ℝ)
    (s : GBDState n m l r) : GBDResult n m → Prop
  | empty (h : gbdMaster d floor s.history = ∅) : GBDStop d floor epsilon s .infeasible
  | gap {z : IntVector m × ℝ} {u : Point n m}
      (master : IsMinimizer (gbdMaster d floor s.history) Prod.snd z)
      (incumbent : s.incumbent = some u)
      (test : d.objective u ≤ z.2 + epsilon) :
      GBDStop d floor epsilon s (.solution u)

theorem gbd_stop_sound (d : ModelData n m l r) {floor epsilon : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {s : GBDState n m l r} (hs : GBDInvariant d s) {result : GBDResult n m}
    (h : GBDStop d floor epsilon s result) : GBDReturnCertificate d epsilon result := by
  cases h with
  | empty he =>
    rintro ⟨p,hp⟩
    obtain ⟨_,_,_,y,_,hpy⟩ := (source_feasible_iff d Set.univ p).mp hp
    have hm := gbd_master_contains_feasible d floor s.history hs.valid hf hconv p hp y hpy
    rw [he] at hm
    exact hm
  | @gap z u hm hi ht =>
    exact ⟨hs.feasible u hi,z.2,gbd_master_lowerBound d floor s.history hs.valid hf hconv hm,ht⟩

theorem gbd_certificate_objectiveWithin (d : ModelData n m l r) {epsilon : ℝ}
    {p : Point n m} (h : GBDReturnCertificate d epsilon (.solution p)) :
    ObjectiveWithin d epsilon p := oa_certificate_objectiveWithin d h

theorem gbd_certificate_zero_optimal (d : ModelData n m l r) {p : Point n m}
    (h : GBDReturnCertificate d 0 (.solution p)) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective p := oa_certificate_zero_optimal d h

/-- A solution certificate itself forces a nonnegative absolute gap. Thus raw
negative-epsilon syntax cannot be mistaken for a usable tolerance guarantee. -/
theorem gbd_solution_certificate_nonnegative (d : ModelData n m l r) {epsilon : ℝ}
    {p : Point n m} (h : GBDReturnCertificate d epsilon (.solution p)) :
    0 ≤ epsilon := by
  obtain ⟨hp,lower,hl,hgap⟩ := h
  have hbound := hl p hp
  linarith

theorem gbd_negative_no_solution_stop (d : ModelData n m l r) {floor epsilon : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (he : epsilon < 0) {s : GBDState n m l r} (hs : GBDInvariant d s)
    {p : Point n m} : ¬ GBDStop d floor epsilon s (.solution p) := by
  intro h
  exact (not_le_of_gt he) (gbd_solution_certificate_nonnegative d (gbd_stop_sound d hf hconv hs h))

theorem gbd_step_total (d : ModelData n m l r) (floor epsilon : ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (s : GBDState n m l r) :
    (∃ result, GBDStop d floor epsilon s result) ∨
      ∃ t, GBDContinue d floor epsilon s t := by
  classical
  rcases gbd_master_reply d floor s.history with hempty | ⟨z,hz⟩
  · exact Or.inl ⟨.infeasible,.empty hempty⟩
  · by_cases hgap : ∃ u, s.incumbent = some u ∧ d.objective u ≤ z.2 + epsilon
    · obtain ⟨u,hu,ht⟩ := hgap
      exact Or.inl ⟨.solution u,.gap hz hu ht⟩
    · have hc : gbdCompetitive d epsilon s z := by
        intro u hu
        exact lt_of_not_ge (fun h => hgap ⟨u,hu,h⟩)
      obtain ⟨b,hb,hby⟩ := gbd_fiber_reply_exists d z.1
        ((gbd_master_mem_iff d floor s.history z).mp hz.1).1 hbase hconv hdiff hCQ
      exact Or.inr ⟨gbdAppend d s b,.step hz hc hb hby.symm⟩

theorem gbd_init_remaining (d : ModelData n m l r) (warm : Option (Point n m)) :
    gbdRemaining d (gbdInit warm) = (oaBox d).card := by
  classical
  simp [gbdRemaining,gbdSeen,gbdInit]

theorem gbd_continue_incumbent_monotone (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} (h : GBDContinue d floor epsilon s t)
    {u : Point n m} (hu : s.incumbent = some u) :
    ∃ v, t.incumbent = some v ∧ d.objective v ≤ d.objective u := by
  cases h with
  | @step z b _ _ _ _ =>
    cases he : gbdBatchOptimalAnchor b with
    | none => exact ⟨u,by simpa only [gbdAppend,he] using hu,le_rfl⟩
    | some p =>
      refine ⟨oaBest d (some u) p,?_,oa_best_le_old d u p⟩
      simp only [gbdAppend,he,hu]

theorem gbd_incumbent_master_nonempty (d : ModelData n m l r) {floor : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {s : GBDState n m l r} (hs : GBDInvariant d s)
    {u : Point n m} (hu : s.incumbent = some u) :
    (gbdMaster d floor s.history).Nonempty := by
  have huf := hs.feasible u hu
  obtain ⟨_,_,_,y,_,huy⟩ := (source_feasible_iff d Set.univ u).mp huf
  exact ⟨(y,d.objective u),
    gbd_master_contains_feasible d floor s.history hs.valid hf hconv u huf y huy⟩

theorem gbd_empty_master_no_incumbent (d : ModelData n m l r) {floor : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {s : GBDState n m l r} (hs : GBDInvariant d s)
    (hempty : gbdMaster d floor s.history = ∅) : s.incumbent = none := by
  cases hi : s.incumbent with
  | none => rfl
  | some u =>
    have hu := gbd_incumbent_master_nonempty d hf hconv hs hi
    rw [hempty] at hu
    exact False.elim (Set.not_nonempty_empty hu)

end Chapter02

#print axioms Chapter02.gbd_init_invariant
#print axioms Chapter02.gbd_append_invariant
#print axioms Chapter02.gbd_continue_invariant
#print axioms Chapter02.gbd_competitive_unseen
#print axioms Chapter02.gbd_seen_append
#print axioms Chapter02.gbd_continue_remaining_lt
#print axioms Chapter02.gbd_continue_history_retained
#print axioms Chapter02.gbd_continue_master_subset
#print axioms Chapter02.gbd_master_values_monotone
#print axioms Chapter02.gbd_stop_sound
#print axioms Chapter02.gbd_certificate_objectiveWithin
#print axioms Chapter02.gbd_certificate_zero_optimal
#print axioms Chapter02.gbd_solution_certificate_nonnegative
#print axioms Chapter02.gbd_negative_no_solution_stop
#print axioms Chapter02.gbd_step_total
#print axioms Chapter02.gbd_init_remaining
#print axioms Chapter02.gbd_continue_incumbent_monotone
#print axioms Chapter02.gbd_incumbent_master_nonempty
#print axioms Chapter02.gbd_empty_master_no_incumbent
