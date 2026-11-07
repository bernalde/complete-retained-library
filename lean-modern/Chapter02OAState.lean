module

public import Chapter02OAHistory
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Lemmas

@[expose] public section

/-! Concrete retained-history OA state. Raw steps store exact subproblem
outcomes, never freshness, KKT multipliers or an exclusion conclusion.
The feasible-master stop is optional; the mandatory weak gap test precedes
each continuing fixed-fiber solve. Independent acceptance is recorded apart. -/
noncomputable section
open scoped BigOperators
namespace Chapter02
variable {n m l r : ℕ}

structure OAState (n m : ℕ) where
  history : List (OABatch n m)
  incumbent : Option (Point n m)

def oaInit (warm : Option (Point n m) := none) : OAState n m := ⟨[],warm⟩

def oaBest (d : ModelData n m l r) (old : Option (Point n m))
    (p : Point n m) : Point n m :=
  match old with
  | none => p
  | some u => if d.objective p < d.objective u then p else u

def oaAppend (d : ModelData n m l r) (s : OAState n m) (b : OABatch n m) :
    OAState n m :=
  ⟨s.history ++ [b], match b.restoration with
    | none => some (oaBest d s.incumbent b.anchor)
    | some _ => s.incumbent⟩

structure OAInvariant (d : ModelData n m l r) (s : OAState n m) : Prop where
  valid : ∀ b ∈ s.history, oaBatchValid d b
  feasible : ∀ u, s.incumbent = some u → u ∈ d.feasibleOn Set.univ
  best : ∀ b ∈ s.history, b.restoration = none →
    ∃ u, s.incumbent = some u ∧ d.objective u ≤ d.objective b.anchor

theorem oa_init_invariant (d : ModelData n m l r)
    (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    OAInvariant d (oaInit warm) := by
  exact ⟨by simp [oaInit], hwarm, by simp [oaInit]⟩

theorem oa_best_le_new (d : ModelData n m l r) (old : Option (Point n m))
    (p : Point n m) : d.objective (oaBest d old p) ≤ d.objective p := by
  cases old with
  | none => exact le_rfl
  | some u =>
    simp only [oaBest]
    split
    · exact le_rfl
    · rename_i h
      exact le_of_not_gt h

theorem oa_best_le_old (d : ModelData n m l r) (u p : Point n m) :
    d.objective (oaBest d (some u) p) ≤ d.objective u := by
  simp only [oaBest]
  split
  · rename_i h
    exact h.le
  · exact le_rfl

theorem oa_best_feasible (d : ModelData n m l r) (old : Option (Point n m))
    (p : Point n m) (hp : p ∈ d.feasibleOn Set.univ)
    (ho : ∀ u, old = some u → u ∈ d.feasibleOn Set.univ) :
    oaBest d old p ∈ d.feasibleOn Set.univ := by
  cases old with
  | none => exact hp
  | some u =>
    simp only [oaBest]
    split
    · exact hp
    · exact ho u rfl

theorem oa_append_invariant (d : ModelData n m l r) {s : OAState n m}
    (hs : OAInvariant d s) (b : OABatch n m) (hb : oaBatchValid d b) :
    OAInvariant d (oaAppend d s b) := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    simp only [oaAppend, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hs.valid c hc
    · exact hb
  · intro u hu
    cases he : b.restoration with
    | none =>
      have hu' : oaBest d s.incumbent b.anchor = u := by
        simpa only [oaAppend, he, Option.some.injEq] using hu
      rw [← hu']
      exact oa_best_feasible d s.incumbent b.anchor
        (oaBatch_feasible_original d b hb he) hs.feasible
    | some rho =>
      exact hs.feasible u (by simpa only [oaAppend,he] using hu)
  · intro c hc hn
    simp only [oaAppend, List.mem_append, List.mem_singleton] at hc
    cases he : b.restoration with
    | none =>
      refine ⟨oaBest d s.incumbent b.anchor, by simp [oaAppend,he], ?_⟩
      rcases hc with hc | rfl
      · obtain ⟨u,hu,hle⟩ := hs.best c hc hn
        rw [hu]
        exact (oa_best_le_old d u b.anchor).trans hle
      · exact oa_best_le_new d s.incumbent c.anchor
    | some rho =>
      rcases hc with hc | rfl
      · simpa only [oaAppend,he] using hs.best c hc hn
      · simp [he] at hn

def oaCompetitive (d : ModelData n m l r) (epsilon : ℝ)
    (s : OAState n m) (q : Point n m) : Prop :=
  ∀ u, s.incumbent = some u → d.objective q + epsilon < d.objective u

inductive OAContinue (d : ModelData n m l r) (epsilon : ℝ) :
    OAState n m → OAState n m → Prop
  | step {s : OAState n m} {q : Point n m} {b : OABatch n m}
      (master : IsMinimizer (oaMaster d s.history) d.objective q)
      (competitive : oaCompetitive d epsilon s q)
      (batch : oaBatchValid d b) (same_integer : q.2 = oaIntCast b.integer) :
      OAContinue d epsilon s (oaAppend d s b)

theorem oa_continue_invariant (d : ModelData n m l r) {epsilon : ℝ}
    {s t : OAState n m} (hs : OAInvariant d s) (h : OAContinue d epsilon s t) :
    OAInvariant d t := by
  cases h with
  | step _ _ hb _ => exact oa_append_invariant d hs _ hb

def oaSeen (s : OAState n m) : Finset (IntVector m) := by
  classical
  exact (s.history.map OABatch.integer).toFinset

def oaBox (d : ModelData n m l r) : Finset (IntVector m) :=
  (integerBox_finite d.lo d.hi).toFinset

def oaRemaining (d : ModelData n m l r) (s : OAState n m) : ℕ := by
  classical
  exact (oaBox d \ oaSeen s).card

theorem oa_competitive_unseen (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) {s : OAState n m} (hs : OAInvariant d s)
    {q : Point n m} (hq : q ∈ oaMaster d s.history)
    (hc : oaCompetitive d epsilon s q) (y : IntVector m)
    (hy : q.2 = oaIntCast y) : y ∉ oaSeen s := by
  classical
  intro hseen
  obtain ⟨b,hb,hby⟩ := List.mem_map.mp (List.mem_toFinset.mp hseen)
  have hqm := (oa_master_mem_iff d s.history q).mp hq
  have hys : q.2 = oaIntCast b.integer := by simpa only [hby] using hy
  cases he : b.restoration with
  | none =>
    obtain ⟨u,hu,hle⟩ := hs.best b hb he
    have hbnd := oaBatch_feasible_lowerBound d b (hs.valid b hb) he
      hconv hdiff hCQ hqm.1 hys (hqm.2.2 b hb)
    have hcomp := hc u hu
    linarith
  | some rho =>
    exact oaBatch_restoration_excludes d b (hs.valid b hb) he
      hconv hdiff hqm.1 hys (hqm.2.2 b hb)

theorem oa_seen_append (d : ModelData n m l r) (s : OAState n m)
    (b : OABatch n m) : oaSeen (oaAppend d s b) = insert b.integer (oaSeen s) := by
  classical
  ext y
  simp [oaSeen, oaAppend, or_comm]

theorem oa_continue_remaining_lt (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) {s t : OAState n m} (hs : OAInvariant d s)
    (h : OAContinue d epsilon s t) : oaRemaining d t < oaRemaining d s := by
  classical
  cases h with
  | @step q b hm hc hb hy =>
    have hn := oa_competitive_unseen d hconv hdiff hCQ hepsilon hs hm.1 hc b.integer hy
    have hmem : b.integer ∈ oaBox d \ oaSeen s := by
      exact Finset.mem_sdiff.mpr ⟨by simpa [oaBox] using hb.1, hn⟩
    have heq : oaBox d \ oaSeen (oaAppend d s b) =
        (oaBox d \ oaSeen s).erase b.integer := by
      rw [oa_seen_append]
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
      tauto
    unfold oaRemaining
    rw [heq]
    exact Finset.card_erase_lt_of_mem hmem

theorem oa_continue_history_retained (d : ModelData n m l r) {epsilon : ℝ}
    {s t : OAState n m} (h : OAContinue d epsilon s t) :
    ∃ b, t.history = s.history ++ [b] := by
  cases h with
  | step _ _ _ _ => exact ⟨_,rfl⟩

theorem oa_continue_master_subset (d : ModelData n m l r) {epsilon : ℝ}
    {s t : OAState n m} (h : OAContinue d epsilon s t) :
    oaMaster d t.history ⊆ oaMaster d s.history := by
  obtain ⟨b,hb⟩ := oa_continue_history_retained d h
  rw [hb,oa_master_append]
  exact Set.inter_subset_left

theorem oa_master_values_monotone (d : ModelData n m l r) {epsilon : ℝ}
    {s t : OAState n m} (h : OAContinue d epsilon s t) {p q : Point n m}
    (hp : IsMinimizer (oaMaster d s.history) d.objective p)
    (hq : IsMinimizer (oaMaster d t.history) d.objective q) :
    d.objective p ≤ d.objective q := hp.2 q (oa_continue_master_subset d h hq.1)

inductive OAResult (n m : ℕ)
  | infeasible
  | solution (p : Point n m)

inductive OAStop (d : ModelData n m l r) (epsilon : ℝ) (s : OAState n m) :
    OAResult n m → Prop
  | empty (h : oaMaster d s.history = ∅) : OAStop d epsilon s .infeasible
  | gap {q u : Point n m} (master : IsMinimizer (oaMaster d s.history) d.objective q)
      (incumbent : s.incumbent = some u)
      (test : d.objective u ≤ d.objective q + epsilon) : OAStop d epsilon s (.solution u)
  | feasible {q : Point n m}
      (master : IsMinimizer (oaMaster d s.history) d.objective q)
      (competitive : oaCompetitive d epsilon s q)
      (feasible : q ∈ d.feasibleOn Set.univ) : OAStop d epsilon s (.solution q)

def ObjectiveWithin (d : ModelData n m l r) (epsilon : ℝ) (p : Point n m) : Prop :=
  p ∈ d.feasibleOn Set.univ ∧
    ∀ z ∈ d.feasibleOn Set.univ, d.objective p ≤ d.objective z + epsilon

def OAReturnCertificate (d : ModelData n m l r) (epsilon : ℝ)
    (result : OAResult n m) : Prop :=
  match result with
  | .infeasible => ¬ (d.feasibleOn Set.univ).Nonempty
  | .solution p => p ∈ d.feasibleOn Set.univ ∧
      ∃ lower : ℝ, IsLowerBound (d.feasibleOn Set.univ) d.objective lower ∧
        d.objective p ≤ lower + epsilon

theorem oa_stop_sound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hepsilon : 0 ≤ epsilon)
    {s : OAState n m} (hs : OAInvariant d s) {result : OAResult n m}
    (h : OAStop d epsilon s result) : OAReturnCertificate d epsilon result := by
  have hout := oa_master_contains_feasible d s.history hconv hdiff
  cases h with
  | empty he =>
    rintro ⟨p,hp⟩
    have hm := hout hp
    rw [he] at hm
    exact hm
  | @gap q u hm hi ht => exact ⟨hs.feasible u hi, d.objective q, fun p hp => hm.2 p (hout hp), ht⟩
  | @feasible q hm _ hf =>
    exact ⟨hf,d.objective q,fun p hp => hm.2 p (hout hp),by linarith⟩

theorem oa_certificate_objectiveWithin (d : ModelData n m l r) {epsilon : ℝ}
    {p : Point n m} (h : OAReturnCertificate d epsilon (.solution p)) :
    ObjectiveWithin d epsilon p := by
  obtain ⟨hp,lower,hl,hgap⟩ := h
  exact ⟨hp,fun z hz => hgap.trans (add_le_add_left (hl z hz) epsilon)⟩

theorem oa_certificate_zero_optimal (d : ModelData n m l r) {p : Point n m}
    (h : OAReturnCertificate d 0 (.solution p)) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective p := by
  have h' := oa_certificate_objectiveWithin d h
  exact ⟨h'.1,by simpa using h'.2⟩

theorem oa_step_total (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (s : OAState n m) :
    (∃ result, OAStop d epsilon s result) ∨ ∃ t, OAContinue d epsilon s t := by
  classical
  rcases oa_master_reply d s.history hbase with hempty | ⟨q,hq⟩
  · exact Or.inl ⟨.infeasible,.empty hempty⟩
  · by_cases hgap : ∃ u, s.incumbent = some u ∧ d.objective u ≤ d.objective q + epsilon
    · obtain ⟨u,hu,ht⟩ := hgap
      exact Or.inl ⟨.solution u,.gap hq hu ht⟩
    · have hc : oaCompetitive d epsilon s q := by
        intro u hu
        exact lt_of_not_ge (fun h => hgap ⟨u,hu,h⟩)
      obtain ⟨y,hy,hqy,hL⟩ := oa_master_integer_witness d s.history q hq.1
      obtain ⟨b,hb,hby⟩ := oa_fiber_reply_exists d y hy hbase hL hdiff
      exact Or.inr ⟨oaAppend d s b,.step hq hc hb (by simpa [hby] using hqy)⟩

theorem oa_init_remaining (d : ModelData n m l r) (warm : Option (Point n m)) :
    oaRemaining d (oaInit warm) = (oaBox d).card := by
  classical
  simp [oaRemaining,oaSeen,oaInit]

theorem oa_continue_incumbent_monotone (d : ModelData n m l r) {epsilon : ℝ}
    {s t : OAState n m} (h : OAContinue d epsilon s t)
    {u : Point n m} (hu : s.incumbent = some u) :
    ∃ v, t.incumbent = some v ∧ d.objective v ≤ d.objective u := by
  cases h with
  | @step q b _ _ _ _ =>
    cases he : b.restoration with
    | none =>
      refine ⟨oaBest d (some u) b.anchor,?_,oa_best_le_old d u b.anchor⟩
      simp only [oaAppend,he,hu]
    | some rho => exact ⟨u,by simpa only [oaAppend,he] using hu,le_rfl⟩

/-- With no nonlinear rows, a source-style run can solve one fiber and then
must stop at its next master. No CQ or nonempty-row assumption is needed. -/
theorem oa_zero_rows_no_two_continuations (d : ModelData n m 0 r) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s t v : OAState n m}
    (hst : OAContinue d epsilon s t) (htv : OAContinue d epsilon t v) : False := by
  cases hst with
  | @step q b hm _ hb hy =>
    have hn := oa_zero_rows_batch_not_restoration d b hb
    have hmin := oaBatch_feasible_minimizer d b hb hn
    have hqL := ((oa_master_mem_iff d s.history q).mp hm.1).1
    have hbq := hmin.2 q ⟨⟨hqL,hy⟩,fun j => Fin.elim0 j⟩
    cases htv with
    | @step q' b' hm' hc' _ _ =>
      have hq' : q' ∈ oaMaster d s.history := by
        rw [oa_zero_rows_master_eq_feasible] at hm'
        rw [oa_zero_rows_master_eq_feasible]
        exact hm'.1
      have hqq' := hm.2 q' hq'
      have hbest := oa_best_le_new d s.incumbent b.anchor
      have hc := hc' (oaBest d s.incumbent b.anchor) (by simp only [oaAppend,hn])
      linarith

theorem oa_zero_rows_optional_stop (d : ModelData n m 0 r) {epsilon : ℝ}
    (s : OAState n m) {q : Point n m}
    (hm : IsMinimizer (oaMaster d s.history) d.objective q)
    (hc : oaCompetitive d epsilon s q) : OAStop d epsilon s (.solution q) := by
  apply OAStop.feasible hm hc
  rw [← oa_zero_rows_master_eq_feasible d s.history]
  exact hm.1

theorem oa_empty_master_no_incumbent (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {s : OAState n m}
    (hs : OAInvariant d s) (hempty : oaMaster d s.history = ∅) :
    s.incumbent = none := by
  cases hi : s.incumbent with
  | none => rfl
  | some u =>
    have hu := oa_master_contains_feasible d s.history hconv hdiff (hs.feasible u hi)
    rw [hempty] at hu
    exact False.elim hu

end Chapter02

#print axioms Chapter02.oa_init_invariant
#print axioms Chapter02.oa_best_le_new
#print axioms Chapter02.oa_best_le_old
#print axioms Chapter02.oa_best_feasible
#print axioms Chapter02.oa_append_invariant
#print axioms Chapter02.oa_continue_invariant
#print axioms Chapter02.oa_competitive_unseen
#print axioms Chapter02.oa_seen_append
#print axioms Chapter02.oa_continue_remaining_lt
#print axioms Chapter02.oa_continue_history_retained
#print axioms Chapter02.oa_continue_master_subset
#print axioms Chapter02.oa_master_values_monotone
#print axioms Chapter02.oa_stop_sound
#print axioms Chapter02.oa_certificate_objectiveWithin
#print axioms Chapter02.oa_certificate_zero_optimal
#print axioms Chapter02.oa_step_total
#print axioms Chapter02.oa_init_remaining
#print axioms Chapter02.oa_continue_incumbent_monotone
#print axioms Chapter02.oa_zero_rows_no_two_continuations
#print axioms Chapter02.oa_zero_rows_optional_stop
#print axioms Chapter02.oa_empty_master_no_incumbent
