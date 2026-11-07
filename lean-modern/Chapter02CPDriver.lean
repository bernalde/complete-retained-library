module

public import Chapter02CPSeparation

@[expose] public section

/-! Actual finite ECP/ESH traces and arbitrary legal-decision selectors.
Existence follows from exact compact master minima and the source policies.
Finite return is derived from retained canonical cuts and compact packing;
neither progress nor existence of an external solver is an input oracle. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

/-- Each appended batch is a literal step at its complete earlier history. -/
def CPTrace (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (seed T : List (CPBatch n m l)) : Prop :=
  ∀ i (hi : i < T.length), CPStep d mode eps (seed ++ T.take i) T[i]

theorem cp_trace_nil (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (seed : List (CPBatch n m l)) : CPTrace d mode eps seed [] := by
  intro i hi
  simp at hi

theorem cp_trace_append (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    {seed T : List (CPBatch n m l)} (hT : CPTrace d mode eps seed T)
    {b : CPBatch n m l} (hb : CPStep d mode eps (seed ++ T) b) :
    CPTrace d mode eps seed (T ++ [b]) := by
  intro i hi
  by_cases hil : i < T.length
  · simpa [List.take_append_of_le_length (Nat.le_of_lt hil),
      List.getElem_append_left hil] using hT i hil
  · have heq : i = T.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hb

theorem cp_trace_trial_mem_base (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    {seed T : List (CPBatch n m l)} (hT : CPTrace d mode eps seed T)
    (i : Fin T.length) : T[i.val].trial ∈ cpBase d :=
  ((cp_master_mem_iff d _ _).mp (hT i.val i.isLt).1.1).1

theorem cp_trace_retains_cut (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    {seed T : List (CPBatch n m l)} (hT : CPTrace d mode eps seed T)
    (i k : Fin T.length) (hik : i < k) : cpBatchCuts d T[i.val] T[k.val].trial := by
  apply ((cp_master_mem_iff d _ _).mp (hT k.val k.isLt).1.1).2
  apply List.mem_append_right
  have hi : i.val < (T.take k.val).length := by simp; exact hik
  have hm := List.getElem_mem (l := T.take k.val) hi
  simpa using hm

/-- The same packing bound applies to every seed and every legal finite trace. -/
theorem cp_all_prefix_bound (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ seed T, CPTrace d mode eps seed T → T.length ≤ N := by
  obtain ⟨delta, hd, hsep⟩ := cp_policy_uniform_separation d mode hbase hconv hC1 ha heps
  obtain ⟨N, hN⟩ := cp_compact_separated_prefix_bound hbase hd
  refine ⟨N, ?_⟩
  intro seed T hT
  apply hN T.length (fun i => T[i.val].trial)
  · exact cp_trace_trial_mem_base d mode eps hT
  · intro i k hik
    exact hsep T[i.val] (hT i.val i.isLt).2.2
      (cp_trace_trial_mem_base d mode eps hT i)
      (cp_failed_test_row d (hT i.val i.isLt).2.1)
      T[k.val].trial (cp_trace_retains_cut d mode eps hT i k hik)

theorem cp_nonterminal_trace_extends (d : ModelData n m l r) (mode : CPMode n m)
    {eps : ℝ} (heps : 0 ≤ eps) (hbase : IsCompact (cpBase d))
    (hcontinuous : ∀ j, Continuous (d.g j)) (ha : CPInterior d mode)
    {seed T : List (CPBatch n m l)} (hT : CPTrace d mode eps seed T)
    (hstop : ¬ ∃ out, CPStop d eps (seed ++ T) out) :
    ∃ b, CPStep d mode eps (seed ++ T) b ∧ CPTrace d mode eps seed (T ++ [b]) := by
  obtain hs | ⟨b, hb⟩ := cp_step_total d mode heps hbase hcontinuous ha (seed ++ T)
  · exact (hstop hs).elim
  · exact ⟨b, hb, cp_trace_append d mode eps hT hb⟩

/-- Thus an infinite legal continuation, whose finite prefixes grow by one
batch per decision, cannot exist at a positive constraint tolerance. -/
theorem cp_no_infinite_prefixes (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 < eps) (seed : List (CPBatch n m l)) :
    ¬ ∃ T : ℕ → List (CPBatch n m l),
      (∀ k, CPTrace d mode eps seed (T k)) ∧ (∀ k, k ≤ (T k).length) := by
  obtain ⟨N, hN⟩ := cp_all_prefix_bound d mode hbase hconv hC1 ha heps
  rintro ⟨T, hT, hlen⟩
  have hb := hN seed (T (N + 1)) (hT (N + 1))
  have hl := hlen (N + 1)
  omega

/-- A legal choice is exactly a stopping certificate or an actual next batch. -/
def CPDecisionLegal (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (H : List (CPBatch n m l)) : CPResult n m ⊕ CPBatch n m l → Prop
  | .inl out => CPStop d eps H out
  | .inr b => CPStep d mode eps H b

def CPSelector (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ) :=
  ∀ H : List (CPBatch n m l), {c : CPResult n m ⊕ CPBatch n m l //
    CPDecisionLegal d mode eps H c}

theorem cp_selector_exists (d : ModelData n m l r) (mode : CPMode n m)
    {eps : ℝ} (heps : 0 ≤ eps) (hbase : IsCompact (cpBase d))
    (hcontinuous : ∀ j, Continuous (d.g j)) (ha : CPInterior d mode) :
    Nonempty (CPSelector d mode eps) := by
  have hex : ∀ H, Nonempty {c : CPResult n m ⊕ CPBatch n m l //
      CPDecisionLegal d mode eps H c} := by
    intro H
    obtain ⟨out, hout⟩ | ⟨b, hb⟩ := cp_step_total d mode heps hbase hcontinuous ha H
    · exact ⟨⟨.inl out, hout⟩⟩
    · exact ⟨⟨.inr b, hb⟩⟩
  exact ⟨fun H => Classical.choice (hex H)⟩

inductive CPDriverState (n m l : ℕ)
  | active (trace : List (CPBatch n m l))
  | stopped (trace : List (CPBatch n m l)) (out : CPResult n m)

def CPDriverState.trace : CPDriverState n m l → List (CPBatch n m l)
  | .active T => T
  | .stopped T _ => T

/-- The operational state relation has no transitions out of a returned state.
An active state may choose any actual minimum and admissible policy batch. -/
inductive CPDriverTransition (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (seed : List (CPBatch n m l)) : CPDriverState n m l → CPDriverState n m l → Prop
  | next {T b} (h : CPStep d mode eps (seed ++ T) b) :
      CPDriverTransition d mode eps seed (.active T) (.active (T ++ [b]))
  | stop {T out} (h : CPStop d eps (seed ++ T) out) :
      CPDriverTransition d mode eps seed (.active T) (.stopped T out)

theorem cp_active_state_not_maximal (d : ModelData n m l r) (mode : CPMode n m)
    {eps : ℝ} (heps : 0 ≤ eps) (hbase : IsCompact (cpBase d))
    (hcontinuous : ∀ j, Continuous (d.g j)) (ha : CPInterior d mode)
    (seed T : List (CPBatch n m l)) :
    ∃ next, CPDriverTransition d mode eps seed (.active T) next := by
  obtain ⟨out, hout⟩ | ⟨b, hb⟩ := cp_step_total d mode heps hbase hcontinuous ha (seed ++ T)
  · exact ⟨.stopped T out, .stop hout⟩
  · exact ⟨.active (T ++ [b]), .next hb⟩

theorem cp_maximal_state_iff_stopped (d : ModelData n m l r) (mode : CPMode n m)
    {eps : ℝ} (heps : 0 ≤ eps) (hbase : IsCompact (cpBase d))
    (hcontinuous : ∀ j, Continuous (d.g j)) (ha : CPInterior d mode)
    (seed : List (CPBatch n m l)) (state : CPDriverState n m l) :
    (¬ ∃ next, CPDriverTransition d mode eps seed state next) ↔
      ∃ T out, state = .stopped T out := by
  cases state with
  | active T =>
    constructor
    · intro h
      exact (h (cp_active_state_not_maximal d mode heps hbase hcontinuous ha seed T)).elim
    · rintro ⟨T', out, h⟩
      cases h
  | stopped T out =>
    constructor
    · intro _; exact ⟨T, out, rfl⟩
    · intro _
      rintro ⟨next, h⟩
      cases h

/-- `k` counts exact master decisions, excluding any supplied seed phase. -/
def cpRun (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (choose : CPSelector d mode eps) (seed : List (CPBatch n m l)) :
    ℕ → CPDriverState n m l
  | 0 => .active []
  | k + 1 =>
    match cpRun d mode eps choose seed k with
    | .stopped T out => .stopped T out
    | .active T =>
      match (choose (seed ++ T)).val with
      | .inl out => .stopped T out
      | .inr b => .active (T ++ [b])

theorem cp_run_zero (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (choose : CPSelector d mode eps) (seed : List (CPBatch n m l)) :
    cpRun d mode eps choose seed 0 = .active [] := rfl

/-- Executed traces and terminal certificates follow from the raw decisions. -/
theorem cp_run_invariant (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (choose : CPSelector d mode eps) (seed : List (CPBatch n m l)) (k : ℕ) :
    match cpRun d mode eps choose seed k with
    | .active T => CPTrace d mode eps seed T ∧ T.length = k
    | .stopped T out => CPTrace d mode eps seed T ∧
        CPStop d eps (seed ++ T) out ∧ T.length < k := by
  induction k with
  | zero => exact ⟨cp_trace_nil d mode eps seed, rfl⟩
  | succ k ih =>
    simp only [cpRun]
    cases hr : cpRun d mode eps choose seed k with
    | active T =>
      rw [hr] at ih
      have hlegal := (choose (seed ++ T)).property
      cases hc : (choose (seed ++ T)).val with
      | inl out =>
        simp only [hc, CPDecisionLegal] at hlegal ⊢
        exact ⟨ih.1, hlegal, by omega⟩
      | inr b =>
        simp only [hc, CPDecisionLegal] at hlegal ⊢
        exact ⟨cp_trace_append d mode eps ih.1 hlegal, by simp [ih.2]⟩
    | stopped T out =>
      rw [hr] at ih
      exact ⟨ih.1, ih.2.1, by omega⟩

theorem cp_run_active_invariant (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (choose : CPSelector d mode eps) (seed : List (CPBatch n m l))
    {k : ℕ} {T : List (CPBatch n m l)}
    (h : cpRun d mode eps choose seed k = .active T) :
    CPTrace d mode eps seed T ∧ T.length = k := by
  simpa only [h] using cp_run_invariant d mode eps choose seed k

theorem cp_run_stopped_invariant (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (choose : CPSelector d mode eps) (seed : List (CPBatch n m l))
    {k : ℕ} {T : List (CPBatch n m l)} {out : CPResult n m}
    (h : cpRun d mode eps choose seed k = .stopped T out) :
    CPTrace d mode eps seed T ∧ CPStop d eps (seed ++ T) out ∧ T.length < k := by
  simpa only [h] using cp_run_invariant d mode eps choose seed k

theorem cp_every_selector_finite_return (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ (choose : CPSelector d mode eps) (seed : List (CPBatch n m l)),
      ∃ T out, cpRun d mode eps choose seed (N + 1) = .stopped T out ∧
        CPTrace d mode eps seed T ∧ T.length ≤ N ∧
        CPStop d eps (seed ++ T) out ∧ CPReturnCertificate d eps out := by
  obtain ⟨N, hN⟩ := cp_all_prefix_bound d mode hbase hconv hC1 ha heps
  refine ⟨N, ?_⟩
  intro choose seed
  cases hr : cpRun d mode eps choose seed (N + 1) with
  | active T =>
    have hi := cp_run_active_invariant d mode eps choose seed hr
    have hb := hN seed T hi.1
    omega
  | stopped T out =>
    have hi := cp_run_stopped_invariant d mode eps choose seed hr
    exact ⟨T, out, rfl, hi.1, hN seed T hi.1, hi.2.1,
      cp_stop_sound d hconv (fun j => (hC1 j).differentiable (by norm_num)) hi.2.1⟩

theorem cp_stopped_run_exists (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 < eps) (seed : List (CPBatch n m l)) :
    ∃ (choose : CPSelector d mode eps) (k : ℕ) (T : List (CPBatch n m l))
      (out : CPResult n m),
      cpRun d mode eps choose seed k = .stopped T out ∧
      CPTrace d mode eps seed T ∧ CPStop d eps (seed ++ T) out ∧
      CPReturnCertificate d eps out := by
  obtain ⟨choose⟩ := cp_selector_exists d mode heps.le hbase (fun j => (hC1 j).continuous) ha
  obtain ⟨N, hN⟩ := cp_every_selector_finite_return d mode hbase hconv hC1 ha heps
  obtain ⟨T, out, hr, hT, _, hs, hc⟩ := hN choose seed
  exact ⟨choose, N + 1, T, out, hr, hT, hs, hc⟩

/-- A maximal finite trace has no legal continuation. Nonblocking implies it
ends in an actual source stop; this definition does not assume a stop. -/
def CPMaximalTrace (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (seed T : List (CPBatch n m l)) : Prop :=
  CPTrace d mode eps seed T ∧ ¬ ∃ b, CPStep d mode eps (seed ++ T) b

theorem cp_maximal_trace_stops (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 ≤ eps) {seed T : List (CPBatch n m l)}
    (hT : CPMaximalTrace d mode eps seed T) :
    ∃ out, CPStop d eps (seed ++ T) out ∧ CPReturnCertificate d eps out := by
  obtain hs | hc := cp_step_total d mode heps hbase (fun j => (hC1 j).continuous) ha (seed ++ T)
  · obtain ⟨out, hout⟩ := hs
    exact ⟨out, hout,
      cp_stop_sound d hconv (fun j => (hC1 j).differentiable (by norm_num)) hout⟩
  · exact (hT.2 hc).elim

theorem cp_maximal_trace_bound (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ seed T, CPMaximalTrace d mode eps seed T →
      T.length ≤ N ∧ ∃ out, CPStop d eps (seed ++ T) out ∧
        CPReturnCertificate d eps out := by
  obtain ⟨N, hN⟩ := cp_all_prefix_bound d mode hbase hconv hC1 ha heps
  exact ⟨N, fun seed T hT => ⟨hN seed T hT.1,
    cp_maximal_trace_stops d mode hbase hconv hC1 ha heps.le hT⟩⟩

end Chapter02

#print axioms Chapter02.cp_trace_nil
#print axioms Chapter02.cp_trace_append
#print axioms Chapter02.cp_trace_trial_mem_base
#print axioms Chapter02.cp_trace_retains_cut
#print axioms Chapter02.cp_all_prefix_bound
#print axioms Chapter02.cp_nonterminal_trace_extends
#print axioms Chapter02.cp_no_infinite_prefixes
#print axioms Chapter02.cp_selector_exists
#print axioms Chapter02.cp_active_state_not_maximal
#print axioms Chapter02.cp_maximal_state_iff_stopped
#print axioms Chapter02.cp_run_zero
#print axioms Chapter02.cp_run_invariant
#print axioms Chapter02.cp_run_active_invariant
#print axioms Chapter02.cp_run_stopped_invariant
#print axioms Chapter02.cp_every_selector_finite_return
#print axioms Chapter02.cp_stopped_run_exists
#print axioms Chapter02.cp_maximal_trace_stops
#print axioms Chapter02.cp_maximal_trace_bound
