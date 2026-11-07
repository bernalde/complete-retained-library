module

public import Chapter03FPUnboundedReturns

@[expose] public section

/-! A separate hard-integer-domain specialization. The main no-A1 theorem
does not require this enclosure, and these finite sets add no master row. -/
noncomputable section
open Chapter02 Chapter03.FP
open scoped RealInnerProductSpace
namespace Chapter03.FPUnbounded
variable {n m l : ℕ}

def failedTargetList (s : State n m) : List (IntVector m) := by
  classical
  exact (s.history.filter (fun e => decide (e.success = none))).map Event.target

def successfulTargetList (s : State n m) : List (IntVector m) := by
  classical
  exact (s.history.filter (fun e => decide (e.success ≠ none))).map Event.target

def failedTargets (s : State n m) : Finset (IntVector m) := by
  classical
  exact (failedTargetList s).toFinset

def successfulTargets (s : State n m) : Finset (IntVector m) := by
  classical
  exact (successfulTargetList s).toFinset

theorem failed_target_list_nodup (d : Data n m l) {s : State n m} (hs : Invariant d s) :
    (failedTargetList s).Nodup := by
  classical
  change List.Pairwise (fun a b => a ≠ b) _
  rw [failedTargetList,List.pairwise_map,List.pairwise_filter]
  apply hs.ordered.imp_of_mem
  intro a b ha _ hc hna _ heq
  have hna' : a.success = none := of_decide_eq_true hna
  have hne : Chapter03.yMap n m a.projection ≠ intY a.target := by
    intro hy
    have ho := (hs.valid a ha).outcome
    rw [hna'] at ho
    exact ho ((distance_zero_iff _ _).mpr ((yMap_eq_intY_iff _ _).mp hy))
  exact retained_normal_excludes_failed hne (hc.1 hna') (congrArg intY heq.symm)

theorem successful_target_list_nodup (d : Data n m l) (hd : 0 < d.delta)
    {s : State n m} (hs : Invariant d s) : (successfulTargetList s).Nodup := by
  classical
  change List.Pairwise (fun a b => a ≠ b) _
  rw [successfulTargetList,List.pairwise_map,List.pairwise_filter]
  exact hs.ordered.imp (fun hc ha hb => hc.2 hd (of_decide_eq_true ha) (of_decide_eq_true hb))

theorem failed_targets_card (d : Data n m l) {s : State n m} (hs : Invariant d s) :
    (failedTargets s).card = (failedTargetList s).length :=
  List.toFinset_card_of_nodup (failed_target_list_nodup d hs)

theorem successful_targets_card (d : Data n m l) (hd : 0 < d.delta)
    {s : State n m} (hs : Invariant d s) :
    (successfulTargets s).card = (successfulTargetList s).length :=
  List.toFinset_card_of_nodup (successful_target_list_nodup d hd hs)

theorem history_count_split (d : Data n m l) (hd : 0 < d.delta)
    {s : State n m} (hs : Invariant d s) :
    s.history.length = (failedTargets s).card + (successfulTargets s).card := by
  classical
  rw [failed_targets_card d hs,successful_targets_card d hd hs]
  simpa [failedTargetList,successfulTargetList] using
    (List.length_eq_length_filter_add (l := s.history) (fun e => decide (e.success = none)))

def HardIntegerEnclosure (d : Data n m l) (T : Finset (IntVector m)) : Prop :=
  ∀ p ∈ d.base, ∀ y : IntVector m, p.2 = intCast y → y ∈ T

theorem chain_targets_in (d : Data n m l) {T : Finset (IntVector m)}
    (hT : HardIntegerEnclosure d T) {cap : Option ℕ} {s t : State n m} {k q : ℕ}
    (hs : ∀ e ∈ s.history, e.target ∈ T) (hc : Chain d cap s k q t) :
    ∀ e ∈ t.history, e.target ∈ T := by
  revert hs
  induction hc with
  | nil _ => exact id
  | @cons s t e k q hstep _ ih =>
    intro hs
    apply ih
    intro c hc
    simp only [append,List.mem_append,List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hs c hc
    · obtain ⟨z,hz,_,hr⟩ := hstep
      exact hT z.1 (master_base d s hz.1) c.target hr.target_eq

theorem target_sets_subset {s : State n m} {T : Finset (IntVector m)}
    (ht : ∀ e ∈ s.history, e.target ∈ T) :
    failedTargets s ⊆ T ∧ successfulTargets s ⊆ T := by
  classical
  constructor
  · intro y hy
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact ht e (List.mem_filter.mp he).1
  · intro y hy
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact ht e (List.mem_filter.mp he).1

theorem master_target_not_failed (d : Data n m l) {s : State n m}
    (hs : Invariant d s) {z : Point n m × ℝ} (hz : z ∈ master d s)
    {y : IntVector m} (hy : z.1.2 = intCast y) : y ∉ failedTargets s := by
  classical
  intro hm
  obtain ⟨e,he,hey⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  have hm' := List.mem_filter.mp he
  have hn : e.success = none := of_decide_eq_true hm'.2
  exact failed_target_excluded d hs hz hm'.1 hn (by simpa [hey] using hy)

theorem stop_failed_count_bound (d : Data n m l) {T : Finset (IntVector m)}
    (hT : HardIntegerEnclosure d T) {s : State n m} (hs : Invariant d s)
    (ht : ∀ e ∈ s.history, e.target ∈ T) {cap : Option ℕ} {reason : StopReason m}
    (hstop : Stop d cap s reason) :
    (failedTargets s).card + terminalProjectionCount reason ≤ T.card := by
  classical
  have hsub := (target_sets_subset ht).1
  cases hstop with
  | emptyMaster _ => simpa [terminalProjectionCount] using Finset.card_le_card hsub
  | handoff _ _ _ => simpa [terminalProjectionCount] using Finset.card_le_card hsub
  | @emptyProjection z y hm hy _ _ =>
    have hyT := hT z.1 (master_base d s hm.1) y hy
    have hfresh := master_target_not_failed d hs hm.1 hy
    have hh := Finset.card_le_card (Finset.insert_subset hyT hsub)
    simpa [Finset.card_insert_of_notMem hfresh,terminalProjectionCount] using hh

theorem chain_success_count (d : Data n m l) {cap : Option ℕ}
    {s t : State n m} {k q : ℕ} (hc : Chain d cap s k q t) :
    (successfulTargetList s).length + q = (successfulTargetList t).length := by
  induction hc with
  | nil _ => simp
  | @cons s t e k q _ _ ih =>
    have he : (successfulTargetList (append s e)).length =
        (successfulTargetList s).length + polishCount e := by
      cases hh : e.success <;>
        simp [successfulTargetList,append,List.filter_append,hh,polishCount]
    rw [he] at ih
    omega

/-- Sharper two-N counts require an actual hard integer enclosure of the base.
The final empty projection is charged to the failed class, never to a fictitious
completed event or to full-history target freshness. -/
theorem finite_hard_target_counts (d : Data n m l) (h : Analytic d) (hd : 0 < d.delta)
    {T : Finset (IntVector m)} (hT : HardIntegerEnclosure d T) {cap : Option ℕ}
    (choose : Selector d cap) {seed : Point n m} (hp : seed ∈ d.relaxation)
    {fuel : ℕ} {out : LoopOutput n m}
    (hr : run d choose fuel (initialState seed) = some out) :
    out.bodies ≤ 2*T.card ∧ out.projections ≤ 2*T.card ∧
      out.masters ≤ 2*T.card+1 ∧ out.polishes ≤ T.card := by
  obtain ⟨hc,hs,hpExact,hmExact,_⟩ := run_execution d choose fuel (initialState seed) hr
  have hi := chain_invariant d h (initial_invariant d hp) hc
  have ht := chain_targets_in d hT (s := initialState seed) (by simp [initialState]) hc
  have hF := stop_failed_count_bound d hT hi ht hs
  have hS := Finset.card_le_card (target_sets_subset ht).2
  have hsplit := history_count_split d hd hi
  have hcount := (chain_counts d hc).1
  simp only [initialState,List.length_nil,Nat.zero_add] at hcount
  have hpol := chain_success_count d hc
  have hpol' : out.polishes = (successfulTargetList out.state).length := by
    simpa [successfulTargetList,initialState] using hpol
  have hscard := successful_targets_card d hd hi
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

end Chapter03.FPUnbounded
