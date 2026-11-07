module

public import Chapter02STState

@[expose] public section

/-! Derived progress for the separately qualified single-tree repair. The
potential counts all live/working occurrences and unseen integer fibers.
Neither the raw state nor any transition carries a progress/freshness oracle. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

def stTreeWeight (s : STState n m l) : ℕ :=
  ((stFrontier s).map (fun b => b.node.weight)).sum

def stPotential (d : ModelData n m l r) (s : STState n m l) : ℕ :=
  stTreeWeight s + oaRemaining d s.oa

def stPhasePotential (d : ModelData n m l r) (s : STState n m l) : ℕ :=
  2 * stPotential d s + if s.working.isNone then 1 else 0

theorem st_select_tree_weight {s t : STState n m l} (h : STSelect s t) :
    stTreeWeight t = stTreeWeight s := by
  cases h
  simp [stTreeWeight, stFrontier, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem st_select_potential (d : ModelData n m l r)
    {s t : STState n m l} (h : STSelect s t) : stPotential d t = stPotential d s := by
  simp only [stPotential, st_select_tree_weight h, st_select_oa h]

theorem st_select_phase_drop (d : ModelData n m l r)
    {s t : STState n m l} (h : STSelect s t) :
    stPhasePotential d t + 1 = stPhasePotential d s := by
  have hp := st_select_potential d h
  cases h
  simpa [stPhasePotential] using hp

theorem st_feasible_update_remaining (d : ModelData n m l r) (o : OAState n m)
    (q : Point n m) : oaRemaining d (stFeasibleUpdate d o q) = oaRemaining d o := rfl

theorem st_callback_unseen (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (seeds : List (STSeed n m l)) (o : OAState n m) (N : BBNode m)
    (ho : OAInvariant d o) (href : N.Refines (bbRootNode d))
    {q : Point n m} {batch : OABatch n m}
    (hq : q ∈ stLP d seeds o.history N) (hc : oaCompetitive d 0 o q)
    (hy : q.2 = oaIntCast batch.integer) : batch.integer ∉ oaSeen o := by
  exact oa_competitive_unseen d hconv hdiff hCQ (by norm_num) ho
    (st_lp_integer_master d seeds o.history N href hq ⟨batch.integer,hy⟩)
    hc batch.integer hy

theorem st_callback_remaining_exact (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (seeds : List (STSeed n m l)) (o : OAState n m) (N : BBNode m)
    (ho : OAInvariant d o) (href : N.Refines (bbRootNode d))
    {q : Point n m} {batch : OABatch n m}
    (hq : q ∈ stLP d seeds o.history N) (hc : oaCompetitive d 0 o q)
    (hb : oaBatchValid d batch) (hy : q.2 = oaIntCast batch.integer) :
    oaRemaining d (oaAppend d o batch) + 1 = oaRemaining d o := by
  classical
  have hn := st_callback_unseen d hconv hdiff hCQ seeds o N ho href hq hc hy
  have hm : batch.integer ∈ oaBox d \ oaSeen o :=
    Finset.mem_sdiff.mpr ⟨by simpa [oaBox] using hb.1, hn⟩
  have he : oaBox d \ oaSeen (oaAppend d o batch) =
      (oaBox d \ oaSeen o).erase batch.integer := by
    rw [oa_seen_append]
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
    tauto
  unfold oaRemaining
  rw [he]
  exact Finset.card_erase_add_one hm

theorem st_delete_potential_drop (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (o o' : OAState n m)
    (live : List (BBRecord m)) (b : BBRecord m)
    (hr : oaRemaining d o' ≤ oaRemaining d o) :
    stPotential d ⟨seeds,o',live,none⟩ + 1 ≤
      stPotential d ⟨seeds,o,live,some b⟩ := by
  have hp := bb_weight_pos b.node
  simp only [stPotential, stTreeWeight, stFrontier, Option.toList_none,
    Option.toList_some, List.nil_append, List.singleton_append, List.map_cons,
    List.sum_cons]
  omega

theorem st_resolve_potential_drop (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    {s t : STState n m l} (hs : STInvariant d s) (h : STResolve d s t) :
    stPotential d t + 1 ≤ stPotential d s := by
  cases h with
  | empty he => exact st_delete_potential_drop d _ _ _ _ _ le_rfl
  | unbounded hu => exact st_delete_potential_drop d _ _ _ _ _ le_rfl
  | unattained hn hb ha => exact st_delete_potential_drop d _ _ _ _ _ le_rfl
  | prune hq hp => exact st_delete_potential_drop d _ _ _ _ _ le_rfl
  | feasible hq hf => exact st_delete_potential_drop d _ _ _ _ _ le_rfl
  | @callback seeds o live b q batch hq hc hb hy =>
    have href := hs.refines b (by simp [stFrontier])
    have hr := st_callback_remaining_exact d hconv hdiff hCQ seeds o b.node
      hs.oa href hq.1 hc hb hy
    simp only [stPotential, stTreeWeight, stFrontier, Option.toList_none,
      Option.toList_some, List.nil_append, List.singleton_append, List.map_cons,
      List.sum_cons, stRaised]
    omega
  | @branch seeds o live b q i hq hc hf =>
    have hw := bb_children_weight_drop b.node i q hq.1.2.1 hf
    simp only [stPotential, stTreeWeight, stFrontier, Option.toList_none,
      Option.toList_some, List.nil_append, List.singleton_append, bbChildren,
      List.cons_append, List.map_cons, List.sum_cons]
    omega

theorem st_resolve_ready {d : ModelData n m l r} {s t : STState n m l}
    (h : STResolve d s t) : t.working = none := by cases h <;> rfl

theorem st_resolve_working {d : ModelData n m l r} {s t : STState n m l}
    (h : STResolve d s t) : s.working.isSome = true := by cases h <;> rfl

theorem st_resolve_phase_drop (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    {s t : STState n m l} (hs : STInvariant d s) (h : STResolve d s t) :
    stPhasePotential d t + 1 ≤ stPhasePotential d s := by
  have hp := st_resolve_potential_drop d hconv hdiff hCQ hs h
  have ht := st_resolve_ready h
  have hw := st_resolve_working h
  have hh : s.working.isNone = false := by
    cases he : s.working <;> simp_all
  simp only [stPhasePotential, ht, Option.isNone_none, Bool.true_eq, if_true,
    hh, Bool.false_eq_true, if_false]
  omega

theorem st_step_phase_drop (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    {s t : STState n m l} (hs : STInvariant d s) (h : STStep d s t) :
    stPhasePotential d t + 1 ≤ stPhasePotential d s := by
  cases h with
  | select h => exact (st_select_phase_drop d h).le
  | resolve h => exact st_resolve_phase_drop d hconv hdiff hCQ hs h

theorem st_process_ready {d : ModelData n m l r} {s t : STState n m l}
    (h : STProcess d s t) : s.working = none ∧ t.working = none := by
  obtain ⟨w,hs,ht⟩ := h
  constructor
  · cases hs; rfl
  · exact st_resolve_ready ht

theorem st_process_potential_drop (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    {s t : STState n m l} (hs : STInvariant d s) (h : STProcess d s t) :
    stPotential d t + 1 ≤ stPotential d s := by
  obtain ⟨w,hsel,hres⟩ := h
  have hp := st_resolve_potential_drop d hconv hdiff hCQ
    (st_select_preserves_invariant d hs hsel) hres
  simpa only [st_select_potential d hsel] using hp

end Chapter02

#print axioms Chapter02.st_select_tree_weight
#print axioms Chapter02.st_select_potential
#print axioms Chapter02.st_select_phase_drop
#print axioms Chapter02.st_feasible_update_remaining
#print axioms Chapter02.st_callback_unseen
#print axioms Chapter02.st_callback_remaining_exact
#print axioms Chapter02.st_delete_potential_drop
#print axioms Chapter02.st_resolve_potential_drop
#print axioms Chapter02.st_resolve_ready
#print axioms Chapter02.st_resolve_working
#print axioms Chapter02.st_resolve_phase_drop
#print axioms Chapter02.st_step_phase_drop
#print axioms Chapter02.st_process_ready
#print axioms Chapter02.st_process_potential_drop
