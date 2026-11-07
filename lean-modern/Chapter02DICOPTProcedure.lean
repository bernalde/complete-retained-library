module

public import Chapter02DICOPTInitialization
public import Chapter02DICOPTMaster

@[expose] public section

/-! Original-source soundness and existence for the qualified DICOPT procedure.
The source analytic theorems derive global fiber/joint minima and actual AP
attainment. This module never assumes optimum, freshness or progress callbacks. -/
noncomputable section
namespace Chapter02.DICOPT
variable {n m e l r : ℕ}

/-- Every processed feasible fiber is represented by an actual globally minimal
source anchor; every processed infeasible fiber is exactly empty. -/
theorem resolved_fiber_classification (d : Data n m e l r) (s : State d)
    (b : BVector m) (hb : b ∈ s.seen) :
    ¬ (d.fiber (realBinary b)).Nonempty ∨
      ∃ a ∈ s.history, a.y = realBinary b ∧
        IsMinimizer (d.fiber a.y) (fun x => d.objective x a.y) a.x := by
  obtain ⟨reply,hreply,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  cases ha : reply.anchor with
  | none => exact Or.inl (reply.empty ha)
  | some a =>
    refine Or.inr ⟨a,?_,reply.same_y a ha,?_⟩
    · exact List.mem_cons.mpr (Or.inr (List.mem_filterMap.mpr ⟨reply,hreply,ha⟩))
    · exact a.kkt.global_min a.convex

/-- The incumbent dominates EVERY original point in each resolved fiber,
including fibers discarded by no-good rows. This is separate from the remaining
master lower bound. -/
theorem resolved_original_bound (d : Data n m e l r) {s : State d}
    (hs : Invariant d s) (p : RealVector n × RealVector m) (hp : p ∈ d.original)
    (b : BVector m) (hy : p.2 = realBinary b) (hb : b ∈ s.seen) :
    ∃ u, s.incumbent = some u ∧ pointObjective d u ≤ pointObjective d p := by
  obtain ⟨reply,hreply,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  cases ha : reply.anchor with
  | none =>
    exfalso
    apply reply.empty ha
    exact ⟨p.1,by change d.Feasible p.1 (realBinary reply.binary); rw [←hy]; exact hp.1⟩
  | some a =>
    obtain ⟨u,hu,hbest⟩ := hs.best reply hreply a ha
    have hfp : p.1 ∈ d.fiber a.y := by
      change d.Feasible p.1 a.y
      rw [reply.same_y a ha,←hy]
      exact hp.1
    refine ⟨u,hu,hbest.trans ?_⟩
    calc
      d.objective a.x a.y ≤ d.objective p.1 a.y := (a.kkt.global_min a.convex).2 p.1 hfp
      _ = pointObjective d p := by rw [reply.same_y a ha,←hy]; rfl

/-- Original feasibility embeds with zero slacks at the same objective in the
literal retained-history master, provided its binary fiber is still unprocessed. -/
theorem remaining_master_embed (d : Data n m e l r) (s : State d)
    (p : RealVector n × RealVector m) (hp : p ∈ d.original)
    (b : BVector m) (hy : p.2 = realBinary b) (hb : b ∉ s.seen) :
    ∃ z : MasterPoint d s.history, z ∈ s.master ∧ s.value z = pointObjective d p := by
  have hng : ∀ c ∈ s.seen, noGoodRow c p.2 ≤ 0 := by
    intro c hc
    rw [hy,noGoodRow_realBinary_iff]
    intro hbc
    exact hb (hbc.symm ▸ hc)
  exact ⟨masterEmbed d s.history p.1 p.2,
    master_embed d s.history s.seen hp.1 hp.2 hng,
    master_embed_objective d s.history p.1 p.2⟩

theorem remaining_master_bound (d : Data n m e l r) (s : State d)
    (q : MasterPoint d s.history) (hq : IsMinimizer s.master s.value q)
    (p : RealVector n × RealVector m) (hp : p ∈ d.original)
    (b : BVector m) (hy : p.2 = realBinary b) (hb : b ∉ s.seen) :
    s.value q ≤ pointObjective d p := by
  obtain ⟨z,hz,hvalue⟩ := remaining_master_embed d s p hp b hy hb
  exact hvalue ▸ hq.2 z hz

theorem stop_sound (d : Data n m e l r) {s : State d}
    (hs : Invariant d s) {result : Result n m} (h : Stop d s result) :
    ReturnCertificate d result := by
  classical
  cases h with
  | empty_none he hi =>
    rintro ⟨p,hp⟩
    obtain ⟨b,hy⟩ := binary_exists_realBinary hp.2
    by_cases hb : b ∈ s.seen
    · obtain ⟨u,hu,_⟩ := resolved_original_bound d hs p hp b hy hb
      simp [hi] at hu
    · obtain ⟨q,hq,_⟩ := remaining_master_embed d s p hp b hy hb
      rw [he] at hq
      exact hq
  | @empty_some he u hi =>
    refine ⟨hs.feasible u hi, ?_⟩
    intro p hp
    obtain ⟨b,hy⟩ := binary_exists_realBinary hp.2
    by_cases hb : b ∈ s.seen
    · obtain ⟨v,hv,hbound⟩ := resolved_original_bound d hs p hp b hy hb
      have huv : u = v := Option.some.inj (hi.symm.trans hv)
      simpa only [huv] using hbound
    · obtain ⟨q,hq,_⟩ := remaining_master_embed d s p hp b hy hb
      rw [he] at hq
      exact False.elim hq
  | @bound q u hq hi ht =>
    refine ⟨hs.feasible u hi, ?_⟩
    intro p hp
    obtain ⟨b,hy⟩ := binary_exists_realBinary hp.2
    by_cases hb : b ∈ s.seen
    · obtain ⟨v,hv,hbound⟩ := resolved_original_bound d hs p hp b hy hb
      have huv : u = v := Option.some.inj (hi.symm.trans hv)
      simpa only [huv] using hbound
    · exact ht.trans (remaining_master_bound d s q hq p hp b hy hb)

theorem completed_sound (d : Data n m e l r) {s : State d} {k : ℕ}
    {result : Result n m} (hs : Invariant d s) (h : Completed d s k result) :
    ReturnCertificate d result := by
  obtain ⟨t,hchain,hstop⟩ := h
  exact stop_sound d (chain_invariant d hs hchain) hstop

theorem run_sound (d : Data n m e l r) (choose : Selector d) (fuel : ℕ)
    (s : State d) (hs : Invariant d s) {result : Result n m} {k : ℕ}
    (h : run d choose fuel s hs = some (result,k)) : ReturnCertificate d result :=
  completed_sound d hs (run_completed d choose fuel s hs h).1

/-- Legal decisions exist by actual AP attainment, classical exact emptiness,
and regularity supplying real KKT/sign-convex data for each nonempty fiber. -/
theorem decision_exists (d : Data n m e l r) (hreg : FiberRegularity d)
    (s : State d) : Nonempty (Decision d s) := by
  classical
  by_cases he : s.master.Nonempty
  · have hh : (hardDomain d s.seen).Nonempty := by
      obtain ⟨q,hq⟩ := he
      exact ⟨(q.x,q.y),hq.1⟩
    obtain ⟨q,hq⟩ := master_attained s.history (history_nonempty s) s.seen hh
    by_cases ht : ∃ u, s.incumbent = some u ∧ pointObjective d u ≤ s.value q
    · obtain ⟨u,hu,hbound⟩ := ht
      exact ⟨.stop (.solution u) (.bound hq hu hbound)⟩
    · have hc : competitive d s q := by
        intro u hu
        exact lt_of_not_ge (fun h => ht ⟨u,hu,h⟩)
      obtain ⟨b,hy⟩ := binary_exists_realBinary hq.1.1.2.1
      obtain ⟨reply,hr⟩ := reply_exists d hreg b
      exact ⟨.next (append d s reply) (.step hq hc (by rw [hr]; exact hy))⟩
  · have hempty : s.master = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    cases hi : s.incumbent with
    | none => exact ⟨.stop .infeasible (.empty_none hempty hi)⟩
    | some u => exact ⟨.stop (.solution u) (.empty_some hempty hi)⟩

theorem selector_exists (d : Data n m e l r) (hreg : FiberRegularity d) :
    Nonempty (Selector d) :=
  ⟨fun s _ => Classical.choice (decision_exists d hreg s)⟩

theorem empty_initializer_sound (d : Data n m e l r)
    (he : ¬ d.relaxed.Nonempty) : ReturnCertificate d .infeasible := by
  rintro ⟨p,hp⟩
  exact he ⟨p,original_subset_relaxed d hp⟩

theorem integral_initializer_sound (d : Data n m e l r)
    (a : RelaxedAnchor d) (hb : Binary a.y) :
    ReturnCertificate d (.solution (a.x,a.y)) := by
  refine ⟨⟨a.kkt.feasible,hb⟩, ?_⟩
  intro p hp
  exact (a.kkt.global_min a.convex).2 p (original_subset_relaxed d hp)

theorem procedure_sound (d : Data n m e l r) (initial : Initialization d)
    (choose : Selector d) (output : Output n m)
    (h : procedure d initial choose = some output) : ReturnCertificate d output.result := by
  cases initial with
  | empty he =>
    have hout : (⟨.infeasible,0,0⟩ : Output n m) = output := Option.some.inj h
    subst output
    exact empty_initializer_sound d he
  | integral a hb =>
    have hout : (⟨.solution (a.x,a.y),0,0⟩ : Output n m) = output := Option.some.inj h
    subst output
    exact integral_initializer_sound d a hb
  | fractional a hb =>
    cases hr : run d choose (Fintype.card (BVector m)+1) (initialState a.toAnchor)
        (initial_invariant a.toAnchor) with
    | none => simp only [procedure,hr,Option.map_none] at h; contradiction
    | some pair =>
      rcases pair with ⟨result,k⟩
      have hout : (⟨result,k,k+1⟩ : Output n m) = output := by
        rw [procedure,hr] at h
        exact Option.some.inj h
      subst output
      exact run_sound d choose _ _ (initial_invariant a.toAnchor) hr

/-- Full source-qualified procedure endpoint. Every actual initializer and every
certificate-bearing selector returns a genuine original global minimum or exact
original infeasibility. The sole oracle assumptions supply KKT/sign-convex
certificates. Minima, valid remaining bounds, legal choices, freshness and finite
return are theorems. One initialization inspection is counted separately. -/
theorem qualified_source_procedure (d : Data n m e l r)
    (hjoint : JointRegularity d) (hfibers : FiberRegularity d) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d) ∧
    ∀ initial : Initialization d, ∀ choose : Selector d, ∃ output,
      procedure d initial choose = some output ∧
      output.binarySolves ≤ 2 ^ m ∧
      output.masterDecisions ≤ 2 ^ m + 1 ∧
      1 + output.masterDecisions ≤ 2 ^ m + 2 ∧
      ReturnCertificate d output.result := by
  refine ⟨initialization_exists d hjoint,selector_exists d hfibers,?_⟩
  intro initial choose
  obtain ⟨output,hout,hbinary,hmaster⟩ := procedure_returns d initial choose
  rw [binary_configuration_count] at hbinary hmaster
  exact ⟨output,hout,hbinary,hmaster,by omega,procedure_sound d initial choose output hout⟩

theorem certificate_infeasible_iff (d : Data n m e l r) (result : Result n m)
    (h : ReturnCertificate d result) : result = .infeasible ↔ ¬ d.original.Nonempty := by
  cases result with
  | infeasible => exact ⟨fun _ => h,fun _ => rfl⟩
  | solution p =>
    constructor
    · intro heq
      cases heq
    · intro he
      exact False.elim (he ⟨p,h.1⟩)

theorem certificate_solution_of_unique (d : Data n m e l r) (result : Result n m)
    (h : ReturnCertificate d result) (p : RealVector n × RealVector m)
    (hp : IsMinimizer d.original (pointObjective d) p)
    (hunique : ∀ q, IsMinimizer d.original (pointObjective d) q → q = p) :
    result = .solution p := by
  cases result with
  | infeasible => exact False.elim (h ⟨p,hp.1⟩)
  | solution q => rw [hunique q h]

/-- With zero integer coordinates, every relaxed initializer is integral, so
its certified early return uses no master decision or binary-fiber solve. -/
theorem zero_integer_procedure (d : Data n 0 e l r) (initial : Initialization d)
    (choose : Selector d) : ∃ output,
      procedure d initial choose = some output ∧
      output.binarySolves = 0 ∧ output.masterDecisions = 0 ∧
      ReturnCertificate d output.result := by
  cases initial with
  | empty he => exact ⟨⟨.infeasible,0,0⟩,rfl,rfl,rfl,empty_initializer_sound d he⟩
  | integral a hb =>
    exact ⟨⟨.solution (a.x,a.y),0,0⟩,rfl,rfl,rfl,integral_initializer_sound d a hb⟩
  | fractional a hb => exact False.elim (hb (fun i => Fin.elim0 i))

end Chapter02.DICOPT
#print axioms Chapter02.DICOPT.qualified_source_procedure
