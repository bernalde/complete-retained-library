module

public import Chapter02STGeometry
public import Chapter02BBState
public import Chapter02OAState

@[expose] public section

/-! The separately named weak-pruning single-tree repair. Every outstanding
occurrence reads the same seed and OA histories. Selection keeps the working
occurrence in the frontier; raw resolution stores exact local outcomes only.
Inherited bounds concern original-feasible node points, not all LP points. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

structure STState (n m l : ℕ) where
  seeds : List (STSeed n m l)
  oa : OAState n m
  live : List (BBRecord m)
  working : Option (BBRecord m)

def stFrontier (s : STState n m l) : List (BBRecord m) :=
  s.working.toList ++ s.live

def stBoundState (s : STState n m l) : BBState n m :=
  ⟨stFrontier s, s.oa.incumbent⟩

def stGlobalBound (d : ModelData n m l r) (s : STState n m l) : BBGlobalBound :=
  bbGlobalBound d.objective (stBoundState s)

def stRaised (d : ModelData n m l r) (b : BBRecord m) (q : Point n m) : BBRecord m :=
  ⟨b.node, max b.lower (d.objective q : WithBot ℝ)⟩

def stFeasibleUpdate (d : ModelData n m l r) (o : OAState n m)
    (q : Point n m) : OAState n m :=
  ⟨o.history, bbUpdate .weak d.objective o.incumbent q⟩

inductive STSelect : STState n m l → STState n m l → Prop
  | choose (seeds : List (STSeed n m l)) (o : OAState n m)
      (pre post : List (BBRecord m)) (b : BBRecord m) :
      STSelect ⟨seeds, o, pre ++ b :: post, none⟩
        ⟨seeds, o, pre ++ post, some b⟩

/-- Exact LP outcomes and fixed-fiber replies, with no progress or invariant
fields. A feasible competitive LP point may take either the shortcut or the
callback-first route. The shortcut always performs a best-incumbent update. -/
inductive STResolve (d : ModelData n m l r) : STState n m l → STState n m l → Prop
  | empty {seeds : List (STSeed n m l)} {o : OAState n m}
      {live : List (BBRecord m)} {b : BBRecord m}
      (h : stLP d seeds o.history b.node = ∅) :
      STResolve d ⟨seeds, o, live, some b⟩ ⟨seeds, o, live, none⟩
  | unbounded {seeds : List (STSeed n m l)} {o : OAState n m}
      {live : List (BBRecord m)} {b : BBRecord m}
      (h : ∀ B : ℝ, ∃ q ∈ stLP d seeds o.history b.node, d.objective q < B) :
      STResolve d ⟨seeds, o, live, some b⟩ ⟨seeds, o, live, none⟩
  | unattained {seeds : List (STSeed n m l)} {o : OAState n m}
      {live : List (BBRecord m)} {b : BBRecord m}
      (hne : (stLP d seeds o.history b.node).Nonempty)
      (hbelow : BddBelow (d.objective '' stLP d seeds o.history b.node))
      (hbad : ¬ ∃ q, IsMinimizer (stLP d seeds o.history b.node) d.objective q) :
      STResolve d ⟨seeds, o, live, some b⟩ ⟨seeds, o, live, none⟩
  | prune {seeds : List (STSeed n m l)} {o : OAState n m}
      {live : List (BBRecord m)} {b : BBRecord m} {q : Point n m}
      (hq : IsMinimizer (stLP d seeds o.history b.node) d.objective q)
      (hp : bbPrunable .weak d.objective o.incumbent (d.objective q)) :
      STResolve d ⟨seeds, o, live, some b⟩ ⟨seeds, o, live, none⟩
  | feasible {seeds : List (STSeed n m l)} {o : OAState n m}
      {live : List (BBRecord m)} {b : BBRecord m} {q : Point n m}
      (hq : IsMinimizer (stLP d seeds o.history b.node) d.objective q)
      (hf : q ∈ d.feasibleOn Set.univ) :
      STResolve d ⟨seeds, o, live, some b⟩
        ⟨seeds, stFeasibleUpdate d o q, live, none⟩
  | callback {seeds : List (STSeed n m l)} {o : OAState n m}
      {live : List (BBRecord m)} {b : BBRecord m} {q : Point n m} {batch : OABatch n m}
      (hq : IsMinimizer (stLP d seeds o.history b.node) d.objective q)
      (hc : oaCompetitive d 0 o q) (hb : oaBatchValid d batch)
      (hy : q.2 = oaIntCast batch.integer) :
      STResolve d ⟨seeds, o, live, some b⟩
        ⟨seeds, oaAppend d o batch, stRaised d b q :: live, none⟩
  | branch {seeds : List (STSeed n m l)} {o : OAState n m}
      {live : List (BBRecord m)} {b : BBRecord m} {q : Point n m} (i : Fin m)
      (hq : IsMinimizer (stLP d seeds o.history b.node) d.objective q)
      (hc : oaCompetitive d 0 o q) (hf : BBFractional (q.2 i)) :
      STResolve d ⟨seeds, o, live, some b⟩
        ⟨seeds, o, bbChildren b i q d.objective ++ live, none⟩

inductive STStep (d : ModelData n m l r) : STState n m l → STState n m l → Prop
  | select {s t} (h : STSelect s t) : STStep d s t
  | resolve {s t} (h : STResolve d s t) : STStep d s t

/-- One complete selection/resolution cycle, distinct from its two microsteps. -/
def STProcess (d : ModelData n m l r) (s t : STState n m l) : Prop :=
  ∃ w, STSelect s w ∧ STResolve d w t

structure STInvariant (d : ModelData n m l r) (s : STState n m l) : Prop where
  oa : OAInvariant d s.oa
  refines : ∀ b ∈ stFrontier s, b.node.Refines (bbRootNode d)
  bounds : ∀ b ∈ stFrontier s, ∀ p ∈ b.node.feasible d,
    b.lower ≤ (d.objective p : WithBot ℝ)
  coverage : ∀ p ∈ d.feasibleOn Set.univ,
    (∃ b ∈ stFrontier s, p ∈ b.node.feasible d) ∨
      bbIncBelow d.objective s.oa.incumbent p

theorem st_select_oa {s t : STState n m l} (h : STSelect s t) : t.oa = s.oa := by
  cases h; rfl

theorem st_select_frontier_mem {s t : STState n m l} (h : STSelect s t)
    (b : BBRecord m) : b ∈ stFrontier t ↔ b ∈ stFrontier s := by
  cases h
  simp [stFrontier, or_assoc, or_left_comm, or_comm]

theorem st_select_preserves_invariant (d : ModelData n m l r)
    {s t : STState n m l} (hs : STInvariant d s) (h : STSelect s t) :
    STInvariant d t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [st_select_oa h] using hs.oa
  · intro b hb
    exact hs.refines b ((st_select_frontier_mem h b).mp hb)
  · intro b hb p hp
    exact hs.bounds b ((st_select_frontier_mem h b).mp hb) p hp
  · intro p hp
    rcases hs.coverage p hp with ⟨b,hb,hp⟩ | hi
    · exact Or.inl ⟨b,(st_select_frontier_mem h b).mpr hb,hp⟩
    · exact Or.inr (by simpa only [st_select_oa h] using hi)

theorem st_feasible_update_invariant (d : ModelData n m l r)
    (o : OAState n m) (ho : OAInvariant d o) (q : Point n m)
    (hq : q ∈ d.feasibleOn Set.univ) : OAInvariant d (stFeasibleUpdate d o q) := by
  refine ⟨ho.valid, ?_, ?_⟩
  · intro p hp
    rcases bb_update_selects .weak d.objective o.incumbent q with he | he
    · change bbUpdate .weak d.objective o.incumbent q = some p at hp
      rw [he] at hp
      cases hp
      exact hq
    · exact ho.feasible p (he.symm.trans hp)
  · intro b hb hn
    obtain ⟨p,hp,hle⟩ := ho.best b hb hn
    exact bb_update_preserves_below .weak d.objective o.incumbent q b.anchor ⟨p,hp,hle⟩

theorem st_append_preserves_below (d : ModelData n m l r) (o : OAState n m)
    (b : OABatch n m) (p : Point n m) (h : bbIncBelow d.objective o.incumbent p) :
    bbIncBelow d.objective (oaAppend d o b).incumbent p := by
  cases he : b.restoration with
  | none =>
    obtain ⟨a,ha,hle⟩ := h
    refine ⟨oaBest d o.incumbent b.anchor, by simp [oaAppend,he], ?_⟩
    rw [ha]
    exact (oa_best_le_old d a b.anchor).trans hle
  | some rho => simpa [oaAppend,he] using h

/-- Local replacement infrastructure; its semantic premises are discharged
from exact replies in the resolution theorem, and are not raw process fields. -/
theorem st_invariant_replace (d : ModelData n m l r)
    {s t : STState n m l} (b : BBRecord m) (live replacement : List (BBRecord m))
    (hs : STInvariant d s) (hfront : stFrontier s = b :: live)
    (htfront : stFrontier t = replacement ++ live) (ho : OAInvariant d t.oa)
    (href : ∀ c ∈ replacement, c.node.Refines (bbRootNode d))
    (hbounds : ∀ c ∈ replacement, ∀ p ∈ c.node.feasible d,
      c.lower ≤ (d.objective p : WithBot ℝ))
    (hdom : ∀ p, bbIncBelow d.objective s.oa.incumbent p →
      bbIncBelow d.objective t.oa.incumbent p)
    (hremoved : ∀ p ∈ b.node.feasible d,
      (∃ c ∈ replacement, p ∈ c.node.feasible d) ∨
        bbIncBelow d.objective t.oa.incumbent p) : STInvariant d t := by
  refine ⟨ho, ?_, ?_, ?_⟩
  · intro c hc
    rw [htfront] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact href c hc
    · exact hs.refines c (by rw [hfront]; simp [hc])
  · intro c hc p hp
    rw [htfront] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hbounds c hc p hp
    · exact hs.bounds c (by rw [hfront]; simp [hc]) p hp
  · intro p hp
    rcases hs.coverage p hp with ⟨c,hc,hpc⟩ | hi
    · rw [hfront] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rcases hremoved p hpc with ⟨c,hc,hpc⟩ | hi
        · exact Or.inl ⟨c,by rw [htfront]; exact List.mem_append_left _ hc,hpc⟩
        · exact Or.inr hi
      · exact Or.inl ⟨c,by rw [htfront]; exact List.mem_append_right _ hc,hpc⟩
    · exact Or.inr (hdom p hi)

theorem st_global_bound_sound (d : ModelData n m l r) (s : STState n m l)
    (h : STInvariant d s) (p : Point n m) (hp : p ∈ d.feasibleOn Set.univ) :
    stGlobalBound d s ≤ bbValue (d.objective p) := by
  rcases h.coverage p hp with ⟨b,hb,hpb⟩ | ⟨a,ha,hav⟩
  · apply (bb_global_le_record d.objective (stBoundState s) b hb).trans
    simpa [bbValue] using h.bounds b hb p hpb
  · exact (bb_global_le_incumbent d.objective (stBoundState s) a ha).trans
      ((bb_value_le_value).2 hav)

theorem st_invariant_delete (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (o : OAState n m)
    (live : List (BBRecord m)) (b : BBRecord m)
    (hs : STInvariant d ⟨seeds,o,live,some b⟩)
    (hremoved : ∀ p ∈ b.node.feasible d, bbIncBelow d.objective o.incumbent p) :
    STInvariant d ⟨seeds,o,live,none⟩ := by
  exact st_invariant_replace d b live [] hs rfl rfl hs.oa
    (by simp) (by simp) (fun _ h => h) (fun p hp => Or.inr (hremoved p hp))

/-- The branching trial need only lie in the box, not the nonlinear region. -/
theorem st_child_feasible_cover (d : ModelData n m l r) (N : BBNode m)
    (i : Fin m) (q : Point n m) (hq : q ∈ N.box) :
    N.feasible d = (N.left i (q.2 i)).feasible d ∪
      (N.right i (q.2 i)).feasible d := by
  ext p
  constructor
  · intro hp
    obtain ⟨hr,hi⟩ := (bb_feasible_mem_iff d N p).mp hp
    rcases bb_children_integer_cover N i q p hq hr.2.2 (bb_integer_coordinate hi i)
      with hl | hr'
    · exact Or.inl ((bb_feasible_mem_iff d _ p).mpr ⟨⟨hr.1,hr.2.1,hl⟩,hi⟩)
    · exact Or.inr ((bb_feasible_mem_iff d _ p).mpr ⟨⟨hr.1,hr.2.1,hr'⟩,hi⟩)
  · rintro (hp | hp)
    · exact bb_feasible_subset_of_refines d (bb_left_refines N i q hq) hp
    · exact bb_feasible_subset_of_refines d (bb_right_refines N i q hq) hp

theorem st_resolve_preserves_invariant (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    {s t : STState n m l} (hs : STInvariant d s) (h : STResolve d s t) :
    STInvariant d t := by
  cases h with
  | @empty seeds o live b he =>
    apply st_invariant_delete d seeds o live b hs
    intro p hp
    have he' := st_lp_empty_feasible d seeds o.history b.node hconv hdiff he
    simp [he'] at hp
  | @unbounded seeds o live b hu =>
    apply st_invariant_delete d seeds o live b hs
    intro p hp
    have he := st_lp_bad_unbounded_empty d seeds o.history b.node hbase
      (hs.refines b (by simp [stFrontier])) hu
    simp [he] at hp
  | @unattained seeds o live b hne hbelow hbad =>
    apply st_invariant_delete d seeds o live b hs
    intro p hp
    have he := st_lp_bad_unattained_empty d seeds o.history b.node hbase
      (hs.refines b (by simp [stFrontier])) hne hbelow hbad
    simp [he] at hp
  | @prune seeds o live b q hq hp =>
    apply st_invariant_delete d seeds o live b hs
    intro p hpf
    obtain ⟨a,ha,hav⟩ := bb_prunable_has_incumbent .weak d.objective o.incumbent _ hp
    exact ⟨a,ha,hav.trans (st_lp_minimum_lower_bound d seeds o.history b.node
      hconv hdiff hq p hpf)⟩
  | @feasible seeds o live b q hq hf =>
    apply st_invariant_replace d b live [] hs rfl rfl
      (st_feasible_update_invariant d o hs.oa q hf) (by simp) (by simp)
      (bb_update_preserves_below .weak d.objective o.incumbent q)
    intro p hp
    right
    obtain ⟨a,ha,hav⟩ := bb_update_below_new .weak d.objective o.incumbent q
    exact ⟨a,ha,hav.trans (st_lp_minimum_lower_bound d seeds o.history b.node
      hconv hdiff hq p hp)⟩
  | @callback seeds o live b q batch hq hc hb hy =>
    apply st_invariant_replace d b live [stRaised d b q] hs rfl rfl
      (oa_append_invariant d hs.oa batch hb)
    · intro c hc
      have he : c = stRaised d b q := by simpa using hc
      subst c
      exact hs.refines b (by simp [stFrontier])
    · intro c hc p hp
      have he : c = stRaised d b q := by simpa using hc
      subst c
      apply max_le (hs.bounds b (by simp [stFrontier]) p hp)
      exact_mod_cast st_lp_minimum_lower_bound d seeds o.history b.node hconv hdiff hq p hp
    · exact st_append_preserves_below d o batch
    · intro p hp
      exact Or.inl ⟨stRaised d b q,by simp,hp⟩
  | @branch seeds o live b q i hq hc hf =>
    apply st_invariant_replace d
      (t := ⟨seeds,o,bbChildren b i q d.objective ++ live,none⟩)
      b live (bbChildren b i q d.objective) hs rfl rfl hs.oa
    · intro c hc
      simp only [bbChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact bb_refines_trans (bb_left_refines b.node i q hq.1.2.1)
          (hs.refines b (by simp [stFrontier]))
      · exact bb_refines_trans (bb_right_refines b.node i q hq.1.2.1)
          (hs.refines b (by simp [stFrontier]))
    · intro c hc p hp
      simp only [bbChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have hp' := bb_feasible_subset_of_refines d (bb_left_refines b.node i q hq.1.2.1) hp
        apply max_le (hs.bounds b (by simp [stFrontier]) p hp')
        exact_mod_cast st_lp_minimum_lower_bound d seeds o.history b.node hconv hdiff hq p hp'
      · have hp' := bb_feasible_subset_of_refines d (bb_right_refines b.node i q hq.1.2.1) hp
        apply max_le (hs.bounds b (by simp [stFrontier]) p hp')
        exact_mod_cast st_lp_minimum_lower_bound d seeds o.history b.node hconv hdiff hq p hp'
    · exact fun _ h => h
    · intro p hp
      left
      rw [st_child_feasible_cover d b.node i q hq.1.2.1] at hp
      rcases hp with hl | hr
      · exact ⟨⟨b.node.left i (q.2 i), max b.lower (d.objective q : WithBot ℝ)⟩,
          by simp [bbChildren],hl⟩
      · exact ⟨⟨b.node.right i (q.2 i), max b.lower (d.objective q : WithBot ℝ)⟩,
          by simp [bbChildren],hr⟩

theorem st_step_preserves_invariant (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    {s t : STState n m l} (hs : STInvariant d s) (h : STStep d s t) : STInvariant d t := by
  cases h with
  | select h => exact st_select_preserves_invariant d hs h
  | resolve h => exact st_resolve_preserves_invariant d hbase hconv hdiff hs h

theorem st_process_preserves_invariant (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    {s t : STState n m l} (hs : STInvariant d s) (h : STProcess d s t) : STInvariant d t := by
  obtain ⟨w,hsel,hres⟩ := h
  exact st_resolve_preserves_invariant d hbase hconv hdiff
    (st_select_preserves_invariant d hs hsel) hres

inductive STStop (d : ModelData n m l r) (epsilon : ℝ) (s : STState n m l) :
    OAResult n m → Prop
  | infeasible (ready : s.working = none) (empty : s.live = [])
      (incumbent : s.oa.incumbent = none) : STStop d epsilon s .infeasible
  | exhausted {u : Point n m} (ready : s.working = none) (empty : s.live = [])
      (incumbent : s.oa.incumbent = some u) : STStop d epsilon s (.solution u)
  | gap {u : Point n m} (lower : ℝ) (ready : s.working = none)
      (incumbent : s.oa.incumbent = some u)
      (bound : bbValue lower ≤ stGlobalBound d s)
      (test : d.objective u ≤ lower + epsilon) : STStop d epsilon s (.solution u)

theorem st_stop_sound (d : ModelData n m l r) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s : STState n m l} (hs : STInvariant d s)
    {result : OAResult n m} (h : STStop d epsilon s result) :
    OAReturnCertificate d epsilon result := by
  cases h with
  | infeasible hr he hi =>
    rintro ⟨p,hp⟩
    rcases hs.coverage p hp with ⟨b,hb,_⟩ | ⟨a,ha,_⟩
    · simp [stFrontier,hr,he] at hb
    · simp [hi] at ha
  | @exhausted u hr he hi =>
    refine ⟨hs.oa.feasible u hi,d.objective u,?_,by linarith⟩
    intro p hp
    rcases hs.coverage p hp with ⟨b,hb,_⟩ | ⟨a,ha,hav⟩
    · simp [stFrontier,hr,he] at hb
    · have heq : a = u := Option.some.inj (ha.symm.trans hi)
      simpa [heq] using hav
  | @gap u lower hr hi hb ht =>
    refine ⟨hs.oa.feasible u hi,lower,?_,ht⟩
    intro p hp
    exact bb_value_le_value.mp (hb.trans (st_global_bound_sound d s hs p hp))

theorem st_stop_zero_optimal (d : ModelData n m l r) {s : STState n m l}
    (hs : STInvariant d s) {u : Point n m} (h : STStop d 0 s (.solution u)) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective u :=
  oa_certificate_zero_optimal d (st_stop_sound d le_rfl hs h)

theorem st_resolve_oa_invariant (d : ModelData n m l r)
    {s t : STState n m l} (hs : OAInvariant d s.oa) (h : STResolve d s t) :
    OAInvariant d t.oa := by
  cases h with
  | empty _ => exact hs
  | unbounded _ => exact hs
  | unattained _ _ _ => exact hs
  | prune _ _ => exact hs
  | feasible _ hf => exact st_feasible_update_invariant d _ hs _ hf
  | callback _ _ hb _ => exact oa_append_invariant d hs _ hb
  | branch _ _ _ _ => exact hs

theorem st_select_global_bound (d : ModelData n m l r)
    {s t : STState n m l} (h : STSelect s t) : stGlobalBound d t = stGlobalBound d s := by
  have he : bbLiveBound (stFrontier t) = bbLiveBound (stFrontier s) := by
    apply le_antisymm
    · apply (bb_le_live_bound_iff _ _).mpr
      intro b hb
      exact ((bb_le_live_bound_iff _ _).mp le_rfl) b ((st_select_frontier_mem h b).mpr hb)
    · apply (bb_le_live_bound_iff _ _).mpr
      intro b hb
      exact ((bb_le_live_bound_iff _ _).mp le_rfl) b ((st_select_frontier_mem h b).mp hb)
  change min (bbIncBound d.objective t.oa.incumbent) (bbLiveBound (stFrontier t)) =
    min (bbIncBound d.objective s.oa.incumbent) (bbLiveBound (stFrontier s))
  rw [st_select_oa h,he]

theorem st_global_replace_mono (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (o o' : OAState n m)
    (live replacement : List (BBRecord m)) (b : BBRecord m)
    (hinc : stGlobalBound d ⟨seeds,o,live,some b⟩ ≤ bbIncBound d.objective o'.incumbent)
    (hreplacement : ∀ c ∈ replacement,
      stGlobalBound d ⟨seeds,o,live,some b⟩ ≤ (c.lower : BBGlobalBound)) :
    stGlobalBound d ⟨seeds,o,live,some b⟩ ≤
      stGlobalBound d ⟨seeds,o',replacement ++ live,none⟩ := by
  simpa [stGlobalBound,stBoundState,stFrontier] using
    bb_global_replace_mono d.objective [] live replacement b o.incumbent o'.incumbent
      hinc hreplacement

theorem st_resolve_global_bound_mono (d : ModelData n m l r)
    {s t : STState n m l} (hs : STInvariant d s) (h : STResolve d s t) :
    stGlobalBound d s ≤ stGlobalBound d t := by
  have htOA := st_resolve_oa_invariant d hs.oa h
  have hinc : stGlobalBound d s ≤ bbIncBound d.objective t.oa.incumbent := by
    cases hi : t.oa.incumbent with
    | none => simp [bbIncBound]
    | some p => exact st_global_bound_sound d s hs p (htOA.feasible p hi)
  cases h with
  | @empty seeds o live b he =>
    simpa using st_global_replace_mono d seeds o o live [] b hinc (by simp)
  | @unbounded seeds o live b hu =>
    simpa using st_global_replace_mono d seeds o o live [] b hinc (by simp)
  | @unattained seeds o live b hne hbelow hbad =>
    simpa using st_global_replace_mono d seeds o o live [] b hinc (by simp)
  | @prune seeds o live b q hq hp =>
    simpa using st_global_replace_mono d seeds o o live [] b hinc (by simp)
  | @feasible seeds o live b q hq hf =>
    simpa using st_global_replace_mono d seeds o (stFeasibleUpdate d o q) live [] b hinc (by simp)
  | @callback seeds o live b q batch hq hc hb hy =>
    apply st_global_replace_mono d seeds o (oaAppend d o batch) live [stRaised d b q] b hinc
    intro c hc
    have he : c = stRaised d b q := by simpa using hc
    subst c
    apply (bb_global_le_record d.objective (stBoundState ⟨seeds,o,live,some b⟩) b
      (by simp [stBoundState,stFrontier])).trans
    exact_mod_cast le_max_left b.lower (d.objective q : WithBot ℝ)
  | @branch seeds o live b q i hq hc hf =>
    apply st_global_replace_mono d seeds o o live (bbChildren b i q d.objective) b hinc
    intro c hc
    simp only [bbChildren,List.mem_cons,List.not_mem_nil,or_false] at hc
    have hh : stGlobalBound d ⟨seeds,o,live,some b⟩ ≤
        ((max b.lower (d.objective q : WithBot ℝ)) : BBGlobalBound) := by
      apply (bb_global_le_record d.objective (stBoundState ⟨seeds,o,live,some b⟩) b
        (by simp [stBoundState,stFrontier])).trans
      exact_mod_cast le_max_left b.lower (d.objective q : WithBot ℝ)
    rcases hc with rfl | rfl <;> exact hh

theorem st_step_global_bound_mono (d : ModelData n m l r)
    {s t : STState n m l} (hs : STInvariant d s) (h : STStep d s t) :
    stGlobalBound d s ≤ stGlobalBound d t := by
  cases h with
  | select h => exact (st_select_global_bound d h).ge
  | resolve h => exact st_resolve_global_bound_mono d hs h

theorem st_process_global_bound_mono (d : ModelData n m l r)
    {s t : STState n m l} (hs : STInvariant d s) (h : STProcess d s t) :
    stGlobalBound d s ≤ stGlobalBound d t := by
  obtain ⟨w,hsel,hres⟩ := h
  rw [← st_select_global_bound d hsel]
  exact st_resolve_global_bound_mono d (st_select_preserves_invariant d hs hsel) hres

theorem st_resolve_incumbent_nonincreasing (d : ModelData n m l r)
    {s t : STState n m l} (h : STResolve d s t) :
    bbIncBound d.objective t.oa.incumbent ≤ bbIncBound d.objective s.oa.incumbent := by
  cases h with
  | empty _ => exact le_rfl
  | unbounded _ => exact le_rfl
  | unattained _ _ _ => exact le_rfl
  | prune _ _ => exact le_rfl
  | @feasible seeds o live b q hq hf =>
    exact (bb_update_inc_bound .weak d.objective o.incumbent q).trans_le (min_le_left _ _)
  | @callback seeds o live b q batch hq hc hb hy =>
    cases he : batch.restoration with
    | some rho => simp [oaAppend,he]
    | none =>
      cases hi : o.incumbent with
      | none => simp [oaAppend,he,hi,bbIncBound]
      | some p =>
        simpa [oaAppend,he,hi,bbIncBound] using
          (bb_value_le_value.mpr (oa_best_le_old d p batch.anchor))
  | branch _ _ _ _ => exact le_rfl

theorem st_step_incumbent_nonincreasing (d : ModelData n m l r)
    {s t : STState n m l} (h : STStep d s t) :
    bbIncBound d.objective t.oa.incumbent ≤ bbIncBound d.objective s.oa.incumbent := by
  cases h with
  | select h => rw [st_select_oa h]
  | resolve h => exact st_resolve_incumbent_nonincreasing d h

theorem st_process_incumbent_nonincreasing (d : ModelData n m l r)
    {s t : STState n m l} (h : STProcess d s t) :
    bbIncBound d.objective t.oa.incumbent ≤ bbIncBound d.objective s.oa.incumbent := by
  obtain ⟨w,hsel,hres⟩ := h
  simpa only [st_select_oa hsel] using st_resolve_incumbent_nonincreasing d hres

theorem st_step_seeds_retained (d : ModelData n m l r)
    {s t : STState n m l} (h : STStep d s t) : t.seeds = s.seeds := by
  cases h with
  | select h => cases h; rfl
  | resolve h => cases h <;> rfl

theorem st_step_history_retained (d : ModelData n m l r)
    {s t : STState n m l} (h : STStep d s t) :
    t.oa.history = s.oa.history ∨ ∃ b, t.oa.history = s.oa.history ++ [b] := by
  cases h with
  | select h => exact Or.inl (congrArg OAState.history (st_select_oa h))
  | resolve h =>
    cases h with
    | empty _ => exact Or.inl rfl
    | unbounded _ => exact Or.inl rfl
    | unattained _ _ _ => exact Or.inl rfl
    | prune _ _ => exact Or.inl rfl
    | feasible _ _ => exact Or.inl rfl
    | callback _ _ _ _ => exact Or.inr ⟨_,rfl⟩
    | branch _ _ _ _ => exact Or.inl rfl

/-- Retained cuts restrict every node, including nodes waiting in the live list. -/
theorem st_step_every_lp_subset (d : ModelData n m l r)
    {s t : STState n m l} (h : STStep d s t) (N : BBNode m) :
    stLP d t.seeds t.oa.history N ⊆ stLP d s.seeds s.oa.history N := by
  rw [st_step_seeds_retained d h]
  rcases st_step_history_retained d h with he | ⟨b,he⟩
  · rw [he]
  · rw [he,st_lp_append_batch]
    exact Set.inter_subset_left

theorem st_process_every_lp_subset (d : ModelData n m l r)
    {s t : STState n m l} (h : STProcess d s t) (N : BBNode m) :
    stLP d t.seeds t.oa.history N ⊆ stLP d s.seeds s.oa.history N := by
  obtain ⟨w,hsel,hres⟩ := h
  exact (st_step_every_lp_subset d (.resolve hres) N).trans
    (st_step_every_lp_subset d (.select hsel) N)

/-- Fresh current-LP values are a separate calculation; inherited bounds need
not equal them. The incumbent is included to account for already closed nodes. -/
def stFreshBound (d : ModelData n m l r) (s : STState n m l)
    (q : BBRecord m → Point n m) : BBGlobalBound :=
  bbGlobalBound d.objective
    ⟨(stFrontier s).map (fun b => ⟨b.node,(d.objective (q b) : WithBot ℝ)⟩),s.oa.incumbent⟩

theorem st_fresh_bound_sound (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (s : STState n m l) (hs : STInvariant d s) (q : BBRecord m → Point n m)
    (hq : ∀ b ∈ stFrontier s, IsMinimizer (stLP d s.seeds s.oa.history b.node)
      d.objective (q b)) (p : Point n m) (hp : p ∈ d.feasibleOn Set.univ) :
    stFreshBound d s q ≤ bbValue (d.objective p) := by
  rcases hs.coverage p hp with ⟨b,hb,hpb⟩ | ⟨a,ha,hav⟩
  · have hm : (⟨b.node,(d.objective (q b) : WithBot ℝ)⟩ : BBRecord m) ∈
        (stFrontier s).map (fun b => ⟨b.node,(d.objective (q b) : WithBot ℝ)⟩) :=
      List.mem_map.mpr ⟨b,hb,rfl⟩
    exact (bb_global_le_record d.objective _
      ⟨b.node,(d.objective (q b) : WithBot ℝ)⟩ hm).trans
      (bb_value_le_value.mpr
        (st_lp_minimum_lower_bound d s.seeds s.oa.history b.node hconv hdiff (hq b hb) p hpb))
  · exact (bb_global_le_incumbent d.objective _ a ha).trans (bb_value_le_value.mpr hav)

theorem st_fresh_bound_eq_stored (d : ModelData n m l r)
    (s : STState n m l) (q : BBRecord m → Point n m)
    (hfresh : ∀ b ∈ stFrontier s, b.lower = (d.objective (q b) : WithBot ℝ)) :
    stFreshBound d s q = stGlobalBound d s := by
  have he : (stFrontier s).map (fun b => (⟨b.node,(d.objective (q b) : WithBot ℝ)⟩ : BBRecord m)) =
      stFrontier s := by
    calc
      _ = (stFrontier s).map id := by
        apply List.map_congr_left
        intro b hb
        cases b
        simp only [id_eq,BBRecord.mk.injEq,true_and]
        exact (hfresh _ hb).symm
      _ = _ := List.map_id _
  simp only [stFreshBound,he,stGlobalBound,stBoundState]

theorem st_fresh_gap_sound (d : ModelData n m l r) {epsilon : ℝ}
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (s : STState n m l) (hs : STInvariant d s) (q : BBRecord m → Point n m)
    (hq : ∀ b ∈ stFrontier s, IsMinimizer (stLP d s.seeds s.oa.history b.node)
      d.objective (q b)) {u : Point n m} (hi : s.oa.incumbent = some u)
    (lower : ℝ) (hl : bbValue lower ≤ stFreshBound d s q)
    (ht : d.objective u ≤ lower + epsilon) : OAReturnCertificate d epsilon (.solution u) := by
  refine ⟨hs.oa.feasible u hi,lower,?_,ht⟩
  intro p hp
  exact bb_value_le_value.mp (hl.trans (st_fresh_bound_sound d hconv hdiff s hs q hq p hp))

end Chapter02

#print axioms Chapter02.st_select_oa
#print axioms Chapter02.st_select_frontier_mem
#print axioms Chapter02.st_select_preserves_invariant
#print axioms Chapter02.st_feasible_update_invariant
#print axioms Chapter02.st_append_preserves_below
#print axioms Chapter02.st_invariant_replace
#print axioms Chapter02.st_global_bound_sound
#print axioms Chapter02.st_invariant_delete
#print axioms Chapter02.st_child_feasible_cover
#print axioms Chapter02.st_resolve_preserves_invariant
#print axioms Chapter02.st_step_preserves_invariant
#print axioms Chapter02.st_process_preserves_invariant
#print axioms Chapter02.st_stop_sound
#print axioms Chapter02.st_stop_zero_optimal
#print axioms Chapter02.st_resolve_oa_invariant
#print axioms Chapter02.st_select_global_bound
#print axioms Chapter02.st_global_replace_mono
#print axioms Chapter02.st_resolve_global_bound_mono
#print axioms Chapter02.st_step_global_bound_mono
#print axioms Chapter02.st_process_global_bound_mono
#print axioms Chapter02.st_resolve_incumbent_nonincreasing
#print axioms Chapter02.st_step_incumbent_nonincreasing
#print axioms Chapter02.st_process_incumbent_nonincreasing
#print axioms Chapter02.st_step_seeds_retained
#print axioms Chapter02.st_step_history_retained
#print axioms Chapter02.st_step_every_lp_subset
#print axioms Chapter02.st_process_every_lp_subset
#print axioms Chapter02.st_fresh_bound_sound
#print axioms Chapter02.st_fresh_bound_eq_stored
#print axioms Chapter02.st_fresh_gap_sound
