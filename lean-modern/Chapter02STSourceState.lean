module

public import Chapter02STSourceGeometry

@[expose] public section

/-! Original-coordinate cumulative-history/current-cut repair of Algorithm 6.
No optional fractional-cut action is included. Raw callbacks carry actual
fixed-fiber outcomes; regularity, support and progress are derived separately.
Coverage is qualified by the current cutoff, since cutoff-empty LPs need not
represent empty original nodes. -/
noncomputable section
namespace Chapter02
variable {N l r : ℕ} {I : Finset (Fin N)}

structure STSourceState (I : Finset (Fin N)) where
  seeds : List (RealVector N)
  history : List (STSourceBatch N)
  incumbent : Option (RealVector N)
  live : List (BBExtendedNode {i : Fin N // i ∈ I})
  working : Option (BBExtendedNode {i : Fin N // i ∈ I})

def stSourceAnchors (s : STSourceState I) : List (RealVector N) :=
  s.seeds ++ s.history.map STSourceBatch.anchor

def stSourceInc (D : BBPolyData N l r) (s : STSourceState I) : Option ℝ :=
  s.incumbent.map D.f

def stSourceFrontier (s : STSourceState I) : List (BBExtendedNode {i : Fin N // i ∈ I}) :=
  s.working.toList ++ s.live

def stSourceBest (f : RealVector N → ℝ) (old : Option (RealVector N))
    (a : RealVector N) : RealVector N :=
  match old with
  | none => a
  | some u => if f a < f u then a else u

def stSourceBatchInc (D : BBPolyData N l r) (inc : Option (RealVector N))
    (b : STSourceBatch N) : Option (RealVector N) :=
  if b.restoration then inc else some (stSourceBest D.f inc b.anchor)

def stSourceUpper (f : RealVector N → ℝ) : Option (RealVector N) → WithTop ℝ
  | none => ⊤
  | some u => (f u : WithTop ℝ)

inductive STSourceSelect : STSourceState I → STSourceState I → Prop
  | choose (seeds : List (RealVector N)) (H : List (STSourceBatch N))
      (inc : Option (RealVector N)) (pre post : List (BBExtendedNode {i : Fin N // i ∈ I}))
      (B : BBExtendedNode {i : Fin N // i ∈ I}) :
      STSourceSelect ⟨seeds,H,inc,pre ++ B :: post,none⟩
        ⟨seeds,H,inc,pre ++ post,some B⟩

inductive STSourceResolve (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) : STSourceState I → STSourceState I → Prop
  | empty {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {live : List (BBExtendedNode {i : Fin N // i ∈ I})}
      {B : BBExtendedNode {i : Fin N // i ∈ I}}
      (he : stSourceLP D B (seeds ++ H.map STSourceBatch.anchor) policy (inc.map D.f) = ∅) :
      STSourceResolve D I w policy ⟨seeds,H,inc,live,some B⟩ ⟨seeds,H,inc,live,none⟩
  | callback {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {live : List (BBExtendedNode {i : Fin N // i ∈ I})}
      {B : BBExtendedNode {i : Fin N // i ∈ I}} {q : RealVector N × ℝ}
      {b : STSourceBatch N}
      (hq : IsMinimizer (stSourceLP D B (seeds ++ H.map STSourceBatch.anchor)
        policy (inc.map D.f)) Prod.snd q)
      (hi : STSourceIntegral I q.1) (hb : stSourceBatchValid D I w b)
      (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = q.1 i) :
      STSourceResolve D I w policy ⟨seeds,H,inc,live,some B⟩
        ⟨seeds,H ++ [b],stSourceBatchInc D inc b,B :: live,none⟩
  | branch {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {live : List (BBExtendedNode {i : Fin N // i ∈ I})}
      {B : BBExtendedNode {i : Fin N // i ∈ I}} {q : RealVector N × ℝ}
      (i : {i : Fin N // i ∈ I})
      (hq : IsMinimizer (stSourceLP D B (seeds ++ H.map STSourceBatch.anchor)
        policy (inc.map D.f)) Prod.snd q) (hf : BBFractional (q.1 i)) :
      STSourceResolve D I w policy ⟨seeds,H,inc,live,some B⟩
        ⟨seeds,H,inc,[B.left i (q.1 i),B.right i (q.1 i)] ++ live,none⟩

inductive STSourceStep (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) : STSourceState I → STSourceState I → Prop
  | select {s t} (h : STSourceSelect s t) : STSourceStep D I w policy s t
  | resolve {s t} (h : STSourceResolve D I w policy s t) : STSourceStep D I w policy s t

def STSourceProcess (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (s t : STSourceState I) : Prop :=
  ∃ v, STSourceSelect s v ∧ STSourceResolve D I w policy v t

structure STSourceInvariant (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (s : STSourceState I) : Prop where
  seeds : ∀ a ∈ s.seeds, a ∈ D.polyhedron
  nonempty : stSourceAnchors s ≠ []
  valid : ∀ b ∈ s.history, stSourceBatchValid D I w b
  feasible : ∀ u, s.incumbent = some u → u ∈ D.feasible I
  best : ∀ b ∈ s.history, b.restoration = false →
    ∃ u, s.incumbent = some u ∧ D.f u ≤ D.f b.anchor
  coverage : ∀ z ∈ D.feasible I, policy.Admits (stSourceInc D s) (D.f z) →
    ∃ B ∈ stSourceFrontier s, B.Holds (fun i => z i)

theorem st_source_best_le_new (f : RealVector N → ℝ) (old : Option (RealVector N))
    (a : RealVector N) : f (stSourceBest f old a) ≤ f a := by
  cases old with
  | none => exact le_rfl
  | some u =>
    simp only [stSourceBest]
    split
    · exact le_rfl
    · exact le_of_not_gt ‹¬ f a < f u›

theorem st_source_best_le_old (f : RealVector N → ℝ) (u a : RealVector N) :
    f (stSourceBest f (some u) a) ≤ f u := by
  simp only [stSourceBest]
  split
  · exact (‹f a < f u›).le
  · exact le_rfl

theorem st_source_best_feasible (D : BBPolyData N l r) (I : Finset (Fin N))
    (old : Option (RealVector N)) (a : RealVector N) (ha : a ∈ D.feasible I)
    (ho : ∀ u, old = some u → u ∈ D.feasible I) :
    stSourceBest D.f old a ∈ D.feasible I := by
  cases old with
  | none => exact ha
  | some u =>
    simp only [stSourceBest]
    split
    · exact ha
    · exact ho u rfl

theorem st_source_batch_inc_dominates (D : BBPolyData N l r)
    (inc : Option (RealVector N)) (b : STSourceBatch N) {u : RealVector N}
    (hu : inc = some u) :
    ∃ v, stSourceBatchInc D inc b = some v ∧ D.f v ≤ D.f u := by
  cases he : b.restoration with
  | true => exact ⟨u,by simp [stSourceBatchInc,he,hu],le_rfl⟩
  | false =>
    refine ⟨stSourceBest D.f inc b.anchor,by simp [stSourceBatchInc,he],?_⟩
    rw [hu]
    exact st_source_best_le_old D.f u b.anchor

theorem st_source_batch_inc_cutoff (D : BBPolyData N l r) (policy : STSourcePolicy)
    (inc : Option (RealVector N)) (b : STSourceBatch N) (eta : ℝ)
    (h : policy.Admits ((stSourceBatchInc D inc b).map D.f) eta) :
    policy.Admits (inc.map D.f) eta := by
  cases hi : inc with
  | none => trivial
  | some u =>
    obtain ⟨v,hv,hle⟩ := st_source_batch_inc_dominates D inc b hi
    rw [hv] at h
    exact st_source_cutoff_incumbent_monotone policy hle h

theorem st_source_select_frontier_mem {s t : STSourceState I} (h : STSourceSelect s t)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    B ∈ stSourceFrontier t ↔ B ∈ stSourceFrontier s := by
  cases h
  simp [stSourceFrontier,or_assoc,or_left_comm,or_comm]

theorem st_source_select_preserves_invariant (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (h : STSourceSelect s t) :
    STSourceInvariant D I w policy t := by
  cases h with
  | choose seeds H inc pre post B =>
    refine ⟨hs.seeds,hs.nonempty,hs.valid,hs.feasible,hs.best,?_⟩
    intro z hz ha
    obtain ⟨C,hC,hzC⟩ := hs.coverage z hz ha
    exact ⟨C,(st_source_select_frontier_mem (STSourceSelect.choose seeds H inc pre post B) C).mpr hC,hzC⟩

theorem st_source_children_cover (B : BBExtendedNode {i : Fin N // i ∈ I})
    (q z : RealVector N) (i : {i : Fin N // i ∈ I})
    (hz : B.Holds (fun j => z j)) (hi : STSourceIntegral I z) :
    (B.left i (q i)).Holds (fun j => z j) ∨
      (B.right i (q i)).Holds (fun j => z j) := by
  classical
  obtain ⟨k,hk⟩ := hi i
  have hc : k ≤ Int.floor (q i) ∨ Int.ceil (q i) ≤ k := by
    have hh := Int.ceil_le_floor_add_one (q i)
    omega
  rcases hc with hl | hr
  · left
    intro j
    by_cases hj : j = i
    · subst j
      refine ⟨(hz i).1,?_⟩
      simp only [BBExtendedNode.left,Function.update_self,WithTop.coe_le_coe]
      rw [← hk]
      exact_mod_cast hl
    · simpa [BBExtendedNode.left,Function.update,hj] using hz j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      refine ⟨?_,(hz i).2⟩
      simp only [BBExtendedNode.right,Function.update_self,WithBot.coe_le_coe]
      rw [← hk]
      exact_mod_cast hr
    · simpa [BBExtendedNode.right,Function.update,hj] using hz j

theorem st_source_callback_anchors (seeds : List (RealVector N))
    (H : List (STSourceBatch N)) (b : STSourceBatch N) :
    seeds ++ (H ++ [b]).map STSourceBatch.anchor =
      (seeds ++ H.map STSourceBatch.anchor) ++ [b.anchor] := by
  simp [List.map_append,List.append_assoc]

theorem st_source_anchor_polyhedron (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {s : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (a : RealVector N)
    (ha : a ∈ stSourceAnchors s) : a ∈ D.polyhedron := by
  rcases List.mem_append.mp ha with ha | ha
  · exact hs.seeds a ha
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact st_source_batch_anchor_polyhedron D I w b (hs.valid b hb)

theorem st_source_initial_batch_invariant (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (policy : STSourcePolicy)
    (b : STSourceBatch N) (hb : stSourceBatchValid D I w b) :
    STSourceInvariant D I w policy
      ⟨[],[b],stSourceBatchInc D none b,[BBExtendedNode.root],none⟩ := by
  refine ⟨by simp,by simp [stSourceAnchors],?_,?_,?_,?_⟩
  · intro c hc
    have he : c = b := by simpa using hc
    simpa [he] using hb
  · intro u hu
    cases he : b.restoration with
    | true => simp [stSourceBatchInc,he] at hu
    | false =>
      have hu' : b.anchor = u := by simpa [stSourceBatchInc,he,stSourceBest] using hu
      rw [← hu']
      exact st_source_batch_feasible D I w b hb he
  · intro c hc hn
    have he : c = b := by simpa using hc
    subst c
    exact ⟨b.anchor,by simp [stSourceBatchInc,hn,stSourceBest],le_rfl⟩
  · intro z hz ha
    exact ⟨BBExtendedNode.root,by simp [stSourceFrontier],BBExtendedNode.holds_root _⟩

theorem st_source_resolve_preserves_invariant (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {s t : STSourceState I} (hs : STSourceInvariant D I w policy s)
    (h : STSourceResolve D I w policy s t) : STSourceInvariant D I w policy t := by
  cases h with
  | @empty seeds H inc live B he =>
    refine ⟨hs.seeds,hs.nonempty,hs.valid,hs.feasible,hs.best,?_⟩
    intro z hz ha
    obtain ⟨C,hC,hzC⟩ := hs.coverage z hz ha
    have hC' : C = B ∨ C ∈ live := by simpa [stSourceFrontier] using hC
    rcases hC' with heC | hC'
    · subst C
      exact (st_source_empty_lp_no_improvement D B _ policy _ hconvf hdf hconv hdiff
        he hz hzC ha).elim
    · exact ⟨C,by simpa [stSourceFrontier] using hC',hzC⟩
  | @callback seeds H inc live B q b hq hi hb hy =>
    refine ⟨hs.seeds,?_,?_,?_,?_,?_⟩
    · simp [stSourceAnchors,List.map_append,List.append_assoc]
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hs.valid c hc
      · have he : c = b := by simpa using hc
        simpa [he] using hb
    · intro u hu
      cases he : b.restoration with
      | true => exact hs.feasible u (by simpa [stSourceBatchInc,he] using hu)
      | false =>
        have hu' : stSourceBest D.f inc b.anchor = u := by
          simpa [stSourceBatchInc,he] using hu
        rw [← hu']
        exact st_source_best_feasible D I inc b.anchor
          (st_source_batch_feasible D I w b hb he) hs.feasible
    · intro c hc hn
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨u,hu,hle⟩ := hs.best c hc hn
        obtain ⟨v,hv,hvu⟩ := st_source_batch_inc_dominates D inc b hu
        exact ⟨v,hv,hvu.trans hle⟩
      · have he : c = b := by simpa using hc
        subst c
        exact ⟨stSourceBest D.f inc b.anchor,by simp [stSourceBatchInc,hn],
          st_source_best_le_new D.f inc b.anchor⟩
    · intro z hz ha
      exact hs.coverage z hz (st_source_batch_inc_cutoff D policy inc b (D.f z) ha)
  | @branch seeds H inc live B q i hq hf =>
    refine ⟨hs.seeds,hs.nonempty,hs.valid,hs.feasible,hs.best,?_⟩
    intro z hz ha
    obtain ⟨C,hC,hzC⟩ := hs.coverage z hz ha
    have hC' : C = B ∨ C ∈ live := by simpa [stSourceFrontier] using hC
    rcases hC' with heC | hC'
    · subst C
      rcases st_source_children_cover B q.1 z i hzC hz.2.2 with hl | hr
      · exact ⟨B.left i (q.1 i),by simp [stSourceFrontier],hl⟩
      · exact ⟨B.right i (q.1 i),by simp [stSourceFrontier],hr⟩
    · exact ⟨C,by simp [stSourceFrontier,hC'],hzC⟩

theorem st_source_step_preserves_invariant (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {s t : STSourceState I} (hs : STSourceInvariant D I w policy s)
    (h : STSourceStep D I w policy s t) : STSourceInvariant D I w policy t := by
  cases h with
  | select h => exact st_source_select_preserves_invariant D w policy hs h
  | resolve h => exact st_source_resolve_preserves_invariant D w policy hconvf hdf hconv hdiff hs h

theorem st_source_process_preserves_invariant (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {s t : STSourceState I} (hs : STSourceInvariant D I w policy s)
    (h : STSourceProcess D I w policy s t) : STSourceInvariant D I w policy t := by
  obtain ⟨v,hsel,hres⟩ := h
  exact st_source_resolve_preserves_invariant D w policy hconvf hdf hconv hdiff
    (st_source_select_preserves_invariant D w policy hs hsel) hres

def STSourceReturnCertificate (D : BBPolyData N l r) (I : Finset (Fin N))
    (policy : STSourcePolicy) : Option (RealVector N) → Prop
  | none => D.feasible I = ∅
  | some u => u ∈ D.feasible I ∧
      ∀ z ∈ D.feasible I, ¬ policy.Admits (some (D.f u)) (D.f z)

inductive STSourceStop (s : STSourceState I) : Option (RealVector N) → Prop
  | exhausted (ready : s.working = none) (empty : s.live = []) :
      STSourceStop s s.incumbent

theorem st_source_exhausted_return (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (he : stSourceFrontier s = []) :
    STSourceReturnCertificate D I policy s.incumbent := by
  cases hi : s.incumbent with
  | none =>
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have ha : policy.Admits (stSourceInc D s) (D.f z) := by
      simp [stSourceInc,hi,STSourcePolicy.Admits]
    obtain ⟨B,hB,_⟩ := hs.coverage z hz ha
    simp [he] at hB
  | some u =>
    refine ⟨hs.feasible u hi,?_⟩
    intro z hz ha
    obtain ⟨B,hB,_⟩ := hs.coverage z hz (by simpa [stSourceInc,hi] using ha)
    simp [he] at hB

theorem st_source_stop_sound (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s : STSourceState I}
    (hs : STSourceInvariant D I w policy s) {out : Option (RealVector N)}
    (h : STSourceStop s out) : STSourceReturnCertificate D I policy out := by
  cases h with
  | exhausted hr he =>
    exact st_source_exhausted_return D w policy hs (by simp [stSourceFrontier,hr,he])

theorem st_source_exhausted_strict_optimal (D : BBPolyData N l r)
    (w : Fin l → ℝ) {s : STSourceState I} (hs : STSourceInvariant D I w .strict s)
    (he : stSourceFrontier s = []) {u : RealVector N} (hi : s.incumbent = some u) :
    IsMinimizer (D.feasible I) D.f u := by
  have hc := st_source_exhausted_return D w .strict hs he
  rw [hi] at hc
  exact ⟨hc.1,fun z hz => st_source_strict_no_improvement (hc.2 z hz)⟩

/-- The closed epsilon cutoff yields a strict absolute-gap conclusion. Its
operational finite-progress theorem separately requires positive epsilon. -/
theorem st_source_exhausted_gap_bound (D : BBPolyData N l r)
    (w : Fin l → ℝ) (epsilon : ℝ) {s : STSourceState I}
    (hs : STSourceInvariant D I w (.gap epsilon) s) (he : stSourceFrontier s = [])
    {u : RealVector N} (hi : s.incumbent = some u) :
    u ∈ D.feasible I ∧ ∀ z ∈ D.feasible I, D.f u < D.f z + epsilon := by
  have hc := st_source_exhausted_return D w (.gap epsilon) hs he
  rw [hi] at hc
  exact ⟨hc.1,fun z hz => st_source_gap_no_improvement (hc.2 z hz)⟩

theorem st_source_exhausted_no_incumbent (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (he : stSourceFrontier s = [])
    (hi : s.incumbent = none) : D.feasible I = ∅ := by
  have hc := st_source_exhausted_return D w policy hs he
  simpa [hi,STSourceReturnCertificate] using hc

theorem st_source_step_incumbent_monotone (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceStep D I w policy s t) {u : RealVector N} (hu : s.incumbent = some u) :
    ∃ v, t.incumbent = some v ∧ D.f v ≤ D.f u := by
  cases h with
  | select h => cases h; exact ⟨u,hu,le_rfl⟩
  | resolve h =>
    cases h with
    | empty _ => exact ⟨u,hu,le_rfl⟩
    | callback _ _ _ _ => exact st_source_batch_inc_dominates D _ _ hu
    | branch _ _ _ => exact ⟨u,hu,le_rfl⟩

theorem st_source_step_upper_nonincreasing (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceStep D I w policy s t) :
    stSourceUpper D.f t.incumbent ≤ stSourceUpper D.f s.incumbent := by
  cases hi : s.incumbent with
  | none => simp [stSourceUpper]
  | some u =>
    obtain ⟨v,hv,hle⟩ := st_source_step_incumbent_monotone D w policy h hi
    simpa [stSourceUpper,hv] using hle

theorem st_source_step_cutoff_subset (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceStep D I w policy s t) (eta : ℝ)
    (ha : policy.Admits (stSourceInc D t) eta) :
    policy.Admits (stSourceInc D s) eta := by
  cases hi : s.incumbent with
  | none => simp [stSourceInc,hi,STSourcePolicy.Admits]
  | some u =>
    obtain ⟨v,hv,hle⟩ := st_source_step_incumbent_monotone D w policy h hi
    have ha' : policy.Admits (some (D.f v)) eta := by simpa [stSourceInc,hv] using ha
    simpa [stSourceInc,hi] using st_source_cutoff_incumbent_monotone policy hle ha'

theorem st_source_step_seeds_retained (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceStep D I w policy s t) : t.seeds = s.seeds := by
  cases h with
  | select h => cases h; rfl
  | resolve h => cases h <;> rfl

theorem st_source_step_history_retained (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceStep D I w policy s t) :
    t.history = s.history ∨ ∃ b, t.history = s.history ++ [b] := by
  cases h with
  | select h => cases h; exact Or.inl rfl
  | resolve h =>
    cases h with
    | empty _ => exact Or.inl rfl
    | callback _ _ _ _ => exact Or.inr ⟨_,rfl⟩
    | branch _ _ _ => exact Or.inl rfl

theorem st_source_step_anchors_retained (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceStep D I w policy s t) :
    stSourceAnchors t = stSourceAnchors s ∨
      ∃ a, stSourceAnchors t = stSourceAnchors s ++ [a] := by
  unfold stSourceAnchors
  rw [st_source_step_seeds_retained D w policy h]
  rcases st_source_step_history_retained D w policy h with he | ⟨b,he⟩
  · exact Or.inl (by rw [he])
  · exact Or.inr ⟨b.anchor,by rw [he,st_source_callback_anchors]⟩

theorem st_source_step_anchor_mem (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceStep D I w policy s t) {a : RealVector N}
    (ha : a ∈ stSourceAnchors s) : a ∈ stSourceAnchors t := by
  rcases st_source_step_anchors_retained D w policy h with he | ⟨b,he⟩
  · simpa [he] using ha
  · rw [he]
    exact List.mem_append_left _ ha

/-- Every removal-time LP sees all retained global cuts and the improved
incumbent cutoff, including LPs at nodes not selected by the current step. -/
theorem st_source_step_every_lp_subset (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceStep D I w policy s t) (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    stSourceLP D B (stSourceAnchors t) policy (stSourceInc D t) ⊆
      stSourceLP D B (stSourceAnchors s) policy (stSourceInc D s) := by
  intro p hp
  have hp' := (st_source_lp_mem_iff D B _ policy _ p).mp hp
  apply (st_source_lp_mem_iff D B _ policy _ p).mpr
  refine ⟨hp'.1,hp'.2.1,?_,?_,st_source_step_cutoff_subset D w policy h p.2 hp'.2.2.2.2⟩
  · intro a ha
    exact hp'.2.2.1 a (st_source_step_anchor_mem D w policy h ha)
  · intro a ha
    exact hp'.2.2.2.1 a (st_source_step_anchor_mem D w policy h ha)

theorem st_source_process_upper_nonincreasing (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceProcess D I w policy s t) :
    stSourceUpper D.f t.incumbent ≤ stSourceUpper D.f s.incumbent := by
  obtain ⟨v,hsel,hres⟩ := h
  exact (st_source_step_upper_nonincreasing D w policy (.resolve hres)).trans
    (st_source_step_upper_nonincreasing D w policy (.select hsel))

theorem st_source_process_every_lp_subset (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState I}
    (h : STSourceProcess D I w policy s t) (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    stSourceLP D B (stSourceAnchors t) policy (stSourceInc D t) ⊆
      stSourceLP D B (stSourceAnchors s) policy (stSourceInc D s) := by
  obtain ⟨v,hsel,hres⟩ := h
  exact (st_source_step_every_lp_subset D w policy (.resolve hres) B).trans
    (st_source_step_every_lp_subset D w policy (.select hsel) B)

end Chapter02

#print axioms Chapter02.st_source_best_le_new
#print axioms Chapter02.st_source_best_le_old
#print axioms Chapter02.st_source_best_feasible
#print axioms Chapter02.st_source_batch_inc_dominates
#print axioms Chapter02.st_source_batch_inc_cutoff
#print axioms Chapter02.st_source_select_frontier_mem
#print axioms Chapter02.st_source_select_preserves_invariant
#print axioms Chapter02.st_source_children_cover
#print axioms Chapter02.st_source_callback_anchors
#print axioms Chapter02.st_source_anchor_polyhedron
#print axioms Chapter02.st_source_initial_batch_invariant
#print axioms Chapter02.st_source_resolve_preserves_invariant
#print axioms Chapter02.st_source_step_preserves_invariant
#print axioms Chapter02.st_source_process_preserves_invariant
#print axioms Chapter02.st_source_exhausted_return
#print axioms Chapter02.st_source_stop_sound
#print axioms Chapter02.st_source_exhausted_strict_optimal
#print axioms Chapter02.st_source_exhausted_gap_bound
#print axioms Chapter02.st_source_exhausted_no_incumbent
#print axioms Chapter02.st_source_step_incumbent_monotone
#print axioms Chapter02.st_source_step_upper_nonincreasing
#print axioms Chapter02.st_source_step_cutoff_subset
#print axioms Chapter02.st_source_step_seeds_retained
#print axioms Chapter02.st_source_step_history_retained
#print axioms Chapter02.st_source_step_anchors_retained
#print axioms Chapter02.st_source_step_anchor_mem
#print axioms Chapter02.st_source_step_every_lp_subset
#print axioms Chapter02.st_source_process_upper_nonincreasing
#print axioms Chapter02.st_source_process_every_lp_subset
