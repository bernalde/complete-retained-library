module

public import Chapter02STSourceDriver

@[expose] public section

/-! An explicit Chapter 7 scheduling repair: finish the ordinary same-node
callback, then append at most one actual extra source batch. No extra-only
process or conversion to the old single-batch process is asserted. -/
noncomputable section
open Set Chapter02
namespace Chapter07.SingleTree
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def appendAux (D : BBPolyData N l r) (s : STSourceState I) :
    Option (STSourceBatch N) → STSourceState I
  | none => s
  | some b => { s with history := s.history ++ [b], incumbent := stSourceBatchInc D s.incumbent b }

def ExtraValid (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ) :
    Option (STSourceBatch N) → Prop
  | none => True
  | some b => stSourceBatchValid D I w b

def Stored (s : STSourceState I) : Prop :=
  ∀ u, s.incumbent = some u → ∃ b ∈ s.history, b.restoration = false ∧ u = b.anchor

theorem appendAux_none (D : BBPolyData N l r) (s : STSourceState I) :
    appendAux D s none = s := rfl

theorem appendAux_frontier (D : BBPolyData N l r) (s : STSourceState I) (extra) :
    stSourceFrontier (appendAux D s extra) = stSourceFrontier s := by
  cases extra <;> rfl

theorem appendAux_ready (D : BBPolyData N l r) (s : STSourceState I) (extra) :
    (appendAux D s extra).working = s.working := by cases extra <;> rfl

theorem appendAux_anchors (D : BBPolyData N l r) (s : STSourceState I) (b) :
    stSourceAnchors (appendAux D s (some b)) = stSourceAnchors s ++ [b.anchor] := by
  simp [appendAux, stSourceAnchors, List.map_append, List.append_assoc]

theorem appendAux_anchor_mem (D : BBPolyData N l r) (s : STSourceState I) (extra)
    {a : RealVector N} (ha : a ∈ stSourceAnchors s) :
    a ∈ stSourceAnchors (appendAux D s extra) := by
  cases extra with
  | none => exact ha
  | some b => rw [appendAux_anchors]; exact List.mem_append_left _ ha

theorem appendAux_history_mem (D : BBPolyData N l r) (s : STSourceState I) (extra)
    {b : STSourceBatch N} (hb : b ∈ s.history) : b ∈ (appendAux D s extra).history := by
  cases extra with
  | none => exact hb
  | some c => exact List.mem_append_left _ hb

theorem appendAux_incumbent_dominates (D : BBPolyData N l r) (s : STSourceState I)
    (extra) {u : RealVector N} (hu : s.incumbent = some u) :
    ∃ v, (appendAux D s extra).incumbent = some v ∧ D.f v ≤ D.f u := by
  cases extra with
  | none => exact ⟨u, hu, le_rfl⟩
  | some b => exact st_source_batch_inc_dominates D s.incumbent b hu

theorem appendAux_upper_nonincreasing (D : BBPolyData N l r) (s : STSourceState I)
    (extra) : stSourceUpper D.f (appendAux D s extra).incumbent ≤
      stSourceUpper D.f s.incumbent := by
  cases hi : s.incumbent with
  | none => simp [stSourceUpper]
  | some u =>
    obtain ⟨v, hv, hle⟩ := appendAux_incumbent_dominates D s extra hi
    simpa [stSourceUpper, hv] using hle

theorem appendAux_cutoff_subset (D : BBPolyData N l r) (policy : STSourcePolicy)
    (s : STSourceState I) (extra) (eta : ℝ)
    (h : policy.Admits (stSourceInc D (appendAux D s extra)) eta) :
    policy.Admits (stSourceInc D s) eta := by
  cases extra with
  | none => exact h
  | some b => exact st_source_batch_inc_cutoff D policy s.incumbent b eta h

theorem appendAux_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {s : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (extra) (he : ExtraValid D I w extra) :
    STSourceInvariant D I w policy (appendAux D s extra) := by
  cases extra with
  | none => exact hs
  | some b =>
    refine ⟨hs.seeds, ?_, ?_, ?_, ?_, ?_⟩
    · rw [appendAux_anchors]
      simp
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hs.valid c hc
      · have hcb : c = b := by simpa using hc
        simpa only [hcb, ExtraValid] using he
    · intro u hu
      cases hb : b.restoration with
      | true => exact hs.feasible u (by simpa [appendAux, stSourceBatchInc, hb] using hu)
      | false =>
        have hbest : stSourceBest D.f s.incumbent b.anchor = u := by
          simpa [appendAux, stSourceBatchInc, hb] using hu
        rw [← hbest]
        exact st_source_best_feasible D I s.incumbent b.anchor
          (st_source_batch_feasible D I w b he hb) hs.feasible
    · intro c hc hn
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨u, hu, hle⟩ := hs.best c hc hn
        obtain ⟨v, hv, hvu⟩ := st_source_batch_inc_dominates D s.incumbent b hu
        exact ⟨v, hv, hvu.trans hle⟩
      · have hcb : c = b := by simpa using hc
        subst c
        exact ⟨stSourceBest D.f s.incumbent b.anchor,
          by simp [appendAux, stSourceBatchInc, hn], st_source_best_le_new D.f s.incumbent b.anchor⟩
    · intro z hz hzcut
      obtain ⟨B, hB, hzB⟩ := hs.coverage z hz (appendAux_cutoff_subset D policy s (some b) _ hzcut)
      exact ⟨B, by simpa only [appendAux_frontier] using hB, hzB⟩

theorem appendAux_every_lp_subset (D : BBPolyData N l r) (policy : STSourcePolicy)
    (s : STSourceState I) (extra) (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    stSourceLP D B (stSourceAnchors (appendAux D s extra)) policy
        (stSourceInc D (appendAux D s extra)) ⊆
      stSourceLP D B (stSourceAnchors s) policy (stSourceInc D s) := by
  intro p hp
  have hp' := (st_source_lp_mem_iff D B _ policy _ p).mp hp
  apply (st_source_lp_mem_iff D B _ policy _ p).mpr
  refine ⟨hp'.1, hp'.2.1, ?_, ?_, appendAux_cutoff_subset D policy s extra _ hp'.2.2.2.2⟩
  · intro a ha
    exact hp'.2.2.1 a (appendAux_anchor_mem D s extra ha)
  · intro a ha
    exact hp'.2.2.2.1 a (appendAux_anchor_mem D s extra ha)

/-- Global coverage includes actual feasible competitors under the new cutoff,
not just the selected node's row set. -/
theorem appendAux_competitor_represented (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (hconvf : ConvexOn ℝ Set.univ D.f)
    (hdf : Differentiable ℝ D.f) (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j)) {s : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (extra) (he : ExtraValid D I w extra)
    {z : RealVector N} (hz : z ∈ D.feasible I)
    (hcut : policy.Admits (stSourceInc D (appendAux D s extra)) (D.f z)) :
    ∃ B ∈ stSourceFrontier (appendAux D s extra),
      (z, D.f z) ∈ stSourceLP D B (stSourceAnchors (appendAux D s extra)) policy
        (stSourceInc D (appendAux D s extra)) := by
  obtain ⟨B, hB, hzB⟩ := (appendAux_invariant D w policy hs extra he).coverage z hz hcut
  exact ⟨B, hB, st_source_feasible_lp D B _ policy _ hconvf hdf hconv hdiff hz hzB hcut⟩

theorem appendAux_seen_mono (D : BBPolyData N l r) (P : BBPartition I n m)
    (s : STSourceState I) (extra) :
    stSourceSeen P s.history ⊆ stSourceSeen P (appendAux D s extra).history := by
  classical
  cases extra with
  | none => exact Finset.Subset.refl _
  | some b =>
    change stSourceSeen P s.history ⊆ stSourceSeen P (s.history ++ [b])
    rw [st_source_seen_append]
    exact Finset.subset_insert _ _

theorem appendAux_remaining_le (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (s : STSourceState I) (extra) :
    stSourceRemaining P K (appendAux D s extra).history ≤ stSourceRemaining P K s.history := by
  classical
  apply Finset.card_le_card
  intro y hy
  rcases Finset.mem_sdiff.mp hy with ⟨hyb, hyn⟩
  exact Finset.mem_sdiff.mpr ⟨hyb, fun hm => hyn (appendAux_seen_mono D P s extra hm)⟩

theorem appendAux_treeWeight (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (s : STSourceState I) (extra) :
    stSourceTreeWeight P K (appendAux D s extra) = stSourceTreeWeight P K s := by
  simp only [stSourceTreeWeight, appendAux_frontier]

theorem appendAux_potential_le (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (s : STSourceState I) (extra) :
    stSourcePotential P K (appendAux D s extra) ≤ stSourcePotential P K s := by
  unfold stSourcePotential
  rw [appendAux_treeWeight]
  exact Nat.add_le_add_left (appendAux_remaining_le D P K s extra) _

theorem appendAux_repeated_key_potential (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (s : STSourceState I) (b : STSourceBatch N)
    (hb : stSourceKey P b.anchor ∈ stSourceSeen P s.history) :
    stSourcePotential P K (appendAux D s (some b)) = stSourcePotential P K s := by
  classical
  unfold stSourcePotential
  rw [appendAux_treeWeight]
  congr 1
  unfold stSourceRemaining
  change (stSourceBox P K \ stSourceSeen P (s.history ++ [b])).card = _
  rw [st_source_seen_append, Finset.insert_eq_of_mem hb]

theorem best_provenance (f : RealVector N → ℝ) (old : Option (RealVector N)) (a) :
    stSourceBest f old a = a ∨ ∃ u, old = some u ∧ stSourceBest f old a = u := by
  cases old with
  | none => exact Or.inl rfl
  | some u =>
    by_cases h : f a < f u
    · exact Or.inl (by simp [stSourceBest, h])
    · exact Or.inr ⟨u, rfl, by simp [stSourceBest, h]⟩

theorem appendAux_stored (D : BBPolyData N l r) {s : STSourceState I}
    (hs : Stored s) (extra) : Stored (appendAux D s extra) := by
  cases extra with
  | none => exact hs
  | some b =>
    intro u hu
    cases hb : b.restoration with
    | true =>
      obtain ⟨c, hc, hn, he⟩ := hs u (by simpa [appendAux, stSourceBatchInc, hb] using hu)
      exact ⟨c, List.mem_append_left _ hc, hn, he⟩
    | false =>
      have hu' : stSourceBest D.f s.incumbent b.anchor = u := by
        simpa [appendAux, stSourceBatchInc, hb] using hu
      rcases best_provenance D.f s.incumbent b.anchor with he | ⟨v, hv, he⟩
      · exact ⟨b, by simp [appendAux], hb, hu'.symm.trans he⟩
      · obtain ⟨c, hc, hn, hec⟩ := hs v hv
        exact ⟨c, List.mem_append_left _ hc, hn, (hu'.symm.trans he).trans hec⟩

/-- Exact same-node integral callback; its fields are the source subproblem
minimum, integrality, actual batch outcome and equality of integer coordinates. -/
inductive Callback (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ)
    (policy : STSourcePolicy) : STSourceState I → STSourceState I → Prop
  | actual {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {live : List (BBExtendedNode {i : Fin N // i ∈ I})}
      {B : BBExtendedNode {i : Fin N // i ∈ I}} {q : RealVector N × ℝ} {b : STSourceBatch N}
      (hq : IsMinimizer (stSourceLP D B (seeds ++ H.map STSourceBatch.anchor)
        policy (inc.map D.f)) Prod.snd q)
      (hi : STSourceIntegral I q.1) (hb : stSourceBatchValid D I w b)
      (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = q.1 i) :
      Callback D I w policy ⟨seeds,H,inc,live,some B⟩
        ⟨seeds,H ++ [b],stSourceBatchInc D inc b,B :: live,none⟩

theorem Callback.toResolve {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s t : STSourceState I} (h : Callback D I w policy s t) :
    STSourceResolve D I w policy s t := by
  cases h with
  | actual hq hi hb hy => exact .callback hq hi hb hy

inductive Process (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ)
    (policy : STSourcePolicy) : STSourceState I → STSourceState I → Prop
  | core {s u} (h : STSourceProcess D I w policy s u) : Process D I w policy s u
  | aux {s v u} (hsel : STSourceSelect s v) (hcallback : Callback D I w policy v u)
      (b : STSourceBatch N) (hb : stSourceBatchValid D I w b) :
      Process D I w policy s (appendAux D u (some b))

theorem process_after_callback {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s v u : STSourceState I}
    (hsel : STSourceSelect s v) (hc : Callback D I w policy v u)
    (extra) (he : ExtraValid D I w extra) : Process D I w policy s (appendAux D u extra) := by
  cases extra with
  | none => exact .core ⟨v, hsel, hc.toResolve⟩
  | some b => exact .aux hsel hc b he

theorem Process.decompose {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s t : STSourceState I} (h : Process D I w policy s t) :
    ∃ u extra, STSourceProcess D I w policy s u ∧ ExtraValid D I w extra ∧ t = appendAux D u extra := by
  cases h with
  | core hc => exact ⟨_, none, hc, trivial, rfl⟩
  | aux hsel hc b hb => exact ⟨_, some b, ⟨_, hsel, hc.toResolve⟩, hb, rfl⟩

theorem process_invariant (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j)) {s t : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (h : Process D I w policy s t) :
    STSourceInvariant D I w policy t := by
  obtain ⟨u, extra, hu, he, rfl⟩ := h.decompose
  exact appendAux_invariant D w policy
    (st_source_process_preserves_invariant D w policy hconvf hdf hconv hdiff hs hu) extra he

theorem process_ready {D : BBPolyData N l r} {w : Fin l → ℝ} {policy : STSourcePolicy}
    {s t : STSourceState I} (h : Process D I w policy s t) : s.working = none ∧ t.working = none := by
  obtain ⟨u, extra, hu, he, rfl⟩ := h.decompose
  rw [appendAux_ready]
  exact st_source_process_ready hu

theorem process_every_lp_subset (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    {s t : STSourceState I} (h : Process D I w policy s t) (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    stSourceLP D B (stSourceAnchors t) policy (stSourceInc D t) ⊆
      stSourceLP D B (stSourceAnchors s) policy (stSourceInc D s) := by
  obtain ⟨u, extra, hu, he, rfl⟩ := h.decompose
  exact (appendAux_every_lp_subset D policy u extra B).trans
    (st_source_process_every_lp_subset D w policy hu B)

theorem process_upper_nonincreasing (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {s t : STSourceState I} (h : Process D I w policy s t) :
    stSourceUpper D.f t.incumbent ≤ stSourceUpper D.f s.incumbent := by
  obtain ⟨u, extra, hu, he, rfl⟩ := h.decompose
  exact (appendAux_upper_nonincreasing D u extra).trans
    (st_source_process_upper_nonincreasing D w policy hu)

theorem process_potential_drop (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (w : Fin l → ℝ) (hw : ∀ j, 0 < w j)
    (policy : STSourcePolicy)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j)) (hCQ : STSourceFiberSlater D I)
    {s t : STSourceState I} (hs : STSourceInvariant D I w policy s)
    (h : Process D I w policy s t) : stSourcePotential P K t + 1 ≤ stSourcePotential P K s := by
  obtain ⟨u, extra, hu, he, rfl⟩ := h.decompose
  have hcore := st_source_process_potential_drop D P K hK w hw policy hpolicy
    hconvf hdf hconv hdiff hCQ hs hu
  have haux := appendAux_potential_le D P K u extra
  omega

theorem select_stored {s t : STSourceState I} (hs : Stored s) (h : STSourceSelect s t) : Stored t := by
  cases h
  exact hs

theorem resolve_stored (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    {s t : STSourceState I} (hs : Stored s) (h : STSourceResolve D I w policy s t) : Stored t := by
  cases h with
  | empty _ => exact hs
  | branch _ _ _ => exact hs
  | @callback seeds H inc live B q b hq hi hb hy =>
    exact appendAux_stored D hs (some b)

theorem process_stored (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    {s t : STSourceState I} (hs : Stored s) (h : Process D I w policy s t) : Stored t := by
  obtain ⟨u, extra, ⟨v, hsel, hres⟩, he, rfl⟩ := h.decompose
  exact appendAux_stored D (resolve_stored D w policy (select_stored hs hsel) hres) extra

/-- Original nonlinear feasibility, rather than OA or epigraph feasibility,
ensures that the same-fiber ordinary reply retains a point at least as good. -/
theorem feasible_candidate_retained (D : BBPolyData N l r) (w : Fin l → ℝ)
    (inc : Option (RealVector N)) (b : STSourceBatch N) (hb : stSourceBatchValid D I w b)
    {q : RealVector N} (hq : q ∈ D.feasible I)
    (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = q i) :
    b.restoration = false ∧ ∃ u, stSourceBatchInc D inc b = some u ∧ D.f u ≤ D.f q := by
  have hqf : q ∈ stSourceNonlinearFiber D I b.anchor :=
    ⟨⟨hq.1, fun i => (hy i).symm⟩, hq.2.1⟩
  cases hr : b.restoration with
  | true =>
    have he : stSourceNonlinearFiber D I b.anchor = ∅ := by
      have h := hb.2
      simp only [hr, Bool.true_eq, if_true] at h
      exact h.1
    rw [he] at hqf
    exact hqf.elim
  | false =>
    have hm : IsMinimizer (stSourceNonlinearFiber D I b.anchor) D.f b.anchor := by
      simpa only [hr, Bool.false_eq_true, if_false] using hb.2
    exact ⟨rfl, stSourceBest D.f inc b.anchor, by simp [stSourceBatchInc, hr],
      (st_source_best_le_new D.f inc b.anchor).trans (hm.2 q hqf)⟩

theorem feasible_candidate_after_aux (D : BBPolyData N l r) (w : Fin l → ℝ)
    (s : STSourceState I) (b : STSourceBatch N) (hb : stSourceBatchValid D I w b)
    {q : RealVector N} (hq : q ∈ D.feasible I)
    (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = q i) (extra) :
    ∃ u, (appendAux D (appendAux D s (some b)) extra).incumbent = some u ∧ D.f u ≤ D.f q := by
  obtain ⟨_, u, hu, hle⟩ := feasible_candidate_retained D w s.incumbent b hb hq hy
  obtain ⟨v, hv, hvu⟩ := appendAux_incumbent_dominates D (appendAux D s (some b)) extra hu
  exact ⟨v, hv, hvu.trans hle⟩

#print axioms Chapter07.SingleTree.appendAux_invariant
#print axioms Chapter07.SingleTree.appendAux_every_lp_subset
#print axioms Chapter07.SingleTree.appendAux_competitor_represented
#print axioms Chapter07.SingleTree.appendAux_potential_le
#print axioms Chapter07.SingleTree.appendAux_repeated_key_potential
#print axioms Chapter07.SingleTree.process_invariant
#print axioms Chapter07.SingleTree.process_potential_drop
#print axioms Chapter07.SingleTree.process_stored
#print axioms Chapter07.SingleTree.feasible_candidate_after_aux
end Chapter07.SingleTree
