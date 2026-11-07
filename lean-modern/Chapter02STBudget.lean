module

public import Chapter02STSourceDriver

@[expose] public section

/-! Finite optional fractional-cut allowance, an explicit repair extension.
All raw actions use the current global height LP and actual fixed-fiber batches.
The allowance belongs to each node occurrence; callbacks reset only that occurrence.
No progress, freshness, support or constraint qualification is a raw-step field. -/
noncomputable section
namespace Chapter02
variable {N n m l r : ℕ} {I : Finset (Fin N)}

structure STBudgetNode (I : Finset (Fin N)) where
  node : BBExtendedNode {i : Fin N // i ∈ I}
  allowance : ℕ

structure STBudgetState (I : Finset (Fin N)) where
  seeds : List (RealVector N)
  history : List (STSourceBatch N)
  incumbent : Option (RealVector N)
  live : List (STBudgetNode I)
  working : Option (STBudgetNode I)

def stBudgetErase (s : STBudgetState I) : STSourceState I :=
  ⟨s.seeds,s.history,s.incumbent,s.live.map STBudgetNode.node,s.working.map STBudgetNode.node⟩

def stBudgetFrontier (s : STBudgetState I) : List (STBudgetNode I) :=
  s.working.toList ++ s.live

structure STBudgetInvariant (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) (s : STBudgetState I) : Prop where
  source : STSourceInvariant D I w policy (stBudgetErase s)
  allowance : ∀ B ∈ stBudgetFrontier s, B.allowance ≤ cap

def stBudgetInitial (D : BBPolyData N l r) (I : Finset (Fin N))
    (cap : ℕ) (b : STSourceBatch N) : STBudgetState I :=
  ⟨[],[b],stSourceBatchInc D none b,[⟨BBExtendedNode.root,cap⟩],none⟩

inductive STBudgetSelect : STBudgetState I → STBudgetState I → Prop
  | choose (seeds : List (RealVector N)) (H : List (STSourceBatch N))
      (inc : Option (RealVector N)) (pre post : List (STBudgetNode I))
      (B : STBudgetNode I) :
      STBudgetSelect ⟨seeds,H,inc,pre ++ B :: post,none⟩
        ⟨seeds,H,inc,pre ++ post,some B⟩

inductive STBudgetResolve (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) :
    STBudgetState I → STBudgetState I → Prop
  | empty {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {live : List (STBudgetNode I)} {B : STBudgetNode I}
      (he : stSourceLP D B.node (seeds ++ H.map STSourceBatch.anchor) policy (inc.map D.f) = ∅) :
      STBudgetResolve D I w policy cap ⟨seeds,H,inc,live,some B⟩ ⟨seeds,H,inc,live,none⟩
  | callback {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {live : List (STBudgetNode I)} {B : STBudgetNode I}
      {q : RealVector N × ℝ} {b : STSourceBatch N}
      (hq : IsMinimizer (stSourceLP D B.node (seeds ++ H.map STSourceBatch.anchor)
        policy (inc.map D.f)) Prod.snd q)
      (hi : STSourceIntegral I q.1) (hb : stSourceBatchValid D I w b)
      (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = q.1 i) :
      STBudgetResolve D I w policy cap ⟨seeds,H,inc,live,some B⟩
        ⟨seeds,H ++ [b],stSourceBatchInc D inc b,⟨B.node,cap⟩ :: live,none⟩
  | branch {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {live : List (STBudgetNode I)} {B : STBudgetNode I}
      {q : RealVector N × ℝ} (i : {i : Fin N // i ∈ I})
      (hq : IsMinimizer (stSourceLP D B.node (seeds ++ H.map STSourceBatch.anchor)
        policy (inc.map D.f)) Prod.snd q) (hf : BBFractional (q.1 i)) :
      STBudgetResolve D I w policy cap ⟨seeds,H,inc,live,some B⟩
        ⟨seeds,H,inc,[⟨B.node.left i (q.1 i),cap⟩,⟨B.node.right i (q.1 i),cap⟩] ++ live,none⟩
  | cut {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {live : List (STBudgetNode I)} {B : STBudgetNode I}
      {q : RealVector N × ℝ} (i : {i : Fin N // i ∈ I})
      (hq : IsMinimizer (stSourceLP D B.node (seeds ++ H.map STSourceBatch.anchor)
        policy (inc.map D.f)) Prod.snd q) (hf : BBFractional (q.1 i))
      (ha : 0 < B.allowance) :
      STBudgetResolve D I w policy cap ⟨seeds,H,inc,live,some B⟩
        ⟨seeds ++ [q.1],H,inc,⟨B.node,B.allowance-1⟩ :: live,none⟩

inductive STBudgetStep (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) : STBudgetState I → STBudgetState I → Prop
  | select {s t} (h : STBudgetSelect s t) : STBudgetStep D I w policy cap s t
  | resolve {s t} (h : STBudgetResolve D I w policy cap s t) : STBudgetStep D I w policy cap s t

def STBudgetProcess (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) (s t : STBudgetState I) : Prop :=
  ∃ v, STBudgetSelect s v ∧ STBudgetResolve D I w policy cap v t

theorem st_budget_initial_erasure (D : BBPolyData N l r) (I : Finset (Fin N))
    (cap : ℕ) (b : STSourceBatch N) :
    stBudgetErase (stBudgetInitial D I cap b) = stSourceInitial D I b := rfl

theorem st_budget_initial_invariant (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) (b : STSourceBatch N)
    (hb : stSourceBatchValid D I w b) :
    STBudgetInvariant D I w policy cap (stBudgetInitial D I cap b) := by
  refine ⟨st_source_initial_batch_invariant D I w policy b hb,?_⟩
  intro B hB
  have he : B = ⟨BBExtendedNode.root,cap⟩ := by simpa [stBudgetFrontier,stBudgetInitial] using hB
  simp [he]

theorem st_budget_select_erasure {s t : STBudgetState I} (h : STBudgetSelect s t) :
    STSourceSelect (stBudgetErase s) (stBudgetErase t) := by
  cases h
  simpa [stBudgetErase,List.map_append] using
    STSourceSelect.choose _ _ _ _ _ _

/-- Every resolution which does not append a seed erases to the exact source core. -/
theorem st_budget_noncut_erasure (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ) {s t : STBudgetState I}
    (h : STBudgetResolve D I w policy cap s t) (he : t.seeds = s.seeds) :
    STSourceResolve D I w policy (stBudgetErase s) (stBudgetErase t) := by
  cases h with
  | empty hp => exact .empty hp
  | callback hq hi hb hy => exact .callback hq hi hb hy
  | branch i hq hf => exact .branch i hq hf
  | cut i hq hf ha =>
    have hh := congrArg List.length he
    simp only [List.length_append,List.length_singleton] at hh
    omega

theorem st_budget_select_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ) {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy cap s) (h : STBudgetSelect s t) :
    STBudgetInvariant D I w policy cap t := by
  refine ⟨st_source_select_preserves_invariant D w policy hs.source
    (st_budget_select_erasure h),?_⟩
  cases h
  intro B hB
  exact hs.allowance B (by simpa [stBudgetFrontier,or_assoc,or_left_comm,or_comm] using hB)

theorem st_budget_resolve_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {s t : STBudgetState I} (hs : STBudgetInvariant D I w policy cap s)
    (h : STBudgetResolve D I w policy cap s t) : STBudgetInvariant D I w policy cap t := by
  constructor
  · cases h with
    | empty he =>
      exact st_source_resolve_preserves_invariant D w policy
        hconvf hdf hconv hdiff hs.source (.empty he)
    | callback hq hi hb hy =>
      exact st_source_resolve_preserves_invariant D w policy
        hconvf hdf hconv hdiff hs.source (.callback hq hi hb hy)
    | branch i hq hf =>
      exact st_source_resolve_preserves_invariant D w policy
        hconvf hdf hconv hdiff hs.source (.branch i hq hf)
    | @cut seeds H inc live B q i hq hf ha =>
      have hqX : q.1 ∈ D.polyhedron := hq.1.1.1
      refine ⟨?_,?_,hs.source.valid,hs.source.feasible,hs.source.best,?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hs.source.seeds a ha
        · simpa only [List.mem_singleton.mp ha] using hqX
      · intro he
        have hh := congrArg List.length he
        simp [stSourceAnchors,stBudgetErase] at hh
      · intro z hz hc
        obtain ⟨C,hC,hzC⟩ := hs.source.coverage z hz hc
        exact ⟨C,by simpa [stSourceFrontier,stBudgetErase] using hC,hzC⟩
  · cases h with
    | empty he =>
      intro C hC
      exact hs.allowance C (by simp only [stBudgetFrontier,Option.toList_some,
        List.singleton_append,List.mem_cons]; exact Or.inr hC)
    | callback hq hi hb hy =>
      intro C hC
      simp only [stBudgetFrontier,Option.toList_none,List.nil_append,List.mem_cons] at hC
      rcases hC with rfl | hC
      · exact le_rfl
      · exact hs.allowance C (by simp [stBudgetFrontier,hC])
    | branch i hq hf =>
      intro C hC
      simp only [stBudgetFrontier,Option.toList_none,List.nil_append,
        List.cons_append,List.mem_cons] at hC
      rcases hC with rfl | rfl | hC
      · exact le_rfl
      · exact le_rfl
      · exact hs.allowance C (by simp [stBudgetFrontier,hC])
    | @cut seeds H inc live B q i hq hf ha =>
      intro C hC
      simp only [stBudgetFrontier,Option.toList_none,List.nil_append,List.mem_cons] at hC
      rcases hC with rfl | hC
      · exact (Nat.sub_le _ _).trans (hs.allowance B (by simp [stBudgetFrontier]))
      · exact hs.allowance C (by simp [stBudgetFrontier,hC])

theorem st_budget_step_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {s t : STBudgetState I} (hs : STBudgetInvariant D I w policy cap s)
    (h : STBudgetStep D I w policy cap s t) : STBudgetInvariant D I w policy cap t := by
  cases h with
  | select h => exact st_budget_select_invariant D w policy cap hs h
  | resolve h => exact st_budget_resolve_invariant D w policy cap hconvf hdf hconv hdiff hs h

theorem st_budget_process_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {s t : STBudgetState I} (hs : STBudgetInvariant D I w policy cap s)
    (h : STBudgetProcess D I w policy cap s t) : STBudgetInvariant D I w policy cap t := by
  obtain ⟨v,hv,ht⟩ := h
  exact st_budget_resolve_invariant D w policy cap hconvf hdf hconv hdiff
    (st_budget_select_invariant D w policy cap hs hv) ht


def stBudgetNodeWeight (P : BBPartition I n m) (K : ℝ) (cap : ℕ)
    (B : STBudgetNode I) : ℕ :=
  (cap+1)*((B.node.clamp P.integerEquiv K).weight-1)+B.allowance+1

def stBudgetPotential (P : BBPartition I n m) (K : ℝ) (cap : ℕ)
    (s : STBudgetState I) : ℕ :=
  ((stBudgetFrontier s).map (stBudgetNodeWeight P K cap)).sum +
    (cap+1)*stSourceRemaining P K s.history

def stBudgetPhasePotential (P : BBPartition I n m) (K : ℝ) (cap : ℕ)
    (s : STBudgetState I) : ℕ :=
  2*stBudgetPotential P K cap s + if s.working.isNone then 1 else 0

theorem st_budget_node_weight_pos (P : BBPartition I n m) (K : ℝ) (cap : ℕ)
    (B : STBudgetNode I) : 0 < stBudgetNodeWeight P K cap B := by
  unfold stBudgetNodeWeight
  omega

theorem st_budget_node_weight_full (P : BBPartition I n m) (K : ℝ) (cap : ℕ)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    stBudgetNodeWeight P K cap ⟨B,cap⟩ = (cap+1)*(B.clamp P.integerEquiv K).weight := by
  have hp := bb_weight_pos (B.clamp P.integerEquiv K)
  have he : (B.clamp P.integerEquiv K).weight = (B.clamp P.integerEquiv K).weight-1+1 := by omega
  unfold stBudgetNodeWeight
  dsimp only
  conv_rhs => rw [he,Nat.mul_add,Nat.mul_one]
  omega

theorem st_budget_select_potential (P : BBPartition I n m) (K : ℝ) (cap : ℕ)
    {s t : STBudgetState I} (h : STBudgetSelect s t) :
    stBudgetPotential P K cap t = stBudgetPotential P K cap s := by
  cases h
  simp [stBudgetPotential,stBudgetFrontier,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem st_budget_select_phase_drop (P : BBPartition I n m) (K : ℝ) (cap : ℕ)
    {s t : STBudgetState I} (h : STBudgetSelect s t) :
    stBudgetPhasePotential P K cap t + 1 = stBudgetPhasePotential P K cap s := by
  have hp := st_budget_select_potential P K cap h
  cases h
  simpa [stBudgetPhasePotential] using hp

theorem st_budget_resolve_ready {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {cap : ℕ} {s t : STBudgetState I}
    (h : STBudgetResolve D I w policy cap s t) : t.working = none := by cases h <;> rfl

theorem st_budget_resolve_working {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {cap : ℕ} {s t : STBudgetState I}
    (h : STBudgetResolve D I w policy cap s t) : s.working.isSome = true := by cases h <;> rfl

theorem st_budget_process_ready {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {cap : ℕ} {s t : STBudgetState I}
    (h : STBudgetProcess D I w policy cap s t) : s.working = none ∧ t.working = none := by
  obtain ⟨v,hv,ht⟩ := h
  exact ⟨by cases hv; rfl,st_budget_resolve_ready ht⟩

theorem st_budget_resolve_potential_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (w : Fin l → ℝ) (hw : ∀ j, 0 < w j) (policy : STSourcePolicy) (cap : ℕ)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy cap s) (h : STBudgetResolve D I w policy cap s t) :
    stBudgetPotential P K cap t + 1 ≤ stBudgetPotential P K cap s := by
  cases h with
  | @empty seeds H inc live B he =>
    have hp := st_budget_node_weight_pos P K cap B
    simp only [stBudgetPotential,stBudgetFrontier,Option.toList_none,Option.toList_some,
      List.nil_append,List.singleton_append,List.map_cons,List.sum_cons]
    omega
  | @callback seeds H inc live B q b hq hi hb hy =>
    have hn := st_source_callback_unseen D P K w hw policy hpolicy hconvf hdf hconv
      hdiff hCQ hs.source B.node hq.1 b hb hy
    have hm := st_source_key_mem_box D P K hK
      (st_source_batch_anchor_polyhedron D I w b hb) hb.1
    have hr := st_source_remaining_append_exact P K H b hm hn
    simp only [stBudgetPotential,stBudgetFrontier,Option.toList_none,Option.toList_some,
      List.nil_append,List.singleton_append,List.map_cons,List.sum_cons,stBudgetNodeWeight]
    rw [← hr,Nat.mul_add,Nat.mul_one]
    omega
  | @branch seeds H inc live B q i hq hf =>
    have hp := st_source_children_weight_drop D P K hK B.node
      (seeds ++ H.map STSourceBatch.anchor) hq.1.1 i hf
    have hp' : ((B.node.left i (q.1 i)).clamp P.integerEquiv K).weight +
        ((B.node.right i (q.1 i)).clamp P.integerEquiv K).weight ≤
        (B.node.clamp P.integerEquiv K).weight-1 := by omega
    have hm := Nat.mul_le_mul_left (cap+1) hp'
    simp only [Nat.mul_add] at hm
    simp only [stBudgetPotential,stBudgetFrontier,Option.toList_none,Option.toList_some,
      List.nil_append,List.singleton_append,List.cons_append,List.map_cons,List.sum_cons,
      st_budget_node_weight_full]
    unfold stBudgetNodeWeight
    omega
  | @cut seeds H inc live B q i hq hf ha =>
    simp only [stBudgetPotential,stBudgetFrontier,Option.toList_none,Option.toList_some,
      List.nil_append,List.singleton_append,List.map_cons,List.sum_cons,stBudgetNodeWeight]
    omega

theorem st_budget_resolve_phase_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (w : Fin l → ℝ) (hw : ∀ j, 0 < w j) (policy : STSourcePolicy) (cap : ℕ)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy cap s) (h : STBudgetResolve D I w policy cap s t) :
    stBudgetPhasePotential P K cap t + 1 ≤ stBudgetPhasePotential P K cap s := by
  have hp := st_budget_resolve_potential_drop D P K hK w hw policy cap hpolicy
    hconvf hdf hconv hdiff hCQ hs h
  have ht := st_budget_resolve_ready h
  have hw := st_budget_resolve_working h
  have hh : s.working.isNone = false := by cases he : s.working <;> simp_all
  simp only [stBudgetPhasePotential,ht,Option.isNone_none,Bool.true_eq,if_true,
    hh,Bool.false_eq_true,if_false]
  omega

theorem st_budget_step_phase_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (w : Fin l → ℝ) (hw : ∀ j, 0 < w j) (policy : STSourcePolicy) (cap : ℕ)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy cap s) (h : STBudgetStep D I w policy cap s t) :
    stBudgetPhasePotential P K cap t + 1 ≤ stBudgetPhasePotential P K cap s := by
  cases h with
  | select h => exact (st_budget_select_phase_drop P K cap h).le
  | resolve h =>
    exact st_budget_resolve_phase_drop D P K hK w hw policy cap hpolicy
      hconvf hdf hconv hdiff hCQ hs h

theorem st_budget_process_potential_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (w : Fin l → ℝ) (hw : ∀ j, 0 < w j) (policy : STSourcePolicy) (cap : ℕ)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy cap s) (h : STBudgetProcess D I w policy cap s t) :
    stBudgetPotential P K cap t + 1 ≤ stBudgetPotential P K cap s := by
  obtain ⟨v,hv,ht⟩ := h
  have hh := st_budget_resolve_potential_drop D P K hK w hw policy cap hpolicy
    hconvf hdf hconv hdiff hCQ (st_budget_select_invariant D w policy cap hs hv) ht
  rw [st_budget_select_potential P K cap hv] at hh
  exact hh


inductive STBudgetInitialize (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (cap : ℕ) : Option (STBudgetState I) → Prop
  | empty (he : stSourceMixedAffine D I = ∅) : STBudgetInitialize D I w cap none
  | seeded (a : RealVector N) (b : STSourceBatch N)
      (ha : a ∈ D.polyhedron) (hi : STSourceIntegral I a)
      (hb : stSourceBatchValid D I w b)
      (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = a i) :
      STBudgetInitialize D I w cap (some (stBudgetInitial D I cap b))

theorem st_budget_initialization_erasure (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (cap : ℕ) {out : Option (STBudgetState I)}
    (h : STBudgetInitialize D I w cap out) :
    STSourceInitialize D I w (out.map stBudgetErase) := by
  cases h with
  | empty he => exact .empty he
  | seeded a b ha hi hb hy => exact .seeded a b ha hi hb hy

theorem st_budget_initialize_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (cap : ℕ) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : Continuous D.f) :
    ∃ out, STBudgetInitialize D I w cap out := by
  obtain ⟨out,ho⟩ := st_cutoff_initialize_exists D I w hX hc hf
  cases ho with
  | empty he => exact ⟨none,.empty he⟩
  | seeded a b ha hi hb hy => exact ⟨_,.seeded a b ha hi hb hy⟩

theorem st_budget_initialization_invariant (D : BBPolyData N l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) {s : STBudgetState I}
    (h : STBudgetInitialize D I w cap (some s)) :
    STBudgetInvariant D I w policy cap s ∧ s.working = none := by
  cases h with
  | seeded a b ha hi hb hy => exact ⟨st_budget_initial_invariant D I w policy cap b hb,rfl⟩

theorem st_budget_initial_potential_bound (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (cap : ℕ) (b : STSourceBatch N) :
    stBudgetPotential P K cap (stBudgetInitial D I cap b) ≤
      (cap+1)*((bbRootNode (D.model P K)).weight+(stSourceBox P K).card) := by
  have hr := st_source_remaining_le P K [b]
  have hm := Nat.mul_le_mul_left (cap+1) hr
  simp only [stBudgetPotential,stBudgetFrontier,stBudgetInitial,Option.toList_none,
    List.nil_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
    st_budget_node_weight_full,BBExtendedNode.clamp_root]
  rw [Nat.mul_add]
  exact Nat.add_le_add_left hm _

inductive STBudgetStop (s : STBudgetState I) : Option (RealVector N) → Prop
  | exhausted (ready : s.working = none) (empty : s.live = []) :
      STBudgetStop s s.incumbent

theorem st_budget_stop_erasure {s : STBudgetState I} {out : Option (RealVector N)}
    (h : STBudgetStop s out) : STSourceStop (stBudgetErase s) out := by
  cases h with
  | exhausted hr he => exact .exhausted (by simp [stBudgetErase,hr]) (by simp [stBudgetErase,he])

theorem st_budget_stop_sound (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ) {s : STBudgetState I} {out : Option (RealVector N)}
    (hs : STBudgetInvariant D I w policy cap s) (h : STBudgetStop s out) :
    STSourceReturnCertificate D I policy out :=
  st_source_stop_sound D w policy hs.source (st_budget_stop_erasure h)

theorem st_budget_resolve_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) (hf : Continuous D.f)
    (s : STBudgetState I) (hs : STBudgetInvariant D I w policy cap s)
    (B : STBudgetNode I) (hB : s.working = some B) :
    ∃ t, STBudgetResolve D I w policy cap s t := by
  classical
  obtain ⟨seeds,H,inc,live,working⟩ := s
  simp only at hB
  subst working
  rcases st_source_lp_reply D B.node (seeds ++ H.map STSourceBatch.anchor)
    policy (inc.map D.f) hX hs.source.nonempty with he | ⟨q,hq⟩
  · exact ⟨_,.empty he⟩
  · by_cases hi : STSourceIntegral I q.1
    · obtain ⟨b,hb,hy⟩ := st_source_lp_fiber_reply D B.node
        (seeds ++ H.map STSourceBatch.anchor) policy (inc.map D.f) w hX hc hf hq.1 hi
      exact ⟨_,.callback hq hi hb hy⟩
    · have hex : ∃ i : {i : Fin N // i ∈ I}, BBFractional (q.1 i) := by
        by_contra hn
        apply hi
        intro i
        by_contra hz
        exact hn ⟨i,hz⟩
      obtain ⟨i,hi⟩ := hex
      exact ⟨_,.branch i hq hi⟩

/-- Choice includes every legal optional cut; nonblocking can always choose branch. -/
theorem st_budget_stop_or_step (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) (hf : Continuous D.f)
    (s : STBudgetState I) (hs : STBudgetInvariant D I w policy cap s) :
    (∃ out, STBudgetStop s out) ∨ ∃ t, STBudgetStep D I w policy cap s t := by
  cases he : s.working with
  | some B =>
    obtain ⟨t,ht⟩ := st_budget_resolve_exists D I w policy cap hX hc hf s hs B he
    exact Or.inr ⟨t,.resolve ht⟩
  | none =>
    obtain ⟨seeds,H,inc,live,working⟩ := s
    simp only at he
    subst working
    cases live with
    | nil => exact Or.inl ⟨inc,.exhausted rfl rfl⟩
    | cons B rest => exact Or.inr ⟨_,.select (.choose seeds H inc [] rest B)⟩

inductive STBudgetTrace (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) :
    ℕ → STBudgetState I → STBudgetState I → Prop
  | nil (s) : STBudgetTrace D I w policy cap 0 s s
  | cons {s t u k} (step : STBudgetProcess D I w policy cap s t)
      (tail : STBudgetTrace D I w policy cap k t u) : STBudgetTrace D I w policy cap (k+1) s u

inductive STBudgetMicroTrace (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) :
    ℕ → STBudgetState I → STBudgetState I → Prop
  | nil (s) : STBudgetMicroTrace D I w policy cap 0 s s
  | cons {s t u k} (step : STBudgetStep D I w policy cap s t)
      (tail : STBudgetMicroTrace D I w policy cap k t u) : STBudgetMicroTrace D I w policy cap (k+1) s u

theorem st_budget_trace_micro (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ) {k : ℕ} {s t : STBudgetState I}
    (h : STBudgetTrace D I w policy cap k s t) : STBudgetMicroTrace D I w policy cap (2*k) s t := by
  induction h with
  | nil => exact .nil _
  | cons step tail ih =>
    obtain ⟨v,hv,ht⟩ := step
    simpa [Nat.mul_add] using STBudgetMicroTrace.cons (.select hv)
      (STBudgetMicroTrace.cons (.resolve ht) ih)

theorem st_budget_micro_append_step (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ) {k : ℕ} {s t u : STBudgetState I}
    (h : STBudgetMicroTrace D I w policy cap k s t) (step : STBudgetStep D I w policy cap t u) :
    STBudgetMicroTrace D I w policy cap (k+1) s u := by
  induction h with
  | nil => exact .cons step (.nil u)
  | cons hs ht ih => exact .cons hs (ih step)


theorem st_budget_trace_potential_bound (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I)
    {k : ℕ} {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy cap s) (h : STBudgetTrace D I w policy cap k s t) :
    stBudgetPotential P K cap t + k ≤ stBudgetPotential P K cap s := by
  induction h with
  | nil => omega
  | cons step tail ih =>
    have hd := st_budget_process_potential_drop D P K hK w hw policy cap hpolicy
      hconvf hdf hconv hdiff hCQ hs step
    have hh := ih (st_budget_process_invariant D w policy cap hconvf hdf hconv hdiff hs step)
    omega

theorem st_budget_micro_potential_bound (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I)
    {k : ℕ} {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy cap s) (h : STBudgetMicroTrace D I w policy cap k s t) :
    stBudgetPhasePotential P K cap t + k ≤ stBudgetPhasePotential P K cap s := by
  induction h with
  | nil => omega
  | cons step tail ih =>
    have hd := st_budget_step_phase_drop D P K hK w hw policy cap hpolicy
      hconvf hdf hconv hdiff hCQ hs step
    have hh := ih (st_budget_step_invariant D w policy cap hconvf hdf hconv hdiff hs step)
    omega

def STBudgetDecisionLegal (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) (s : STBudgetState I) :
    Option (RealVector N) ⊕ STBudgetState I → Prop
  | .inl out => STBudgetStop s out
  | .inr t => STBudgetStep D I w policy cap s t

/-- Selectors range over every legal raw microstep, including allowed cut rounds. -/
def STBudgetSelector (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ) :=
  ∀ s : STBudgetState I, {c : Option (RealVector N) ⊕ STBudgetState I //
    STBudgetInvariant D I w policy cap s → STBudgetDecisionLegal D I w policy cap s c}

theorem st_budget_selector_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) (hf : Continuous D.f) :
    Nonempty (STBudgetSelector D I w policy cap) := by
  classical
  have hex : ∀ s : STBudgetState I, Nonempty {c : Option (RealVector N) ⊕ STBudgetState I //
      STBudgetInvariant D I w policy cap s → STBudgetDecisionLegal D I w policy cap s c} := by
    intro s
    by_cases hs : STBudgetInvariant D I w policy cap s
    · rcases st_budget_stop_or_step D I w policy cap hX hc hf s hs with ⟨out,ho⟩ | ⟨t,ht⟩
      · exact ⟨⟨.inl out,fun _ => ho⟩⟩
      · exact ⟨⟨.inr t,fun _ => ht⟩⟩
    · exact ⟨⟨.inl none,fun h => (hs h).elim⟩⟩
  exact ⟨fun s => Classical.choice (hex s)⟩

inductive STBudgetDriverState (I : Finset (Fin N))
  | active (state : STBudgetState I)
  | stopped (state : STBudgetState I) (out : Option (RealVector N))

def stBudgetRun (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ)
    (choose : STBudgetSelector D I w policy cap) (initial : STBudgetState I) :
    ℕ → STBudgetDriverState I
  | 0 => .active initial
  | k+1 => match stBudgetRun D I w policy cap choose initial k with
    | .stopped s out => .stopped s out
    | .active s => match (choose s).val with
      | .inl out => .stopped s out
      | .inr t => .active t

theorem st_budget_run_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (choose : STBudgetSelector D I w policy cap) (initial : STBudgetState I)
    (hi : STBudgetInvariant D I w policy cap initial) (k : ℕ) :
    match stBudgetRun D I w policy cap choose initial k with
    | .active s => STBudgetMicroTrace D I w policy cap k initial s ∧
        STBudgetInvariant D I w policy cap s
    | .stopped s out => ∃ j<k, STBudgetMicroTrace D I w policy cap j initial s ∧
        STBudgetInvariant D I w policy cap s ∧ STBudgetStop s out := by
  induction k with
  | zero => exact ⟨.nil initial,hi⟩
  | succ k ih =>
    simp only [stBudgetRun]
    cases hh : stBudgetRun D I w policy cap choose initial k with
    | active s =>
      rw [hh] at ih
      have hlegal := (choose s).property ih.2
      cases hc : (choose s).val with
      | inl out =>
        simp only [hc,STBudgetDecisionLegal] at hlegal ⊢
        exact ⟨k,by omega,ih.1,ih.2,hlegal⟩
      | inr t =>
        simp only [hc,STBudgetDecisionLegal] at hlegal ⊢
        exact ⟨st_budget_micro_append_step D w policy cap ih.1 hlegal,
          st_budget_step_invariant D w policy cap hconvf hdf hconv hdiff ih.2 hlegal⟩
    | stopped s out =>
      rw [hh] at ih
      obtain ⟨j,hj,htrace,hs,hstop⟩ := ih
      exact ⟨j,by omega,htrace,hs,hstop⟩

theorem st_budget_every_selector_finite_return (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I)
    (choose : STBudgetSelector D I w policy cap) (initial : STBudgetState I)
    (hi : STBudgetInvariant D I w policy cap initial) :
    ∃ s out, stBudgetRun D I w policy cap choose initial (stBudgetPhasePotential P K cap initial+1) =
      .stopped s out := by
  have hh := st_budget_run_invariant D w policy cap hconvf hdf hconv hdiff choose initial hi
    (stBudgetPhasePotential P K cap initial+1)
  cases he : stBudgetRun D I w policy cap choose initial (stBudgetPhasePotential P K cap initial+1) with
  | active s =>
    rw [he] at hh
    have hb := st_budget_micro_potential_bound D w policy cap P K hK hw hpolicy
      hconvf hdf hconv hdiff hCQ hi hh.1
    omega
  | stopped s out => exact ⟨s,out,rfl⟩

theorem st_budget_every_initialized_selector_returns (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I)
    (choose : STBudgetSelector D I w policy cap) {initial : STBudgetState I}
    (hinit : STBudgetInitialize D I w cap (some initial)) :
    ∃ s out k, k ≤ 2*((cap+1)*((bbRootNode (D.model P K)).weight+(stSourceBox P K).card))+1 ∧
      STBudgetMicroTrace D I w policy cap k initial s ∧ STBudgetStop s out ∧
      STSourceReturnCertificate D I policy out ∧
      stBudgetRun D I w policy cap choose initial (stBudgetPhasePotential P K cap initial+1) =
        .stopped s out := by
  obtain ⟨hi,hr⟩ := st_budget_initialization_invariant D w policy cap hinit
  obtain ⟨s,out,he⟩ := st_budget_every_selector_finite_return D w policy cap P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ choose initial hi
  have hh := st_budget_run_invariant D w policy cap hconvf hdf hconv hdiff choose initial hi
    (stBudgetPhasePotential P K cap initial+1)
  rw [he] at hh
  obtain ⟨k,hk,ht,hs,hstop⟩ := hh
  have hb := st_budget_micro_potential_bound D w policy cap P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ hi ht
  have hib : stBudgetPotential P K cap initial ≤
      (cap+1)*((bbRootNode (D.model P K)).weight+(stSourceBox P K).card) := by
    cases hinit with
    | seeded a b ha hi hb hy => exact st_budget_initial_potential_bound D P K cap b
  simp only [stBudgetPhasePotential,hr,Option.isNone_none,Bool.true_eq,if_true] at hb
  exact ⟨s,out,k,by omega,ht,hstop,st_budget_stop_sound D w policy cap hs hstop,he⟩

theorem st_budget_initialized_micro_bound (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ) (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {initial t : STBudgetState I} {j : ℕ}
    (hinit : STBudgetInitialize D I w cap (some initial))
    (ht : STBudgetMicroTrace D I w policy cap j initial t) :
    j ≤ 2*((cap+1)*((bbRootNode (D.model P K)).weight + (stSourceBox P K).card))+1 := by
  obtain ⟨hi,hr⟩ := st_budget_initialization_invariant D w policy cap hinit
  have hb := st_budget_micro_potential_bound D w policy cap P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ hi ht
  have hib : stBudgetPotential P K cap initial ≤
      (cap+1)*((bbRootNode (D.model P K)).weight + (stSourceBox P K).card) := by
    cases hinit with
    | seeded a b ha hi hb hy => exact st_budget_initial_potential_bound D P K cap b
  simp only [stBudgetPhasePotential,hr,Option.isNone_none,Bool.true_eq,if_true] at hb
  omega

theorem st_budget_source_no_infinite_raw_execution (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ)
    (hX : Bornology.IsBounded D.polyhedron) (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) (run : ℕ → STBudgetState I)
    (hinit : STBudgetInitialize D I w cap (some (run 0))) :
    ¬ ∀ k, STBudgetStep D I w policy cap (run k) (run (k+1)) := by
  intro hrun
  let P := bbCanonicalPartition I
  obtain ⟨K,hK⟩ := D.exists_enclosing_bound hX
  have traces : ∀ start count, STBudgetMicroTrace D I w policy cap count
      (run start) (run (start+count)) := by
    intro start count
    induction count generalizing start with
    | zero => simpa using STBudgetMicroTrace.nil (D := D) (I := I) (w := w) (policy := policy) (run start)
    | succ count ih =>
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        STBudgetMicroTrace.cons (hrun start) (ih (start+1))
  let bound := 2*((cap+1)*((bbRootNode (D.model P K)).weight + (stSourceBox P K).card))+1
  have ht : STBudgetMicroTrace D I w policy cap (bound+1) (run 0) (run (bound+1)) := by
    simpa using traces 0 (bound+1)
  have hb := st_budget_initialized_micro_bound D w policy cap P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ hinit ht
  change bound+1 ≤ bound at hb
  omega

/-- Source-only existence and every-selector endpoint. C2 and convexity concern
actual D.f/D.c; the proof-only partition/enclosure are derived, not requested
from a source caller. Empty initialization is an exact global certificate. -/
theorem st_budget_source_every_selector_returns (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (policy : STSourcePolicy) (cap : ℕ)
    (hX : Bornology.IsBounded D.polyhedron) (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hf2 : ContDiff ℝ 2 D.f) (hc2 : ContDiff ℝ 2 D.c)
    (hconvf : ConvexOn ℝ Set.univ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) :
    (∃ init, STBudgetInitialize D I w cap init) ∧ Nonempty (STBudgetSelector D I w policy cap) ∧
    ∀ choose : STBudgetSelector D I w policy cap, ∀ init,
      STBudgetInitialize D I w cap init →
      match init with
      | none => D.feasible I = ∅
      | some initial => ∃ s out k, STBudgetMicroTrace D I w policy cap k initial s ∧
          STBudgetStop s out ∧ STSourceReturnCertificate D I policy out ∧
          ∃ steps, stBudgetRun D I w policy cap choose initial steps = .stopped s out := by
  have hdf := hf2.differentiable (by norm_num)
  have hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j) :=
    fun j => ((contDiff_apply ℝ (fun _ => ℝ) j).comp hc2).differentiable (by norm_num)
  refine ⟨st_budget_initialize_exists D I w cap hX hc2.continuous hf2.continuous,
    st_budget_selector_exists D I w policy cap hX hc2.continuous hf2.continuous,?_⟩
  intro choose init hi
  cases init with
  | none =>
    exact st_cutoff_empty_initialization_sound D I w
      (st_budget_initialization_erasure D I w cap hi)
  | some initial =>
    let P := bbCanonicalPartition I
    obtain ⟨K,hK⟩ := D.exists_enclosing_bound hX
    obtain ⟨s,out,k,hk,ht,hs,hc,hr⟩ := st_budget_every_initialized_selector_returns
      D w policy cap P K hK hw hpolicy hconvf hdf hconv hdiff hCQ choose hi
    exact ⟨s,out,k,ht,hs,hc,_,hr⟩

/-- With zero allowance, every actual resolution erases to a core resolution. -/
theorem st_budget_zero_resolve_erasure (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy 0 s) (h : STBudgetResolve D I w policy 0 s t) :
    STSourceResolve D I w policy (stBudgetErase s) (stBudgetErase t) := by
  cases h with
  | empty he => exact .empty he
  | callback hq hi hb hy => exact .callback hq hi hb hy
  | branch i hq hf => exact .branch i hq hf
  | @cut seeds H inc live B q i hq hf ha =>
    have hb := hs.allowance B (by simp [stBudgetFrontier])
    omega

theorem st_budget_zero_step_erasure (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {s t : STBudgetState I}
    (hs : STBudgetInvariant D I w policy 0 s) (h : STBudgetStep D I w policy 0 s t) :
    STSourceStep D I w policy (stBudgetErase s) (stBudgetErase t) := by
  cases h with
  | select h => exact .select (st_budget_select_erasure h)
  | resolve h => exact .resolve (st_budget_zero_resolve_erasure D w policy hs h)

theorem st_budget_step_upper_nonincreasing (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ) {s t : STBudgetState I}
    (h : STBudgetStep D I w policy cap s t) :
    stSourceUpper D.f t.incumbent ≤ stSourceUpper D.f s.incumbent := by
  cases h with
  | select h => cases h; exact le_rfl
  | resolve h =>
    cases h with
    | empty he => exact le_rfl
    | callback hq hi hb hy =>
      exact st_source_step_upper_nonincreasing D w policy (.resolve (.callback (live := []) hq hi hb hy))
    | branch i hq hf => exact le_rfl
    | cut i hq hf ha => exact le_rfl

theorem st_budget_step_every_lp_subset (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ) {s t : STBudgetState I}
    (h : STBudgetStep D I w policy cap s t) (C : BBExtendedNode {i : Fin N // i ∈ I}) :
    stSourceLP D C (stSourceAnchors (stBudgetErase t)) policy (stSourceInc D (stBudgetErase t)) ⊆
      stSourceLP D C (stSourceAnchors (stBudgetErase s)) policy (stSourceInc D (stBudgetErase s)) := by
  cases h with
  | select h => exact st_source_step_every_lp_subset D w policy (.select (st_budget_select_erasure h)) C
  | resolve h =>
    cases h with
    | empty he => exact Set.Subset.rfl
    | callback hq hi hb hy =>
      exact st_source_step_every_lp_subset D w policy (.resolve (.callback hq hi hb hy)) C
    | branch i hq hf => exact Set.Subset.rfl
    | @cut seeds H inc live B q i hq hf ha =>
      intro z hz
      have hm := (st_source_lp_mem_iff D C _ policy _ z).mp hz
      apply (st_source_lp_mem_iff D C _ policy _ z).mpr
      have hanchors : ∀ a ∈ seeds ++ H.map STSourceBatch.anchor,
          a ∈ (seeds ++ [q.1]) ++ H.map STSourceBatch.anchor := by
        intro a ha
        simp only [List.mem_append,List.mem_singleton] at ha ⊢
        tauto
      exact ⟨hm.1,hm.2.1,fun a ha => hm.2.2.1 a (hanchors a ha),
        fun a ha => hm.2.2.2.1 a (hanchors a ha),hm.2.2.2.2⟩


theorem st_budget_trace_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {k : ℕ} {s t : STBudgetState I} (hs : STBudgetInvariant D I w policy cap s)
    (h : STBudgetTrace D I w policy cap k s t) : STBudgetInvariant D I w policy cap t := by
  induction h with
  | nil => exact hs
  | cons step tail ih =>
    exact ih (st_budget_process_invariant D w policy cap hconvf hdf hconv hdiff hs step)


theorem st_budget_micro_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (cap : ℕ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {k : ℕ} {s t : STBudgetState I} (hs : STBudgetInvariant D I w policy cap s)
    (h : STBudgetMicroTrace D I w policy cap k s t) : STBudgetInvariant D I w policy cap t := by
  induction h with
  | nil => exact hs
  | cons step tail ih =>
    exact ih (st_budget_step_invariant D w policy cap hconvf hdf hconv hdiff hs step)

end Chapter02

#print axioms Chapter02.st_budget_initial_erasure
#print axioms Chapter02.st_budget_initial_invariant
#print axioms Chapter02.st_budget_select_erasure
#print axioms Chapter02.st_budget_noncut_erasure
#print axioms Chapter02.st_budget_select_invariant
#print axioms Chapter02.st_budget_resolve_invariant
#print axioms Chapter02.st_budget_step_invariant
#print axioms Chapter02.st_budget_process_invariant
#print axioms Chapter02.st_budget_node_weight_pos
#print axioms Chapter02.st_budget_node_weight_full
#print axioms Chapter02.st_budget_select_potential
#print axioms Chapter02.st_budget_select_phase_drop
#print axioms Chapter02.st_budget_resolve_ready
#print axioms Chapter02.st_budget_resolve_working
#print axioms Chapter02.st_budget_process_ready
#print axioms Chapter02.st_budget_resolve_potential_drop
#print axioms Chapter02.st_budget_resolve_phase_drop
#print axioms Chapter02.st_budget_step_phase_drop
#print axioms Chapter02.st_budget_process_potential_drop
#print axioms Chapter02.st_budget_initialization_erasure
#print axioms Chapter02.st_budget_initialize_exists
#print axioms Chapter02.st_budget_initialization_invariant
#print axioms Chapter02.st_budget_initial_potential_bound
#print axioms Chapter02.st_budget_stop_erasure
#print axioms Chapter02.st_budget_stop_sound
#print axioms Chapter02.st_budget_resolve_exists
#print axioms Chapter02.st_budget_stop_or_step
#print axioms Chapter02.st_budget_trace_micro
#print axioms Chapter02.st_budget_micro_append_step
#print axioms Chapter02.st_budget_trace_potential_bound
#print axioms Chapter02.st_budget_micro_potential_bound
#print axioms Chapter02.st_budget_selector_exists
#print axioms Chapter02.st_budget_run_invariant
#print axioms Chapter02.st_budget_every_selector_finite_return
#print axioms Chapter02.st_budget_every_initialized_selector_returns
#print axioms Chapter02.st_budget_initialized_micro_bound
#print axioms Chapter02.st_budget_source_no_infinite_raw_execution
#print axioms Chapter02.st_budget_source_every_selector_returns
#print axioms Chapter02.st_budget_zero_resolve_erasure
#print axioms Chapter02.st_budget_zero_step_erasure
#print axioms Chapter02.st_budget_step_upper_nonincreasing
#print axioms Chapter02.st_budget_step_every_lp_subset
#print axioms Chapter02.st_budget_trace_invariant
#print axioms Chapter02.st_budget_micro_invariant
