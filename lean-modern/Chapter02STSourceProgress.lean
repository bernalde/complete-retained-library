module

public import Chapter02STSourceState
public import Chapter02OAState

@[expose] public section

/-! Derived finite progress for the original-coordinate cutoff repair. Integer
keys are computed from actual anchors; neither freshness nor a decreasing rank
is a field of the raw source process. Clamping is a proof-only finite enclosure
for arbitrary coordinate partitions, preserving empty children. -/
noncomputable section
namespace Chapter02
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def stSourceKey (P : BBPartition I n m) (a : RealVector N) : IntVector m :=
  fun j => Int.floor ((P.split a).2 j)

theorem st_source_key_cast (P : BBPartition I n m) (a : RealVector N)
    (ha : STSourceIntegral I a) : oaIntCast (stSourceKey P a) = (P.split a).2 := by
  obtain ⟨y,hy⟩ := (P.integral_iff a).mp ha
  funext j
  simp only [stSourceKey,oaIntCast,hy,Int.floor_intCast]

theorem st_source_key_eq_iff (P : BBPartition I n m) (a b : RealVector N)
    (ha : STSourceIntegral I a) (hb : STSourceIntegral I b) :
    stSourceKey P a = stSourceKey P b ↔
      ∀ i : {i : Fin N // i ∈ I}, a i = b i := by
  rw [st_source_same_integer_iff P b a]
  constructor
  · intro h
    rw [← st_source_key_cast P a ha,← st_source_key_cast P b hb,h]
  · intro h
    funext j
    simp only [stSourceKey,h]

def stSourceBox (_P : BBPartition I n m) (K : ℝ) : Finset (IntVector m) :=
  (integerBox_finite (fun _ => -K) (fun _ => K)).toFinset

theorem st_source_key_mem_box (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) {a : RealVector N}
    (ha : a ∈ D.polyhedron) (hi : STSourceIntegral I a) :
    stSourceKey P a ∈ stSourceBox P K := by
  change stSourceKey P a ∈ (integerBox_finite (fun _ => -K) (fun _ => K)).toFinset
  rw [Set.Finite.mem_toFinset]
  intro j
  have hh := congrFun (st_source_key_cast P a hi) j
  change ((stSourceKey P a j : ℤ) : ℝ) = a (P.integerEquiv.symm j) at hh
  rw [hh]
  exact abs_le.mp (hK.2 a ha (P.integerEquiv.symm j))

theorem st_source_projection_clamped (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    {q : RealVector N} (hq : q ∈ stSourceProjection D B H) :
    P.split q ∈ (B.clamp P.integerEquiv K).box := by
  exact (B.clamp_holds_iff P.integerEquiv K (fun i => q i)).mpr
    ⟨hq.2.1,fun i => abs_le.mp (hK.2 q hq.1 i)⟩

theorem st_source_children_weight_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    {q : RealVector N} (hq : q ∈ stSourceProjection D B H)
    (i : {i : Fin N // i ∈ I}) (hi : BBFractional (q i)) :
    ((B.left i (q i)).clamp P.integerEquiv K).weight +
      ((B.right i (q i)).clamp P.integerEquiv K).weight + 1 ≤
      (B.clamp P.integerEquiv K).weight := by
  have hk := abs_le.mp (hK.2 q hq.1 i)
  rw [B.clamp_left P.integerEquiv K i (q i) hk.2,
    B.clamp_right P.integerEquiv K i (q i) hk.1]
  have hh := bb_children_weight_drop (B.clamp P.integerEquiv K)
    (P.integerEquiv i) (P.split q) (st_source_projection_clamped D P K hK B H hq)
    (by simpa only [BBPartition.split,Equiv.symm_apply_apply] using hi)
  simpa only [BBPartition.split,Equiv.symm_apply_apply] using hh

def stSourceSeen (P : BBPartition I n m) (H : List (STSourceBatch N)) :
    Finset (IntVector m) := by
  classical
  exact (H.map (fun b => stSourceKey P b.anchor)).toFinset

def stSourceRemaining (P : BBPartition I n m) (K : ℝ)
    (H : List (STSourceBatch N)) : ℕ := by
  classical
  exact (stSourceBox P K \ stSourceSeen P H).card

theorem st_source_seen_append (P : BBPartition I n m)
    (H : List (STSourceBatch N)) (b : STSourceBatch N) :
    stSourceSeen P (H ++ [b]) = insert (stSourceKey P b.anchor) (stSourceSeen P H) := by
  classical
  ext y
  simp [stSourceSeen,or_comm]

theorem st_source_remaining_le (P : BBPartition I n m) (K : ℝ)
    (H : List (STSourceBatch N)) : stSourceRemaining P K H ≤ (stSourceBox P K).card :=
  Finset.card_le_card Finset.sdiff_subset

theorem st_source_remaining_append_exact (P : BBPartition I n m) (K : ℝ)
    (H : List (STSourceBatch N)) (b : STSourceBatch N)
    (hb : stSourceKey P b.anchor ∈ stSourceBox P K)
    (hn : stSourceKey P b.anchor ∉ stSourceSeen P H) :
    stSourceRemaining P K (H ++ [b]) + 1 = stSourceRemaining P K H := by
  classical
  have he : stSourceBox P K \ stSourceSeen P (H ++ [b]) =
      (stSourceBox P K \ stSourceSeen P H).erase (stSourceKey P b.anchor) := by
    rw [st_source_seen_append]
    ext y
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase,not_or]
    tauto
  unfold stSourceRemaining
  rw [he]
  exact Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨hb,hn⟩)

def stSourceTreeWeight (P : BBPartition I n m) (K : ℝ) (s : STSourceState I) : ℕ :=
  ((stSourceFrontier s).map (fun B => (B.clamp P.integerEquiv K).weight)).sum

def stSourcePotential (P : BBPartition I n m) (K : ℝ) (s : STSourceState I) : ℕ :=
  stSourceTreeWeight P K s + stSourceRemaining P K s.history

def stSourcePhasePotential (P : BBPartition I n m) (K : ℝ) (s : STSourceState I) : ℕ :=
  2 * stSourcePotential P K s + if s.working.isNone then 1 else 0

theorem st_source_select_potential (P : BBPartition I n m) (K : ℝ)
    {s t : STSourceState I} (h : STSourceSelect s t) :
    stSourcePotential P K t = stSourcePotential P K s := by
  cases h
  simp [stSourcePotential,stSourceTreeWeight,stSourceFrontier,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem st_source_select_phase_drop (P : BBPartition I n m) (K : ℝ)
    {s t : STSourceState I} (h : STSourceSelect s t) :
    stSourcePhasePotential P K t + 1 = stSourcePhasePotential P K s := by
  have hp := st_source_select_potential P K h
  cases h
  simpa [stSourcePhasePotential] using hp

theorem st_source_callback_unseen (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (w : Fin l → ℝ) (hw : ∀ j, 0 < w j)
    (policy : STSourcePolicy)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s : STSourceState I}
    (hs : STSourceInvariant D I w policy s)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) {q : RealVector N × ℝ}
    (hq : q ∈ stSourceLP D B (stSourceAnchors s) policy (stSourceInc D s))
    (b : STSourceBatch N) (hb : stSourceBatchValid D I w b)
    (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = q.1 i) :
    stSourceKey P b.anchor ∉ stSourceSeen P s.history := by
  classical
  intro hn
  obtain ⟨c,hc,hkey⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
  have hcv := hs.valid c hc
  have heq := (st_source_key_eq_iff P c.anchor b.anchor hcv.1 hb.1).mp hkey
  have hsame : ∀ i : {i : Fin N // i ∈ I}, q.1 i = c.anchor i :=
    fun i => (hy i).symm.trans (heq i).symm
  have hm := (st_source_lp_mem_iff D B (stSourceAnchors s) policy (stSourceInc D s) q).mp hq
  have hca : c.anchor ∈ stSourceAnchors s := by
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨c,hc,rfl⟩))
  obtain ⟨hr,hle⟩ := st_source_batch_support D P K w c hcv hw hconvf hdf hconv hdiff
    hCQ ⟨hm.1,hsame⟩ (hm.2.2.1 c.anchor hca) (hm.2.2.2.1 c.anchor hca)
  obtain ⟨u,hu,hub⟩ := hs.best c hc hr
  have hcut : policy.Admits (some (D.f u)) q.2 := by
    simpa only [stSourceInc,hu,Option.map_some] using hm.2.2.2.2
  exact (not_lt_of_ge (hub.trans hle))
    (st_source_cutoff_strict_competitive policy hpolicy hcut)

theorem st_source_resolve_ready {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s t : STSourceState I}
    (h : STSourceResolve D I w policy s t) : t.working = none := by cases h <;> rfl

theorem st_source_resolve_working {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s t : STSourceState I}
    (h : STSourceResolve D I w policy s t) : s.working.isSome = true := by cases h <;> rfl

theorem st_source_resolve_potential_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (w : Fin l → ℝ) (hw : ∀ j, 0 < w j) (policy : STSourcePolicy)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s t : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (h : STSourceResolve D I w policy s t) :
    stSourcePotential P K t + 1 ≤ stSourcePotential P K s := by
  cases h with
  | @empty seeds H inc live B he =>
    have hp := bb_weight_pos (B.clamp P.integerEquiv K)
    simp only [stSourcePotential,stSourceTreeWeight,stSourceFrontier,
      Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append,
      List.map_cons,List.sum_cons]
    omega
  | @callback seeds H inc live B q b hq hi hb hy =>
    have hn := st_source_callback_unseen D P K w hw policy hpolicy hconvf hdf hconv
      hdiff hCQ hs B hq.1 b hb hy
    have hm := st_source_key_mem_box D P K hK
      (st_source_batch_anchor_polyhedron D I w b hb) hb.1
    have hr := st_source_remaining_append_exact P K H b hm hn
    simp only [stSourcePotential,stSourceTreeWeight,stSourceFrontier,
      Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append,
      List.map_cons,List.sum_cons]
    omega
  | @branch seeds H inc live B q i hq hf =>
    have hp := st_source_children_weight_drop D P K hK B
      (seeds ++ H.map STSourceBatch.anchor) hq.1.1 i hf
    simp only [stSourcePotential,stSourceTreeWeight,stSourceFrontier,
      Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append,
      List.cons_append,List.nil_append,List.map_cons,List.sum_cons]
    omega

theorem st_source_resolve_phase_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (w : Fin l → ℝ) (hw : ∀ j, 0 < w j) (policy : STSourcePolicy)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s t : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (h : STSourceResolve D I w policy s t) :
    stSourcePhasePotential P K t + 1 ≤ stSourcePhasePotential P K s := by
  have hp := st_source_resolve_potential_drop D P K hK w hw policy hpolicy
    hconvf hdf hconv hdiff hCQ hs h
  have ht := st_source_resolve_ready h
  have hw := st_source_resolve_working h
  have hh : s.working.isNone = false := by cases he : s.working <;> simp_all
  simp only [stSourcePhasePotential,ht,Option.isNone_none,Bool.true_eq,if_true,
    hh,Bool.false_eq_true,if_false]
  omega

theorem st_source_step_phase_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (w : Fin l → ℝ) (hw : ∀ j, 0 < w j) (policy : STSourcePolicy)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s t : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (h : STSourceStep D I w policy s t) :
    stSourcePhasePotential P K t + 1 ≤ stSourcePhasePotential P K s := by
  cases h with
  | select h => exact (st_source_select_phase_drop P K h).le
  | resolve h =>
    exact st_source_resolve_phase_drop D P K hK w hw policy hpolicy
      hconvf hdf hconv hdiff hCQ hs h

theorem st_source_process_ready {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s t : STSourceState I}
    (h : STSourceProcess D I w policy s t) : s.working = none ∧ t.working = none := by
  obtain ⟨v,hsel,hres⟩ := h
  constructor
  · cases hsel; rfl
  · exact st_source_resolve_ready hres

theorem st_source_process_potential_drop (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (w : Fin l → ℝ) (hw : ∀ j, 0 < w j) (policy : STSourcePolicy)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {s t : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (h : STSourceProcess D I w policy s t) :
    stSourcePotential P K t + 1 ≤ stSourcePotential P K s := by
  obtain ⟨v,hsel,hres⟩ := h
  have hp := st_source_resolve_potential_drop D P K hK w hw policy hpolicy
    hconvf hdf hconv hdiff hCQ (st_source_select_preserves_invariant D w policy hs hsel) hres
  simpa only [st_source_select_potential P K hsel] using hp

end Chapter02

#print axioms Chapter02.st_source_key_cast
#print axioms Chapter02.st_source_key_eq_iff
#print axioms Chapter02.st_source_key_mem_box
#print axioms Chapter02.st_source_projection_clamped
#print axioms Chapter02.st_source_children_weight_drop
#print axioms Chapter02.st_source_seen_append
#print axioms Chapter02.st_source_remaining_le
#print axioms Chapter02.st_source_remaining_append_exact
#print axioms Chapter02.st_source_select_potential
#print axioms Chapter02.st_source_select_phase_drop
#print axioms Chapter02.st_source_callback_unseen
#print axioms Chapter02.st_source_resolve_ready
#print axioms Chapter02.st_source_resolve_working
#print axioms Chapter02.st_source_resolve_potential_drop
#print axioms Chapter02.st_source_resolve_phase_drop
#print axioms Chapter02.st_source_step_phase_drop
#print axioms Chapter02.st_source_process_ready
#print axioms Chapter02.st_source_process_potential_drop
