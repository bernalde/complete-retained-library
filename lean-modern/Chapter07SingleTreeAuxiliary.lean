module

public import Chapter07SingleTreeSource
public import Chapter07SevenRankings
public import Mathlib.Topology.Instances.Int

@[expose] public section

/-! Global all-row capped auxiliary geometry. No selected-node branch bounds
or competitive incumbent cutoff appear in this set. A weak finite lower bound
may yield an empty level; the exact reply then skips the extra batch. -/
noncomputable section
open Set Chapter02
namespace Chapter07.SingleTreeAuxiliary
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def base (D : BBPolyData N l r) (I : Finset (Fin N))
    (H : List (RealVector N)) : Set (RealVector N) :=
  {z | z ∈ D.polyhedron ∧ STSourceIntegral I z ∧ ∀ a ∈ H, stSourceRows D a z}

def capped (D : BBPolyData N l r) (I : Finset (Fin N))
    (H : STObjectiveHistory (RealVector N)) (cap : ℝ) : Set (RealVector N × ℝ) :=
  stHeightLP D.f (base D I H.anchors) H.anchors (.closed cap)

theorem integral_closed (I : Finset (Fin N)) : IsClosed {z | STSourceIntegral I z} := by
  have he : {z | STSourceIntegral I z} =
      ⋂ i : {i : Fin N // i ∈ I}, (fun z : RealVector N => z i) ⁻¹' range ((↑) : ℤ → ℝ) := by
    ext z
    simp [STSourceIntegral]
  rw [he]
  exact isClosed_iInter fun i =>
    Int.isClosedEmbedding_coe_real.isClosed_range.preimage (continuous_apply i.val)

theorem rows_closed (D : BBPolyData N l r) (H : List (RealVector N)) :
    IsClosed {z | ∀ a ∈ H, stSourceRows D a z} := by
  have he : {z | ∀ a ∈ H, stSourceRows D a z} =
      ⋂ a : {a // a ∈ H}, ⋂ j : Fin l, {z | stTangent (fun x => D.c x j) a.val z ≤ 0} := by
    ext z
    simp [stSourceRows, stTangent]
  rw [he]
  exact isClosed_iInter fun a => isClosed_iInter fun j =>
    isClosed_le (st_tangent_continuous (fun x => D.c x j) a.val) continuous_const

theorem base_closed (D : BBPolyData N l r) (I : Finset (Fin N))
    (H : List (RealVector N)) : IsClosed (base D I H) :=
  D.polyhedron_closed.inter ((integral_closed I).inter (rows_closed D H))

theorem base_compact (D : BBPolyData N l r) (I : Finset (Fin N))
    (H : List (RealVector N)) (hX : Bornology.IsBounded D.polyhedron) :
    IsCompact (base D I H) :=
  (D.polyhedron_compact hX).of_isClosed_subset (base_closed D I H) (fun _ h => h.1)

theorem capped_iff (D : BBPolyData N l r) (I : Finset (Fin N))
    (H : STObjectiveHistory (RealVector N)) (cap : ℝ) (p : RealVector N × ℝ) :
    p ∈ capped D I H cap ↔
      p.1 ∈ base D I H.anchors ∧ stObjectiveEnvelope D.f H p.1 ≤ p.2 ∧ p.2 ≤ cap :=
  st_height_lp_envelope_iff D.f (base D I H.anchors) H (.closed cap) p

theorem capped_closed (D : BBPolyData N l r) (I : Finset (Fin N))
    (H : STObjectiveHistory (RealVector N)) (cap : ℝ) : IsClosed (capped D I H cap) := by
  have he : capped D I H cap =
      Prod.fst ⁻¹' base D I H.anchors ∩
        {p | stObjectiveEnvelope D.f H p.1 ≤ p.2} ∩ {p | p.2 ≤ cap} := by
    ext p
    rw [capped_iff]
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq]
    tauto
  rw [he]
  exact ((base_closed D I H.anchors).preimage continuous_fst).inter
    (isClosed_le ((st_objective_envelope_continuous D.f H).comp continuous_fst) continuous_snd) |>.inter
    (isClosed_le continuous_snd continuous_const)

theorem capped_compact (D : BBPolyData N l r) (I : Finset (Fin N))
    (H : STObjectiveHistory (RealVector N)) (cap : ℝ)
    (hX : Bornology.IsBounded D.polyhedron) : IsCompact (capped D I H cap) := by
  by_cases hn : (base D I H.anchors).Nonempty
  · obtain ⟨z,hz⟩ := compact_feasible_attainment (base_compact D I H.anchors hX) hn
      (st_objective_envelope_continuous D.f H).continuousOn
    apply ((base_compact D I H.anchors hX).prod
      (isCompact_Icc : IsCompact (Icc (stObjectiveEnvelope D.f H z) cap))).of_isClosed_subset
      (capped_closed D I H cap)
    intro p hp
    have h := (capped_iff D I H cap p).mp hp
    exact ⟨h.1, (hz.2 p.1 h.1).trans h.2.1, h.2.2⟩
  · have he : capped D I H cap = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hn ⟨p.1, ((capped_iff D I H cap p).mp hp).1⟩
    rw [he]
    exact isCompact_empty

theorem minimum_attained (D : BBPolyData N l r) (I : Finset (Fin N))
    (H : STObjectiveHistory (RealVector N)) (cap : ℝ)
    (hX : Bornology.IsBounded D.polyhedron) (phi : RealVector N → ℝ)
    (hc : Continuous phi) (hn : (capped D I H cap).Nonempty) :
    ∃ q, IsMinimizer (capped D I H cap) (fun p => phi p.1) q :=
  compact_feasible_attainment (capped_compact D I H cap hX) hn
    (hc.comp continuous_fst).continuousOn

/-- A skipped reply certifies actual emptiness. A processed reply retains the
actual continuous-ranking minimum and an actual same-trial-fiber batch. -/
inductive Reply (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ)
    (H : STObjectiveHistory (RealVector N)) (cap : ℝ) (phi : RealVector N → ℝ) where
  | skipped (he : ¬ (capped D I H cap).Nonempty)
  | processed (q : RealVector N × ℝ)
      (hq : IsMinimizer (capped D I H cap) (fun p => phi p.1) q)
      (b : STSourceBatch N) (hb : stSourceBatchValid D I w b)
      (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = q.1 i)

theorem reply_available (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ)
    (H : STObjectiveHistory (RealVector N)) (cap : ℝ) (phi : RealVector N → ℝ)
    (hX : Bornology.IsBounded D.polyhedron) (hf : Continuous D.f)
    (hg : Continuous D.c) (hc : Continuous phi) : Nonempty (Reply D I w H cap phi) := by
  by_cases hn : (capped D I H cap).Nonempty
  · obtain ⟨q,hq⟩ := minimum_attained D I H cap hX phi hc hn
    have hbase := ((capped_iff D I H cap q).mp hq.1).1
    obtain ⟨b,hb,hy⟩ := st_source_batch_reply D I w q.1 hbase.2.1
      ⟨q.1,hbase.1,fun _ => rfl⟩ hX hg hf
    exact ⟨.processed q hq b hb hy⟩
  · exact ⟨.skipped hn⟩

def Reply.extra {D : BBPolyData N l r} {w : Fin l → ℝ}
    {H : STObjectiveHistory (RealVector N)} {cap : ℝ} {phi : RealVector N → ℝ} :
    Reply D I w H cap phi → Option (STSourceBatch N)
  | .skipped _ => none
  | .processed _ _ b _ _ => some b

theorem Reply.extra_valid {D : BBPolyData N l r} {w : Fin l → ℝ}
    {H : STObjectiveHistory (RealVector N)} {cap : ℝ} {phi : RealVector N → ℝ}
    (reply : Reply D I w H cap phi) (b : STSourceBatch N) (he : reply.extra = some b) :
    stSourceBatchValid D I w b := by
  cases reply with
  | skipped h => simp [Reply.extra] at he
  | processed q hq b' hb hy =>
    have h : b' = b := by simpa [Reply.extra] using he
    simpa [h] using hb

theorem Reply.skipped_iff_empty {D : BBPolyData N l r} {w : Fin l → ℝ}
    {H : STObjectiveHistory (RealVector N)} {cap : ℝ} {phi : RealVector N → ℝ}
    (reply : Reply D I w H cap phi) :
    reply.extra = none ↔ ¬ (capped D I H cap).Nonempty := by
  cases reply with
  | skipped he => simp [Reply.extra,he]
  | processed q hq b hb hy =>
    have hn : (capped D I H cap).Nonempty := ⟨q,hq.1⟩
    simp [Reply.extra,hn]

def sevenRanking (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (a : Point n m) (rho : ℝ)
    (kind : SevenRankings.Kind) : RealVector N → ℝ :=
  fun z => SevenRankings.ranking d lambda mu a rho kind (P.split z)

theorem sevenRanking_continuous (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (a : Point n m) (rho : ℝ)
    (kind : SevenRankings.Kind) : Continuous (sevenRanking P d lambda mu a rho kind) :=
  (SevenRankings.ranking_continuous d lambda mu a rho kind).comp P.continuous_split

theorem sevenRanking_convex (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (a : Point n m) (rho : ℝ)
    (kind : SevenRankings.Kind) (hf : ConvexOn ℝ univ d.f)
    (hg : ∀ j, ConvexOn ℝ univ (d.g j)) (hl : ∀ j, 0 ≤ lambda j) (hm : ∀ j, 0 ≤ mu j)
    (hf2 : ContDiff ℝ 2 d.f) (hg2 : ∀ j, ContDiff ℝ 2 (d.g j)) (hrho : 0 ≤ rho) :
    ConvexOn ℝ univ (sevenRanking P d lambda mu a rho kind) := by
  have h := SevenRankings.ranking_convex d lambda mu hf hg hl hm hf2 hg2 a rho hrho kind
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  change SevenRankings.ranking d lambda mu a rho kind (P.linearEquiv (s • x + t • y)) ≤
    s • SevenRankings.ranking d lambda mu a rho kind (P.linearEquiv x) +
      t • SevenRankings.ranking d lambda mu a rho kind (P.linearEquiv y)
  rw [map_add, map_smul, map_smul]
  exact h.2 (mem_univ _) (mem_univ _) hs ht hst

end Chapter07.SingleTreeAuxiliary
#print axioms Chapter07.SingleTreeAuxiliary.capped_compact
#print axioms Chapter07.SingleTreeAuxiliary.minimum_attained
#print axioms Chapter07.SingleTreeAuxiliary.reply_available
#print axioms Chapter07.SingleTreeAuxiliary.Reply.extra_valid
#print axioms Chapter07.SingleTreeAuxiliary.Reply.skipped_iff_empty
#print axioms Chapter07.SingleTreeAuxiliary.sevenRanking_continuous
#print axioms Chapter07.SingleTreeAuxiliary.sevenRanking_convex
