module

public import Chapter07SingleTreeAugment
public import Chapter07SingleTreeSource
public import Chapter07SingleTreeAuxiliary

@[expose] public section

/-! Every-choice finite return for the explicitly repaired ordinary-first,
at-most-one-extra single-tree process. Exact source initialization and ordinary
query availability are inherited; augmented progress and runs are new. -/
noncomputable section
open Set Chapter02
namespace Chapter07.SingleTree
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def objectiveHistory (H : List (RealVector N)) (hne : H ≠ []) :
    STObjectiveHistory (RealVector N) :=
  match H with
  | [] => False.elim (hne rfl)
  | a :: tail => ⟨a, tail⟩

theorem objectiveHistory_anchors (H : List (RealVector N)) (hne : H ≠ []) :
    (objectiveHistory H hne).anchors = H := by
  cases H with
  | nil => exact (hne rfl).elim
  | cons a tail => rfl

theorem callback_anchors_nonempty {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {v u : STSourceState I} (hc : Callback D I w policy v u) :
    stSourceAnchors u ≠ [] := by
  cases hc
  simp [stSourceAnchors, List.map_append, List.append_assoc]

def callbackHistory {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {v u : STSourceState I} (hc : Callback D I w policy v u) :
    STObjectiveHistory (RealVector N) :=
  objectiveHistory (stSourceAnchors u) (callback_anchors_nonempty hc)

theorem callbackHistory_anchors {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {v u : STSourceState I} (hc : Callback D I w policy v u) :
    (callbackHistory hc).anchors = stSourceAnchors u :=
  objectiveHistory_anchors _ _

/-- The typed reply retains its actual minimizing trial or empty-set proof.
Its objective history is exactly the cumulative post-callback history. -/
theorem callback_reply_process {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s v u : STSourceState I}
    (hsel : STSourceSelect s v) (hc : Callback D I w policy v u)
    (cap : ℝ) (phi : RealVector N → ℝ)
    (reply : SingleTreeAuxiliary.Reply D I w (callbackHistory hc) cap phi) :
    Process D I w policy s (appendAux D u reply.extra) ∧
      stSourceFrontier (appendAux D u reply.extra) = stSourceFrontier u ∧
      (reply.extra = none ↔
        ¬ (SingleTreeAuxiliary.capped D I (callbackHistory hc) cap).Nonempty) := by
  have he : ExtraValid D I w reply.extra := by
    cases hx : reply.extra with
    | none => trivial
    | some b => exact reply.extra_valid b hx
  exact ⟨process_after_callback hsel hc reply.extra he,
    appendAux_frontier D u reply.extra, reply.skipped_iff_empty⟩

theorem callback_reply_available (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (hX : Bornology.IsBounded D.polyhedron)
    (hf : Continuous D.f) (hg : Continuous D.c) {s v u : STSourceState I}
    (hsel : STSourceSelect s v) (hc : Callback D I w policy v u)
    (cap : ℝ) (phi : RealVector N → ℝ) (hphi : Continuous phi) :
    ∃ reply : SingleTreeAuxiliary.Reply D I w (callbackHistory hc) cap phi,
      Process D I w policy s (appendAux D u reply.extra) ∧
      stSourceFrontier (appendAux D u reply.extra) = stSourceFrontier u ∧
      (reply.extra = none ↔
        ¬ (SingleTreeAuxiliary.capped D I (callbackHistory hc) cap).Nonempty) := by
  let reply := Classical.choice
    (SingleTreeAuxiliary.reply_available D I w (callbackHistory hc) cap phi hX hf hg hphi)
  exact ⟨reply, callback_reply_process hsel hc cap phi reply⟩

/-- Every literal ranking is available at the actual post-core incumbent and
all retained global rows. These C2/nonnegative-multiplier hypotheses also retain
the stated convex ranking interpretation; generic continuous replies above need
less. No lower-bound validity or dual-storage provenance is inferred from L. -/
theorem callback_seven_ranked_available (P : BBPartition I n m)
    (d : Chapter06.Level.Data n m l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hcompact : IsCompact d.hard) (hf2 : ContDiff ℝ 2 d.f)
    (hg2 : ∀ j, ContDiff ℝ 2 (d.g j)) (hconvf : ConvexOn ℝ univ d.f)
    (hconv : ∀ j, ConvexOn ℝ univ (d.g j))
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (hl : ∀ j, 0 ≤ lambda j) (hm : ∀ j, 0 ≤ mu j)
    (rho : ℝ) (hrho : 0 ≤ rho) (kind : SevenRankings.Kind)
    {s v u : STSourceState I} (hsel : STSourceSelect s v)
    (hc : Callback (SingleTreeSource.data P d) I w policy v u)
    (inc : RealVector N) (_hinc : u.incumbent = some inc)
    (L alpha : ℝ) (_ha : 0 < alpha) (_ha1 : alpha ≤ 1) :
    let D := SingleTreeSource.data P d
    let phi := SingleTreeAuxiliary.sevenRanking P d lambda mu (P.split inc) rho kind
    let cap := Chapter06.Level L (D.f inc) alpha
    ConvexOn ℝ univ phi ∧
      ∃ reply : SingleTreeAuxiliary.Reply D I w (callbackHistory hc) cap phi,
        Process D I w policy s (appendAux D u reply.extra) ∧
        stSourceFrontier (appendAux D u reply.extra) = stSourceFrontier u ∧
        (reply.extra = none ↔
          ¬ (SingleTreeAuxiliary.capped D I (callbackHistory hc) cap).Nonempty) := by
  have hf1 : ContDiff ℝ 1 d.f := hf2.of_le (by norm_num)
  have hg1 : ∀ j, ContDiff ℝ 1 (d.g j) := fun j => (hg2 j).of_le (by norm_num)
  exact ⟨SingleTreeAuxiliary.sevenRanking_convex P d lambda mu (P.split inc) rho kind hconvf hconv
      hl hm hf2 hg2 hrho,
    callback_reply_available (SingleTreeSource.data P d) w policy
      (SingleTreeSource.polyhedron_compact P d hcompact).isBounded
      (SingleTreeSource.objective_C1 P d hf1).continuous
      (SingleTreeSource.rows_C1 P d hg1).continuous hsel hc _ _
      (SingleTreeAuxiliary.sevenRanking_continuous P d lambda mu (P.split inc) rho kind)⟩

inductive Trace (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ)
    (policy : STSourcePolicy) : ℕ → STSourceState I → STSourceState I → Prop
  | nil (s) : Trace D I w policy 0 s s
  | cons {k s t u} (step : Process D I w policy s t) (tail : Trace D I w policy k t u) :
      Trace D I w policy (k + 1) s u

theorem trace_trans (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    {j k : ℕ} {s t u : STSourceState I} (h : Trace D I w policy j s t)
    (ht : Trace D I w policy k t u) : Trace D I w policy (j + k) s u := by
  induction h with
  | nil s => simpa using ht
  | cons step tail ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons step (ih ht)

theorem trace_append_step (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    {k : ℕ} {s t u : STSourceState I} (h : Trace D I w policy k s t)
    (step : Process D I w policy t u) : Trace D I w policy (k + 1) s u :=
  trace_trans D w policy h (.cons step (.nil u))

theorem trace_invariant (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {k : ℕ} {s t : STSourceState I} (hs : STSourceInvariant D I w policy s)
    (h : Trace D I w policy k s t) : STSourceInvariant D I w policy t := by
  induction h with
  | nil => exact hs
  | cons step tail ih => exact ih (process_invariant D w policy hconvf hdf hconv hdiff hs step)

theorem trace_stored (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    {k : ℕ} {s t : STSourceState I} (hs : Stored s) (h : Trace D I w policy k s t) : Stored t := by
  induction h with
  | nil => exact hs
  | cons step tail ih => exact ih (process_stored D w policy hs step)

theorem trace_every_lp_subset (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    {k : ℕ} {s t : STSourceState I} (h : Trace D I w policy k s t)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    stSourceLP D B (stSourceAnchors t) policy (stSourceInc D t) ⊆
      stSourceLP D B (stSourceAnchors s) policy (stSourceInc D s) := by
  induction h with
  | nil => exact Set.Subset.refl _
  | cons step tail ih => exact ih.trans (process_every_lp_subset D w policy step B)

theorem trace_potential_bound (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j)) (hCQ : STSourceFiberSlater D I)
    {k : ℕ} {s t : STSourceState I} (hs : STSourceInvariant D I w policy s)
    (h : Trace D I w policy k s t) : stSourcePotential P K t + k ≤ stSourcePotential P K s := by
  induction h with
  | nil => omega
  | cons step tail ih =>
    have hd := process_potential_drop D P K hK w hw policy hpolicy hconvf hdf hconv hdiff hCQ hs step
    have ht := ih (process_invariant D w policy hconvf hdf hconv hdiff hs step)
    omega

def DecisionLegal (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (s : STSourceState I) :
    Option (RealVector N) ⊕ STSourceState I → Prop
  | .inl out => STSourceStop s out
  | .inr t => Process D I w policy s t

def Selector (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ)
    (policy : STSourcePolicy) :=
  ∀ s : STSourceState I, {c : Option (RealVector N) ⊕ STSourceState I //
    STSourceInvariant D I w policy s → s.working = none → DecisionLegal D I w policy s c}

/-- Optional augmentation cannot deadlock a legal core action: choosing none
always gives a new legal macro-step, from actual ordinary query availability. -/
theorem selector_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) (hf : Continuous D.f) :
    Nonempty (Selector D I w policy) := by
  classical
  have hex : ∀ s : STSourceState I, Nonempty {c : Option (RealVector N) ⊕ STSourceState I //
      STSourceInvariant D I w policy s → s.working = none → DecisionLegal D I w policy s c} := by
    intro s
    by_cases hv : STSourceInvariant D I w policy s ∧ s.working = none
    · by_cases he : s.live = []
      · exact ⟨⟨.inl s.incumbent, fun _ _ => .exhausted hv.2 he⟩⟩
      · obtain ⟨t, ht⟩ := st_cutoff_process_exists D I w policy hX hc hf s hv.1 hv.2 he
        exact ⟨⟨.inr t, fun _ _ => Process.core ht⟩⟩
    · exact ⟨⟨.inl none, fun hs hr => (hv ⟨hs,hr⟩).elim⟩⟩
  exact ⟨fun s => Classical.choice (hex s)⟩

def run (D : BBPolyData N l r) (I : Finset (Fin N)) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (choose : Selector D I w policy)
    (initial : STSourceState I) : ℕ → STSourceDriverState I
  | 0 => .active initial
  | k+1 => match run D I w policy choose initial k with
    | .stopped s out => .stopped s out
    | .active s => match (choose s).val with
      | .inl out => .stopped s out
      | .inr t => .active t

/-- The stopped case records the actual k macro-steps and the first final
inspection k+1, rather than counting any later stopped-state stuttering. -/
theorem run_invariant (D : BBPolyData N l r) (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (choose : Selector D I w policy) (initial : STSourceState I)
    (hi : STSourceInvariant D I w policy initial) (hr : initial.working = none) (k : ℕ) :
    match run D I w policy choose initial k with
    | .active s => Trace D I w policy k initial s ∧
        STSourceInvariant D I w policy s ∧ s.working = none
    | .stopped s out => ∃ j<k, Trace D I w policy j initial s ∧
        STSourceInvariant D I w policy s ∧ STSourceStop s out ∧
        run D I w policy choose initial (j+1) = .stopped s out := by
  induction k with
  | zero => exact ⟨.nil initial, hi, hr⟩
  | succ k ih =>
    simp only [run]
    cases hh : run D I w policy choose initial k with
    | active s =>
      rw [hh] at ih
      have hlegal := (choose s).property ih.2.1 ih.2.2
      cases hc : (choose s).val with
      | inl out =>
        simp only [hc, DecisionLegal] at hlegal ⊢
        exact ⟨k, by omega, ih.1, ih.2.1, hlegal, by simp [run, hh, hc]⟩
      | inr t =>
        simp only [hc, DecisionLegal] at hlegal ⊢
        exact ⟨trace_append_step D w policy ih.1 hlegal,
          process_invariant D w policy hconvf hdf hconv hdiff ih.2.1 hlegal,
          (process_ready hlegal).2⟩
    | stopped s out =>
      rw [hh] at ih
      obtain ⟨j, hj, ht, hs, hstop, he⟩ := ih
      exact ⟨j, by omega, ht, hs, hstop, he⟩

theorem every_selector_finite_return (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j)) (hCQ : STSourceFiberSlater D I)
    (choose : Selector D I w policy) (initial : STSourceState I)
    (hi : STSourceInvariant D I w policy initial) (hr : initial.working = none) :
    ∃ s out, run D I w policy choose initial (stSourcePotential P K initial+1) = .stopped s out := by
  have h := run_invariant D w policy hconvf hdf hconv hdiff choose initial hi hr
    (stSourcePotential P K initial+1)
  cases he : run D I w policy choose initial (stSourcePotential P K initial+1) with
  | active s =>
    rw [he] at h
    have hb := trace_potential_bound D w policy P K hK hw hpolicy hconvf hdf hconv hdiff hCQ hi h.1
    omega
  | stopped s out => exact ⟨s,out,rfl⟩

/-- Ready-state endpoint for every legal augmented selector, with the actual
first closing inspection and the retained ordinary source return certificate. -/
theorem every_ready_selector_returns (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j)) (hCQ : STSourceFiberSlater D I)
    (choose : Selector D I w policy) (initial : STSourceState I)
    (hi : STSourceInvariant D I w policy initial) (hr : initial.working = none) :
    ∃ s out k, k ≤ stSourcePotential P K initial ∧ Trace D I w policy k initial s ∧
      STSourceInvariant D I w policy s ∧ STSourceStop s out ∧
      STSourceReturnCertificate D I policy out ∧
      (Stored initial → Stored s) ∧
      run D I w policy choose initial (k+1) = .stopped s out ∧
      run D I w policy choose initial (stSourcePotential P K initial+1) = .stopped s out := by
  obtain ⟨s,out,he⟩ := every_selector_finite_return D w policy P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ choose initial hi hr
  have h := run_invariant D w policy hconvf hdf hconv hdiff choose initial hi hr
    (stSourcePotential P K initial+1)
  rw [he] at h
  obtain ⟨k,hk,ht,hs,hstop,hfirst⟩ := h
  exact ⟨s,out,k,by omega,ht,hs,hstop,st_source_stop_sound D w policy hs hstop,
    fun hstored => trace_stored D w policy hstored ht,hfirst,he⟩

theorem initial_stored (D : BBPolyData N l r) (b : STSourceBatch N) :
    Stored (stSourceInitial D I b) := by
  intro u hu
  cases hr : b.restoration with
  | true => simp [stSourceInitial, stSourceBatchInc, hr] at hu
  | false =>
    have he : b.anchor = u := by simpa [stSourceInitial, stSourceBatchInc, hr, stSourceBest] using hu
    exact ⟨b, by simp [stSourceInitial], hr, he.symm⟩

theorem initialization_stored (D : BBPolyData N l r) (w : Fin l → ℝ)
    {initial : STSourceState I} (hinit : STSourceInitialize D I w (some initial)) : Stored initial := by
  cases hinit with
  | seeded a b ha hi hb hy => exact initial_stored D b

/-- Initialization is the separately named accepted integer-fiber initializer,
not the printed continuous-relaxation initialization. A restoration batch is
allowed, and no feasible incumbent is assumed. -/
theorem every_initialized_selector_returns (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j)) (hCQ : STSourceFiberSlater D I)
    (choose : Selector D I w policy) {initial : STSourceState I}
    (hinit : STSourceInitialize D I w (some initial)) :
    ∃ s out k, k ≤ (bbRootNode (D.model P K)).weight + (stSourceBox P K).card ∧
      Trace D I w policy k initial s ∧ STSourceStop s out ∧
      STSourceReturnCertificate D I policy out ∧ Stored s ∧
      run D I w policy choose initial (k+1) = .stopped s out ∧
      run D I w policy choose initial (stSourcePotential P K initial+1) = .stopped s out := by
  obtain ⟨hi,hr⟩ := st_cutoff_initialization_invariant D I w policy hinit
  obtain ⟨s,out,k,hk,ht,hs,hstop,hcert,hstored,hfirst,he⟩ := every_ready_selector_returns
    D w policy P K hK hw hpolicy hconvf hdf hconv hdiff hCQ choose initial hi hr
  have hib : stSourcePotential P K initial ≤
      (bbRootNode (D.model P K)).weight + (stSourceBox P K).card := by
    cases hinit with
    | seeded a b ha hi hb hy => exact st_cutoff_initial_potential_bound D P K b
  exact ⟨s,out,k,hk.trans hib,ht,hstop,hcert,hstored (initialization_stored D w hinit),hfirst,he⟩

theorem strict_return_optimal (D : BBPolyData N l r) {u : RealVector N}
    (h : STSourceReturnCertificate D I .strict (some u)) : IsMinimizer (D.feasible I) D.f u :=
  ⟨h.1, fun z hz => st_source_strict_no_improvement (h.2 z hz)⟩

theorem gap_return_bound (D : BBPolyData N l r) (epsilon : ℝ) {u : RealVector N}
    (h : STSourceReturnCertificate D I (.gap epsilon) (some u)) :
    u ∈ D.feasible I ∧ ∀ z ∈ D.feasible I, D.f u < D.f z + epsilon :=
  ⟨h.1, fun z hz => st_source_gap_no_improvement (h.2 z hz)⟩

/-- General original-coordinate data endpoint, including the empty hard region
and globally infeasible integer models. Compact finite enclosure is derived. -/
theorem source_every_selector_returns (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (hX : Bornology.IsBounded D.polyhedron)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hc : Continuous D.c) (hf : Continuous D.f)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j)) (hCQ : STSourceFiberSlater D I) :
    (∃ init, STSourceInitialize D I w init) ∧ Nonempty (Selector D I w policy) ∧
    ∀ choose : Selector D I w policy, ∀ init, STSourceInitialize D I w init →
      match init with
      | none => D.feasible I = ∅
      | some initial => ∃ s out k, Trace D I w policy k initial s ∧ STSourceStop s out ∧
          STSourceReturnCertificate D I policy out ∧ Stored s ∧
          run D I w policy choose initial (k+1) = .stopped s out := by
  refine ⟨st_cutoff_initialize_exists D I w hX hc hf, selector_exists D I w policy hX hc hf, ?_⟩
  intro choose init hi
  cases init with
  | none => exact st_cutoff_empty_initialization_sound D I w hi
  | some initial =>
    let P := bbCanonicalPartition I
    obtain ⟨K, hK⟩ := D.exists_enclosing_bound hX
    obtain ⟨s,out,k,hk,ht,hstop,hcert,hstored,hfirst,he⟩ := every_initialized_selector_returns
      D w policy P K hK hw hpolicy hconvf hdf hconv hdiff hCQ choose hi
    exact ⟨s,out,k,ht,hstop,hcert,hstored,hfirst⟩

/-- Return certificate in the actual split source coordinates. -/
def SourceCertificate (d : Chapter06.Level.Data n m l r) (policy : STSourcePolicy) :
    Option (Point n m) → Prop
  | none => d.original = ∅
  | some u => u ∈ d.original ∧
      ∀ z ∈ d.original, ¬ policy.Admits (some (d.f u)) (d.f z)

theorem return_transport (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (policy : STSourcePolicy) {out : Option (RealVector N)}
    (h : STSourceReturnCertificate (SingleTreeSource.data P d) I policy out) :
    SourceCertificate d policy (out.map P.split) := by
  cases out with
  | none =>
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz' : P.join z ∈ (SingleTreeSource.data P d).feasible I :=
      (SingleTreeSource.feasible_iff P d (P.join z)).mpr (by simpa only [P.split_join] using hz)
    change (SingleTreeSource.data P d).feasible I = ∅ at h
    rw [h] at hz'
    exact hz'
  | some u =>
    refine ⟨(SingleTreeSource.feasible_iff P d u).mp h.1, ?_⟩
    intro z hz
    have hz' : P.join z ∈ (SingleTreeSource.data P d).feasible I :=
      (SingleTreeSource.feasible_iff P d (P.join z)).mpr (by simpa only [P.split_join] using hz)
    simpa only [SingleTreeSource.data, P.split_join] using h.2 (P.join z) hz'

/-- Source-facing single-tree endpoint. The actual objective and every affine
and nonlinear row are transported by an explicit complete concatenation. Hard
compactness allows the empty case; no feasible seed or hard-nonempty premise
is introduced. The initial batch route and ordinary-first schedule are repairs. -/
theorem source_data_every_selector_returns (d : Chapter06.Level.Data n m l r)
    (w : Fin l → ℝ) (policy : STSourcePolicy) (hcompact : IsCompact d.hard)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hf1 : ContDiff ℝ 1 d.f) (hg1 : ∀ j, ContDiff ℝ 1 (d.g j))
    (hconvf : ConvexOn ℝ Set.univ d.f) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hslater : ∀ y, (d.feasibleFiber y).Nonempty →
      ∃ p ∈ d.hardFiber y, ∀ j, d.g j p < 0) :
    let P := SingleTreeSource.partition n m
    let D := SingleTreeSource.data P d
    let J := SingleTreeSource.integerIndices n m
    ∃ K, D.Encloses K ∧ (∃ init, STSourceInitialize D J w init) ∧
      Nonempty (Selector D J w policy) ∧
      ∀ choose : Selector D J w policy, ∀ init, STSourceInitialize D J w init →
        match init with
        | none => d.original = ∅
        | some initial => ∃ s out k,
            k ≤ (bbRootNode (D.model P K)).weight + (stSourceBox P K).card ∧
            Trace D J w policy k initial s ∧ STSourceStop s out ∧
            SourceCertificate d policy (out.map P.split) ∧ Stored s ∧
            run D J w policy choose initial (k+1) = .stopped s out := by
  let P := SingleTreeSource.partition n m
  let D := SingleTreeSource.data P d
  let J := SingleTreeSource.integerIndices n m
  have hX : Bornology.IsBounded D.polyhedron :=
    (SingleTreeSource.polyhedron_compact P d hcompact).isBounded
  have hfD := SingleTreeSource.objective_C1 P d hf1
  have hcD := SingleTreeSource.rows_C1 P d hg1
  have hdf : Differentiable ℝ D.f := hfD.differentiable (by norm_num)
  have hdc : ∀ j, Differentiable ℝ (fun x => D.c x j) :=
    fun j => ((contDiff_apply ℝ (fun _ => ℝ) j).comp hcD).differentiable (by norm_num)
  have hcf := SingleTreeSource.objective_convex P d hconvf
  have hcc := SingleTreeSource.rows_convex P d hconv
  have hCQ := SingleTreeSource.fiber_slater P d hslater
  obtain ⟨K, hK⟩ := SingleTreeSource.enclosing_bound P d hcompact
  refine ⟨K, hK, st_cutoff_initialize_exists D J w hX hcD.continuous hfD.continuous,
    selector_exists D J w policy hX hcD.continuous hfD.continuous, ?_⟩
  intro choose init hi
  cases init with
  | none =>
    exact return_transport P d policy (out := none) (st_cutoff_empty_initialization_sound D J w hi)
  | some initial =>
    obtain ⟨s,out,k,hk,ht,hstop,hcert,hstored,hfirst,he⟩ := every_initialized_selector_returns
      D w policy P K hK hw hpolicy hcf hdf hcc hdc hCQ choose hi
    exact ⟨s,out,k,hk,ht,hstop,return_transport P d policy hcert,hstored,hfirst⟩

theorem source_strict_optimal (d : Chapter06.Level.Data n m l r) {u : Point n m}
    (h : SourceCertificate d .strict (some u)) : IsMinimizer d.original d.f u :=
  ⟨h.1, fun z hz => st_source_strict_no_improvement (h.2 z hz)⟩

theorem source_gap_bound (d : Chapter06.Level.Data n m l r) (epsilon : ℝ) {u : Point n m}
    (h : SourceCertificate d (.gap epsilon) (some u)) :
    u ∈ d.original ∧ ∀ z ∈ d.original, d.f u < d.f z + epsilon :=
  ⟨h.1, fun z hz => st_source_gap_no_improvement (h.2 z hz)⟩

#print axioms Chapter07.SingleTree.callbackHistory_anchors
#print axioms Chapter07.SingleTree.callback_reply_process
#print axioms Chapter07.SingleTree.callback_reply_available
#print axioms Chapter07.SingleTree.callback_seven_ranked_available
#print axioms Chapter07.SingleTree.return_transport
#print axioms Chapter07.SingleTree.source_data_every_selector_returns
#print axioms Chapter07.SingleTree.source_strict_optimal
#print axioms Chapter07.SingleTree.source_gap_bound
#print axioms Chapter07.SingleTree.selector_exists
#print axioms Chapter07.SingleTree.trace_potential_bound
#print axioms Chapter07.SingleTree.every_ready_selector_returns
#print axioms Chapter07.SingleTree.every_initialized_selector_returns
#print axioms Chapter07.SingleTree.source_every_selector_returns
#print axioms Chapter07.SingleTree.strict_return_optimal
#print axioms Chapter07.SingleTree.gap_return_bound
end Chapter07.SingleTree
