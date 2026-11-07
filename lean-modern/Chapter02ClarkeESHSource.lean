module

public import Chapter02ClarkeESH
public import Chapter02ConvexSubgradientSource
public import Chapter02CPHistory

@[expose] public section

/-! Literal complete retained Clarke cuts and exact zero-level source procedure.
Classical legal choices give mathematical existence, not an implemented oracle.
The general boundary-normal existence assumption remains explicit. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Chapter02
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ClarkeESHBatch (E J : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  trial : E
  parameter : ℝ
  row : J
  normal : E →L[ℝ] ℝ

def ClarkeESHBatch.origin (a : E) (b : ClarkeESHBatch E J) : E :=
  AffineMap.lineMap a b.trial b.parameter

def clarkeESHFeasible (B : Set E) (g : J → E → ℝ) : Set E :=
  {p | p ∈ B ∧ ∀ j, g j p ≤ 0}

def ClarkeESHPolicy (g : J → E → ℝ) (a : E) (b : ClarkeESHBatch E J) : Prop :=
  b.parameter ∈ Ioo (0 : ℝ) 1 ∧ (∀ j, g j (b.origin a) ≤ 0) ∧
  g b.row (b.origin a) = 0 ∧
  b.normal ∈ clarkeSubdifferential (g b.row) (b.origin a) ∧ b.normal ≠ 0

def clarkeESHMaster (B : Set E) (a : E) (H : List (ClarkeESHBatch E J)) : Set E :=
  {p | p ∈ B ∧ ∀ b ∈ H, b.normal (p - b.origin a) ≤ 0}

def ClarkeESHStep (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E)
    (H : List (ClarkeESHBatch E J)) (b : ClarkeESHBatch E J) : Prop :=
  IsMinimizer (clarkeESHMaster B a H) f b.trial ∧
    (∃ j, 0 < g j b.trial) ∧ ClarkeESHPolicy g a b

def ClarkeESHStop (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E)
    (H : List (ClarkeESHBatch E J)) : Option E → Prop
  | none => clarkeESHMaster B a H = ∅
  | some q => IsMinimizer (clarkeESHMaster B a H) f q ∧ ∀ j, g j q ≤ 0

theorem clarke_esh_master_compact {B : Set E} (hB : IsCompact B)
    (a : E) (H : List (ClarkeESHBatch E J)) : IsCompact (clarkeESHMaster B a H) := by
  have hc : IsClosed {p | ∀ b ∈ H, b.normal (p - b.origin a) ≤ 0} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro b
    apply isClosed_iInter
    intro _
    exact isClosed_le (b.normal.continuous.comp (continuous_id.sub continuous_const)) continuous_const
  exact hB.inter_right hc

theorem clarke_esh_master_antitone (B : Set E) (a : E)
    {H K : List (ClarkeESHBatch E J)} (h : H ⊆ K) :
    clarkeESHMaster B a K ⊆ clarkeESHMaster B a H :=
  fun _ hp => ⟨hp.1, fun b hb => hp.2 b (h hb)⟩

theorem clarke_esh_master_contains {B : Set E} {g : J → E → ℝ} {a : E}
    (hweak : ∀ j, ClarkeQuasiconvex (g j)) {H : List (ClarkeESHBatch E J)}
    (hH : ∀ b ∈ H, ClarkeESHPolicy g a b) :
    clarkeESHFeasible B g ⊆ clarkeESHMaster B a H := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro b hb
  have hv := hH b hb
  exact clarke_normal_le_zero (hweak b.row) hv.2.2.2.1 (by rw [hv.2.2.1]; exact hp.2 b.row)

/-- Literal boundary hypotheses are asserted only at feasible zero-level roots. -/
def ClarkeESHNormals (L : Set E) (g : J → E → ℝ) : Prop :=
  ∀ z ∈ L, (∀ j, g j z ≤ 0) → ∀ j, g j z = 0 →
    (clarkeSubdifferential (g j) z).Nonempty ∧ 0 ∉ clarkeSubdifferential (g j) z

theorem clarke_esh_policy_exists [Fintype J] [Nonempty J]
    {B L : Set E} (hBL : B ⊆ L) (hL : Convex ℝ L)
    {g : J → E → ℝ} (hg : ∀ j, Continuous (g j)) {a : E}
    (haL : a ∈ L) (ha : ∀ j, g j a < 0) (hn : ClarkeESHNormals L g)
    {q : E} (hq : q ∈ B) (hbad : ∃ j, 0 < g j q) :
    ∃ b : ClarkeESHBatch E J, b.trial = q ∧ ClarkeESHPolicy g a b := by
  obtain ⟨t, ht, hf, j, hj⟩ := esh_boundary_exists hg ha hbad
  have hz := hL.lineMap_mem haL (hBL hq) ⟨ht.1.le, ht.2.le⟩
  obtain ⟨⟨D, hD⟩, hzero⟩ := hn _ hz hf j hj
  exact ⟨⟨q, t, j, D⟩, rfl, ht, hf, hj, hD, fun h => hzero (h ▸ hD)⟩

theorem clarke_esh_step_total [Fintype J] [Nonempty J]
    {B L : Set E} (hB : IsCompact B) (hBL : B ⊆ L) (hL : Convex ℝ L)
    {f : E → ℝ} (hf : Continuous f) {g : J → E → ℝ} (hg : ∀ j, Continuous (g j))
    {a : E} (haL : a ∈ L) (ha : ∀ j, g j a < 0) (hn : ClarkeESHNormals L g)
    (H : List (ClarkeESHBatch E J)) :
    (∃ out, ClarkeESHStop B f g a H out) ∨ ∃ b, ClarkeESHStep B f g a H b := by
  classical
  rcases (clarkeESHMaster B a H).eq_empty_or_nonempty with he | hne
  · exact Or.inl ⟨none, he⟩
  obtain ⟨q, hq⟩ := compact_feasible_attainment (clarke_esh_master_compact hB a H) hne hf.continuousOn
  by_cases hgood : ∀ j, g j q ≤ 0
  · exact Or.inl ⟨some q, hq, hgood⟩
  have hbad : ∃ j, 0 < g j q := by simpa only [not_forall, not_le] using hgood
  obtain ⟨b, hb, hv⟩ := clarke_esh_policy_exists hBL hL hg haL ha hn hq.1.1 hbad
  exact Or.inr ⟨b, by simpa only [hb] using hq, by simpa only [hb] using hbad, hv⟩

def ClarkeESHDecisionLegal (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E)
    (H : List (ClarkeESHBatch E J)) : Option E ⊕ ClarkeESHBatch E J → Prop
  | .inl out => ClarkeESHStop B f g a H out
  | .inr b => ClarkeESHStep B f g a H b

def ClarkeESHSelector (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E) :=
  ∀ H : List (ClarkeESHBatch E J),
    {c : Option E ⊕ ClarkeESHBatch E J // ClarkeESHDecisionLegal B f g a H c}

theorem clarke_esh_selector_exists [Fintype J] [Nonempty J]
    {B L : Set E} (hB : IsCompact B) (hBL : B ⊆ L) (hL : Convex ℝ L)
    {f : E → ℝ} (hf : Continuous f) {g : J → E → ℝ} (hg : ∀ j, Continuous (g j))
    {a : E} (haL : a ∈ L) (ha : ∀ j, g j a < 0) (hn : ClarkeESHNormals L g) :
    Nonempty (ClarkeESHSelector B f g a) := by
  have hex : ∀ H, Nonempty {c : Option E ⊕ ClarkeESHBatch E J //
      ClarkeESHDecisionLegal B f g a H c} := by
    intro H
    obtain ⟨out, hs⟩ | ⟨b, hb⟩ := clarke_esh_step_total hB hBL hL hf hg haL ha hn H
    · exact ⟨⟨.inl out, hs⟩⟩
    · exact ⟨⟨.inr b, hb⟩⟩
  exact ⟨fun H => Classical.choice (hex H)⟩

def ClarkeESHTrace (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E)
    (H : List (ClarkeESHBatch E J)) : Prop :=
  ∀ i (hi : i < H.length), ClarkeESHStep B f g a (H.take i) H[i]

theorem clarke_esh_trace_nil (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E) :
    ClarkeESHTrace B f g a [] := by intro i hi; simp at hi

theorem clarke_esh_trace_append {B : Set E} {f : E → ℝ} {g : J → E → ℝ} {a : E}
    {H : List (ClarkeESHBatch E J)} (hH : ClarkeESHTrace B f g a H)
    {b : ClarkeESHBatch E J} (hb : ClarkeESHStep B f g a H b) :
    ClarkeESHTrace B f g a (H ++ [b]) := by
  intro i hi
  by_cases hil : i < H.length
  · simpa [List.take_append_of_le_length (Nat.le_of_lt hil), List.getElem_append_left hil]
      using hH i hil
  · have heq : i = H.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hb

theorem clarke_esh_trace_policy {B : Set E} {f : E → ℝ} {g : J → E → ℝ} {a : E}
    {H : List (ClarkeESHBatch E J)} (hH : ClarkeESHTrace B f g a H) :
    ∀ b ∈ H, ClarkeESHPolicy g a b := by
  intro b hb
  obtain ⟨i, hi, hbi⟩ := List.mem_iff_getElem.mp hb
  subst b
  exact (hH i hi).2.2

theorem clarke_esh_stop_sound {B : Set E} {f : E → ℝ} {g : J → E → ℝ} {a : E}
    (hweak : ∀ j, ClarkeQuasiconvex (g j))
    (hne : (clarkeESHFeasible B g).Nonempty) {H : List (ClarkeESHBatch E J)}
    (hH : ClarkeESHTrace B f g a H) {out : Option E} (hs : ClarkeESHStop B f g a H out) :
    ∃ q, out = some q ∧ IsMinimizer (clarkeESHFeasible B g) f q := by
  have hsub := clarke_esh_master_contains (B := B) hweak (clarke_esh_trace_policy hH)
  cases out with
  | none =>
    obtain ⟨p, hp⟩ := hne
    have hm := hsub hp
    rw [show clarkeESHMaster B a H = ∅ from hs] at hm
    exact hm.elim
  | some q =>
    exact ⟨q, rfl, ⟨hs.1.1.1, hs.2⟩, fun p hp => hs.1.2 p (hsub hp)⟩

inductive ClarkeESHState (E J : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  | active (history : List (ClarkeESHBatch E J))
  | stopped (history : List (ClarkeESHBatch E J)) (out : Option E)

def ClarkeESHState.history : ClarkeESHState E J → List (ClarkeESHBatch E J)
  | .active H => H
  | .stopped H _ => H

def clarkeESHRun (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E)
    (choose : ClarkeESHSelector B f g a) : ℕ → ClarkeESHState E J
  | 0 => .active []
  | k + 1 =>
    match clarkeESHRun B f g a choose k with
    | .stopped H out => .stopped H out
    | .active H =>
      match (choose H).val with
      | .inl out => .stopped H out
      | .inr b => .active (H ++ [b])

theorem clarke_esh_run_invariant (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E)
    (choose : ClarkeESHSelector B f g a) (k : ℕ) :
    match clarkeESHRun B f g a choose k with
    | .active H => ClarkeESHTrace B f g a H ∧ H.length = k
    | .stopped H out => ClarkeESHTrace B f g a H ∧
        ClarkeESHStop B f g a H out ∧ H.length < k := by
  induction k with
  | zero => exact ⟨clarke_esh_trace_nil B f g a, rfl⟩
  | succ k ih =>
    simp only [clarkeESHRun]
    cases hr : clarkeESHRun B f g a choose k with
    | active H =>
      rw [hr] at ih
      have hl := (choose H).property
      cases hc : (choose H).val with
      | inl out =>
        simp only [hc, ClarkeESHDecisionLegal] at hl ⊢
        exact ⟨ih.1, hl, by omega⟩
      | inr b =>
        simp only [hc, ClarkeESHDecisionLegal] at hl ⊢
        exact ⟨clarke_esh_trace_append ih.1 hl, by simp [ih.2]⟩
    | stopped H out =>
      rw [hr] at ih
      exact ⟨ih.1, ih.2.1, by omega⟩

structure ClarkeESHExecution (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E) where
  history : ℕ → List (ClarkeESHBatch E J)
  batch : ℕ → ClarkeESHBatch E J
  initial : history 0 = []
  append : ∀ k, history (k + 1) = history k ++ [batch k]
  step : ∀ k, ClarkeESHStep B f g a (history k) (batch k)

def ClarkeESHExecution.trial {B : Set E} {f : E → ℝ} {g : J → E → ℝ} {a : E}
    (run : ClarkeESHExecution B f g a) (k : ℕ) : E := (run.batch k).trial

theorem clarke_esh_history_nested {H : ℕ → List (ClarkeESHBatch E J)}
    {b : ℕ → ClarkeESHBatch E J} (happend : ∀ k, H (k + 1) = H k ++ [b k])
    {i k : ℕ} (hik : i ≤ k) : H i ⊆ H k := by
  induction k with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact List.Subset.refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hik with heq | hlt
    · subst i; exact List.Subset.refl _
    · intro x hx
      rw [happend]
      exact List.mem_append_left _ (ih (by omega) hx)

theorem clarke_esh_batch_mem_later {H : ℕ → List (ClarkeESHBatch E J)}
    {b : ℕ → ClarkeESHBatch E J} (happend : ∀ k, H (k + 1) = H k ++ [b k])
    {i k : ℕ} (hik : i < k) : b i ∈ H k := by
  have hi : b i ∈ H (i + 1) := by rw [happend]; simp
  exact clarke_esh_history_nested happend (by omega) hi

theorem clarke_esh_execution_trace {B : Set E} {f : E → ℝ} {g : J → E → ℝ} {a : E}
    (run : ClarkeESHExecution B f g a) (k : ℕ) :
    ClarkeESHTrace B f g a (run.history k) := by
  induction k with
  | zero => rw [run.initial]; exact clarke_esh_trace_nil B f g a
  | succ k ih => rw [run.append]; exact clarke_esh_trace_append ih (run.step k)

/-- Geometry needs only master membership, the retained append equations and
actual normal/root policy. Exact minimization is deliberately absent. -/
theorem clarke_esh_history_separation [Fintype J] [Nonempty J]
    {B : Set E} (hB : IsCompact B) {g : J → E → ℝ}
    (hg : ∀ j, Continuous (g j)) (hweak : ∀ j, ClarkeQuasiconvex (g j))
    {a : E} (ha : ∀ j, g j a < 0)
    (H : ℕ → List (ClarkeESHBatch E J)) (b : ℕ → ClarkeESHBatch E J)
    (happend : ∀ k, H (k + 1) = H k ++ [b k])
    (hmem : ∀ k, (b k).trial ∈ clarkeESHMaster B a (H k))
    (hpolicy : ∀ k, ClarkeESHPolicy g a (b k)) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ i k, i < k → (∃ j, eps < g j (b i).trial) →
      delta ≤ dist (b i).trial (b k).trial := by
  obtain ⟨delta, hd, hs⟩ := clarke_esh_uniform_separation hB hg hweak ha heps
  refine ⟨delta, hd, ?_⟩
  intro i k hik hv
  obtain ⟨j, hj⟩ := hv
  have hp := hpolicy i
  exact hs (b i).trial (hmem i).1 ⟨j, hj.le⟩ (b i).parameter
    ⟨hp.1.1.le, hp.1.2.le⟩ hp.2.1 (b i).row hp.2.2.1
    (b i).normal hp.2.2.2.1 hp.2.2.2.2 (b k).trial
    ((hmem k).2 (b i) (clarke_esh_batch_mem_later happend hik))

theorem clarke_esh_feasible_history_limits [Fintype J] [Nonempty J]
    {B : Set E} (hB : IsCompact B) {g : J → E → ℝ}
    (hg : ∀ j, Continuous (g j)) (hweak : ∀ j, ClarkeQuasiconvex (g j))
    {a : E} (ha : ∀ j, g j a < 0)
    (H : ℕ → List (ClarkeESHBatch E J)) (b : ℕ → ClarkeESHBatch E J)
    (happend : ∀ k, H (k + 1) = H k ++ [b k])
    (hmem : ∀ k, (b k).trial ∈ clarkeESHMaster B a (H k))
    (hpolicy : ∀ k, ClarkeESHPolicy g a (b k)) :
    (∀ eps > 0, {k | ∃ j, eps < g j (b k).trial}.Finite) ∧
    ∀ p, MapClusterPt p atTop (fun k => (b k).trial) → p ∈ clarkeESHFeasible B g := by
  have hsep := fun eps heps => clarke_esh_history_separation hB hg hweak ha H b happend hmem hpolicy (eps := eps) heps
  have hsmall := cp_eventually_residual_le hB (fun k => (b k).trial) (fun k => (hmem k).1) hsep
  refine ⟨fun eps heps => cp_threshold_indices_finite hB _ (fun k => (hmem k).1) hsep heps, ?_⟩
  intro p hp
  exact cp_mapClusterPt_feasible hB.isClosed (fun k => (hmem k).1) hg hsmall hp

structure ClarkeESHLimiting (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (q : ℕ → E) : Prop where
  threshold_finite : ∀ eps > 0, {k | ∃ j, eps < g j (q k)}.Finite
  feasible_nonempty : (clarkeESHFeasible B g).Nonempty
  cluster_minimizer : ∀ p, MapClusterPt p atTop q → IsMinimizer (clarkeESHFeasible B g) f p
  objective_monotone : Monotone (f ∘ q)
  optimum_subsequence : ∃ p, IsMinimizer (clarkeESHFeasible B g) f p ∧
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (q ∘ phi) atTop (𝓝 p) ∧
      Tendsto (f ∘ q) atTop (𝓝 (f p))

theorem clarke_esh_execution_limiting [Fintype J] [Nonempty J]
    {B : Set E} (hB : IsCompact B) {f : E → ℝ} (hf : Continuous f)
    {g : J → E → ℝ} (hg : ∀ j, Continuous (g j)) (hweak : ∀ j, ClarkeQuasiconvex (g j))
    {a : E} (ha : ∀ j, g j a < 0) (run : ClarkeESHExecution B f g a) :
    ClarkeESHLimiting B f g run.trial := by
  have hq : ∀ k, run.trial k ∈ B := fun k => (run.step k).1.1.1
  have hsep := fun eps heps => clarke_esh_history_separation hB hg hweak ha
    run.history run.batch run.append (fun k => (run.step k).1.1)
    (fun k => (run.step k).2.2) (eps := eps) heps
  have hlower : ∀ k, IsLowerBound (clarkeESHFeasible B g) f (f (run.trial k)) := by
    intro k p hp
    exact (run.step k).1.2 p
      (clarke_esh_master_contains hweak (clarke_esh_trace_policy (clarke_esh_execution_trace run k)) hp)
  have hmono : Monotone (f ∘ run.trial) := by
    intro i k hik
    exact (run.step i).1.2 _ (clarke_esh_master_antitone B a
      (clarke_esh_history_nested run.append hik) (run.step k).1.1)
  obtain ⟨hfinite, hne, hc, hs⟩ := cp_compact_limiting_certificate hB hq hg hf hsep hlower hmono
  exact ⟨hfinite, hne, hc, hmono, hs⟩

def ClarkeESHFollows {B : Set E} {f : E → ℝ} {g : J → E → ℝ} {a : E}
    (run : ClarkeESHExecution B f g a) (choose : ClarkeESHSelector B f g a) : Prop :=
  (∀ k, clarkeESHRun B f g a choose k = .active (run.history k)) ∧
    ∀ k, (choose (run.history k)).val = .inr (run.batch k)

theorem clarke_esh_execution_of_never_stops
    (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E)
    (choose : ClarkeESHSelector B f g a)
    (hnever : ¬ ∃ k H out, clarkeESHRun B f g a choose k = .stopped H out) :
    ∃ run : ClarkeESHExecution B f g a, ClarkeESHFollows run choose := by
  let H (k : ℕ) := (clarkeESHRun B f g a choose k).history
  have hactive (k : ℕ) : clarkeESHRun B f g a choose k = .active (H k) := by
    cases h : clarkeESHRun B f g a choose k with
    | active t => simp [H, h, ClarkeESHState.history]
    | stopped t out => exact (hnever ⟨k, t, out, h⟩).elim
  have hnext (k : ℕ) : ∃ b, (choose (H k)).val = .inr b := by
    cases h : (choose (H k)).val with
    | inr b => exact ⟨b, rfl⟩
    | inl out =>
      have hs : clarkeESHRun B f g a choose (k + 1) = .stopped (H k) out := by
        simp only [clarkeESHRun, hactive k, h]
      exact (hnever ⟨k + 1, H k, out, hs⟩).elim
  choose b hb using hnext
  have happ (k : ℕ) : H (k + 1) = H k ++ [b k] := by
    have hr : clarkeESHRun B f g a choose (k + 1) = .active (H k ++ [b k]) := by
      simp only [clarkeESHRun, hactive k, hb k]
    exact congrArg ClarkeESHState.history hr
  have hstep (k : ℕ) : ClarkeESHStep B f g a (H k) (b k) := by
    have hl := (choose (H k)).property
    simpa only [hb k, ClarkeESHDecisionLegal] using hl
  let run : ClarkeESHExecution B f g a := {
    history := H
    batch := b
    initial := by simp [H, clarkeESHRun, ClarkeESHState.history]
    append := happ
    step := hstep }
  exact ⟨run, hactive, hb⟩

def ClarkeESHZeroDichotomy (B : Set E) (f : E → ℝ) (g : J → E → ℝ) (a : E)
    (choose : ClarkeESHSelector B f g a) : Prop :=
  (∃ k H q, clarkeESHRun B f g a choose k = .stopped H (some q) ∧
    ClarkeESHTrace B f g a H ∧ ClarkeESHStop B f g a H (some q) ∧
      IsMinimizer (clarkeESHFeasible B g) f q) ∨
  ∃ run : ClarkeESHExecution B f g a,
    ClarkeESHFollows run choose ∧ ClarkeESHLimiting B f g run.trial

theorem clarke_esh_every_selector_dichotomy [Fintype J] [Nonempty J]
    {B : Set E} (hB : IsCompact B) {f : E → ℝ} (hf : Continuous f)
    {g : J → E → ℝ} (hg : ∀ j, Continuous (g j)) (hweak : ∀ j, ClarkeQuasiconvex (g j))
    {a : E} (ha : ∀ j, g j a < 0) (hne : (clarkeESHFeasible B g).Nonempty)
    (choose : ClarkeESHSelector B f g a) : ClarkeESHZeroDichotomy B f g a choose := by
  classical
  by_cases hs : ∃ k H out, clarkeESHRun B f g a choose k = .stopped H out
  · obtain ⟨k, H, out, hr⟩ := hs
    have hi := clarke_esh_run_invariant B f g a choose k
    simp only [hr] at hi
    obtain ⟨q, hq, hm⟩ := clarke_esh_stop_sound hweak hne hi.1 hi.2.1
    subst out
    exact Or.inl ⟨k, H, q, hr, hi.1, hi.2.1, hm⟩
  · obtain ⟨run, hfollow⟩ := clarke_esh_execution_of_never_stops B f g a choose hs
    exact Or.inr ⟨run, hfollow, clarke_esh_execution_limiting hB hf hg hweak ha run⟩

section LiteralSource
variable {n m l r : ℕ}
open scoped BigOperators

/-- Eronen's unrestricted integer carrier inside the literal affine region. -/
def clarkeESHIntegerLinear (d : ModelData n m l r) : Set (Point n m) :=
  {p | p ∈ d.linearRegion ∧ ∃ y : IntVector m, p.2 = fun i => (y i : ℝ)}

def clarkeESHOriginalFeasible (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) : Set (Point n m) :=
  {p | p ∈ d.linearRegion ∧ ∃ y : IntVector m,
    p.2 = (fun i => (y i : ℝ)) ∧ ∀ j, gMixed j p.1 y ≤ 0}

def clarkeESHMixedObjective (d : ModelData n m l r) (x : RealVector n)
    (y : IntVector m) : ℝ := (∑ i, d.c1 i * x i) + ∑ i, d.c2 i * (y i : ℝ)

theorem clarke_esh_base_compact (d : ModelData n m l r)
    (hL : IsCompact d.linearRegion) : IsCompact (cpBase d) := by
  have hY : IsClosed (IntegerCylinder (n := n) d.lo d.hi) := by
    have hfin := (integerBox_finite d.lo d.hi).image
      (fun y : IntVector m => fun i => (y i : ℝ))
    have heq : IntegerCylinder (n := n) d.lo d.hi =
        Prod.snd ⁻¹' ((fun y : IntVector m => fun i => (y i : ℝ)) '' IntegerBox d.lo d.hi) := by
      ext p
      simp [IntegerCylinder, eq_comm]
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  exact hL.inter_right hY

theorem clarke_esh_source_sets (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ)
    (hExtension : ∀ j x y, d.g j (x, fun i => (y i : ℝ)) = gMixed j x y)
    (hBounds : ∀ p ∈ d.linearRegion, ∀ i, d.lo i ≤ p.2 i ∧ p.2 i ≤ d.hi i) :
    clarkeESHIntegerLinear d = cpBase d ∧
    clarkeESHOriginalFeasible d gMixed = sourceMixedFeasible d gMixed Set.univ ∧
    sourceMixedFeasible d gMixed Set.univ = d.feasibleOn Set.univ ∧
    d.feasibleOn Set.univ = clarkeESHFeasible (cpBase d) d.g := by
  have hcarrier : clarkeESHIntegerLinear d = cpBase d := by
    ext p
    constructor
    · rintro ⟨hp, y, hy⟩
      refine ⟨hp, y, ?_, hy⟩
      intro i
      simpa [hy] using hBounds p hp i
    · rintro ⟨hp, y, _, hy⟩
      exact ⟨hp, y, hy⟩
  have horiginal : clarkeESHOriginalFeasible d gMixed = sourceMixedFeasible d gMixed Set.univ := by
    ext p
    constructor
    · rintro ⟨hp, y, hy, hg⟩
      refine ⟨Set.mem_univ _, hp, y, ?_, hy, hg⟩
      intro i
      simpa [hy] using hBounds p hp i
    · rintro ⟨_, hp, y, _, hy, hg⟩
      exact ⟨hp, y, hy, hg⟩
  have hsource : sourceMixedFeasible d gMixed Set.univ = d.feasibleOn Set.univ := by
    ext p
    constructor
    · rintro ⟨hpK, hpL, y, hy, hcast, hrows⟩
      apply (source_feasible_iff d Set.univ p).mpr
      refine ⟨hpK, ?_, hpL, y, hy, hcast⟩
      intro j
      have he : d.g j p = gMixed j p.1 y := by
        simpa only [← hcast] using hExtension j p.1 y
      rw [he]
      exact hrows j
    · intro hp
      obtain ⟨hpK, hrows, hpL, y, hy, hcast⟩ := (source_feasible_iff d Set.univ p).mp hp
      refine ⟨hpK, hpL, y, hy, hcast, ?_⟩
      intro j
      have he : d.g j p = gMixed j p.1 y := by
        simpa only [← hcast] using hExtension j p.1 y
      rw [← he]
      exact hrows j
  refine ⟨hcarrier, horiginal, hsource, ?_⟩
  ext p
  simp [ModelData.feasibleOn, MixedFeasible, ModelData.nonlinearRegion, cpBase,
    clarkeESHFeasible, and_assoc, and_comm, and_left_comm]

/-- Original witnesses, affine restrictions and objective comparison use
unrestricted original integer vectors, not only the bounded encoded set. -/
def ClarkeESHOriginalOptimal (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) (q : Point n m) : Prop :=
  IsMinimizer (clarkeESHOriginalFeasible d gMixed) d.objective q ∧
  ∃ y : IntVector m, q.2 = (fun i => (y i : ℝ)) ∧ y ∈ IntegerBox d.lo d.hi ∧
    (∀ row, LinearForm (d.A row) (d.B row) q ≤ d.rhs row) ∧
    (∀ j, gMixed j q.1 y ≤ 0) ∧ d.objective q = clarkeESHMixedObjective d q.1 y ∧
    ∀ x z, (x, fun i => (z i : ℝ)) ∈ d.linearRegion → (∀ j, gMixed j x z ≤ 0) →
      clarkeESHMixedObjective d q.1 y ≤ clarkeESHMixedObjective d x z

theorem clarke_esh_original_optimal (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ)
    (hExtension : ∀ j x y, d.g j (x, fun i => (y i : ℝ)) = gMixed j x y)
    (hBounds : ∀ p ∈ d.linearRegion, ∀ i, d.lo i ≤ p.2 i ∧ p.2 i ≤ d.hi i)
    {q : Point n m} (hq : IsMinimizer (clarkeESHFeasible (cpBase d) d.g) d.objective q) :
    ClarkeESHOriginalOptimal d gMixed q := by
  obtain ⟨_, ho, hs, hb⟩ := clarke_esh_source_sets d gMixed hExtension hBounds
  have heq : clarkeESHOriginalFeasible d gMixed = clarkeESHFeasible (cpBase d) d.g :=
    ho.trans (hs.trans hb)
  have hqOrig : IsMinimizer (clarkeESHOriginalFeasible d gMixed) d.objective q := by rwa [heq]
  obtain ⟨hL, y, hy, hg⟩ := hqOrig.1
  have hvalue : d.objective q = clarkeESHMixedObjective d q.1 y := by
    simp only [ModelData.objective, LinearForm, clarkeESHMixedObjective, hy]
  refine ⟨hqOrig, y, hy, ?_, hL, hg, hvalue, ?_⟩
  · intro i
    simpa [hy] using hBounds q hL i
  · intro x z hx hz
    have h := hqOrig.2 (x, fun i => (z i : ℝ)) ⟨hx, z, rfl, hz⟩
    rw [hvalue] at h
    exact h

structure ClarkeESHOriginalLimiting (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) (q : ℕ → Point n m) : Prop where
  threshold_finite : ∀ eps > 0, {k | ∃ j, eps < d.g j (q k)}.Finite
  cluster_original_optimal : ∀ p, MapClusterPt p atTop q → ClarkeESHOriginalOptimal d gMixed p
  objective_monotone : Monotone (d.objective ∘ q)
  optimum_subsequence : ∃ p, ClarkeESHOriginalOptimal d gMixed p ∧
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (q ∘ phi) atTop (𝓝 p) ∧
      Tendsto (d.objective ∘ q) atTop (𝓝 (d.objective p))

def ClarkeESHSourceDichotomy (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) (a : Point n m)
    (choose : ClarkeESHSelector (cpBase d) d.objective d.g a) : Prop :=
  (∃ k H q, clarkeESHRun (cpBase d) d.objective d.g a choose k = .stopped H (some q) ∧
    ClarkeESHTrace (cpBase d) d.objective d.g a H ∧
    ClarkeESHStop (cpBase d) d.objective d.g a H (some q) ∧ ClarkeESHOriginalOptimal d gMixed q) ∨
  ∃ run : ClarkeESHExecution (cpBase d) d.objective d.g a,
    ClarkeESHFollows run choose ∧ ClarkeESHOriginalLimiting d gMixed run.trial

/-- One substantive source endpoint: literal source equivalence, reachable
nonempty attained complete masters, procedure existence, and every-choice
finite original optimum or same-driver optimal limiting certificate.
General actual Clarke-normal nonemptiness and the weak all-ambient law are
visible analytic prerequisites. This is an exact zero-tolerance theorem. -/
theorem source_clarke_esh_zero_procedure [Nonempty (Fin l)] (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) (a : Point n m)
    (hExtension : ∀ j x y, d.g j (x, fun i => (y i : ℝ)) = gMixed j x y)
    (hL : IsCompact d.linearRegion)
    (hBounds : ∀ p ∈ d.linearRegion, ∀ i, d.lo i ≤ p.2 i ∧ p.2 i ≤ d.hi i)
    (hweak : ∀ j, ClarkeQuasiconvex (d.g j))
    (haL : a ∈ d.linearRegion) (ha : ∀ j, d.g j a < 0)
    (hne : (d.feasibleOn Set.univ).Nonempty)
    (hn : ClarkeESHNormals d.linearRegion d.g) :
    clarkeESHIntegerLinear d = cpBase d ∧
    clarkeESHOriginalFeasible d gMixed = sourceMixedFeasible d gMixed Set.univ ∧
    sourceMixedFeasible d gMixed Set.univ = d.feasibleOn Set.univ ∧
    d.feasibleOn Set.univ = clarkeESHFeasible (cpBase d) d.g ∧
    IsCompact (cpBase d) ∧
    (∀ H, ClarkeESHTrace (cpBase d) d.objective d.g a H →
      IsCompact (clarkeESHMaster (cpBase d) a H) ∧
      (clarkeESHMaster (cpBase d) a H).Nonempty ∧
      ∃ q, IsMinimizer (clarkeESHMaster (cpBase d) a H) d.objective q) ∧
    Nonempty (ClarkeESHSelector (cpBase d) d.objective d.g a) ∧
    ∀ choose : ClarkeESHSelector (cpBase d) d.objective d.g a,
      ClarkeESHSourceDichotomy d gMixed a choose := by
  obtain ⟨hcarrier, ho, hs, hb⟩ := clarke_esh_source_sets d gMixed hExtension hBounds
  have hB := clarke_esh_base_compact d hL
  have hg : ∀ j, Continuous (d.g j) := fun j => (hweak j).1.continuous
  have hf : Continuous d.objective := linearForm_continuous d.c1 d.c2
  have hneB : (clarkeESHFeasible (cpBase d) d.g).Nonempty := by rwa [← hb]
  refine ⟨hcarrier, ho, hs, hb, hB, ?_, ?_, ?_⟩
  · intro H hH
    have hc := clarke_esh_master_compact hB a H
    have hnm : (clarkeESHMaster (cpBase d) a H).Nonempty :=
      hneB.mono (clarke_esh_master_contains hweak (clarke_esh_trace_policy hH))
    exact ⟨hc, hnm, compact_feasible_attainment hc hnm hf.continuousOn⟩
  · exact clarke_esh_selector_exists hB (fun _ hp => hp.1) (source_linearRegion_convex d)
      hf hg haL ha hn
  · intro choose
    rcases clarke_esh_every_selector_dichotomy hB hf hg hweak ha hneB choose with hstop | hinf
    · obtain ⟨k, H, q, hr, ht, hst, hmin⟩ := hstop
      exact Or.inl ⟨k, H, q, hr, ht, hst,
        clarke_esh_original_optimal d gMixed hExtension hBounds hmin⟩
    · obtain ⟨run, hfollow, hlim⟩ := hinf
      refine Or.inr ⟨run, hfollow, hlim.threshold_finite, ?_, hlim.objective_monotone, ?_⟩
      · intro p hp
        exact clarke_esh_original_optimal d gMixed hExtension hBounds (hlim.cluster_minimizer p hp)
      · obtain ⟨p, hp, phi, hphi, hpt, hft⟩ := hlim.optimum_subsequence
        exact ⟨p, clarke_esh_original_optimal d gMixed hExtension hBounds hp, phi, hphi, hpt, hft⟩

end LiteralSource
end Chapter02

#print axioms Chapter02.source_clarke_esh_zero_procedure

