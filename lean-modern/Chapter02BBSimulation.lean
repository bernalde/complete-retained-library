module

public import Chapter02BBExternal
public import Chapter02BBDriver
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Both-direction simulation of the independent original-coordinate Algorithm 1
and the finite exact engine in belottiAlgorithm mode. The heap relation retains
occurrences and existentially forgets only inherited lower-bound ghost data.
Every enumeration and every valid enclosing real bound remain parameters. -/
noncomputable section
namespace Chapter02
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def BBHeapRelated (P : BBPartition I n m) (K : ℝ)
    (xs : List (BBExternalNode I)) (ys : List (BBRecord m)) : Prop :=
  List.Forall₂ (fun B b => b.node = B.clamp P.integerEquiv K) xs ys

def BBStatesRelated (P : BBPartition I n m) (K : ℝ)
    (s : BBExternalState I) (t : BBState n m) : Prop :=
  BBHeapRelated P K s.live t.live ∧ t.incumbent = s.incumbent.map P.split

theorem bb_forall2_split_left {α β : Type*} {R : α → β → Prop}
    (pre post : List α) (a : α) {bs : List β}
    (h : List.Forall₂ R (pre ++ a :: post) bs) :
    ∃ pre' b post', bs = pre' ++ b :: post' ∧
      List.Forall₂ R pre pre' ∧ R a b ∧ List.Forall₂ R post post' := by
  induction pre generalizing bs with
  | nil =>
    cases h with
    | cons hab htail => exact ⟨[], _, _, rfl, .nil, hab, htail⟩
  | cons x pre ih =>
    cases h with
    | cons hxy htail =>
      obtain ⟨pre', b, post', heq, hp, hab, hpost⟩ := ih htail
      exact ⟨_ :: pre', b, post', by simp [heq], .cons hxy hp, hab, hpost⟩

theorem bb_forall2_split_right {α β : Type*} {R : α → β → Prop}
    (pre post : List β) (b : β) {xs : List α}
    (h : List.Forall₂ R xs (pre ++ b :: post)) :
    ∃ pre' a post', xs = pre' ++ a :: post' ∧
      List.Forall₂ R pre' pre ∧ R a b ∧ List.Forall₂ R post' post := by
  obtain ⟨pre', a, post', heq, hp, hab, hpost⟩ :=
    bb_forall2_split_left pre post b h.flip
  exact ⟨pre', a, post', heq, hp.flip, hab, hpost.flip⟩

theorem bb_sim_initial (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ) :
    BBStatesRelated P K (bbExternalInitial I) (bbInitial (D.model P K) none) :=
  ⟨.cons rfl .nil, rfl⟩

theorem bb_sim_empty_live_iff (P : BBPartition I n m) (K : ℝ)
    {s : BBExternalState I} {t : BBState n m} (h : BBStatesRelated P K s t) :
    s.live = [] ↔ t.live = [] := by
  have hl := h.1.length_eq
  constructor
  · intro hs
    apply List.length_eq_zero_iff.mp
    simpa only [hs, List.length_nil] using hl.symm
  · intro ht
    apply List.length_eq_zero_iff.mp
    simpa only [ht, List.length_nil] using hl

theorem bb_sim_prunable_iff (D : BBPolyData N l r) (P : BBPartition I n m)
    (inc : Option (RealVector N)) (v : ℝ) :
    bbPrunable .belottiAlgorithm (D.objective P) (inc.map P.split) v ↔
      bbExternalUpper D.f inc < (v : WithTop ℝ) := by
  cases inc <;> simp [bbPrunable, bbExternalUpper]

theorem bb_sim_update (D : BBPolyData N l r) (P : BBPartition I n m)
    (inc : Option (RealVector N)) (z : RealVector N)
    (hk : ¬ bbExternalUpper D.f inc < (D.f z : WithTop ℝ)) :
    bbUpdate .belottiAlgorithm (D.objective P) (inc.map P.split) (P.split z) =
      some (P.split z) := by
  cases inc with
  | none => rfl
  | some w =>
    have hw : D.f z ≤ D.f w := by simpa [bbExternalUpper] using hk
    simp [bbUpdate, hw]

theorem bb_sim_minimum_join (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) {B : BBExternalNode I} {b : BBRecord m}
    (hb : b.node = B.clamp P.integerEquiv K) {q : Point n m}
    (hq : IsMinimizer (b.node.region (D.model P K)) (D.objective P) q) :
    IsMinimizer (D.relaxation B) D.f (P.join q) := by
  apply (D.minimizer_iff P K hK B (P.join q)).mpr
  simpa only [P.split_join, hb, BBNode.region] using hq

/-- Forward simulation constructs the actual inherited max bounds in both
children. No validity or progress invariant is assumed in the state relation. -/
theorem bb_simulate_process_forward (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) {s u : BBExternalState I} {t : BBState n m}
    (hstep : BBExternalProcess D I s u) (hrel : BBStatesRelated P K s t) :
    ∃ v, BBProcess (D.model P K) (D.objective P) .belottiAlgorithm t v ∧
      BBStatesRelated P K u v := by
  rcases t with ⟨live, inc'⟩
  cases hstep with
  | @empty pre post B inc he =>
    rcases hrel with ⟨hh, hi⟩
    obtain ⟨epre, b, epost, heq, hp, hb, ht⟩ := bb_forall2_split_left pre post B hh
    dsimp only at heq
    subst live
    change inc' = inc.map P.split at hi
    subst inc'
    refine ⟨⟨epre ++ epost, inc.map P.split⟩, .empty ?_, List.rel_append hp ht, rfl⟩
    simpa only [hb, BBNode.region] using (D.relaxation_empty_iff P K hK B).mp he
  | @prune pre post B inc z hz hpr =>
    rcases hrel with ⟨hh, hi⟩
    obtain ⟨epre, b, epost, heq, hp, hb, ht⟩ := bb_forall2_split_left pre post B hh
    dsimp only at heq
    subst live
    change inc' = inc.map P.split at hi
    subst inc'
    refine ⟨⟨epre ++ epost, inc.map P.split⟩, .prune (q := P.split z) ?_ ?_,
      List.rel_append hp ht, rfl⟩
    · simpa only [hb, BBNode.region] using (D.minimizer_iff P K hK B z).mp hz
    · exact (bb_sim_prunable_iff D P inc _).mpr (by simpa using hpr)
  | @integral pre post B inc z hz hk hI =>
    rcases hrel with ⟨hh, hi⟩
    obtain ⟨epre, b, epost, heq, hp, hb, ht⟩ := bb_forall2_split_left pre post B hh
    dsimp only at heq
    subst live
    change inc' = inc.map P.split at hi
    subst inc'
    have hm : IsMinimizer (b.node.region (D.model P K)) (D.objective P) (P.split z) := by
      simpa only [hb, BBNode.region] using (D.minimizer_iff P K hK B z).mp hz
    have hkeep : ¬ bbPrunable .belottiAlgorithm (D.objective P) (inc.map P.split)
        (D.objective P (P.split z)) := by
      simpa only [bb_sim_prunable_iff, BBPolyData.objective_split] using hk
    have hstep' := BBProcess.integral (pre := epre) (post := epost) hm hkeep
      ((P.integral_iff z).mp hI)
    rw [bb_sim_update D P inc z hk] at hstep'
    exact ⟨_, hstep', List.rel_append hp ht, rfl⟩
  | @branch pre post B inc z i hz hk hfrac =>
    rcases hrel with ⟨hh, hi⟩
    obtain ⟨epre, b, epost, heq, hp, hb, ht⟩ := bb_forall2_split_left pre post B hh
    dsimp only at heq
    subst live
    change inc' = inc.map P.split at hi
    subst inc'
    have hm : IsMinimizer (b.node.region (D.model P K)) (D.objective P) (P.split z) := by
      simpa only [hb, BBNode.region] using (D.minimizer_iff P K hK B z).mp hz
    have hkeep : ¬ bbPrunable .belottiAlgorithm (D.objective P) (inc.map P.split)
        (D.objective P (P.split z)) := by
      simpa only [bb_sim_prunable_iff, BBPolyData.objective_split] using hk
    have hfrac' : BBFractional ((P.split z).2 (P.integerEquiv i)) := by
      simpa [BBPartition.split] using hfrac
    refine ⟨_, .branch (pre := epre) (post := epost) (P.integerEquiv i) hm hkeep hfrac', ?_, rfl⟩
    apply List.rel_append (List.rel_append hp ?_) ht
    refine .cons ?_ (.cons ?_ .nil)
    · exact hb ▸ (D.left_commutes P K hK B z hz.1.1 i).symm
    · exact hb ▸ (D.right_commutes P K hK B z hz.1.1 i).symm

/-- Backward simulation excludes exact bad statuses by bounded-X attainment,
then transports the same selected occurrence, minimizer and fractional index. -/
theorem bb_simulate_process_backward (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron)
    {s : BBExternalState I} {t v : BBState n m}
    (hstep : BBProcess (D.model P K) (D.objective P) .belottiAlgorithm t v)
    (hrel : BBStatesRelated P K s t) :
    ∃ u, BBExternalProcess D I s u ∧ BBStatesRelated P K u v := by
  rcases s with ⟨live, inc⟩
  cases hstep with
  | @empty pre post b inc' he =>
    rcases hrel with ⟨hh, hi⟩
    obtain ⟨xpre, B, xpost, heq, hp, hb, ht⟩ := bb_forall2_split_right pre post b hh
    dsimp only at heq
    subst live
    refine ⟨⟨xpre ++ xpost, inc⟩, .empty ?_, List.rel_append hp ht, hi⟩
    apply (D.relaxation_empty_iff P K hK B).mpr
    simpa only [hb, BBNode.region] using he
  | @unbounded pre post b inc' hbad =>
    obtain ⟨xpre, B, xpost, heq, hp, hb, ht⟩ := bb_forall2_split_right pre post b hrel.1
    exfalso
    apply D.clamped_not_unbounded P K hK B hX hc hf
    simpa only [hb, BBNode.region] using hbad
  | @unattained pre post b inc' hn hbelow hbad =>
    obtain ⟨xpre, B, xpost, heq, hp, hb, ht⟩ := bb_forall2_split_right pre post b hrel.1
    exfalso
    apply hbad
    have hn' : (bbNodeRelaxation (D.model P K) (B.clamp P.integerEquiv K).lower
        (B.clamp P.integerEquiv K).upper).Nonempty := by simpa only [hb, BBNode.region] using hn
    simpa only [hb, BBNode.region] using D.clamped_no_unattained P K hK B hX hc hf hn'
  | @prune pre post b inc' q hq hpr =>
    rcases hrel with ⟨hh, hi⟩
    obtain ⟨xpre, B, xpost, heq, hp, hb, ht⟩ := bb_forall2_split_right pre post b hh
    dsimp only at heq
    subst live
    have hm := bb_sim_minimum_join D P K hK hb hq
    refine ⟨⟨xpre ++ xpost, inc⟩, .prune hm ?_, List.rel_append hp ht, hi⟩
    change inc' = inc.map P.split at hi
    rw [hi] at hpr
    exact (bb_sim_prunable_iff D P inc _).mp hpr
  | @integral pre post b inc' q hq hk hI =>
    rcases hrel with ⟨hh, hi⟩
    obtain ⟨xpre, B, xpost, heq, hp, hb, ht⟩ := bb_forall2_split_right pre post b hh
    dsimp only at heq
    subst live
    change inc' = inc.map P.split at hi
    subst inc'
    have hm := bb_sim_minimum_join D P K hK hb hq
    have hkeep : ¬ bbExternalUpper D.f inc < (D.f (P.join q) : WithTop ℝ) :=
      fun h => hk ((bb_sim_prunable_iff D P inc _).mpr h)
    have hI' : bbExternalInteger I (P.join q) := by
      apply (P.integral_iff (P.join q)).mpr
      simpa [BBIntegerPoint] using hI
    refine ⟨⟨xpre ++ xpost, some (P.join q)⟩, .integral hm hkeep hI',
      List.rel_append hp ht, ?_⟩
    change bbUpdate .belottiAlgorithm (D.objective P) (inc.map P.split) q =
      some (P.split (P.join q))
    rw [P.split_join]
    simpa only [P.split_join] using bb_sim_update D P inc (P.join q) hkeep
  | @branch pre post b inc' q i hq hk hfrac =>
    rcases hrel with ⟨hh, hi⟩
    obtain ⟨xpre, B, xpost, heq, hp, hb, ht⟩ := bb_forall2_split_right pre post b hh
    dsimp only at heq
    subst live
    change inc' = inc.map P.split at hi
    subst inc'
    have hm := bb_sim_minimum_join D P K hK hb hq
    have hkeep : ¬ bbExternalUpper D.f inc < (D.f (P.join q) : WithTop ℝ) :=
      fun h => hk ((bb_sim_prunable_iff D P inc _).mpr h)
    have hfrac' : BBFractional (P.join q (P.integerEquiv.symm i)) := by
      simpa using hfrac
    refine ⟨_, .branch (pre := xpre) (post := xpost) (P.integerEquiv.symm i) hm hkeep hfrac', ?_, rfl⟩
    apply List.rel_append (List.rel_append hp ?_) ht
    refine .cons ?_ (.cons ?_ .nil)
    · have hh := (D.left_commutes P K hK B (P.join q) hm.1.1 (P.integerEquiv.symm i)).symm
      simpa only [P.integerEquiv.apply_symm_apply, P.split_join, ← hb] using hh
    · have hh := (D.right_commutes P K hK B (P.join q) hm.1.1 (P.integerEquiv.symm i)).symm
      simpa only [P.integerEquiv.apply_symm_apply, P.split_join, ← hb] using hh

theorem bb_external_trace_trans (D : BBPolyData N l r)
    {s t u : BBExternalState I} {k j : ℕ}
    (h : BBExternalTrace D I s k t) (h' : BBExternalTrace D I t j u) :
    BBExternalTrace D I s (k + j) u := by
  induction h' with
  | refl => simpa using h
  | step h' hs ih => simpa [Nat.add_assoc] using BBExternalTrace.step ih hs

theorem bb_simulate_trace_forward (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) {s u : BBExternalState I} {t : BBState n m} {k : ℕ}
    (htrace : BBExternalTrace D I s k u) (hrel : BBStatesRelated P K s t) :
    ∃ v, BBTrace (D.model P K) (D.objective P) .belottiAlgorithm k t v ∧
      BBStatesRelated P K u v := by
  induction htrace with
  | refl => exact ⟨t, .nil t, hrel⟩
  | step h hs ih =>
    obtain ⟨v, hv, hr⟩ := ih
    obtain ⟨w, hw, hr'⟩ := bb_simulate_process_forward D P K hK hs hr
    exact ⟨w, bb_trace_append_step _ _ _ hv hw, hr'⟩

theorem bb_simulate_trace_backward (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron)
    {s : BBExternalState I} {t v : BBState n m} {k : ℕ}
    (htrace : BBTrace (D.model P K) (D.objective P) .belottiAlgorithm k t v)
    (hrel : BBStatesRelated P K s t) :
    ∃ u, BBExternalTrace D I s k u ∧ BBStatesRelated P K u v := by
  induction htrace generalizing s with
  | nil t => exact ⟨s, .refl s, hrel⟩
  | cons hs htail ih =>
    obtain ⟨u, hu, hr⟩ := bb_simulate_process_backward D P K hK hX hc hf hs hrel
    obtain ⟨w, hw, hr'⟩ := ih hr
    exact ⟨w, by simpa [Nat.add_comm] using
      bb_external_trace_trans D (.step (.refl s) hu) hw, hr'⟩

theorem bb_external_every_trace_bound (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) {s : BBExternalState I} {k : ℕ}
    (htrace : BBExternalTrace D I (bbExternalInitial I) k s) :
    k ≤ (bbRootNode (D.model P K)).weight := by
  obtain ⟨t, ht, _⟩ := bb_simulate_trace_forward D P K hK htrace (bb_sim_initial D P K)
  simpa only [bb_initial_potential] using bb_every_trace_length_bound _ _ _ ht

theorem bb_simulate_reachable_forward (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) {s : BBExternalState I}
    (hs : BBExternalReachable D I s) :
    ∃ t, BBReachable (D.model P K) (D.objective P) .belottiAlgorithm none t ∧
      BBStatesRelated P K s t := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨t, ht, hr⟩ := bb_simulate_trace_forward D P K hK hk (bb_sim_initial D P K)
  exact ⟨t, bb_trace_reachable _ _ _ none BBReachable.initial ht, hr⟩

theorem bb_simulate_reachable_backward (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron) {t : BBState n m}
    (ht : BBReachable (D.model P K) (D.objective P) .belottiAlgorithm none t) :
    ∃ s, BBExternalReachable D I s ∧ BBStatesRelated P K s t := by
  induction ht with
  | initial => exact ⟨bbExternalInitial I, ⟨0, .refl _⟩, bb_sim_initial D P K⟩
  | next ht step ih =>
    obtain ⟨s, ⟨k, hs⟩, hr⟩ := ih
    obtain ⟨u, hu, hr'⟩ := bb_simulate_process_backward D P K hK hX hc hf step hr
    exact ⟨u, ⟨k + 1, .step hs hu⟩, hr'⟩

theorem bb_external_no_infinite_execution (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (s : ℕ → BBExternalState I)
    (h0 : s 0 = bbExternalInitial I) :
    ¬ ∀ k, BBExternalProcess D I (s k) (s (k + 1)) := by
  intro hs
  have ht : ∀ k, BBExternalTrace D I (bbExternalInitial I) k (s k) := by
    intro k
    induction k with
    | zero => simpa only [h0] using BBExternalTrace.refl (D := D) (bbExternalInitial I)
    | succ k ih => exact .step ih (hs k)
  have hb := bb_external_every_trace_bound D P K hK
    (ht ((bbRootNode (D.model P K)).weight + 1))
  omega

theorem bb_sim_objective_continuous_root (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (hf : ContinuousOn D.f D.polyhedron) :
    ContinuousOn (D.objective P) (bbAffineRelaxation (D.model P K)
      (D.model P K).lo (D.model P K).hi) := by
  apply hf.comp P.continuous_join.continuousOn
  intro p hp
  apply (D.affine_root_iff P K hK (P.join p)).mp
  simpa only [P.split_join, BBPolyData.model] using hp

def BBExternalOutcome (D : BBPolyData N l r) (I : Finset (Fin N)) :
    Option (RealVector N) → Prop
  | none => D.feasible I = ∅
  | some z => IsMinimizer (D.feasible I) D.f z

theorem bb_external_reachable_correct (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron)
    {s : BBExternalState I} (hs : BBExternalReachable D I s) (he : s.live = []) :
    BBExternalOutcome D I s.incumbent := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨t, ht, hr⟩ := bb_simulate_trace_forward D P K hK hk (bb_sim_initial D P K)
  have htReach := bb_trace_reachable (D.model P K) (D.objective P) .belottiAlgorithm
    none BBReachable.initial ht
  have htEmpty := (bb_sim_empty_live_iff P K hr).mp he
  have hbase := D.mixed_root_compact P K hK hX
  have hg := D.rows_continuous P K hc
  have hf' := bb_sim_objective_continuous_root D P K hK hf
  cases hi : s.incumbent with
  | none =>
    apply (D.feasible_empty_iff P K hK).mpr
    exact bb_reachable_empty_live_infeasible _ _ .belottiAlgorithm none
      (by simp) hbase hg hf' htReach htEmpty (by simpa only [hi, Option.map_none] using hr.2)
  | some z =>
    apply (D.feasible_minimizer_iff P K hK z).mpr
    exact bb_reachable_empty_live_optimal _ _ .belottiAlgorithm none
      (by simp) hbase hg hf' htReach htEmpty (P.split z)
      (by simpa only [hi, Option.map_some] using hr.2)

def BBExternalDecisionLegal (D : BBPolyData N l r) (I : Finset (Fin N))
    (s : BBExternalState I) : Option (RealVector N) ⊕ BBExternalState I → Prop
  | .inl out => s.live = [] ∧ out = s.incumbent
  | .inr t => BBExternalProcess D I s t

def BBExternalSelector (D : BBPolyData N l r) (I : Finset (Fin N)) :=
  ∀ s : BBExternalState I,
    {c : Option (RealVector N) ⊕ BBExternalState I // BBExternalDecisionLegal D I s c}

theorem bb_external_selector_exists (D : BBPolyData N l r)
    (I : Finset (Fin N)) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron) :
    Nonempty (BBExternalSelector D I) := by
  classical
  have hex : ∀ s : BBExternalState I, Nonempty
      {c : Option (RealVector N) ⊕ BBExternalState I // BBExternalDecisionLegal D I s c} := by
    intro s
    by_cases he : s.live = []
    · exact ⟨⟨.inl s.incumbent, he, rfl⟩⟩
    · obtain ⟨t, ht⟩ := bb_external_nonblocking D hX hc hf s he
      exact ⟨⟨.inr t, ht⟩⟩
  exact ⟨fun s => Classical.choice (hex s)⟩

inductive BBExternalDriverState (I : Finset (Fin N))
  | active (state : BBExternalState I)
  | stopped (state : BBExternalState I) (out : Option (RealVector N))

def bbExternalRun (D : BBPolyData N l r) (I : Finset (Fin N))
    (choose : BBExternalSelector D I) : ℕ → BBExternalDriverState I
  | 0 => .active (bbExternalInitial I)
  | k + 1 => match bbExternalRun D I choose k with
    | .stopped s out => .stopped s out
    | .active s => match (choose s).val with
      | .inl out => .stopped s out
      | .inr t => .active t

theorem bb_external_run_invariant (D : BBPolyData N l r) (I : Finset (Fin N))
    (choose : BBExternalSelector D I) (k : ℕ) :
    match bbExternalRun D I choose k with
    | .active s => BBExternalTrace D I (bbExternalInitial I) k s
    | .stopped s out => ∃ j < k, BBExternalTrace D I (bbExternalInitial I) j s ∧
        s.live = [] ∧ out = s.incumbent := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    simp only [bbExternalRun]
    cases hr : bbExternalRun D I choose k with
    | active s =>
      rw [hr] at ih
      have hlegal := (choose s).property
      cases hh : (choose s).val with
      | inl out =>
        simp only [hh, BBExternalDecisionLegal] at hlegal ⊢
        exact ⟨k, by omega, ih, hlegal⟩
      | inr t =>
        simp only [hh, BBExternalDecisionLegal] at hlegal ⊢
        exact .step ih hlegal
    | stopped s out =>
      rw [hr] at ih
      obtain ⟨j, hj, ht, he, ho⟩ := ih
      exact ⟨j, by omega, ht, he, ho⟩

theorem bb_external_every_selector_finite_return (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (choose : BBExternalSelector D I) :
    ∃ s out, bbExternalRun D I choose ((bbRootNode (D.model P K)).weight + 1) =
      .stopped s out := by
  have h := bb_external_run_invariant D I choose ((bbRootNode (D.model P K)).weight + 1)
  cases hr : bbExternalRun D I choose ((bbRootNode (D.model P K)).weight + 1) with
  | active s =>
    rw [hr] at h
    have hh := bb_external_every_trace_bound D P K hK h
    omega
  | stopped s out => exact ⟨s, out, rfl⟩

theorem bb_external_stopped_run_trace (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (choose : BBExternalSelector D I)
    {s : BBExternalState I} {out : Option (RealVector N)} {k : ℕ}
    (h : bbExternalRun D I choose k = .stopped s out) :
    ∃ j ≤ (bbRootNode (D.model P K)).weight, j < k ∧
      BBExternalTrace D I (bbExternalInitial I) j s ∧ s.live = [] ∧ out = s.incumbent := by
  have hi := bb_external_run_invariant D I choose k
  rw [h] at hi
  obtain ⟨j, hj, ht, he, ho⟩ := hi
  exact ⟨j, bb_external_every_trace_bound D P K hK ht, hj, ht, he, ho⟩

theorem bb_external_return_correct (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron)
    (choose : BBExternalSelector D I) {s : BBExternalState I}
    {out : Option (RealVector N)} {k : ℕ}
    (h : bbExternalRun D I choose k = .stopped s out) : BBExternalOutcome D I out := by
  obtain ⟨j, hj, hjk, ht, he, ho⟩ := bb_external_stopped_run_trace D P K hK choose h
  rw [ho]
  exact bb_external_reachable_correct D P K hK hX hc hf ⟨j, ht⟩ he

theorem bb_external_every_selector_exact_return (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : ContinuousOn D.f D.polyhedron) (choose : BBExternalSelector D I) :
    ∃ (s : BBExternalState I) (out : Option (RealVector N)) (j : ℕ),
      j ≤ (bbRootNode (D.model P K)).weight ∧ BBExternalTrace D I (bbExternalInitial I) j s ∧
      s.live = [] ∧ out = s.incumbent ∧
      bbExternalRun D I choose ((bbRootNode (D.model P K)).weight + 1) = .stopped s out ∧
      BBExternalOutcome D I out := by
  obtain ⟨s, out, h⟩ := bb_external_every_selector_finite_return D P K hK choose
  obtain ⟨j, hj, hjk, ht, he, ho⟩ := bb_external_stopped_run_trace D P K hK choose h
  exact ⟨s, out, j, hj, ht, he, ho, h, bb_external_return_correct D P K hK hX hc hf choose h⟩

/-- Belotti source scope: general C2 f and vector-valued C2/convex c on the
explicit bounded polyhedron, arbitrary I, literal infinity root, Algorithm-1
strict solved pruning and replacement on ties. Convexity is an unused source
premise of this exact global-solve endpoint. Epsilon/CQ/runtime are not claimed. -/
theorem bb_belotti_every_selector_exact_return (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hX : Bornology.IsBounded D.polyhedron) (hc : ContDiff ℝ 2 D.c)
    (hf : ContDiff ℝ 2 D.f) (_hcconv : ConvexOn ℝ Set.univ D.c)
    (_hfconv : ConvexOn ℝ Set.univ D.f) (choose : BBExternalSelector D I) :
    ∃ (s : BBExternalState I) (out : Option (RealVector N)) (j : ℕ),
      j ≤ (bbRootNode (D.model P K)).weight ∧ BBExternalTrace D I (bbExternalInitial I) j s ∧
      s.live = [] ∧ out = s.incumbent ∧
      bbExternalRun D I choose ((bbRootNode (D.model P K)).weight + 1) = .stopped s out ∧
      BBExternalOutcome D I out :=
  bb_external_every_selector_exact_return D P K hK hX hc.continuous hf.continuous.continuousOn choose

theorem bb_belotti_stopped_run_exists (D : BBPolyData N l r) (P : BBPartition I n m)
    (K : ℝ) (hK : D.Encloses K) (hX : Bornology.IsBounded D.polyhedron)
    (hc : ContDiff ℝ 2 D.c) (hf : ContDiff ℝ 2 D.f)
    (hcconv : ConvexOn ℝ Set.univ D.c) (hfconv : ConvexOn ℝ Set.univ D.f) :
    ∃ choose : BBExternalSelector D I, ∃ s out,
      bbExternalRun D I choose ((bbRootNode (D.model P K)).weight + 1) = .stopped s out ∧
      BBExternalOutcome D I out := by
  obtain ⟨choose⟩ := bb_external_selector_exists D I hX hc.continuous hf.continuous.continuousOn
  obtain ⟨s, out, j, hj, ht, he, ho, hrun, hout⟩ :=
    bb_belotti_every_selector_exact_return D P K hK hX hc hf hcconv hfconv choose
  exact ⟨choose, s, out, hrun, hout⟩

theorem bb_external_reachable_maximal_correct (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : ContinuousOn D.f D.polyhedron) {s : BBExternalState I}
    (hs : BBExternalReachable D I s) (hmax : ¬ ∃ t, BBExternalProcess D I s t) :
    BBExternalOutcome D I s.incumbent :=
  bb_external_reachable_correct D P K hK hX hc hf hs
    ((bb_external_no_step_iff D hX hc hf s).mp hmax)

/-- A source-only uniform bound exists: neither a coordinate enumeration nor
an enclosing number is an extra hypothesis of the bounded-polyhedron result. -/
theorem bb_belotti_uniform_trace_bound (D : BBPolyData N l r) (I : Finset (Fin N))
    (hX : Bornology.IsBounded D.polyhedron) :
    ∃ M : ℕ, ∀ (k : ℕ) (s : BBExternalState I),
      BBExternalTrace D I (bbExternalInitial I) k s → k ≤ M := by
  obtain ⟨K, hK⟩ := D.exists_enclosing_bound hX
  let P := bbCanonicalPartition I
  exact ⟨(bbRootNode (D.model P K)).weight,
    fun _ _ h => bb_external_every_trace_bound D P K hK h⟩

theorem bb_belotti_no_infinite_execution (D : BBPolyData N l r) (I : Finset (Fin N))
    (hX : Bornology.IsBounded D.polyhedron) (s : ℕ → BBExternalState I)
    (h0 : s 0 = bbExternalInitial I) :
    ¬ ∀ k, BBExternalProcess D I (s k) (s (k + 1)) := by
  obtain ⟨K, hK⟩ := D.exists_enclosing_bound hX
  exact bb_external_no_infinite_execution D (bbCanonicalPartition I) K hK s h0

/-- Original-coordinate source conclusion for every actual selector, deriving
all enclosing-box and enumeration data rather than supplying them as oracles. -/
theorem bb_belotti_every_selector_returns (D : BBPolyData N l r) (I : Finset (Fin N))
    (hX : Bornology.IsBounded D.polyhedron) (hc : ContDiff ℝ 2 D.c)
    (hf : ContDiff ℝ 2 D.f) (hcconv : ConvexOn ℝ Set.univ D.c)
    (hfconv : ConvexOn ℝ Set.univ D.f) (choose : BBExternalSelector D I) :
    ∃ k s out, bbExternalRun D I choose k = .stopped s out ∧ BBExternalOutcome D I out := by
  obtain ⟨K, hK⟩ := D.exists_enclosing_bound hX
  let P := bbCanonicalPartition I
  obtain ⟨s, out, j, hj, ht, he, ho, hrun, hout⟩ :=
    bb_belotti_every_selector_exact_return D P K hK hX hc hf hcconv hfconv choose
  exact ⟨_, s, out, hrun, hout⟩

theorem bb_belotti_procedure_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (hX : Bornology.IsBounded D.polyhedron) (hc : ContDiff ℝ 2 D.c)
    (hf : ContDiff ℝ 2 D.f) (hcconv : ConvexOn ℝ Set.univ D.c)
    (hfconv : ConvexOn ℝ Set.univ D.f) :
    ∃ choose : BBExternalSelector D I, ∃ k s out,
      bbExternalRun D I choose k = .stopped s out ∧ BBExternalOutcome D I out := by
  obtain ⟨choose⟩ := bb_external_selector_exists D I hX hc.continuous hf.continuous.continuousOn
  exact ⟨choose, bb_belotti_every_selector_returns D I hX hc hf hcconv hfconv choose⟩

end Chapter02

#print axioms Chapter02.bb_forall2_split_left
#print axioms Chapter02.bb_forall2_split_right
#print axioms Chapter02.bb_sim_initial
#print axioms Chapter02.bb_sim_empty_live_iff
#print axioms Chapter02.bb_sim_prunable_iff
#print axioms Chapter02.bb_sim_update
#print axioms Chapter02.bb_sim_minimum_join
#print axioms Chapter02.bb_simulate_process_forward
#print axioms Chapter02.bb_simulate_process_backward
#print axioms Chapter02.bb_external_trace_trans
#print axioms Chapter02.bb_simulate_trace_forward
#print axioms Chapter02.bb_simulate_trace_backward
#print axioms Chapter02.bb_external_every_trace_bound
#print axioms Chapter02.bb_simulate_reachable_forward
#print axioms Chapter02.bb_simulate_reachable_backward
#print axioms Chapter02.bb_external_no_infinite_execution
#print axioms Chapter02.bb_sim_objective_continuous_root
#print axioms Chapter02.bb_external_reachable_correct
#print axioms Chapter02.bb_external_selector_exists
#print axioms Chapter02.bb_external_run_invariant
#print axioms Chapter02.bb_external_every_selector_finite_return
#print axioms Chapter02.bb_external_stopped_run_trace
#print axioms Chapter02.bb_external_return_correct
#print axioms Chapter02.bb_external_every_selector_exact_return
#print axioms Chapter02.bb_belotti_every_selector_exact_return
#print axioms Chapter02.bb_belotti_stopped_run_exists
#print axioms Chapter02.bb_external_reachable_maximal_correct
#print axioms Chapter02.bb_belotti_uniform_trace_bound
#print axioms Chapter02.bb_belotti_no_infinite_execution
#print axioms Chapter02.bb_belotti_every_selector_returns
#print axioms Chapter02.bb_belotti_procedure_exists
