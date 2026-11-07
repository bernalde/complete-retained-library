module

public import Chapter02STSourceProgress
public import Chapter02BBNodes

@[expose] public section

/-! Actual integer-fiber initialization and every-choice finite return for the
separately named original-coordinate cutoff repair. Empty selected fibers are
not global infeasibility. Initialization and the final inspection are counted
separately from actual selection/resolution cycles. -/
noncomputable section
namespace Chapter02
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def stSourceMixedAffine (D : BBPolyData N l r) (I : Finset (Fin N)) : Set (RealVector N) :=
  {a | a ∈ D.polyhedron ∧ STSourceIntegral I a}

def stSourceInitial (D : BBPolyData N l r) (I : Finset (Fin N))
    (b : STSourceBatch N) : STSourceState I :=
  ⟨[],[b],stSourceBatchInc D none b,[BBExtendedNode.root],none⟩

inductive STSourceInitialize (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) : Option (STSourceState I) → Prop
  | empty (he : stSourceMixedAffine D I = ∅) : STSourceInitialize D I w none
  | seeded (a : RealVector N) (b : STSourceBatch N)
      (ha : a ∈ D.polyhedron) (hi : STSourceIntegral I a)
      (hb : stSourceBatchValid D I w b)
      (hy : ∀ i : {i : Fin N // i ∈ I}, b.anchor i = a i) :
      STSourceInitialize D I w (some (stSourceInitial D I b))

theorem st_cutoff_initialize_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : Continuous D.f) :
    ∃ out, STSourceInitialize D I w out := by
  classical
  by_cases he : stSourceMixedAffine D I = ∅
  · exact ⟨none,.empty he⟩
  · obtain ⟨a,ha,hi⟩ := Set.nonempty_iff_ne_empty.mpr he
    obtain ⟨b,hb,hy⟩ := st_source_batch_reply D I w a hi ⟨a,ha,fun _ => rfl⟩ hX hc hf
    exact ⟨some (stSourceInitial D I b),.seeded a b ha hi hb hy⟩

theorem st_cutoff_empty_initialization_sound (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ)
    (h : STSourceInitialize D I w none) : D.feasible I = ∅ := by
  cases h with
  | empty he =>
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hm : z ∈ stSourceMixedAffine D I := ⟨hz.1,hz.2.2⟩
    rw [he] at hm
    exact hm

theorem st_cutoff_empty_X_initialization (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (he : D.polyhedron = ∅) :
    STSourceInitialize D I w none := by
  apply STSourceInitialize.empty
  ext a
  simp [stSourceMixedAffine,he]

theorem st_cutoff_initialization_invariant (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (policy : STSourcePolicy)
    {s : STSourceState I} (h : STSourceInitialize D I w (some s)) :
    STSourceInvariant D I w policy s ∧ s.working = none := by
  cases h with
  | seeded a b ha hi hb hy =>
    exact ⟨st_source_initial_batch_invariant D I w policy b hb,rfl⟩

theorem st_cutoff_initial_potential_bound (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (b : STSourceBatch N) :
    stSourcePotential P K (stSourceInitial D I b) ≤
      (bbRootNode (D.model P K)).weight + (stSourceBox P K).card := by
  have hr := st_source_remaining_le P K [b]
  simpa [stSourcePotential,stSourceTreeWeight,stSourceFrontier,stSourceInitial,
    bbRootNode,BBPolyData.model] using Nat.add_le_add_left hr
      (bbRootNode (D.model P K)).weight

inductive STSourceTrace (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) :
    ℕ → STSourceState I → STSourceState I → Prop
  | nil (s) : STSourceTrace D I w policy 0 s s
  | cons {k s t u} (step : STSourceProcess D I w policy s t)
      (tail : STSourceTrace D I w policy k t u) : STSourceTrace D I w policy (k+1) s u

inductive STSourceMicroTrace (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) :
    ℕ → STSourceState I → STSourceState I → Prop
  | nil (s) : STSourceMicroTrace D I w policy 0 s s
  | cons {k s t u} (step : STSourceStep D I w policy s t)
      (tail : STSourceMicroTrace D I w policy k t u) : STSourceMicroTrace D I w policy (k+1) s u

theorem st_cutoff_trace_trans (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {k j : ℕ} {s t u : STSourceState I}
    (h : STSourceTrace D I w policy k s t) (h' : STSourceTrace D I w policy j t u) :
    STSourceTrace D I w policy (k+j) s u := by
  induction h with
  | nil => simpa using h'
  | cons step tail ih =>
    have hh := STSourceTrace.cons step (ih h')
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem st_cutoff_trace_append_step (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {k : ℕ} {s t u : STSourceState I}
    (h : STSourceTrace D I w policy k s t) (step : STSourceProcess D I w policy t u) :
    STSourceTrace D I w policy (k+1) s u :=
  st_cutoff_trace_trans D w policy h (.cons step (.nil u))

theorem st_cutoff_trace_micro (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {k : ℕ} {s t : STSourceState I}
    (h : STSourceTrace D I w policy k s t) : STSourceMicroTrace D I w policy (2*k) s t := by
  induction h with
  | nil => exact .nil _
  | cons step tail ih =>
    obtain ⟨v,hsel,hres⟩ := step
    simpa [Nat.mul_add,Nat.add_assoc] using
      STSourceMicroTrace.cons (.select hsel) (.cons (.resolve hres) ih)

theorem st_cutoff_trace_ready (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {k : ℕ} {s t : STSourceState I}
    (hs : s.working = none) (h : STSourceTrace D I w policy k s t) : t.working = none := by
  induction h with
  | nil => exact hs
  | cons step tail ih => exact ih (st_source_process_ready step).2

theorem st_cutoff_step_from_ready {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s t : STSourceState I}
    (hs : s.working = none) (h : STSourceStep D I w policy s t) : STSourceSelect s t := by
  cases h with
  | select h => exact h
  | resolve h => have hh := st_source_resolve_working h; simp [hs] at hh

theorem st_cutoff_select_target_working {s t : STSourceState I}
    (h : STSourceSelect s t) : t.working.isSome = true := by cases h; rfl

theorem st_cutoff_step_from_working {D : BBPolyData N l r} {w : Fin l → ℝ}
    {policy : STSourcePolicy} {s t : STSourceState I}
    (hs : s.working.isSome = true) (h : STSourceStep D I w policy s t) :
    STSourceResolve D I w policy s t := by
  cases h with
  | resolve h => exact h
  | select h => cases h; simp at hs

theorem st_cutoff_micro_ready_cycles (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) {j : ℕ} {s t : STSourceState I}
    (hs : s.working = none) (ht : t.working = none)
    (h : STSourceMicroTrace D I w policy j s t) :
    ∃ k, j = 2*k ∧ STSourceTrace D I w policy k s t := by
  induction j using Nat.strong_induction_on generalizing s with
  | h j ih =>
    cases h with
    | nil => exact ⟨0,rfl,.nil _⟩
    | @cons a s v t step tail =>
      have hsel := st_cutoff_step_from_ready hs step
      have hv := st_cutoff_select_target_working hsel
      cases tail with
      | nil => simp [ht] at hv
      | @cons b v u t step' tail' =>
        have hres := st_cutoff_step_from_working hv step'
        obtain ⟨k,hk,htrace⟩ := ih b (by omega) (st_source_resolve_ready hres) tail'
        exact ⟨k+1,by omega,.cons ⟨v,hsel,hres⟩ htrace⟩

theorem st_cutoff_resolve_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) (hf : Continuous D.f)
    (s : STSourceState I) (hs : STSourceInvariant D I w policy s)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (hB : s.working = some B) :
    ∃ t, STSourceResolve D I w policy s t := by
  classical
  obtain ⟨seeds,H,inc,live,working⟩ := s
  simp only at hB
  subst working
  rcases st_source_lp_reply D B (seeds ++ H.map STSourceBatch.anchor)
    policy (inc.map D.f) hX hs.nonempty with he | ⟨q,hq⟩
  · exact ⟨_,.empty he⟩
  · by_cases hi : STSourceIntegral I q.1
    · obtain ⟨b,hb,hy⟩ := st_source_lp_fiber_reply D B
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

theorem st_cutoff_process_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) (hf : Continuous D.f)
    (s : STSourceState I) (hs : STSourceInvariant D I w policy s)
    (hr : s.working = none) (hne : s.live ≠ []) :
    ∃ t, STSourceProcess D I w policy s t := by
  obtain ⟨seeds,H,inc,live,working⟩ := s
  simp only at hr hne
  subst working
  cases live with
  | nil => exact (hne rfl).elim
  | cons B rest =>
    have hsel := STSourceSelect.choose seeds H inc [] rest B
    obtain ⟨t,ht⟩ := st_cutoff_resolve_exists D I w policy hX hc hf _
      (st_source_select_preserves_invariant D w policy hs hsel) B rfl
    exact ⟨t,_,hsel,ht⟩


theorem st_cutoff_trace_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {k : ℕ} {s t : STSourceState I} (hs : STSourceInvariant D I w policy s)
    (h : STSourceTrace D I w policy k s t) : STSourceInvariant D I w policy t := by
  induction h with
  | nil => exact hs
  | cons step tail ih =>
    exact ih (st_source_process_preserves_invariant D w policy hconvf hdf hconv hdiff hs step)

theorem st_cutoff_micro_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {k : ℕ} {s t : STSourceState I} (hs : STSourceInvariant D I w policy s)
    (h : STSourceMicroTrace D I w policy k s t) : STSourceInvariant D I w policy t := by
  induction h with
  | nil => exact hs
  | cons step tail ih =>
    exact ih (st_source_step_preserves_invariant D w policy hconvf hdf hconv hdiff hs step)

theorem st_cutoff_trace_potential_bound (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {k : ℕ} {s t : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (h : STSourceTrace D I w policy k s t) :
    stSourcePotential P K t + k ≤ stSourcePotential P K s := by
  induction h with
  | nil => omega
  | cons step tail ih =>
    have hd := st_source_process_potential_drop D P K hK w hw policy hpolicy
      hconvf hdf hconv hdiff hCQ hs step
    have hh := ih (st_source_process_preserves_invariant D w policy hconvf hdf hconv hdiff hs step)
    omega

theorem st_cutoff_micro_potential_bound (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {k : ℕ} {s t : STSourceState I}
    (hs : STSourceInvariant D I w policy s) (h : STSourceMicroTrace D I w policy k s t) :
    stSourcePhasePotential P K t + k ≤ stSourcePhasePotential P K s := by
  induction h with
  | nil => omega
  | cons step tail ih =>
    have hd := st_source_step_phase_drop D P K hK w hw policy hpolicy
      hconvf hdf hconv hdiff hCQ hs step
    have hh := ih (st_source_step_preserves_invariant D w policy hconvf hdf hconv hdiff hs step)
    omega

def STSourceDecisionLegal (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (s : STSourceState I) :
    Option (RealVector N) ⊕ STSourceState I → Prop
  | .inl out => STSourceStop s out
  | .inr t => STSourceProcess D I w policy s t

def STSourceSelector (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) :=
  ∀ s : STSourceState I, {c : Option (RealVector N) ⊕ STSourceState I //
    STSourceInvariant D I w policy s → s.working = none → STSourceDecisionLegal D I w policy s c}

theorem st_cutoff_selector_exists (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) (hf : Continuous D.f) :
    Nonempty (STSourceSelector D I w policy) := by
  classical
  have hex : ∀ s : STSourceState I, Nonempty {c : Option (RealVector N) ⊕ STSourceState I //
      STSourceInvariant D I w policy s → s.working = none → STSourceDecisionLegal D I w policy s c} := by
    intro s
    by_cases hv : STSourceInvariant D I w policy s ∧ s.working = none
    · by_cases he : s.live = []
      · exact ⟨⟨.inl s.incumbent,fun _ _ => .exhausted hv.2 he⟩⟩
      · obtain ⟨t,ht⟩ := st_cutoff_process_exists D I w policy hX hc hf s hv.1 hv.2 he
        exact ⟨⟨.inr t,fun _ _ => ht⟩⟩
    · exact ⟨⟨.inl none,fun hs hr => (hv ⟨hs,hr⟩).elim⟩⟩
  exact ⟨fun s => Classical.choice (hex s)⟩

inductive STSourceDriverState (I : Finset (Fin N))
  | active (state : STSourceState I)
  | stopped (state : STSourceState I) (out : Option (RealVector N))

def stSourceRun (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (policy : STSourcePolicy) (choose : STSourceSelector D I w policy)
    (initial : STSourceState I) : ℕ → STSourceDriverState I
  | 0 => .active initial
  | k+1 => match stSourceRun D I w policy choose initial k with
    | .stopped s out => .stopped s out
    | .active s => match (choose s).val with
      | .inl out => .stopped s out
      | .inr t => .active t

theorem st_cutoff_run_invariant (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (choose : STSourceSelector D I w policy) (initial : STSourceState I)
    (hi : STSourceInvariant D I w policy initial) (hr : initial.working = none) (k : ℕ) :
    match stSourceRun D I w policy choose initial k with
    | .active s => STSourceTrace D I w policy k initial s ∧
        STSourceInvariant D I w policy s ∧ s.working = none
    | .stopped s out => ∃ j<k, STSourceTrace D I w policy j initial s ∧
        STSourceInvariant D I w policy s ∧ STSourceStop s out := by
  induction k with
  | zero => exact ⟨.nil initial,hi,hr⟩
  | succ k ih =>
    simp only [stSourceRun]
    cases hh : stSourceRun D I w policy choose initial k with
    | active s =>
      rw [hh] at ih
      have hlegal := (choose s).property ih.2.1 ih.2.2
      cases hc : (choose s).val with
      | inl out =>
        simp only [hc,STSourceDecisionLegal] at hlegal ⊢
        exact ⟨k,by omega,ih.1,ih.2.1,hlegal⟩
      | inr t =>
        simp only [hc,STSourceDecisionLegal] at hlegal ⊢
        exact ⟨st_cutoff_trace_append_step D w policy ih.1 hlegal,
          st_source_process_preserves_invariant D w policy hconvf hdf hconv hdiff ih.2.1 hlegal,
          (st_source_process_ready hlegal).2⟩
    | stopped s out =>
      rw [hh] at ih
      obtain ⟨j,hj,htrace,hs,hstop⟩ := ih
      exact ⟨j,by omega,htrace,hs,hstop⟩

theorem st_cutoff_every_selector_finite_return (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I)
    (choose : STSourceSelector D I w policy) (initial : STSourceState I)
    (hi : STSourceInvariant D I w policy initial) (hr : initial.working = none) :
    ∃ s out, stSourceRun D I w policy choose initial (stSourcePotential P K initial+1) =
      .stopped s out := by
  have hh := st_cutoff_run_invariant D w policy hconvf hdf hconv hdiff choose initial hi hr
    (stSourcePotential P K initial+1)
  cases he : stSourceRun D I w policy choose initial (stSourcePotential P K initial+1) with
  | active s =>
    rw [he] at hh
    have hb := st_cutoff_trace_potential_bound D w policy P K hK hw hpolicy
      hconvf hdf hconv hdiff hCQ hi hh.1
    omega
  | stopped s out => exact ⟨s,out,rfl⟩

theorem st_cutoff_every_initialized_selector_returns (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy)
    (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) (choose : STSourceSelector D I w policy)
    {initial : STSourceState I} (hinit : STSourceInitialize D I w (some initial)) :
    ∃ s out k, k ≤ (bbRootNode (D.model P K)).weight + (stSourceBox P K).card ∧
      STSourceTrace D I w policy k initial s ∧ STSourceMicroTrace D I w policy (2*k) initial s ∧
      STSourceStop s out ∧ STSourceReturnCertificate D I policy out ∧
      stSourceRun D I w policy choose initial (stSourcePotential P K initial+1) = .stopped s out := by
  obtain ⟨hi,hr⟩ := st_cutoff_initialization_invariant D I w policy hinit
  obtain ⟨s,out,he⟩ := st_cutoff_every_selector_finite_return D w policy P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ choose initial hi hr
  have hh := st_cutoff_run_invariant D w policy hconvf hdf hconv hdiff choose initial hi hr
    (stSourcePotential P K initial+1)
  rw [he] at hh
  obtain ⟨k,hk,ht,hs,hstop⟩ := hh
  have hb := st_cutoff_trace_potential_bound D w policy P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ hi ht
  have hib : stSourcePotential P K initial ≤
      (bbRootNode (D.model P K)).weight + (stSourceBox P K).card := by
    cases hinit with
    | seeded a b ha hi hb hy => exact st_cutoff_initial_potential_bound D P K b
  exact ⟨s,out,k,by omega,ht,st_cutoff_trace_micro D w policy ht,hstop,
    st_source_stop_sound D w policy hs hstop,he⟩


theorem st_cutoff_initialized_micro_bound (D : BBPolyData N l r) (w : Fin l → ℝ)
    (policy : STSourcePolicy) (P : BBPartition I n m) (K : ℝ) (hK : D.Encloses K)
    (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {initial t : STSourceState I} {j : ℕ}
    (hinit : STSourceInitialize D I w (some initial))
    (ht : STSourceMicroTrace D I w policy j initial t) :
    j ≤ 2*((bbRootNode (D.model P K)).weight + (stSourceBox P K).card)+1 := by
  obtain ⟨hi,hr⟩ := st_cutoff_initialization_invariant D I w policy hinit
  have hb := st_cutoff_micro_potential_bound D w policy P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ hi ht
  have hib : stSourcePotential P K initial ≤
      (bbRootNode (D.model P K)).weight + (stSourceBox P K).card := by
    cases hinit with
    | seeded a b ha hi hb hy => exact st_cutoff_initial_potential_bound D P K b
  simp only [stSourcePhasePotential,hr,Option.isNone_none,Bool.true_eq,if_true] at hb
  omega

theorem st_cutoff_source_no_infinite_raw_execution (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hX : Bornology.IsBounded D.polyhedron) (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) (run : ℕ → STSourceState I)
    (hinit : STSourceInitialize D I w (some (run 0))) :
    ¬ ∀ k, STSourceStep D I w policy (run k) (run (k+1)) := by
  intro hrun
  let P := bbCanonicalPartition I
  obtain ⟨K,hK⟩ := D.exists_enclosing_bound hX
  have traces : ∀ start count, STSourceMicroTrace D I w policy count
      (run start) (run (start+count)) := by
    intro start count
    induction count generalizing start with
    | zero => simpa using STSourceMicroTrace.nil (D := D) (I := I) (w := w) (policy := policy) (run start)
    | succ count ih =>
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        STSourceMicroTrace.cons (hrun start) (ih (start+1))
  let bound := 2*((bbRootNode (D.model P K)).weight + (stSourceBox P K).card)+1
  have ht : STSourceMicroTrace D I w policy (bound+1) (run 0) (run (bound+1)) := by
    simpa using traces 0 (bound+1)
  have hb := st_cutoff_initialized_micro_bound D w policy P K hK hw hpolicy
    hconvf hdf hconv hdiff hCQ hinit ht
  change bound+1 ≤ bound at hb
  omega

/-- Source-only existence and every-selector endpoint. C2 and convexity concern
actual D.f/D.c; the proof-only partition/enclosure are derived, not requested
from a source caller. Empty initialization is an exact global certificate. -/
theorem st_cutoff_source_every_selector_returns (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (policy : STSourcePolicy)
    (hX : Bornology.IsBounded D.polyhedron) (hw : ∀ j, 0 < w j)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    (hf2 : ContDiff ℝ 2 D.f) (hc2 : ContDiff ℝ 2 D.c)
    (hconvf : ConvexOn ℝ Set.univ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) :
    (∃ init, STSourceInitialize D I w init) ∧ Nonempty (STSourceSelector D I w policy) ∧
    ∀ choose : STSourceSelector D I w policy, ∀ init,
      STSourceInitialize D I w init →
      match init with
      | none => D.feasible I = ∅
      | some initial => ∃ s out k, STSourceTrace D I w policy k initial s ∧
          STSourceMicroTrace D I w policy (2*k) initial s ∧ STSourceStop s out ∧
          STSourceReturnCertificate D I policy out ∧
          ∃ steps, stSourceRun D I w policy choose initial steps = .stopped s out := by
  have hdf := hf2.differentiable (by norm_num)
  have hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j) :=
    fun j => ((contDiff_apply ℝ (fun _ => ℝ) j).comp hc2).differentiable (by norm_num)
  refine ⟨st_cutoff_initialize_exists D I w hX hc2.continuous hf2.continuous,
    st_cutoff_selector_exists D I w policy hX hc2.continuous hf2.continuous,?_⟩
  intro choose init hi
  cases init with
  | none => exact st_cutoff_empty_initialization_sound D I w hi
  | some initial =>
    let P := bbCanonicalPartition I
    obtain ⟨K,hK⟩ := D.exists_enclosing_bound hX
    obtain ⟨s,out,k,hk,ht,hm,hs,hc,hr⟩ := st_cutoff_every_initialized_selector_returns
      D w policy P K hK hw hpolicy hconvf hdf hconv hdiff hCQ choose hi
    exact ⟨s,out,k,ht,hm,hs,hc,_,hr⟩

end Chapter02

#print axioms Chapter02.st_cutoff_initialize_exists
#print axioms Chapter02.st_cutoff_empty_initialization_sound
#print axioms Chapter02.st_cutoff_empty_X_initialization
#print axioms Chapter02.st_cutoff_initialization_invariant
#print axioms Chapter02.st_cutoff_initial_potential_bound
#print axioms Chapter02.st_cutoff_trace_trans
#print axioms Chapter02.st_cutoff_trace_append_step
#print axioms Chapter02.st_cutoff_trace_micro
#print axioms Chapter02.st_cutoff_trace_ready
#print axioms Chapter02.st_cutoff_step_from_ready
#print axioms Chapter02.st_cutoff_select_target_working
#print axioms Chapter02.st_cutoff_step_from_working
#print axioms Chapter02.st_cutoff_micro_ready_cycles
#print axioms Chapter02.st_cutoff_resolve_exists
#print axioms Chapter02.st_cutoff_process_exists
#print axioms Chapter02.st_cutoff_trace_invariant
#print axioms Chapter02.st_cutoff_micro_invariant
#print axioms Chapter02.st_cutoff_trace_potential_bound
#print axioms Chapter02.st_cutoff_micro_potential_bound
#print axioms Chapter02.st_cutoff_selector_exists
#print axioms Chapter02.st_cutoff_run_invariant
#print axioms Chapter02.st_cutoff_every_selector_finite_return
#print axioms Chapter02.st_cutoff_every_initialized_selector_returns
#print axioms Chapter02.st_cutoff_initialized_micro_bound
#print axioms Chapter02.st_cutoff_source_no_infinite_raw_execution
#print axioms Chapter02.st_cutoff_source_every_selector_returns
