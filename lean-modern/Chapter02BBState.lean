module

public import Chapter02BBNodes

@[expose] public section

/-! Actual occurrence-based exact NLP-BB states and three named policies.
Raw process constructors contain only local reply and policy witnesses.
Semantic invariants and progress are proved separately from literal states. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

inductive BBPolicy
  | source
  | belottiAlgorithm
  | weak
  deriving DecidableEq

structure BBRecord (m : ℕ) where
  node : BBNode m
  lower : WithBot ℝ

structure BBState (n m : ℕ) where
  live : List (BBRecord m)
  incumbent : Option (Point n m)

abbrev BBGlobalBound := WithTop (WithBot ℝ)

def bbValue (v : ℝ) : BBGlobalBound := ((v : WithBot ℝ) : BBGlobalBound)

def bbPrunable (policy : BBPolicy) (f : Point n m → ℝ)
    (inc : Option (Point n m)) (v : ℝ) : Prop :=
  match inc with
  | none => False
  | some p => if policy = .weak then f p ≤ v else f p < v

def bbUpdate (policy : BBPolicy) (f : Point n m → ℝ)
    (inc : Option (Point n m)) (q : Point n m) : Option (Point n m) :=
  match inc with
  | none => some q
  | some p => if policy = .belottiAlgorithm then
      (if f q ≤ f p then some q else some p)
    else (if f q < f p then some q else some p)

def bbIncBelow (f : Point n m → ℝ) (inc : Option (Point n m))
    (p : Point n m) : Prop := ∃ q, inc = some q ∧ f q ≤ f p

def bbIncBound (f : Point n m → ℝ) : Option (Point n m) → BBGlobalBound
  | none => ⊤
  | some p => bbValue (f p)

def bbLiveBound : List (BBRecord m) → BBGlobalBound
  | [] => ⊤
  | b :: bs => min (b.lower : BBGlobalBound) (bbLiveBound bs)

def bbGlobalBound (f : Point n m → ℝ) (s : BBState n m) : BBGlobalBound :=
  min (bbIncBound f s.incumbent) (bbLiveBound s.live)

def bbPotential (s : BBState n m) : ℕ := (s.live.map (fun b => b.node.weight)).sum

def bbChildren (b : BBRecord m) (i : Fin m) (q : Point n m)
    (f : Point n m → ℝ) : List (BBRecord m) :=
  [⟨b.node.left i (q.2 i), max b.lower (f q : WithBot ℝ)⟩,
   ⟨b.node.right i (q.2 i), max b.lower (f q : WithBot ℝ)⟩]

theorem bb_value_le_value {a b : ℝ} : bbValue a ≤ bbValue b ↔ a ≤ b := by
  simp [bbValue]

theorem bb_update_selects (policy : BBPolicy) (f : Point n m → ℝ)
    (inc : Option (Point n m)) (q : Point n m) :
    bbUpdate policy f inc q = some q ∨ bbUpdate policy f inc q = inc := by
  cases inc with
  | none => exact Or.inl rfl
  | some p =>
    simp only [bbUpdate]
    split <;> split <;> simp

theorem bb_update_below_new (policy : BBPolicy) (f : Point n m → ℝ)
    (inc : Option (Point n m)) (q : Point n m) :
    bbIncBelow f (bbUpdate policy f inc q) q := by
  cases inc with
  | none => exact ⟨q, rfl, le_rfl⟩
  | some p =>
    simp only [bbUpdate]
    split
    · split
      · exact ⟨q, rfl, le_rfl⟩
      · exact ⟨p, rfl, (le_of_not_ge ‹¬ f q ≤ f p›)⟩
    · split
      · exact ⟨q, rfl, le_rfl⟩
      · exact ⟨p, rfl, le_of_not_gt ‹¬ f q < f p›⟩

theorem bb_update_preserves_below (policy : BBPolicy) (f : Point n m → ℝ)
    (inc : Option (Point n m)) (q p : Point n m)
    (h : bbIncBelow f inc p) : bbIncBelow f (bbUpdate policy f inc q) p := by
  rcases h with ⟨a, rfl, ha⟩
  simp only [bbUpdate]
  split
  · split
    · exact ⟨q, rfl, le_trans ‹f q ≤ f a› ha⟩
    · exact ⟨a, rfl, ha⟩
  · split
    · exact ⟨q, rfl, le_trans (le_of_lt ‹f q < f a›) ha⟩
    · exact ⟨a, rfl, ha⟩

theorem bb_update_inc_bound (policy : BBPolicy) (f : Point n m → ℝ)
    (inc : Option (Point n m)) (q : Point n m) :
    bbIncBound f (bbUpdate policy f inc q) = min (bbIncBound f inc) (bbValue (f q)) := by
  cases inc with
  | none => simp [bbUpdate, bbIncBound]
  | some p =>
    simp only [bbUpdate]
    split
    · split
      · simp only [bbIncBound]
        exact (min_eq_right ((bb_value_le_value).2 ‹f q ≤ f p›)).symm
      · simp only [bbIncBound]
        exact (min_eq_left ((bb_value_le_value).2 (le_of_not_ge ‹¬ f q ≤ f p›))).symm
    · split
      · simp only [bbIncBound]
        exact (min_eq_right ((bb_value_le_value).2 (le_of_lt ‹f q < f p›))).symm
      · simp only [bbIncBound]
        exact (min_eq_left ((bb_value_le_value).2 (le_of_not_gt ‹¬ f q < f p›))).symm

theorem bb_prunable_has_incumbent (policy : BBPolicy) (f : Point n m → ℝ)
    (inc : Option (Point n m)) (v : ℝ) (h : bbPrunable policy f inc v) :
    ∃ p, inc = some p ∧ f p ≤ v := by
  cases inc with
  | none => exact h.elim
  | some p =>
    refine ⟨p, rfl, ?_⟩
    simp only [bbPrunable] at h
    split at h
    · exact h
    · exact h.le

theorem bb_le_live_bound_iff (v : BBGlobalBound) (bs : List (BBRecord m)) :
    v ≤ bbLiveBound bs ↔ ∀ b ∈ bs, v ≤ (b.lower : BBGlobalBound) := by
  induction bs with
  | nil => simp [bbLiveBound]
  | cons b bs ih => simp [bbLiveBound, le_min_iff, ih]

theorem bb_le_global_bound_iff (f : Point n m → ℝ) (s : BBState n m)
    (v : BBGlobalBound) : v ≤ bbGlobalBound f s ↔
    (∀ p, s.incumbent = some p → v ≤ bbValue (f p)) ∧
    ∀ b ∈ s.live, v ≤ (b.lower : BBGlobalBound) := by
  simp only [bbGlobalBound, le_min_iff, bb_le_live_bound_iff]
  cases hi : s.incumbent <;> simp [bbIncBound]

theorem bb_global_le_record (f : Point n m → ℝ) (s : BBState n m)
    (b : BBRecord m) (hb : b ∈ s.live) : bbGlobalBound f s ≤ (b.lower : BBGlobalBound) :=
  ((bb_le_global_bound_iff f s _).mp le_rfl).2 b hb

theorem bb_global_le_incumbent (f : Point n m → ℝ) (s : BBState n m)
    (p : Point n m) (hp : s.incumbent = some p) : bbGlobalBound f s ≤ bbValue (f p) :=
  ((bb_le_global_bound_iff f s _).mp le_rfl).1 p hp

theorem bb_potential_eq_zero_iff (s : BBState n m) : bbPotential s = 0 ↔ s.live = [] := by
  cases h : s.live with
  | nil => simp [bbPotential, h]
  | cons b bs =>
    have hpos := bb_weight_pos b.node
    simp only [bbPotential, h, List.map_cons, List.sum_cons, List.cons_ne_nil, iff_false]
    omega

def bbInitial (d : ModelData n m l r) (warm : Option (Point n m)) : BBState n m :=
  ⟨[⟨bbRootNode d, ⊥⟩], warm⟩

/-- The unguarded bad-status actions are sound only at endpoints carrying the
source compact mixed-base premise. They are not numerical status adapters. -/
inductive BBProcess (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) : BBState n m → BBState n m → Prop
  | empty {pre post : List (BBRecord m)} {b : BBRecord m} {inc}
      (h : b.node.region d = ∅) :
      BBProcess d f policy ⟨pre ++ b :: post, inc⟩ ⟨pre ++ post, inc⟩
  | unbounded {pre post : List (BBRecord m)} {b : BBRecord m} {inc}
      (h : ∀ B : ℝ, ∃ q ∈ b.node.region d, f q < B) :
      BBProcess d f policy ⟨pre ++ b :: post, inc⟩ ⟨pre ++ post, inc⟩
  | unattained {pre post : List (BBRecord m)} {b : BBRecord m} {inc}
      (hne : (b.node.region d).Nonempty) (hbelow : BddBelow (f '' b.node.region d))
      (hbad : ¬ ∃ q, IsMinimizer (b.node.region d) f q) :
      BBProcess d f policy ⟨pre ++ b :: post, inc⟩ ⟨pre ++ post, inc⟩
  | prune {pre post : List (BBRecord m)} {b : BBRecord m} {inc q}
      (hq : IsMinimizer (b.node.region d) f q) (hp : bbPrunable policy f inc (f q)) :
      BBProcess d f policy ⟨pre ++ b :: post, inc⟩ ⟨pre ++ post, inc⟩
  | integral {pre post : List (BBRecord m)} {b : BBRecord m} {inc q}
      (hq : IsMinimizer (b.node.region d) f q) (hkeep : ¬ bbPrunable policy f inc (f q))
      (hi : BBIntegerPoint q) :
      BBProcess d f policy ⟨pre ++ b :: post, inc⟩
        ⟨pre ++ post, bbUpdate policy f inc q⟩
  | branch {pre post : List (BBRecord m)} {b : BBRecord m} {inc q} (i : Fin m)
      (hq : IsMinimizer (b.node.region d) f q) (hkeep : ¬ bbPrunable policy f inc (f q))
      (hf : BBFractional (q.2 i)) :
      BBProcess d f policy ⟨pre ++ b :: post, inc⟩
        ⟨pre ++ bbChildren b i q f ++ post, inc⟩

structure BBInvariant (d : ModelData n m l r) (f : Point n m → ℝ)
    (s : BBState n m) : Prop where
  refines : ∀ b ∈ s.live, b.node.Refines (bbRootNode d)
  bounds : ∀ b ∈ s.live, ∀ p ∈ b.node.region d, b.lower ≤ (f p : WithBot ℝ)
  incumbent : ∀ p, s.incumbent = some p → p ∈ d.feasibleOn Set.univ
  coverage : ∀ p ∈ d.feasibleOn Set.univ,
    (∃ b ∈ s.live, p ∈ b.node.feasible d) ∨ bbIncBelow f s.incumbent p

theorem bb_initial_invariant (d : ModelData n m l r) (f : Point n m → ℝ)
    (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ) :
    BBInvariant d f (bbInitial d warm) := by
  constructor
  · intro b hb
    have heq : b = ⟨bbRootNode d, ⊥⟩ := by simpa [bbInitial] using hb
    subst b
    exact bb_refines_refl _
  · intro b hb p hp
    have heq : b = ⟨bbRootNode d, ⊥⟩ := by simpa [bbInitial] using hb
    subst b
    exact bot_le
  · exact hwarm
  · intro p hp
    left
    refine ⟨⟨bbRootNode d, ⊥⟩, by simp [bbInitial], ?_⟩
    simpa [bb_root_feasible] using hp

/-- Conditional replacement lemma. Every premise about replacement records is
discharged from local reply data in `bb_process_preserves_invariant`. -/
theorem bb_invariant_replace (d : ModelData n m l r) (f : Point n m → ℝ)
    (pre post replacement : List (BBRecord m)) (b : BBRecord m)
    (inc inc' : Option (Point n m))
    (h : BBInvariant d f ⟨pre ++ b :: post, inc⟩)
    (href : ∀ c ∈ replacement, c.node.Refines (bbRootNode d))
    (hbounds : ∀ c ∈ replacement, ∀ p ∈ c.node.region d, c.lower ≤ (f p : WithBot ℝ))
    (hinc : ∀ p, inc' = some p → p ∈ d.feasibleOn Set.univ)
    (hdom : ∀ p, bbIncBelow f inc p → bbIncBelow f inc' p)
    (hremoved : ∀ p ∈ b.node.feasible d,
      (∃ c ∈ replacement, p ∈ c.node.feasible d) ∨ bbIncBelow f inc' p) :
    BBInvariant d f ⟨pre ++ replacement ++ post, inc'⟩ := by
  constructor
  · intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact h.refines c (by simp [hc])
    · exact href c hc
    · exact h.refines c (by simp [hc])
  · intro c hc p hp
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact h.bounds c (by simp [hc]) p hp
    · exact hbounds c hc p hp
    · exact h.bounds c (by simp [hc]) p hp
  · exact hinc
  · intro p hp
    rcases h.coverage p hp with ⟨c, hc, hpc⟩ | hd
    · simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | (hc | hc)
      · exact Or.inl ⟨c, by simp [hc], hpc⟩
      · subst c
        rcases hremoved p hpc with ⟨c, hc, hpc⟩ | hd
        · exact Or.inl ⟨c, by simp [hc], hpc⟩
        · exact Or.inr hd
      · exact Or.inl ⟨c, by simp [hc], hpc⟩
    · exact Or.inr (hdom p hd)

theorem bb_invariant_delete (d : ModelData n m l r) (f : Point n m → ℝ)
    (pre post : List (BBRecord m)) (b : BBRecord m) (inc : Option (Point n m))
    (h : BBInvariant d f ⟨pre ++ b :: post, inc⟩)
    (hremoved : ∀ p ∈ b.node.feasible d, bbIncBelow f inc p) :
    BBInvariant d f ⟨pre ++ post, inc⟩ := by
  have hh := bb_invariant_replace d f pre post [] b inc inc h
    (by simp) (by simp) h.incumbent (fun _ hd => hd)
    (fun p hp => Or.inr (hremoved p hp))
  simpa using hh

theorem bb_process_preserves_invariant (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi))
    {s t : BBState n m} (h : BBInvariant d f s) (step : BBProcess d f policy s t) :
    BBInvariant d f t := by
  cases step with
  | @empty pre post b inc he =>
    apply bb_invariant_delete d f pre post b inc h
    intro p hp
    have he' := bb_empty_node_feasible d he
    simp [he'] at hp
  | @unbounded pre post b inc hu =>
    apply bb_invariant_delete d f pre post b inc h
    intro p hp
    have he := bb_bad_unbounded_empty d f hbase hg hf (h.refines b (by simp)) hu
    simp [he] at hp
  | @unattained pre post b inc hne hbelow hbad =>
    apply bb_invariant_delete d f pre post b inc h
    intro p hp
    have he := bb_bad_unattained_empty d f hbase hg hf (h.refines b (by simp)) hne hbelow hbad
    simp [he] at hp
  | @prune pre post b inc q hq hp =>
    apply bb_invariant_delete d f pre post b inc h
    intro p hpf
    obtain ⟨a, ha, hav⟩ := bb_prunable_has_incumbent policy f inc (f q) hp
    exact ⟨a, ha, hav.trans (hq.2 p (bb_feasible_subset_region d b.node hpf))⟩
  | @integral pre post b inc q hq hkeep hi =>
    have hqF := bb_feasible_subset_root d (h.refines b (by simp))
      ((bb_feasible_mem_iff d b.node q).2 ⟨hq.1, hi⟩)
    have hnew : ∀ p, bbUpdate policy f inc q = some p → p ∈ d.feasibleOn Set.univ := by
      intro p hp
      rcases bb_update_selects policy f inc q with he | he
      · rw [he] at hp
        cases hp
        exact hqF
      · exact h.incumbent p (he.symm.trans hp)
    have hh := bb_invariant_replace d f pre post [] b inc (bbUpdate policy f inc q)
      h (by simp) (by simp) hnew (bb_update_preserves_below policy f inc q) ?_
    · simpa using hh
    · intro p hp
      right
      obtain ⟨a, ha, hav⟩ := bb_update_below_new policy f inc q
      exact ⟨a, ha, hav.trans (hq.2 p (bb_feasible_subset_region d b.node hp))⟩
  | @branch pre post b inc q i hq hkeep hfrac =>
    apply bb_invariant_replace d f pre post (bbChildren b i q f) b inc inc h
    · intro c hc
      simp only [bbChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact bb_refines_trans (bb_left_refines b.node i q hq.1.2.2) (h.refines b (by simp))
      · exact bb_refines_trans (bb_right_refines b.node i q hq.1.2.2) (h.refines b (by simp))
    · intro c hc p hp
      simp only [bbChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have hp' := bb_region_subset_of_refines d (bb_left_refines b.node i q hq.1.2.2) hp
        exact max_le (h.bounds b (by simp) p hp') (by exact_mod_cast hq.2 p hp')
      · have hp' := bb_region_subset_of_refines d (bb_right_refines b.node i q hq.1.2.2) hp
        exact max_le (h.bounds b (by simp) p hp') (by exact_mod_cast hq.2 p hp')
    · exact h.incumbent
    · exact fun _ hd => hd
    · intro p hp
      left
      rw [bb_child_feasible_cover d b.node i q hq.1] at hp
      rcases hp with hl | hr
      · exact ⟨⟨b.node.left i (q.2 i), max b.lower (f q : WithBot ℝ)⟩, by simp [bbChildren], hl⟩
      · exact ⟨⟨b.node.right i (q.2 i), max b.lower (f q : WithBot ℝ)⟩, by simp [bbChildren], hr⟩

inductive BBReachable (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m)) : BBState n m → Prop
  | initial : BBReachable d f policy warm (bbInitial d warm)
  | next {s t} (hs : BBReachable d f policy warm s) (step : BBProcess d f policy s t) :
      BBReachable d f policy warm t

theorem bb_reachable_invariant (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi))
    {s : BBState n m} (hs : BBReachable d f policy warm s) : BBInvariant d f s := by
  induction hs with
  | initial => exact bb_initial_invariant d f warm hwarm
  | next hs step ih => exact bb_process_preserves_invariant d f policy hbase hg hf ih step

theorem bb_global_bound_sound (d : ModelData n m l r) (f : Point n m → ℝ)
    (s : BBState n m) (h : BBInvariant d f s) (p : Point n m)
    (hp : p ∈ d.feasibleOn Set.univ) : bbGlobalBound f s ≤ bbValue (f p) := by
  rcases h.coverage p hp with ⟨b, hb, hpb⟩ | ⟨a, ha, hav⟩
  · apply (bb_global_le_record f s b hb).trans
    simpa [bbValue] using h.bounds b hb p (bb_feasible_subset_region d b.node hpb)
  · exact (bb_global_le_incumbent f s a ha).trans ((bb_value_le_value).2 hav)

theorem bb_empty_live_incumbent_optimal (d : ModelData n m l r) (f : Point n m → ℝ)
    (s : BBState n m) (h : BBInvariant d f s) (he : s.live = [])
    (q : Point n m) (hq : s.incumbent = some q) :
    IsMinimizer (d.feasibleOn Set.univ) f q := by
  refine ⟨h.incumbent q hq, ?_⟩
  intro p hp
  rcases h.coverage p hp with ⟨b, hb, _⟩ | ⟨a, ha, hav⟩
  · simp [he] at hb
  · have heq : a = q := Option.some.inj (ha.symm.trans hq)
    simpa [heq] using hav

theorem bb_empty_live_no_incumbent_infeasible (d : ModelData n m l r)
    (f : Point n m → ℝ) (s : BBState n m) (h : BBInvariant d f s)
    (he : s.live = []) (hi : s.incumbent = none) : d.feasibleOn Set.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases h.coverage p hp with ⟨b, hb, _⟩ | ⟨a, ha, _⟩
  · simp [he] at hb
  · simp [hi] at ha

theorem bb_delete_potential_drop (pre post : List (BBRecord m)) (b : BBRecord m)
    (inc inc' : Option (Point n m)) :
    bbPotential ⟨pre ++ post, inc'⟩ + 1 ≤ bbPotential ⟨pre ++ b :: post, inc⟩ := by
  have hw := bb_weight_pos b.node
  simp only [bbPotential, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  omega

theorem bb_branch_potential_drop (pre post : List (BBRecord m)) (b : BBRecord m)
    (inc : Option (Point n m)) (i : Fin m) (q : Point n m) (f : Point n m → ℝ)
    (hq : q ∈ b.node.box) (hf : BBFractional (q.2 i)) :
    bbPotential ⟨pre ++ bbChildren b i q f ++ post, inc⟩ + 1 ≤
      bbPotential ⟨pre ++ b :: post, inc⟩ := by
  have hw := bb_children_weight_drop b.node i q hq hf
  simp only [bbPotential, bbChildren, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  omega

theorem bb_process_potential_drop (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) {s t : BBState n m} (h : BBProcess d f policy s t) :
    bbPotential t + 1 ≤ bbPotential s := by
  cases h with
  | empty _ => exact bb_delete_potential_drop _ _ _ _ _
  | unbounded _ => exact bb_delete_potential_drop _ _ _ _ _
  | unattained _ _ _ => exact bb_delete_potential_drop _ _ _ _ _
  | prune _ _ => exact bb_delete_potential_drop _ _ _ _ _
  | integral _ _ _ => exact bb_delete_potential_drop _ _ _ _ _
  | branch i hq _ hf => exact bb_branch_potential_drop _ _ _ _ i _ f hq.1.2.2 hf

theorem bb_global_replace_mono (f : Point n m → ℝ)
    (pre post replacement : List (BBRecord m)) (b : BBRecord m)
    (inc inc' : Option (Point n m))
    (hinc : bbGlobalBound f ⟨pre ++ b :: post, inc⟩ ≤ bbIncBound f inc')
    (hreplacement : ∀ c ∈ replacement,
      bbGlobalBound f ⟨pre ++ b :: post, inc⟩ ≤ (c.lower : BBGlobalBound)) :
    bbGlobalBound f ⟨pre ++ b :: post, inc⟩ ≤
      bbGlobalBound f ⟨pre ++ replacement ++ post, inc'⟩ := by
  apply (bb_le_global_bound_iff f _ _).2
  constructor
  · intro p hp
    change inc' = some p at hp
    simpa [hp, bbIncBound] using hinc
  · intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact bb_global_le_record f _ c (by simp [hc])
    · exact hreplacement c hc
    · exact bb_global_le_record f _ c (by simp [hc])

theorem bb_process_global_bound_mono (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) {s t : BBState n m} (h : BBInvariant d f s)
    (step : BBProcess d f policy s t) : bbGlobalBound f s ≤ bbGlobalBound f t := by
  cases step with
  | @empty pre post b inc he =>
    simpa using bb_global_replace_mono f pre post [] b inc inc (min_le_left _ _) (by simp)
  | @unbounded pre post b inc hu =>
    simpa using bb_global_replace_mono f pre post [] b inc inc (min_le_left _ _) (by simp)
  | @unattained pre post b inc hne hbelow hbad =>
    simpa using bb_global_replace_mono f pre post [] b inc inc (min_le_left _ _) (by simp)
  | @prune pre post b inc q hq hp =>
    simpa using bb_global_replace_mono f pre post [] b inc inc (min_le_left _ _) (by simp)
  | @integral pre post b inc q hq hkeep hi =>
    have hgq : bbGlobalBound f ⟨pre ++ b :: post, inc⟩ ≤ bbValue (f q) := by
      apply (bb_global_le_record f _ b (by simp)).trans
      simpa [bbValue] using h.bounds b (by simp) q hq.1
    have hinc : bbGlobalBound f ⟨pre ++ b :: post, inc⟩ ≤
        bbIncBound f (bbUpdate policy f inc q) := by
      rw [bb_update_inc_bound]
      exact le_min (min_le_left _ _) hgq
    simpa using bb_global_replace_mono f pre post [] b inc (bbUpdate policy f inc q)
      hinc (by simp)
  | @branch pre post b inc q i hq hkeep hfrac =>
    apply bb_global_replace_mono f pre post (bbChildren b i q f) b inc inc (min_le_left _ _)
    intro c hc
    simp only [bbChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
    have hh : bbGlobalBound f ⟨pre ++ b :: post, inc⟩ ≤
        ((max b.lower (f q : WithBot ℝ)) : BBGlobalBound) := by
      apply (bb_global_le_record f _ b (by simp)).trans
      exact_mod_cast le_max_left b.lower (f q : WithBot ℝ)
    rcases hc with rfl | rfl <;> exact hh

theorem bb_process_incumbent_bound_nonincreasing (d : ModelData n m l r)
    (f : Point n m → ℝ) (policy : BBPolicy) {s t : BBState n m}
    (step : BBProcess d f policy s t) : bbIncBound f t.incumbent ≤ bbIncBound f s.incumbent := by
  cases step with
  | empty _ => exact le_rfl
  | unbounded _ => exact le_rfl
  | unattained _ _ _ => exact le_rfl
  | prune _ _ => exact le_rfl
  | integral _ _ _ => exact (bb_update_inc_bound _ _ _ _).trans_le (min_le_left _ _)
  | branch _ _ _ _ => exact le_rfl

theorem bb_initial_global_bound (d : ModelData n m l r) (f : Point n m → ℝ)
    (warm : Option (Point n m)) : bbGlobalBound f (bbInitial d warm) = ⊥ := by
  simp [bbGlobalBound, bbLiveBound, bbInitial]

theorem bb_initial_potential (d : ModelData n m l r) (warm : Option (Point n m)) :
    bbPotential (bbInitial d warm) = (bbRootNode d).weight := by
  simp [bbPotential, bbInitial]

theorem bb_empty_live_global_bound (f : Point n m → ℝ) (s : BBState n m)
    (h : s.live = []) : bbGlobalBound f s = bbIncBound f s.incumbent := by
  simp [bbGlobalBound, h, bbLiveBound]

theorem bb_reachable_global_bound_sound (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi)) {s : BBState n m}
    (hs : BBReachable d f policy warm s) (p : Point n m) (hp : p ∈ d.feasibleOn Set.univ) :
    bbGlobalBound f s ≤ bbValue (f p) :=
  bb_global_bound_sound d f s (bb_reachable_invariant d f policy warm hwarm hbase hg hf hs) p hp

theorem bb_reachable_empty_live_optimal (d : ModelData n m l r) (f : Point n m → ℝ)
    (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi)) {s : BBState n m}
    (hs : BBReachable d f policy warm s) (he : s.live = [])
    (q : Point n m) (hq : s.incumbent = some q) :
    IsMinimizer (d.feasibleOn Set.univ) f q :=
  bb_empty_live_incumbent_optimal d f s
    (bb_reachable_invariant d f policy warm hwarm hbase hg hf hs) he q hq

theorem bb_reachable_empty_live_infeasible (d : ModelData n m l r)
    (f : Point n m → ℝ) (policy : BBPolicy) (warm : Option (Point n m))
    (hwarm : ∀ p, warm = some p → p ∈ d.feasibleOn Set.univ)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi)) {s : BBState n m}
    (hs : BBReachable d f policy warm s) (he : s.live = []) (hi : s.incumbent = none) :
    d.feasibleOn Set.univ = ∅ :=
  bb_empty_live_no_incumbent_infeasible d f s
    (bb_reachable_invariant d f policy warm hwarm hbase hg hf hs) he hi

end Chapter02



#print axioms Chapter02.bb_value_le_value
#print axioms Chapter02.bb_update_selects
#print axioms Chapter02.bb_update_below_new
#print axioms Chapter02.bb_update_preserves_below
#print axioms Chapter02.bb_update_inc_bound
#print axioms Chapter02.bb_prunable_has_incumbent
#print axioms Chapter02.bb_le_live_bound_iff
#print axioms Chapter02.bb_le_global_bound_iff
#print axioms Chapter02.bb_global_le_record
#print axioms Chapter02.bb_global_le_incumbent
#print axioms Chapter02.bb_potential_eq_zero_iff
#print axioms Chapter02.bb_initial_invariant
#print axioms Chapter02.bb_invariant_replace
#print axioms Chapter02.bb_invariant_delete
#print axioms Chapter02.bb_process_preserves_invariant
#print axioms Chapter02.bb_reachable_invariant
#print axioms Chapter02.bb_global_bound_sound
#print axioms Chapter02.bb_empty_live_incumbent_optimal
#print axioms Chapter02.bb_empty_live_no_incumbent_infeasible
#print axioms Chapter02.bb_delete_potential_drop
#print axioms Chapter02.bb_branch_potential_drop
#print axioms Chapter02.bb_process_potential_drop
#print axioms Chapter02.bb_global_replace_mono
#print axioms Chapter02.bb_process_global_bound_mono
#print axioms Chapter02.bb_process_incumbent_bound_nonincreasing
#print axioms Chapter02.bb_initial_global_bound
#print axioms Chapter02.bb_initial_potential
#print axioms Chapter02.bb_empty_live_global_bound
#print axioms Chapter02.bb_reachable_global_bound_sound
#print axioms Chapter02.bb_reachable_empty_live_optimal
#print axioms Chapter02.bb_reachable_empty_live_infeasible
