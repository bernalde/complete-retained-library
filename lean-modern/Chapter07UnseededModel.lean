module

public import Chapter07Auxiliary

@[expose] public section

/-!
Initialization and retained-anchor geometry for the qualified Chapter 7 driver.
The continuous initializer is an actual relaxation minimum. Generic master
lemmas allow an arbitrary cut anchor; that freedom does not identify an
arbitrary anchor with the source initializer. The two-anchor level retains the
initial cuts while using a separately stored feasible incumbent baseline.
-/
noncomputable section
open Set Chapter02 Chapter06.Level
namespace Chapter07.Unseeded

variable {n m l r : ℕ} {d : Data n m l r}

def relaxation (d : Data n m l r) : Set (Point n m) :=
  {q | q ∈ d.hard ∧ ∀ j, d.g j q ≤ 0}

theorem original_subset_relaxation : d.original ⊆ relaxation d :=
  fun _ h => ⟨h.1.1, h.2⟩

/-- The hard-empty boundary is outside `Regularity`, whose hard domain is
nonempty. No inconsistent regularity premise is used for this case. -/
theorem hard_empty_relaxation_empty (hh : ¬ d.hard.Nonempty) :
    ¬ (relaxation d).Nonempty := by
  rintro ⟨q, hq⟩
  exact hh ⟨q, hq.1⟩

theorem relaxation_empty_original_empty (he : ¬ (relaxation d).Nonempty) :
    ¬ d.original.Nonempty := by
  rintro ⟨q, hq⟩
  exact he ⟨q, original_subset_relaxation hq⟩

theorem hard_empty_original_empty (hh : ¬ d.hard.Nonempty) :
    ¬ d.original.Nonempty :=
  relaxation_empty_original_empty (hard_empty_relaxation_empty hh)

theorem relaxation_compact (hr : Regularity d) : IsCompact (relaxation d) := by
  have hc : IsClosed {q : Point n m | ∀ j, d.g j q ≤ 0} := by
    have he : {q : Point n m | ∀ j, d.g j q ≤ 0} =
        ⋂ j, {q : Point n m | d.g j q ≤ 0} := by
      ext q
      simp
    rw [he]
    exact isClosed_iInter fun j =>
      isClosed_le (hr.constraint_C1 j).continuous continuous_const
  exact hr.hard_compact.inter_right hc

theorem relaxation_attained (hr : Regularity d) (hne : (relaxation d).Nonempty) :
    ∃ a, IsMinimizer (relaxation d) d.f a :=
  compact_feasible_attainment (relaxation_compact hr) hne
    hr.objective_C1.continuous.continuousOn

theorem relaxation_empty_or_attained (hr : Regularity d) :
    (¬ (relaxation d).Nonempty) ∨ ∃ a, IsMinimizer (relaxation d) d.f a := by
  by_cases h : (relaxation d).Nonempty
  · exact Or.inr (relaxation_attained hr h)
  · exact Or.inl h

/-- The initial objective tangent ensures a nonempty finite envelope, even
before any event has been processed. Its epigraph projects exactly to its base. -/
theorem master_nonempty_iff (a0 : Point n m) (H : List (Event d)) :
    (master d a0 H).Nonempty ↔ (masterBase d a0 H).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, hp.1⟩
  · rintro ⟨q, hq⟩
    obtain ⟨beta, hb⟩ := (psc_envelope_epigraph_projection
      (masterBase d a0 H) (tangent d.f) a0 (H.map Event.anchor) q).mpr hq
    exact ⟨(q, beta), hb⟩

theorem master_attained_of_nonempty (hr : Regularity d) (a0 : Point n m)
    (H : List (Event d)) (hne : (master d a0 H).Nonempty) :
    ∃ p, IsMinimizer (master d a0 H) Prod.snd p := by
  obtain ⟨p, hp⟩ := psc_envelope_epigraph_attainment
    (masterBase d a0 H) (tangent d.f) (origins a0 H) (fun _ => 0)
    (by simp [origins]) (masterBase_compact hr a0 H)
    ((master_nonempty_iff a0 H).mp hne) continuous_const.continuousOn
    (fun a _ => (tangent_continuous d.f a).continuousOn)
  exact ⟨p, by simpa only [IsMinimizer, master, pscEnvelopeObjective, zero_add] using hp⟩

/-- Exhaustive actual outcome; no positivity of the integer-target count is
required. An empty physical mixed set gives the empty first master. -/
theorem master_empty_or_attained (hr : Regularity d) (a0 : Point n m)
    (H : List (Event d)) :
    (¬ (master d a0 H).Nonempty) ∨ ∃ p, IsMinimizer (master d a0 H) Prod.snd p := by
  by_cases h : (master d a0 H).Nonempty
  · exact Or.inr (master_attained_of_nonempty hr a0 H h)
  · exact Or.inl h

theorem mixed_empty_master_empty (a0 : Point n m) (H : List (Event d))
    (hm : ¬ d.mixed.Nonempty) : ¬ (master d a0 H).Nonempty := by
  rintro ⟨p, hp⟩
  exact hm ⟨p.1, hp.1.1⟩

/-- A nonempty continuous relaxation need not provide any integer target.
The zero-target boundary yields a genuinely empty master, not fuel exhaustion. -/
theorem zero_targets_master_empty (hr : Regularity d) (a0 : Point n m)
    (H : List (Event d)) (hN : (targets d hr).card = 0) :
    ¬ (master d a0 H).Nonempty := by
  rintro ⟨p, hp⟩
  obtain ⟨y, hy⟩ := hp.1.1.2
  have hym : y ∈ targets d hr :=
    (mem_targets d hr y).mpr ⟨p.1, hp.1.1.1, hy⟩
  have hpos := Finset.card_pos.mpr ⟨y, hym⟩
  omega

theorem master_empty_original_empty (hr : Regularity d) {a0 : Point n m}
    {H : List (Event d)} (he : ¬ (master d a0 H).Nonempty) :
    ¬ d.original.Nonempty := by
  rintro ⟨q, hq⟩
  exact he ⟨(q, d.f q), original_in_master hr a0 H hq⟩

theorem master_attained_of_feasible (hr : Regularity d) {u : Point n m}
    (hu : u ∈ d.original) (a0 : Point n m) (H : List (Event d)) :
    ∃ p, IsMinimizer (master d a0 H) Prod.snd p :=
  master_attained_of_nonempty hr a0 H ⟨(u, d.f u), original_in_master hr a0 H hu⟩

/-- The retained master anchor and the feasible incumbent baseline are distinct
parameters. In particular, neither the initial tangent nor old events are reset. -/
def level (d : Data n m l r) (a0 u : Point n m) (H : List (Event d))
    (LB alpha : ℝ) : Set (Point n m × ℝ) :=
  Auxiliary.cappedMaster d a0 H (Chapter06.Level LB (d.f (incumbent d u H)) alpha)

theorem level_available (hr : Regularity d) {a0 u : Point n m}
    (hu : u ∈ d.original) {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d a0 H) Prod.snd p) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) : p ∈ level d a0 u H p.2 alpha :=
  Chapter06.master_candidate_satisfies_level _ p p.2 (d.f (incumbent d u H))
    alpha hp.1 rfl (master_lower_bound hr hp (incumbent_original hu H)) ha ha1

theorem level_nonempty (hr : Regularity d) {a0 u : Point n m}
    (hu : u ∈ d.original) {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d a0 H) Prod.snd p) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) : (level d a0 u H p.2 alpha).Nonempty :=
  ⟨p, level_available hr hu hp ha ha1⟩

theorem level_compact (hr : Regularity d) {a0 u : Point n m}
    {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d a0 H) Prod.snd p) (alpha : ℝ) :
    IsCompact (level d a0 u H p.2 alpha) :=
  Auxiliary.cappedMaster_compact hr hp
    (Chapter06.Level p.2 (d.f (incumbent d u H)) alpha)

theorem physical_minimum_attained (hr : Regularity d) {a0 u : Point n m}
    (hu : u ∈ d.original) {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d a0 H) Prod.snd p) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (phi : Point n m → ℝ)
    (hphi : Continuous phi) :
    ∃ q, IsMinimizer (level d a0 u H p.2 alpha) (fun z => phi z.1) q :=
  compact_feasible_attainment (level_compact hr hp alpha)
    (level_nonempty hr hu hp ha ha1) (hphi.comp continuous_fst).continuousOn

/-- Restoration-only prefix exclusion needs no incumbent or level bound. -/
theorem master_excludes_restored (hr : Regularity d) {a0 : Point n m}
    {H : List (Event d)} {p : Point n m × ℝ} {e : Event d}
    (hp : p ∈ master d a0 H) (he : e ∈ H) (hrest : e.slack ≠ none) :
    p.1.2 ≠ intCast e.target := by
  intro hy
  have hv := e.valid
  cases hs : e.slack with
  | none => exact hrest hs
  | some rho =>
    rw [hs] at hv
    have hrows : selectedRows d e.anchor rho p.1 := by
      simpa [Event.rho, hs] using hp.1.2.2 e he
    exact restoration_selected_excludes d hr e.target hv.1 hv.2
      ⟨hp.1.1.1, hy⟩ hrows

/-- The two-anchor positive-gap level excludes every old target. The feasible
baseline is needed for availability/correct return, not this exclusion step. -/
theorem level_excludes_processed (hr : Regularity d) {a0 u : Point n m}
    {H : List (Event d)} {LB alpha : ℝ} {q : Point n m × ℝ}
    (hq : q ∈ level d a0 u H LB alpha)
    (hgap : LB < d.f (incumbent d u H)) (ha : 0 < alpha)
    {e : Event d} (he : e ∈ H) : q.1.2 ≠ intCast e.target := by
  intro hy
  have hfiber : q.1 ∈ d.hardFiber e.target := ⟨hq.1.1.1.1, hy⟩
  have hrows := hq.1.1.2.2 e he
  have hv := e.valid
  cases hs : e.slack with
  | none =>
    rw [hs] at hv
    have hrows0 : selectedRows d e.anchor 0 q.1 := by
      simpa [Event.rho, hs] using hrows
    have hlower := feasible_selected_lower d hr e.target hv hfiber hrows0
    have hobj := master_event_objective hq.1 he
    exact Chapter06.level_excludes_old_fiber (d.f e.anchor) q.2 LB
      (d.f (incumbent d u H)) alpha (hlower.trans hobj)
      (incumbent_le_event u he hs) hq.2 hgap ha
  | some rho =>
    exact (master_excludes_restored hr hq.1 he (by rw [hs]; simp)) hy

end Chapter07.Unseeded

#print axioms Chapter07.Unseeded.original_subset_relaxation
#print axioms Chapter07.Unseeded.hard_empty_relaxation_empty
#print axioms Chapter07.Unseeded.relaxation_empty_original_empty
#print axioms Chapter07.Unseeded.hard_empty_original_empty
#print axioms Chapter07.Unseeded.relaxation_compact
#print axioms Chapter07.Unseeded.relaxation_attained
#print axioms Chapter07.Unseeded.relaxation_empty_or_attained
#print axioms Chapter07.Unseeded.master_nonempty_iff
#print axioms Chapter07.Unseeded.master_attained_of_nonempty
#print axioms Chapter07.Unseeded.master_empty_or_attained
#print axioms Chapter07.Unseeded.mixed_empty_master_empty
#print axioms Chapter07.Unseeded.zero_targets_master_empty
#print axioms Chapter07.Unseeded.master_empty_original_empty
#print axioms Chapter07.Unseeded.master_attained_of_feasible
#print axioms Chapter07.Unseeded.level_available
#print axioms Chapter07.Unseeded.level_nonempty
#print axioms Chapter07.Unseeded.level_compact
#print axioms Chapter07.Unseeded.physical_minimum_attained
#print axioms Chapter07.Unseeded.master_excludes_restored
#print axioms Chapter07.Unseeded.level_excludes_processed
