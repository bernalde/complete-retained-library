module

public import Chapter06LevelFiber
public import Chapter02PSCEnvelope

@[expose] public section

/-!
Seeded literal outer-approximation history for the qualified Chapter 6 driver.
The supplied feasible seed need not solve its fiber. Events retain actual
fixed-fiber minima; support and exclusion are derived, not event premises.
-/
noncomputable section
open Set Chapter02
namespace Chapter06.Level

variable {n m l r : ℕ} {d : Data n m l r}

/-- A processed fiber event. `none` is an actual nonlinear-f minimum; `some rho`
is an actual minimum of the literal nonnegative common-slack restoration. -/
structure Event (d : Data n m l r) where
  target : IntVector m
  anchor : Point n m
  slack : Option ℝ
  valid : match slack with
    | none => IsMinimizer (d.feasibleFiber target) d.f anchor
    | some rho => ¬ (d.feasibleFiber target).Nonempty ∧
        IsMinimizer (d.restoration target) Prod.snd (anchor, rho)

def Event.rho (e : Event d) : ℝ := e.slack.getD 0

def keepBetter (d : Data n m l r) (old new : Point n m) : Point n m :=
  if d.f new < d.f old then new else old

/-- Histories are stored newest first. Restoration events never change the
stored feasible incumbent. -/
def incumbent (d : Data n m l r) (seed : Point n m) : List (Event d) → Point n m
  | [] => seed
  | e :: H => match e.slack with
      | none => keepBetter d (incumbent d seed H) e.anchor
      | some _ => incumbent d seed H

theorem keepBetter_mem (old new : Point n m) :
    keepBetter d old new = old ∨ keepBetter d old new = new := by
  unfold keepBetter
  split_ifs <;> simp

theorem keepBetter_le_old (old new : Point n m) :
    d.f (keepBetter d old new) ≤ d.f old := by
  unfold keepBetter
  split_ifs with h
  · exact le_of_lt h
  · exact le_rfl

theorem keepBetter_le_new (old new : Point n m) :
    d.f (keepBetter d old new) ≤ d.f new := by
  unfold keepBetter
  split_ifs with h
  · exact le_rfl
  · exact le_of_not_gt h

theorem incumbent_cons_le (seed : Point n m) (e : Event d) (H : List (Event d)) :
    d.f (incumbent d seed (e :: H)) ≤ d.f (incumbent d seed H) := by
  cases he : e.slack with
  | none => simpa [incumbent, he] using keepBetter_le_old (incumbent d seed H) e.anchor
  | some rho => simp [incumbent, he]

theorem incumbent_le_seed (seed : Point n m) (H : List (Event d)) :
    d.f (incumbent d seed H) ≤ d.f seed := by
  induction H with
  | nil => exact le_rfl
  | cons e H ih => exact (incumbent_cons_le seed e H).trans ih

theorem incumbent_le_event (seed : Point n m) {H : List (Event d)}
    {e : Event d} (he : e ∈ H) (hf : e.slack = none) :
    d.f (incumbent d seed H) ≤ d.f e.anchor := by
  induction H with
  | nil => simp at he
  | cons a H ih =>
    rcases List.mem_cons.mp he with rfl | he
    · simpa [incumbent, hf] using keepBetter_le_new (incumbent d seed H) e.anchor
    · exact (incumbent_cons_le seed a H).trans (ih he)

theorem incumbent_provenance (seed : Point n m) (H : List (Event d)) :
    incumbent d seed H = seed ∨
      ∃ e ∈ H, e.slack = none ∧ incumbent d seed H = e.anchor := by
  induction H with
  | nil => exact Or.inl rfl
  | cons e H ih =>
    cases he : e.slack with
    | some rho =>
      simpa only [incumbent, he] using ih.imp id (by
        rintro ⟨a, ha, hf, hx⟩
        exact ⟨a, List.mem_cons_of_mem e ha, hf, hx⟩)
    | none =>
      rcases keepBetter_mem (d := d) (incumbent d seed H) e.anchor with h | h
      · have hx : incumbent d seed (e :: H) = incumbent d seed H := by
          simpa [incumbent, he] using h
        rcases ih with ih | ⟨a, ha, hf, haeq⟩
        · exact Or.inl (hx.trans ih)
        · exact Or.inr ⟨a, List.mem_cons_of_mem e ha, hf, hx.trans haeq⟩
      · exact Or.inr ⟨e, List.mem_cons_self, he, by simpa [incumbent, he] using h⟩

/-- The initial tangent is retained even when the seed is not a fixed-fiber
minimum. Every processed event contributes all its selected nonlinear rows. -/
def masterBase (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :
    Set (Point n m) :=
  {q | q ∈ d.mixed ∧ selectedRows d seed 0 q ∧
    ∀ e ∈ H, selectedRows d e.anchor e.rho q}

def origins (seed : Point n m) (H : List (Event d)) : List (Point n m) :=
  seed :: H.map Event.anchor

/-- The epigraph height is not bounded above. Attainment is obtained from the
finite continuous envelope on `masterBase`, rather than height compactness. -/
def master (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :
    Set (Point n m × ℝ) :=
  pscEnvelopeEpigraph (masterBase d seed H) (tangent d.f) (origins seed H)

def levelSet (d : Data n m l r) (seed : Point n m) (H : List (Event d))
    (LB alpha : ℝ) : Set (Point n m × ℝ) :=
  {z ∈ master d seed H | z.2 ≤ Chapter06.Level LB (d.f (incumbent d seed H)) alpha}

theorem Event.feasible_original (e : Event d) (he : e.slack = none) :
    e.anchor ∈ d.original := by
  have hv := e.valid
  rw [he] at hv
  exact feasibleFiber_original d e.target hv.1

theorem Event.hardFiber (e : Event d) : e.anchor ∈ d.hardFiber e.target := by
  have hv := e.valid
  cases he : e.slack with
  | none => rw [he] at hv; exact hv.1.1
  | some rho => rw [he] at hv; exact hv.2.1.1

theorem Event.target_mem (hr : Regularity d) (e : Event d) :
    e.target ∈ targets d hr :=
  (mem_targets d hr e.target).mpr ⟨e.anchor, e.hardFiber.1, e.hardFiber.2⟩

theorem incumbent_original {seed : Point n m} (hs : seed ∈ d.original)
    (H : List (Event d)) : incumbent d seed H ∈ d.original := by
  rcases incumbent_provenance seed H with he | ⟨e, _, hf, he⟩
  · simpa [he] using hs
  · simpa [he] using e.feasible_original hf

theorem masterBase_compact (hr : Regularity d) (seed : Point n m)
    (H : List (Event d)) : IsCompact (masterBase d seed H) := by
  have hc : IsClosed {q | ∀ e ∈ H, selectedRows d e.anchor e.rho q} := by
    have he : {q | ∀ e ∈ H, selectedRows d e.anchor e.rho q} =
        ⋂ e, ⋂ (_ : e ∈ H), {q | selectedRows d e.anchor e.rho q} := by
      ext q
      simp
    rw [he]
    exact isClosed_iInter fun e => isClosed_iInter fun _ =>
      selectedRows_closed d e.anchor e.rho
  exact (mixed_compact d hr).inter_right ((selectedRows_closed d seed 0).inter hc)

theorem original_in_masterBase (hr : Regularity d) (seed : Point n m)
    (H : List (Event d)) {q : Point n m} (hq : q ∈ d.original) :
    q ∈ masterBase d seed H :=
  ⟨hq.1, selectedRows_original d hr seed 0 hq,
    fun e _ => selectedRows_original d hr e.anchor e.rho hq⟩

theorem original_in_master (hr : Regularity d) (seed : Point n m)
    (H : List (Event d)) {q : Point n m} (hq : q ∈ d.original) :
    (q, d.f q) ∈ master d seed H := by
  refine ⟨original_in_masterBase hr seed H hq, ?_⟩
  intro a _
  exact tangent_support hr.objective_convex hr.objective_C1 a q

theorem master_attained (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) (H : List (Event d)) :
    ∃ p, IsMinimizer (master d seed H) Prod.snd p := by
  obtain ⟨p, hp⟩ := psc_envelope_epigraph_attainment
    (masterBase d seed H) (tangent d.f) (origins seed H) (fun _ => 0)
    (by simp [origins]) (masterBase_compact hr seed H)
    ⟨seed, original_in_masterBase hr seed H hs⟩ continuous_const.continuousOn
    (fun a _ => (tangent_continuous d.f a).continuousOn)
  exact ⟨p, by simpa only [IsMinimizer, master, pscEnvelopeObjective, zero_add] using hp⟩

theorem master_lower_bound (hr : Regularity d) {seed : Point n m}
    {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d seed H) Prod.snd p)
    {q : Point n m} (hq : q ∈ d.original) : p.2 ≤ d.f q :=
  hp.2 (q, d.f q) (original_in_master hr seed H hq)

theorem level_available (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d seed H) Prod.snd p)
    {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    p ∈ levelSet d seed H p.2 alpha :=
  Chapter06.master_candidate_satisfies_level _ p p.2 (d.f (incumbent d seed H))
    alpha hp.1 rfl (master_lower_bound hr hp (incumbent_original hs H)) ha ha1

theorem master_event_objective {seed : Point n m} {H : List (Event d)}
    {p : Point n m × ℝ} (hp : p ∈ master d seed H) {e : Event d} (he : e ∈ H) :
    tangent d.f e.anchor p.1 ≤ p.2 :=
  hp.2 e.anchor (List.mem_cons_of_mem seed (List.mem_map.mpr ⟨e, he, rfl⟩))

/-- Inserting the internally derived integer box preserves the literal master
including its unbounded epigraph coordinate and every retained source row. -/
def boxedMaster (d : Data n m l r) (hr : Regularity d) (seed : Point n m)
    (H : List (Event d)) : Set (Point n m × ℝ) :=
  {z | z.1 ∈ (boxedModel d hr).linearRegion ∩
      IntegerCylinder (n := n) (boxedModel d hr).lo (boxedModel d hr).hi ∧
    selectedRows d seed 0 z.1 ∧ (∀ e ∈ H, selectedRows d e.anchor e.rho z.1) ∧
    pscEnvelopeRows (tangent d.f) (origins seed H) z.1 z.2}

theorem boxedMaster_eq (hr : Regularity d) (seed : Point n m) (H : List (Event d)) :
    boxedMaster d hr seed H = master d seed H := by
  rw [boxedMaster, boxed_restriction_eq]
  ext z
  simp only [master, pscEnvelopeEpigraph, masterBase, Set.mem_setOf_eq, and_assoc]

theorem boxedLevel_eq (hr : Regularity d) (seed : Point n m) (H : List (Event d))
    (LB alpha : ℝ) :
    {z ∈ boxedMaster d hr seed H |
      z.2 ≤ Chapter06.Level LB (d.f (incumbent d seed H)) alpha} =
      levelSet d seed H LB alpha := by rw [boxedMaster_eq]; rfl

/-- Every previously processed feasible fiber carries an actual original-f
minimum, and every restoration fiber carries its actual positive-slack row.
The arbitrary seed alone is deliberately absent from this exclusion claim. -/
theorem level_excludes_processed (hr : Regularity d) {seed : Point n m}
    {H : List (Event d)} {LB alpha : ℝ} {q : Point n m × ℝ}
    (hq : q ∈ levelSet d seed H LB alpha)
    (hgap : LB < d.f (incumbent d seed H)) (ha : 0 < alpha)
    {e : Event d} (he : e ∈ H) : q.1.2 ≠ intCast e.target := by
  intro hy
  have hfiber : q.1 ∈ d.hardFiber e.target := ⟨hq.1.1.1.1, hy⟩
  have hrows := hq.1.1.2.2 e he
  have hv := e.valid
  cases hslack : e.slack with
  | none =>
    rw [hslack] at hv
    have hrows0 : selectedRows d e.anchor 0 q.1 := by
      simpa [Event.rho, hslack] using hrows
    have hlower := feasible_selected_lower d hr e.target hv hfiber hrows0
    have hobj := master_event_objective hq.1 he
    exact Chapter06.level_excludes_old_fiber (d.f e.anchor) q.2 LB
      (d.f (incumbent d seed H)) alpha (hlower.trans hobj)
      (incumbent_le_event seed he hslack) hq.2 hgap ha
  | some rho =>
    rw [hslack] at hv
    have hrowsR : selectedRows d e.anchor rho q.1 := by
      simpa [Event.rho, hslack] using hrows
    exact restoration_selected_excludes d hr e.target hv.1 hv.2 hfiber hrowsR

theorem history_target_bound (hr : Regularity d) {H : List (Event d)}
    (hn : (H.map Event.target).Nodup) : H.length ≤ (targets d hr).card := by
  classical
  have hsub : (H.map Event.target).toFinset ⊆ targets d hr := by
    intro y hy
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact e.target_mem hr
  calc
    H.length = (H.map Event.target).length := (List.length_map _).symm
    _ = (H.map Event.target).toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ ≤ (targets d hr).card := Finset.card_le_card hsub

end Chapter06.Level
