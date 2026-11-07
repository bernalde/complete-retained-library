module

public import Chapter06LevelExecution

@[expose] public section

/-!
Actual auxiliary attainment on the full capped OA epigraph. Compactness permits
an arbitrary initial linearization anchor. The seeded selector separately uses
a stored original-feasible point to prove nonemptiness. No successful auxiliary
oracle, finite-progress premise or numerical solver specification is assumed.
-/
noncomputable section
open Set Chapter02 Chapter06.Level
namespace Chapter07.Auxiliary

variable {n m l r : ℕ} {d : Data n m l r}

def cappedMaster (d : Data n m l r) (anchor : Point n m)
    (H : List (Event d)) (cap : ℝ) : Set (Point n m × ℝ) :=
  {z ∈ master d anchor H | z.2 ≤ cap}

theorem master_closed (hr : Regularity d) (anchor : Point n m)
    (H : List (Event d)) : IsClosed (master d anchor H) := by
  have hrows : IsClosed {z : Point n m × ℝ |
      ∀ a ∈ origins anchor H, tangent d.f a z.1 ≤ z.2} := by
    have he : {z : Point n m × ℝ |
        ∀ a ∈ origins anchor H, tangent d.f a z.1 ≤ z.2} =
        ⋂ a, ⋂ (_ : a ∈ origins anchor H),
          {z : Point n m × ℝ | tangent d.f a z.1 ≤ z.2} := by
      ext z
      simp
    rw [he]
    exact isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_le ((tangent_continuous d.f a).comp continuous_fst) continuous_snd
  exact ((masterBase_compact hr anchor H).isClosed.preimage continuous_fst).inter hrows

theorem cappedMaster_closed (hr : Regularity d) (anchor : Point n m)
    (H : List (Event d)) (cap : ℝ) : IsClosed (cappedMaster d anchor H cap) :=
  (master_closed hr anchor H).inter (isClosed_le continuous_snd continuous_const)

/-- The lower height bound comes from actual master optimality. The uncapped
master is not asserted compact. No feasible-anchor premise is needed here. -/
theorem cappedMaster_compact (hr : Regularity d) {anchor : Point n m}
    {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d anchor H) Prod.snd p) (cap : ℝ) :
    IsCompact (cappedMaster d anchor H cap) := by
  apply ((masterBase_compact hr anchor H).prod
    (isCompact_Icc : IsCompact (Icc p.2 cap))).of_isClosed_subset
    (cappedMaster_closed hr anchor H cap)
  intro z hz
  exact ⟨hz.1.1, hp.2 z hz.1, hz.2⟩

theorem levelSet_compact (hr : Regularity d) {seed : Point n m}
    {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d seed H) Prod.snd p) (alpha : ℝ) :
    IsCompact (levelSet d seed H p.2 alpha) :=
  cappedMaster_compact hr hp (Chapter06.Level p.2 (d.f (incumbent d seed H)) alpha)

theorem levelSet_nonempty (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d seed H) Prod.snd p) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    (levelSet d seed H p.2 alpha).Nonempty :=
  ⟨p, level_available hr hs hp ha ha1⟩

/-- Every continuous physical objective attains over the complete capped
physical/height set, for every history and every actual master minimum. -/
theorem physical_minimum_attained (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d seed H) Prod.snd p) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (phi : Point n m → ℝ)
    (hphi : Continuous phi) :
    ∃ q, IsMinimizer (levelSet d seed H p.2 alpha) (fun z => phi z.1) q :=
  compact_feasible_attainment (levelSet_compact hr hp alpha)
    (levelSet_nonempty hr hs hp ha ha1) (hphi.comp continuous_fst).continuousOn

def minimizer (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (ranking : List (Event d) → Point n m → ℝ)
    (hc : ∀ H, Continuous (ranking H)) (H : List (Event d))
    (p : Point n m × ℝ) (hp : IsMinimizer (master d seed H) Prod.snd p) :
    {q // IsMinimizer (levelSet d seed H p.2 alpha) (fun z => ranking H z.1) q} :=
  ⟨Classical.choose (physical_minimum_attained hr hs hp ha ha1 (ranking H) (hc H)),
    Classical.choose_spec (physical_minimum_attained hr hs hp ha ha1 (ranking H) (hc H))⟩

/-- A constructed exact mathematical selector. Its auxiliary is an attained
minimum rather than an assumed successful chooser. Return correctness is the
existing Chapter 6 theorem; this definition introduces no new progress proof. -/
def selector (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (ranking : List (Event d) → Point n m → ℝ)
    (hc : ∀ H, Continuous (ranking H)) : Exec.Selector d seed alpha :=
  Exec.withAuxiliary (Exec.exactSelector hr hs ha ha1)
    (fun H z => ranking H z.1) (minimizer hr hs ha ha1 ranking hc)

theorem selector_trial_minimizer (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (ranking : List (Event d) → Point n m → ℝ)
    (hc : ∀ H, Continuous (ranking H)) (H : List (Event d))
    (p : Point n m × ℝ) (hp : IsMinimizer (master d seed H) Prod.snd p) :
    IsMinimizer (levelSet d seed H p.2 alpha) (fun z => ranking H z.1)
      ((selector hr hs ha ha1 ranking hc).trial H p hp).val :=
  (minimizer hr hs ha ha1 ranking hc H p hp).property

end Chapter07.Auxiliary

#print axioms Chapter07.Auxiliary.master_closed
#print axioms Chapter07.Auxiliary.cappedMaster_closed
#print axioms Chapter07.Auxiliary.cappedMaster_compact
#print axioms Chapter07.Auxiliary.levelSet_compact
#print axioms Chapter07.Auxiliary.levelSet_nonempty
#print axioms Chapter07.Auxiliary.physical_minimum_attained
#print axioms Chapter07.Auxiliary.selector_trial_minimizer
