module

public import Chapter07UnseededExecution
public import Chapter07SevenRankings

@[expose] public section

/-! Actual current-incumbent rankings for the initialized unseeded driver.
The original master anchor remains fixed. Each state's auxiliary minimum retains
its own certificate. Arbitrary supplied nonnegative weights give generalized
rankings; source KKT labels additionally require polished-fiber provenance. -/
noncomputable section
open Set Chapter02 Chapter06.Level
namespace Chapter07.UnseededRankings
open UnseededExec

variable {n m l r : ℕ} {d : Data n m l r}

/-- The two anchors and the ranking centre are independent for attainment. -/
theorem seven_level_attained (hr : Regularity d) {a0 u : Point n m}
    (hu : u ∈ d.original) {H : List (Event d)} {p : Point n m × ℝ}
    (hp : IsMinimizer (master d a0 H) Prod.snd p) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (lambda : Fin l → ℝ) (mu : Fin r → ℝ) (a : Point n m)
    (rho : ℝ) (kind : SevenRankings.Kind) :
    IsCompact (Unseeded.level d a0 u H p.2 alpha) ∧
      (Unseeded.level d a0 u H p.2 alpha).Nonempty ∧
      ∃ q, IsMinimizer (Unseeded.level d a0 u H p.2 alpha)
        (fun z => SevenRankings.ranking d lambda mu a rho kind z.1) q :=
  ⟨Unseeded.level_compact hr hp alpha, Unseeded.level_nonempty hr hu hp ha ha1,
    Unseeded.physical_minimum_attained hr hu hp ha ha1 _
      (SevenRankings.ranking_continuous d lambda mu a rho kind)⟩

/-- The fallback only totalizes prefix states, which use no auxiliary ranking. -/
def stateCentre (a0 : Point n m) (s : State d) : Point n m :=
  match s.baseline with
  | none => a0
  | some u => incumbent d u.val s.history

theorem stateCentre_some (a0 : Point n m) (s : State d)
    (u : {u : Point n m // u ∈ d.original}) (hb : s.baseline = some u) :
    stateCentre a0 s = incumbent d u.val s.history := by
  simp [stateCentre, hb]

def stateRanking (d : Data n m l r) (a0 : Point n m)
    (lambda : State d → Fin l → ℝ) (mu : State d → Fin r → ℝ)
    (rho : State d → ℝ) (kind : State d → SevenRankings.Kind)
    (s : State d) : Point n m → ℝ :=
  SevenRankings.ranking d (lambda s) (mu s) (stateCentre a0 s) (rho s) (kind s)

theorem stateRanking_continuous (a0 : Point n m)
    (lambda : State d → Fin l → ℝ) (mu : State d → Fin r → ℝ)
    (rho : State d → ℝ) (kind : State d → SevenRankings.Kind) (s : State d) :
    Continuous (stateRanking d a0 lambda mu rho kind s) :=
  SevenRankings.ranking_continuous d (lambda s) (mu s) (stateCentre a0 s)
    (rho s) (kind s)

/-- Apply the existing existence theorem separately at this state, with its
current centre fixed in the dummy history argument. No fixed initial centre is
silently substituted in later states. -/
def sevenDecision (hr : Regularity d) (a0 : Point n m)
    {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (lambda : State d → Fin l → ℝ) (mu : State d → Fin r → ℝ)
    (rho : State d → ℝ) (kind : State d → SevenRankings.Kind) (s : State d) :
    RankedDecision d a0 alpha epsilon
      (fun _ => stateRanking d a0 lambda mu rho kind s) s :=
  Classical.choice (ranked_decision_available hr a0 ha ha1
    (fun _ => stateRanking d a0 lambda mu rho kind s)
    (fun _ => stateRanking_continuous a0 lambda mu rho kind s) s)

def sevenSelector (hr : Regularity d) (a0 : Point n m)
    {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (lambda : State d → Fin l → ℝ) (mu : State d → Fin r → ℝ)
    (rho : State d → ℝ) (kind : State d → SevenRankings.Kind) :
    Selector d a0 alpha epsilon :=
  fun s => (sevenDecision hr a0 ha ha1 lambda mu rho kind s).toDecision

theorem sevenSelector_spec (hr : Regularity d) (a0 : Point n m)
    {alpha epsilon : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (lambda : State d → Fin l → ℝ) (mu : State d → Fin r → ℝ)
    (rho : State d → ℝ) (kind : State d → SevenRankings.Kind) (s : State d) :
    RankedLegal a0 alpha epsilon (fun _ => stateRanking d a0 lambda mu rho kind s) s
      (sevenSelector (epsilon := epsilon) hr a0 ha ha1 lambda mu rho kind s).action :=
  (sevenDecision hr a0 ha ha1 lambda mu rho kind s).ranked

/-- Named initialized seven-ranking return, with the actual statewise minimum
certificate, convex physical ranking, and the full generic initialized guarantee.
The mixed-integer level itself is not claimed convex. -/
theorem source_initialized_seven_return (hr : Regularity d)
    (hf2 : ContDiff ℝ 2 d.f) (hg2 : ∀ j, ContDiff ℝ 2 (d.g j))
    (lambda : State d → Fin l → ℝ) (mu : State d → Fin r → ℝ)
    (hl : ∀ s j, 0 ≤ lambda s j) (hm : ∀ s i, 0 ≤ mu s i)
    (rho : State d → ℝ) (hrho : ∀ s, 0 ≤ rho s)
    (kind : State d → SevenRankings.Kind) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon)
    (init : Initialization d) :
    let select := fun a0 => sevenSelector (epsilon := epsilon) hr a0
      (le_of_lt ha) ha1 lambda mu rho kind
    let execution := initializeRun hr init select
    (∀ a0 s, ConvexOn ℝ univ (stateRanking d a0 lambda mu rho kind s)) ∧
      (∀ a0 s, RankedLegal a0 alpha epsilon
        (fun _ => stateRanking d a0 lambda mu rho kind s) s (select a0 s).action) ∧
      Invariant execution.result.state ∧
      (execution.result.state.history.map Event.target).Nodup ∧
      Correct epsilon execution.result.state execution.result.outcome ∧
      execution.result.processed ≤ (targets d hr).card ∧
      execution.result.state.history.length = execution.result.processed ∧
      InitializationCounts init execution.result ∧ execution.initializerInspections = 1 := by
  dsimp only
  refine ⟨?_, ?_, source_initialized_return hr ha heps init _⟩
  · intro a0 s
    exact SevenRankings.ranking_convex d (lambda s) (mu s) hr.objective_convex
      hr.constraint_convex (hl s) (hm s) hf2 hg2 (stateCentre a0 s)
      (rho s) (hrho s) (kind s)
  · exact fun a0 s => sevenSelector_spec hr a0 (le_of_lt ha) ha1 lambda mu rho kind s

theorem source_total_seven_return (hr : Regularity d)
    (hf2 : ContDiff ℝ 2 d.f) (hg2 : ∀ j, ContDiff ℝ 2 (d.g j))
    (lambda : State d → Fin l → ℝ) (mu : State d → Fin r → ℝ)
    (hl : ∀ s j, 0 ≤ lambda s j) (hm : ∀ s i, 0 ≤ mu s i)
    (rho : State d → ℝ) (hrho : ∀ s, 0 ≤ rho s)
    (kind : State d → SevenRankings.Kind) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon) :
    ∃ init : Initialization d, ∃ select : ∀ a0, Selector d a0 alpha epsilon,
      (∀ a0 s, ConvexOn ℝ univ (stateRanking d a0 lambda mu rho kind s)) ∧
      (∀ a0 s, RankedLegal a0 alpha epsilon
        (fun _ => stateRanking d a0 lambda mu rho kind s) s (select a0 s).action) ∧
      let execution := initializeRun hr init select
      Invariant execution.result.state ∧
      (execution.result.state.history.map Event.target).Nodup ∧
      Correct epsilon execution.result.state execution.result.outcome ∧
      execution.result.processed ≤ (targets d hr).card ∧
      execution.result.state.history.length = execution.result.processed ∧
      InitializationCounts init execution.result ∧ execution.initializerInspections = 1 := by
  let init := Classical.choice (initialization_available hr)
  exact ⟨init, fun a0 => sevenSelector hr a0 (le_of_lt ha) ha1 lambda mu rho kind,
    source_initialized_seven_return hr hf2 hg2 lambda mu hl hm rho hrho kind ha ha1 heps init⟩

end Chapter07.UnseededRankings

#print axioms Chapter07.UnseededRankings.seven_level_attained
#print axioms Chapter07.UnseededRankings.stateCentre_some
#print axioms Chapter07.UnseededRankings.sevenSelector_spec
#print axioms Chapter07.UnseededRankings.source_initialized_seven_return
#print axioms Chapter07.UnseededRankings.source_total_seven_return
