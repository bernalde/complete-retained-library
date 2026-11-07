module

public import Chapter07Auxiliary
public import Chapter07SevenRankings

@[expose] public section

/-! The seven actual regularizers supply attained auxiliary selections for the
accepted Chapter6 repaired seeded driver. No progress or successful auxiliary
oracle is assumed. Supplied initial multipliers need not be KKT multipliers. -/
noncomputable section
open Set Chapter02 Chapter06.Level
namespace Chapter07.RegularizedReturn

variable {n m l r : ℕ} {d : Data n m l r}

def historyRanking (d : Data n m l r) (seed : Point n m)
    (lambda : List (Event d) → Fin l → ℝ) (mu : List (Event d) → Fin r → ℝ)
    (rho : List (Event d) → ℝ) (kind : List (Event d) → SevenRankings.Kind)
    (H : List (Event d)) : Point n m → ℝ :=
  SevenRankings.ranking d (lambda H) (mu H) (incumbent d seed H) (rho H) (kind H)

theorem historyRanking_continuous (seed : Point n m)
    (lambda : List (Event d) → Fin l → ℝ) (mu : List (Event d) → Fin r → ℝ)
    (rho : List (Event d) → ℝ) (kind : List (Event d) → SevenRankings.Kind)
    (H : List (Event d)) : Continuous (historyRanking d seed lambda mu rho kind H) :=
  SevenRankings.ranking_continuous d (lambda H) (mu H)
    (incumbent d seed H) (rho H) (kind H)

def selector (hr : Regularity d) {seed : Point n m} (hs : seed ∈ d.original)
    {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (lambda : List (Event d) → Fin l → ℝ) (mu : List (Event d) → Fin r → ℝ)
    (rho : List (Event d) → ℝ) (kind : List (Event d) → SevenRankings.Kind) :
    Exec.Selector d seed alpha :=
  Auxiliary.selector hr hs ha ha1 (historyRanking d seed lambda mu rho kind)
    (historyRanking_continuous seed lambda mu rho kind)

theorem every_auxiliary_minimum (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) {alpha : ℝ} (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (lambda : List (Event d) → Fin l → ℝ) (mu : List (Event d) → Fin r → ℝ)
    (rho : List (Event d) → ℝ) (kind : List (Event d) → SevenRankings.Kind)
    (H : List (Event d)) (p : Point n m × ℝ)
    (hp : IsMinimizer (master d seed H) Prod.snd p) :
    IsMinimizer (levelSet d seed H p.2 alpha)
      (fun z => historyRanking d seed lambda mu rho kind H z.1)
      ((selector hr hs ha ha1 lambda mu rho kind).trial H p hp).val :=
  Auxiliary.selector_trial_minimizer hr hs ha ha1
    (historyRanking d seed lambda mu rho kind)
    (historyRanking_continuous seed lambda mu rho kind) H p hp

/-- Exact source-qualified endpoint: actual C2/nonnegative full weights justify
the displayed Hessian rankings; a proved auxiliary minimum supplies every trial.
Finite progress and the stored-incumbent return are reused, not assumed. -/
theorem source_seven_rankings_return (hr : Regularity d) {seed : Point n m}
    (hs : seed ∈ d.original) (hf2 : ContDiff ℝ 2 d.f)
    (hg2 : ∀ j, ContDiff ℝ 2 (d.g j))
    (lambda : List (Event d) → Fin l → ℝ) (mu : List (Event d) → Fin r → ℝ)
    (hl : ∀ H j, 0 ≤ lambda H j) (hm : ∀ H i, 0 ≤ mu H i)
    (rho : List (Event d) → ℝ) (hrho : ∀ H, 0 ≤ rho H)
    (kind : List (Event d) → SevenRankings.Kind) {alpha epsilon : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (heps : 0 ≤ epsilon) :
    let select := selector hr hs (le_of_lt ha) ha1 lambda mu rho kind
    let result := Exec.solve hr select epsilon
    (∀ H, ConvexOn ℝ univ (historyRanking d seed lambda mu rho kind H)) ∧
      (∀ H p (hp : IsMinimizer (master d seed H) Prod.snd p),
        IsMinimizer (levelSet d seed H p.2 alpha)
          (fun z => historyRanking d seed lambda mu rho kind H z.1)
          (select.trial H p hp).val) ∧
      Exec.Trace select epsilon [] result.history ∧
      (result.history.map Event.target).Nodup ∧
      (∃ u, result.answer = some u ∧ Exec.StoredCorrect d seed epsilon result.history u) ∧
      result.processed ≤ (targets d hr).card ∧
      result.history.length = result.processed ∧
      result.queries = result.processed + 1 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro H
    exact SevenRankings.ranking_convex d (lambda H) (mu H) hr.objective_convex
      hr.constraint_convex (hl H) (hm H) hf2 hg2 (incumbent d seed H)
      (rho H) (hrho H) (kind H)
  · exact every_auxiliary_minimum hr hs (le_of_lt ha) ha1 lambda mu rho kind
  · exact Exec.source_seeded_return hr hs ha ha1 heps
      (selector hr hs (le_of_lt ha) ha1 lambda mu rho kind)

end Chapter07.RegularizedReturn

#print axioms Chapter07.RegularizedReturn.historyRanking_continuous
#print axioms Chapter07.RegularizedReturn.every_auxiliary_minimum
#print axioms Chapter07.RegularizedReturn.source_seven_rankings_return
