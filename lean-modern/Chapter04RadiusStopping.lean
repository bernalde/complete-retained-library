module

public import Chapter04DiscoveryBall

@[expose] public section

/-! A finite-history stopping certificate for actual stored polishes. One
positive threshold precedes every finite valid empty-seed history and exact
final master. This does not assert finite return, final-master availability,
an arbitrary positive-tolerance guarantee, or feasibility of the final center.
The accepted Algorithm 2.b strict-violation event semantics are unchanged. -/

noncomputable section
namespace Chapter04.CenterCut
open Chapter02

/-- Actual stored polishes, with no default point or chosen tie-breaking rule. -/
def storedPolishes {n m : ℕ} (H : List (TrialEvent n m)) : Set (Point n m) :=
  {p | ∃ e ∈ H, e.polished = some p}

theorem stored_polishes_feasible {n m l k : ℕ} (d : ModelData n m l k)
    (H : List (TrialEvent n m)) (hvalid : ∀ e ∈ H, eventValid d e)
    (p : Point n m) (hp : p ∈ storedPolishes H) :
    p ∈ d.feasibleOn Set.univ := by
  obtain ⟨e, he, hpolish⟩ := hp
  exact event_polished_feasible d e (hvalid e he) p hpolish

/-- A stored global minimizer witnesses best-stored existence. Every best
stored point is then globally optimal, including ties between distinct points. -/
theorem best_stored_optimal_of_stored_global {n m l k : ℕ}
    (d : ModelData n m l k) (H : List (TrialEvent n m))
    (hvalid : ∀ e ∈ H, eventValid d e) (p : Point n m)
    (hp : p ∈ storedPolishes H)
    (hmin : IsMinimizer (d.feasibleOn Set.univ) d.objective p) :
    (∃ b, IsMinimizer (storedPolishes H) d.objective b) ∧
      ∀ b, IsMinimizer (storedPolishes H) d.objective b →
        IsMinimizer (d.feasibleOn Set.univ) d.objective b := by
  constructor
  · exact ⟨p, hp, fun b hb => hmin.2 b (stored_polishes_feasible d H hvalid b hb)⟩
  · intro b hb
    refine ⟨stored_polishes_feasible d H hvalid b hb.1, ?_⟩
    intro q hq
    exact (hb.2 p hp).trans (hmin.2 q hq)

/-- One model-dependent positive threshold precedes every finite valid history.
A smaller exact final radius ensures a best stored polish exists and every
best stored polish is globally optimal. No previous exact-master solves,
nonzero objective, supplied radius limit or discovered optimum are assumed. -/
theorem source_small_radius_best_stored {n m l k : ℕ} (d : ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hfeas : (d.feasibleOn Set.univ).Nonempty) (hSlater : OAFiberSlater d) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ H : List (TrialEvent n m), (∀ e ∈ H, eventValid d e) →
        ∀ w : Point n m × ℝ, ExactRadiusMax (sourceMaster d [] H) w →
          w.2 < ρ →
          (∃ b, IsMinimizer (storedPolishes H) d.objective b) ∧
            ∀ b, IsMinimizer (storedPolishes H) d.objective b →
              IsMinimizer (d.feasibleOn Set.univ) d.objective b := by
  classical
  obtain ⟨center, ρ, _, hρ, hball⟩ :=
    source_pre_discovery_ball d hconv hdiff hcompact hfeas hSlater
  refine ⟨ρ, hρ, ?_⟩
  intro H hvalid w hmax hsmall
  have hex : ∃ p, p ∈ storedPolishes H ∧
      IsMinimizer (d.feasibleOn Set.univ) d.objective p := by
    by_contra hnone
    have hb : (center, ρ) ∈ sourceMaster d [] H := by
      apply hball H hvalid
      intro e he p hp hmin
      exact hnone ⟨p, ⟨e, he, hp⟩, hmin⟩
    exact (not_le_of_gt hsmall) (hmax.2 (center, ρ) hb)
  obtain ⟨p, hp, hmin⟩ := hex
  exact best_stored_optimal_of_stored_global d H hvalid p hp hmin

/-- A supplied nonpositive exact final radius certifies the stored incumbent.
Zero is the intended stopping case. This does not assert that such a final
master exists or is reached, in particular after zero-objective discovery. -/
theorem source_nonpositive_radius_best_stored {n m l k : ℕ}
    (d : ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hfeas : (d.feasibleOn Set.univ).Nonempty) (hSlater : OAFiberSlater d)
    (H : List (TrialEvent n m)) (hvalid : ∀ e ∈ H, eventValid d e)
    (w : Point n m × ℝ) (hmax : ExactRadiusMax (sourceMaster d [] H) w)
    (hstop : w.2 ≤ 0) :
    (∃ b, IsMinimizer (storedPolishes H) d.objective b) ∧
      ∀ b, IsMinimizer (storedPolishes H) d.objective b →
        IsMinimizer (d.feasibleOn Set.univ) d.objective b := by
  obtain ⟨ρ, hρ, hcertificate⟩ :=
    source_small_radius_best_stored d hconv hdiff hcompact hfeas hSlater
  exact hcertificate H hvalid w hmax (hstop.trans_lt hρ)

end Chapter04.CenterCut
