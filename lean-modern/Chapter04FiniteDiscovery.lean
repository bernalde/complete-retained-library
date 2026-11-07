module

public import Chapter04DiscoveryBall

@[expose] public section

/-! Finite discovery of an actual globally optimal stored polish. The first
trial is supplied, the seed is empty, and only positive-index masters before
discovery are required to be exact. There is no post-discovery master oracle,
initial empty-master argmax, while execution, or finite-zero-return assertion.
The nonlinear rows follow the accepted Algorithm 2.b strict-violation reading.
-/

noncomputable section
open Filter
open scoped Topology
namespace Chapter04.CenterCut

def optimalPolish {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (e : TrialEvent n m) : Prop :=
  ∃ p : Chapter02.Point n m, e.polished = some p ∧
    Chapter02.IsMinimizer (d.feasibleOn Set.univ) d.objective p

def noEarlierOptimalPolish {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (events : ℕ → TrialEvent n m) (i : ℕ) : Prop :=
  ∀ j : ℕ, j < i → ¬ optimalPolish d (events j)

/-- The infeasible branch of the retained-trial bound needs no nonzero objective.
A feasible witness forces the actual normal of a strictly violated row nonzero. -/
theorem retained_infeasible_trial_radius_le {n m l k : ℕ}
    (d : Chapter02.ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hfeas : (d.feasibleOn Set.univ).Nonempty)
    (H : List (TrialEvent n m)) (e : TrialEvent n m)
    (he : e ∈ H) (hvalid : eventValid d e) (hnone : e.polished = none)
    (q : Chapter02.Point n m) (r : ℝ)
    (hmaster : (q,r) ∈ sourceMaster d [] H) :
    r ≤ ‖coordinates n m q - coordinates n m e.trial‖ := by
  have hrows := hmaster.2.2 e he
  have hbranch := hvalid.2
  simp only [eventRows, hnone] at hrows
  simp only [hnone] at hbranch
  change ¬ (∀ j, d.g j e.trial ≤ 0) at hbranch
  push_neg at hbranch
  obtain ⟨j, hj⟩ := hbranch
  obtain ⟨w, hw⟩ := hfeas
  have hwj := ((Chapter02.source_feasible_iff d Set.univ w).mp hw).2.1 j
  have hnormal := euclideanGradient_ne_zero_of_violation (hconv j)
    (hdiff j e.trial) hj hwj
  exact Chapter04.separating_cut_radius_le_distance _ _ _ _ _ hnormal hj.le (hrows j hj)

/-- Narrow all-infeasible empty-seed support used in the zero-objective branch.
Only the positive-index tail is exact; the initial radius is unconstrained. -/
theorem infeasible_history_radius_tendsto_zero {n m l k : ℕ}
    (d : Chapter02.ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ Chapter02.IntegerCylinder (n := n) d.lo d.hi))
    (hfeas : (d.feasibleOn Set.univ).Nonempty)
    (events : ℕ → TrialEvent n m) (radius : ℕ → ℝ)
    (hvalid : ∀ i, eventValid d (events i))
    (hnone : ∀ i, (events i).polished = none)
    (hmax : ∀ i, ExactRadiusMax
      (sourceMaster d [] (historyPrefix events (i + 1)))
      ((events (i + 1)).trial, radius (i + 1))) :
    Tendsto radius atTop (𝓝 0) := by
  obtain ⟨pStar, hmin⟩ := Chapter02.source_minimum_attained d hcompact
    (fun j => (hdiff j).continuous) hfeas
  have hseed : seedAdmissible d [] := by
    intro p hp row hrow
    simp at hrow
  have hnonneg : ∀ i, 0 ≤ radius (i + 1) := by
    intro i
    apply (hmax i).2 (pStar, 0)
    apply optimizer_mem_sourceMaster d hconv hdiff [] hseed _ _ pStar hmin
    intro e he
    obtain ⟨j, _, rfl⟩ := (mem_historyPrefix events (i + 1) e).mp he
    exact hvalid j
  have hmono : Antitone (fun i => radius (i + 1)) := by
    apply antitone_nat_of_succ_le
    intro i
    apply source_master_radius_le_of_append d [] (historyPrefix events (i + 1))
      [events (i + 1)] ((events (i + 1)).trial, radius (i + 1))
      ((events (i + 1 + 1)).trial, radius (i + 1 + 1)) (hmax i)
    simpa only [← historyPrefix_succ] using (hmax (i + 1)).1
  have hpair : ∀ j i, j < i → radius (i + 1) ≤
      dist (coordinates n m (events (i + 1)).trial)
        (coordinates n m (events (j + 1)).trial) := by
    intro j i hji
    rw [dist_eq_norm]
    apply retained_infeasible_trial_radius_le d hconv hdiff hfeas
      (historyPrefix events (i + 1)) (events (j + 1)) _ (hvalid (j + 1))
      (hnone (j + 1)) (events (i + 1)).trial (radius (i + 1)) (hmax i).1
    exact (mem_historyPrefix events (i + 1) (events (j + 1))).mpr
      ⟨j + 1, Nat.add_lt_add_right hji 1, rfl⟩
  have ht : Tendsto (fun i => radius (i + 1)) atTop (𝓝 0) := by
    apply Chapter04.compact_radius_tendsto_zero
      (hcompact.image (coordinates n m).continuous)
      (fun i => coordinates n m (events (i + 1)).trial)
      (fun i => radius (i + 1)) _ hnonneg hmono hpair
    intro i
    exact ⟨(events (i + 1)).trial, (hvalid (i + 1)).1, rfl⟩
  exact (tendsto_add_atTop_iff_nat 1).mp ht

/-- Some actual stored polish is globally optimal. Validity and chosen-master
exactness are required only before an earlier success, including at the first
successful event itself. No uniqueness, nonzero objective, post-success oracle,
supplied radius bound, execution trace or finite-zero-return claim is present. -/
theorem source_finite_optimal_polish {n m l k : ℕ}
    (d : Chapter02.ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ Chapter02.IntegerCylinder (n := n) d.lo d.hi))
    (hfeas : (d.feasibleOn Set.univ).Nonempty)
    (hSlater : Chapter02.OAFiberSlater d)
    (events : ℕ → TrialEvent n m) (radius : ℕ → ℝ)
    (hvalid : ∀ i, noEarlierOptimalPolish d events i → eventValid d (events i))
    (hmax : ∀ i, noEarlierOptimalPolish d events (i + 1) →
      ExactRadiusMax (sourceMaster d [] (historyPrefix events (i + 1)))
        ((events (i + 1)).trial, radius (i + 1))) :
    ∃ i : ℕ, ∃ p : Chapter02.Point n m,
      (events i).polished = some p ∧
        Chapter02.IsMinimizer (d.feasibleOn Set.univ) d.objective p := by
  by_contra hdiscovery
  have hno : ∀ i, ¬ optimalPolish d (events i) := by
    intro i hi
    obtain ⟨p, hp, hmin⟩ := hi
    exact hdiscovery ⟨i, p, hp, hmin⟩
  have hbefore : ∀ i, noEarlierOptimalPolish d events i := by
    intro i j _
    exact hno j
  have hvalid' : ∀ i, eventValid d (events i) := fun i => hvalid i (hbefore i)
  have hmax' : ∀ i, ExactRadiusMax
      (sourceMaster d [] (historyPrefix events (i + 1)))
      ((events (i + 1)).trial, radius (i + 1)) :=
    fun i => hmax i (hbefore (i + 1))
  obtain ⟨center, ρ, _, hρ, hball⟩ :=
    source_pre_discovery_ball d hconv hdiff hcompact hfeas hSlater
  have hlower : ∀ i, ρ ≤ radius (i + 1) := by
    intro i
    apply (hmax' i).2 (center, ρ)
    apply hball (historyPrefix events (i + 1))
    · intro e he
      obtain ⟨j, _, rfl⟩ := (mem_historyPrefix events (i + 1) e).mp he
      exact hvalid' j
    · intro e he p hp hmin
      obtain ⟨j, _, rfl⟩ := (mem_historyPrefix events (i + 1) e).mp he
      exact hno j ⟨p, hp, hmin⟩
  have hlimit : Tendsto radius atTop (𝓝 0) := by
    by_cases hc : coordinates n m (d.c1, d.c2) = 0
    · have hobj : ∀ p : Chapter02.Point n m, d.objective p = 0 := by
        intro p
        rw [objective_eq_inner_coordinates, hc, inner_zero_left]
      have hnone : ∀ i, (events i).polished = none := by
        intro i
        cases hp : (events i).polished with
        | none => rfl
        | some p =>
            exfalso
            apply hno i
            refine ⟨p, hp, event_polished_feasible d (events i) (hvalid' i) p hp, ?_⟩
            intro q hq
            rw [hobj p, hobj q]
      exact infeasible_history_radius_tendsto_zero d hconv hdiff hcompact hfeas
        events radius hvalid' hnone hmax'
    · have hseed : seedAdmissible d [] := by
        intro p hp row hrow
        simp at hrow
      exact source_history_radius_tendsto_zero d hconv hdiff hcompact hfeas hc
        [] hseed events radius hvalid' hmax'
  have hsmall : ∀ᶠ i in atTop, radius i < ρ := (tendsto_order.1 hlimit).2 ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  exact not_lt_of_ge (hlower N) (hN (N + 1) (Nat.le_succ N))

end Chapter04.CenterCut
