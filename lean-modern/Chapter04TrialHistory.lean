module

public import Chapter04GradientRows
public import Chapter02Restoration

@[expose] public section

/-! Retained actual MILP trials, separate exact NLP polishes, and radius limits.
The infeasible branch follows Algorithm 2.b: all strictly violated rows. The
broader active-and-violated g ≥ 0 reading of the displayed equations is not
formalized here. Exact masters are supplied only after the initial trial;
neither an initial argmax nor a real value equal to infinity is asserted.
Seed/master availability and finite discovery/return remain outside this module.
-/

noncomputable section
open Filter
open scoped Topology
namespace Chapter04.CenterCut

abbrev TrialEvent (n m : ℕ) :=
  Chapter02.Point n m × Option (Chapter02.Point n m)

def TrialEvent.trial {n m : ℕ} (e : TrialEvent n m) : Chapter02.Point n m := e.1

def TrialEvent.polished {n m : ℕ} (e : TrialEvent n m) :
    Option (Chapter02.Point n m) := e.2

def eventValid {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (e : TrialEvent n m) : Prop :=
  e.trial ∈ d.linearRegion ∩ Chapter02.IntegerCylinder (n := n) d.lo d.hi ∧
  match e.polished with
  | none => ¬ e.trial ∈ d.nonlinearRegion
  | some p => e.trial ∈ d.nonlinearRegion ∧
      Chapter02.IsMinimizer (d.fixedNonlinearFiber e.trial.2) d.objective p

/-- Algorithm 2.b strict violations, or active rows and objective at the polish.
The broader g ≥ 0 infeasible-row reading is not represented by this definition. -/
def eventRows {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (e : TrialEvent n m) (q : Chapter02.Point n m) (r : ℝ) : Prop :=
  match e.polished with
  | none => ∀ j, 0 < d.g j e.trial →
      d.g j e.trial + inner ℝ (euclideanGradient (d.g j) e.trial)
        (coordinates n m q - coordinates n m e.trial) +
        r * ‖euclideanGradient (d.g j) e.trial‖ ≤ 0
  | some p =>
      (∀ j, d.g j p = 0 →
        d.g j p + inner ℝ (euclideanGradient (d.g j) p)
          (coordinates n m q - coordinates n m p) +
          r * ‖euclideanGradient (d.g j) p‖ ≤ 0) ∧
      d.objective q + r * ‖coordinates n m (d.c1, d.c2)‖ ≤ d.objective p

def sourceMaster {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (seed : List (EuclideanPoint n m × ℝ)) (H : List (TrialEvent n m)) :
    Set (Chapter02.Point n m × ℝ) :=
  {w | w.1 ∈ d.linearRegion ∩ Chapter02.IntegerCylinder (n := n) d.lo d.hi ∧
    (∀ row ∈ seed, inner ℝ row.1 (coordinates n m w.1) + w.2 * ‖row.1‖ ≤ row.2) ∧
    ∀ e ∈ H, eventRows d e w.1 w.2}

def ExactRadiusMax {n m : ℕ} (M : Set (Chapter02.Point n m × ℝ))
    (w : Chapter02.Point n m × ℝ) : Prop :=
  w ∈ M ∧ ∀ z ∈ M, z.2 ≤ w.2

def seedAdmissible {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (seed : List (EuclideanPoint n m × ℝ)) : Prop :=
  ∀ pStar, Chapter02.IsMinimizer (d.feasibleOn Set.univ) d.objective pStar →
    ∀ row ∈ seed, inner ℝ row.1 (coordinates n m pStar) ≤ row.2

def historyPrefix {n m : ℕ} (events : ℕ → TrialEvent n m) (i : ℕ) :
    List (TrialEvent n m) := (List.range i).map events

theorem mem_historyPrefix {n m : ℕ} (events : ℕ → TrialEvent n m)
    (i : ℕ) (e : TrialEvent n m) :
    e ∈ historyPrefix events i ↔ ∃ j, j < i ∧ events j = e := by
  simp [historyPrefix]

theorem historyPrefix_succ {n m : ℕ} (events : ℕ → TrialEvent n m) (i : ℕ) :
    historyPrefix events (i + 1) = historyPrefix events i ++ [events i] := by
  simp [historyPrefix, List.range_succ, List.map_append]

theorem sourceMaster_append_subset {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (seed : List (EuclideanPoint n m × ℝ)) (H tail : List (TrialEvent n m)) :
    sourceMaster d seed (H ++ tail) ⊆ sourceMaster d seed H := by
  intro w hw
  exact ⟨hw.1, hw.2.1, fun e he => hw.2.2 e (List.mem_append.mpr (Or.inl he))⟩

theorem source_master_radius_le_of_append {n m l k : ℕ}
    (d : Chapter02.ModelData n m l k) (seed : List (EuclideanPoint n m × ℝ))
    (H tail : List (TrialEvent n m)) (old next : Chapter02.Point n m × ℝ)
    (hold : ExactRadiusMax (sourceMaster d seed H) old)
    (hnext : next ∈ sourceMaster d seed (H ++ tail)) : next.2 ≤ old.2 :=
  hold.2 next (sourceMaster_append_subset d seed H tail hnext)

/-- Retained cuts bound the radius against the actual earlier MILP trial.
Only Algorithm 2.b's strict-violation row reading is represented. Full
feasibility and a nonzero objective are explicit; no master exactness is needed. -/
theorem source_retained_trial_radius_le {n m l k : ℕ}
    (d : Chapter02.ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hfeas : (d.feasibleOn Set.univ).Nonempty)
    (hc : coordinates n m (d.c1, d.c2) ≠ 0)
    (seed : List (EuclideanPoint n m × ℝ)) (H : List (TrialEvent n m))
    (e : TrialEvent n m) (he : e ∈ H) (hvalid : eventValid d e)
    (q : Chapter02.Point n m) (r : ℝ) (hmaster : (q,r) ∈ sourceMaster d seed H) :
    r ≤ ‖coordinates n m q - coordinates n m e.trial‖ := by
  have hrows := hmaster.2.2 e he
  obtain ⟨hbase, hbranch⟩ := hvalid
  cases hp : e.polished with
  | none =>
      simp only [eventRows, hp] at hrows
      simp only [hp] at hbranch
      change ¬ (∀ j, d.g j e.trial ≤ 0) at hbranch
      push_neg at hbranch
      obtain ⟨j, hj⟩ := hbranch
      obtain ⟨w, hw⟩ := hfeas
      have hwj := ((Chapter02.source_feasible_iff d Set.univ w).mp hw).2.1 j
      have hnormal := euclideanGradient_ne_zero_of_violation (hconv j)
        (hdiff j e.trial) hj hwj
      have hrow : d.g j e.trial + inner ℝ (euclideanGradient (d.g j) e.trial)
          (coordinates n m q - coordinates n m e.trial) +
          r * ‖euclideanGradient (d.g j) e.trial‖ ≤ 0 := hrows j hj
      exact Chapter04.separating_cut_radius_le_distance _ _ _ _ _ hnormal hj.le hrow
  | some p =>
      simp only [eventRows, hp] at hrows
      have hb : e.trial ∈ d.nonlinearRegion ∧
          Chapter02.IsMinimizer (d.fixedNonlinearFiber e.trial.2) d.objective p := by
        simpa only [hp] using hbranch
      have htrial : e.trial ∈ d.fixedNonlinearFiber e.trial.2 :=
        (Chapter02.mem_fixedNonlinearFiber d e.trial.2 e.trial).mpr
          ⟨hbase.1, rfl, hb.1⟩
      have himprove := hb.2.2 e.trial htrial
      have hrow : d.objective q + r * ‖coordinates n m (d.c1, d.c2)‖ ≤ d.objective p :=
        hrows.2
      have hidentity : inner ℝ (coordinates n m (d.c1, d.c2))
          (coordinates n m q - coordinates n m e.trial) =
          d.objective q - d.objective e.trial := by
        rw [inner_sub_right, ← objective_eq_inner_coordinates, ← objective_eq_inner_coordinates]
      apply Chapter04.separating_cut_radius_le_distance
        (coordinates n m (d.c1, d.c2)) (coordinates n m q) (coordinates n m e.trial)
        (d.objective e.trial - d.objective p) r hc (sub_nonneg.mpr himprove)
      rw [hidentity]
      linarith

theorem event_polished_feasible {n m l k : ℕ} (d : Chapter02.ModelData n m l k)
    (e : TrialEvent n m) (hvalid : eventValid d e) (p : Chapter02.Point n m)
    (hp : e.polished = some p) : p ∈ d.feasibleOn Set.univ := by
  have hb : e.trial ∈ d.nonlinearRegion ∧
      Chapter02.IsMinimizer (d.fixedNonlinearFiber e.trial.2) d.objective p := by
    simpa only [hp] using hvalid.2
  have hmem := (Chapter02.mem_fixedNonlinearFiber d e.trial.2 p).mp hb.2.1
  obtain ⟨y, hy, heq⟩ := hvalid.1.2
  exact (Chapter02.source_feasible_iff d Set.univ p).mpr
    ⟨Set.mem_univ _, hmem.2.2, hmem.1, y, hy, hmem.2.1.trans heq⟩

theorem optimizer_mem_sourceMaster {n m l k : ℕ}
    (d : Chapter02.ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (seed : List (EuclideanPoint n m × ℝ)) (hseed : seedAdmissible d seed)
    (H : List (TrialEvent n m)) (hvalid : ∀ e ∈ H, eventValid d e)
    (pStar : Chapter02.Point n m)
    (hmin : Chapter02.IsMinimizer (d.feasibleOn Set.univ) d.objective pStar) :
    (pStar, 0) ∈ sourceMaster d seed H := by
  have hstar := (Chapter02.source_feasible_iff d Set.univ pStar).mp hmin.1
  refine ⟨⟨hstar.2.2.1, hstar.2.2.2⟩, ?_, ?_⟩
  · intro row hrow
    simpa only [zero_mul, add_zero] using hseed pStar hmin row hrow
  · intro e he
    cases hp : e.polished with
    | none =>
        simp only [eventRows, hp, zero_mul, add_zero]
        intro j _
        exact euclideanGradient_tangent_valid (hconv j) (hdiff j e.trial) (hstar.2.1 j)
    | some p =>
        simp only [eventRows, hp, zero_mul, add_zero]
        constructor
        · intro j _
          exact euclideanGradient_tangent_valid (hconv j) (hdiff j p) (hstar.2.1 j)
        · exact hmin.2 p (event_polished_feasible d e (hvalid e he) p hp)

/-- The radius limit for exact positive-index masters of an actual-trial history.
There is no exactness or sign hypothesis at index zero. Infeasible events use
Algorithm 2.b strict violations, not the broader g ≥ 0 displayed-equation rule.
The supplied seed/exact-master contracts do not certify initial argmax,
positive-ball preservation, finite discovery, or a literal zero-radius loop. -/
theorem source_history_radius_tendsto_zero {n m l k : ℕ}
    (d : Chapter02.ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ Chapter02.IntegerCylinder (n := n) d.lo d.hi))
    (hfeas : (d.feasibleOn Set.univ).Nonempty)
    (hc : coordinates n m (d.c1, d.c2) ≠ 0)
    (seed : List (EuclideanPoint n m × ℝ)) (hseed : seedAdmissible d seed)
    (events : ℕ → TrialEvent n m) (radius : ℕ → ℝ)
    (hvalid : ∀ i, eventValid d (events i))
    (hmax : ∀ i, ExactRadiusMax
      (sourceMaster d seed (historyPrefix events (i + 1)))
      ((events (i + 1)).trial, radius (i + 1))) :
    Tendsto radius atTop (𝓝 0) := by
  obtain ⟨pStar, hmin⟩ := Chapter02.source_minimum_attained d hcompact
    (fun j => (hdiff j).continuous) hfeas
  have hnonneg : ∀ i, 0 ≤ radius (i + 1) := by
    intro i
    apply (hmax i).2 (pStar, 0)
    apply optimizer_mem_sourceMaster d hconv hdiff seed hseed _ _ pStar hmin
    intro e he
    obtain ⟨j, _, rfl⟩ := (mem_historyPrefix events (i + 1) e).mp he
    exact hvalid j
  have hmono : Antitone (fun i => radius (i + 1)) := by
    apply antitone_nat_of_succ_le
    intro i
    apply source_master_radius_le_of_append d seed (historyPrefix events (i + 1))
      [events (i + 1)] ((events (i + 1)).trial, radius (i + 1))
      ((events (i + 1 + 1)).trial, radius (i + 1 + 1)) (hmax i)
    simpa only [← historyPrefix_succ] using (hmax (i + 1)).1
  have hpair : ∀ j i, j < i → radius (i + 1) ≤
      dist (coordinates n m (events (i + 1)).trial)
        (coordinates n m (events (j + 1)).trial) := by
    intro j i hji
    rw [dist_eq_norm]
    apply source_retained_trial_radius_le d hconv hdiff hfeas hc seed
      (historyPrefix events (i + 1)) (events (j + 1)) _ (hvalid (j + 1))
      (events (i + 1)).trial (radius (i + 1)) (hmax i).1
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

end Chapter04.CenterCut
