module

public import Chapter03FPSearchModel

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch
variable {n m l : ℕ}

theorem toUnbounded_relaxation (d : Data n m l) :
    d.toUnbounded.relaxation = d.relaxation := rfl

theorem toUnbounded_original (d : Data n m l) :
    d.toUnbounded.original = d.original := rfl

theorem relaxation_compact (d : Data n m l) (h : Analytic d) :
    IsCompact d.relaxation := FPUnbounded.relaxation_compact d.toUnbounded h

theorem relaxation_convex (d : Data n m l) (h : Analytic d) :
    Convex ℝ d.relaxation := FPUnbounded.relaxation_convex d.toUnbounded h

theorem relaxation_attained (d : Data n m l) (h : Analytic d)
    (hne : d.relaxation.Nonempty) : ∃ p, IsMinimizer d.relaxation d.f p :=
  FPUnbounded.relaxation_attained d.toUnbounded h hne

theorem projection_attained (d : Data n m l) (h : Analytic d)
    (q : IntVector m) (hne : d.relaxation.Nonempty) :
    ∃ p, IsMinimizer d.relaxation (distance q) p :=
  compact_feasible_attainment (relaxation_compact d h) hne
    (FPUnbounded.distance_continuous q).continuousOn

/-- This equivalence concerns the projection objective alone. -/
theorem norm_projection_iff (C : Set (Point n m)) (q : IntVector m) (p : Point n m) :
    IsMinimizer C (fun z => ‖intY q - Chapter03.yMap n m z‖) p ↔
      IsMinimizer C (distance q) p := by
  constructor
  · rintro ⟨hp, hm⟩
    exact ⟨hp, fun z hz => pow_le_pow_left₀ (norm_nonneg _) (hm z hz) 2⟩
  · rintro ⟨hp, hm⟩
    refine ⟨hp, fun z hz => ?_⟩
    have hh := hm z hz
    change ‖intY q - Chapter03.yMap n m p‖^2 ≤
      ‖intY q - Chapter03.yMap n m z‖^2 at hh
    nlinarith [norm_nonneg (intY q - Chapter03.yMap n m p),
      norm_nonneg (intY q - Chapter03.yMap n m z)]

theorem projection_normal (d : Data n m l) (h : Analytic d)
    (q : IntVector m) {p : Point n m}
    (hp : IsMinimizer d.relaxation (distance q) p)
    {z : Point n m} (hz : z ∈ d.relaxation) :
    0 ≤ @inner ℝ _ _ (Chapter03.yMap n m p - intY q)
      (Chapter03.yMap n m z - Chapter03.yMap n m p) := by
  have hm : Chapter03.ProjectionMin (Chapter03.yMap n m '' d.relaxation)
      (intY q) (Chapter03.yMap n m p) := by
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    rintro v ⟨w, hw, rfl⟩
    exact hp.2 w hw
  exact Chapter03.projection_cut_valid
    ((relaxation_convex d h).linear_image (Chapter03.yMap n m)) hm _ ⟨z, hz, rfl⟩

/-- The proof minimizes over integer L1 sublevels and keeps a full witness.
The artificial scalar is fixed to zero and is not part of the search master. -/
theorem master_attained (d : Data n m l) (mode : Mode) (s : State n m)
    (hne : (master d mode s).Nonempty) :
    ∃ p, IsMinimizer (master d mode s) (masterCost s) p := by
  let S : Set (Point n m × ℝ) := {z | z.1 ∈ master d mode s ∧ z.2 = 0}
  have hS : S.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨(p, 0), hp, rfl⟩
  obtain ⟨z, hz, hm⟩ := FPUnbounded.integer_value_attained S s.reference
    (fun z hz => hz.1.2.1) hS
  refine ⟨z.1, hz.1, fun p hp => ?_⟩
  exact hm (p, 0) ⟨hp, rfl⟩

theorem initialization_nonempty (d : Data n m l) (h : Analytic d) :
    Nonempty (Initialization d) := by
  classical
  by_cases he : d.relaxation.Nonempty
  · obtain ⟨p, hp⟩ := relaxation_attained d h he
    exact ⟨.minimum p hp⟩
  · exact ⟨.empty he⟩

theorem decision_nonempty (d : Data n m l) (h : Analytic d) (mode : Mode)
    (s : State n m) (hs : s.seed ∈ d.relaxation) : Nonempty (Decision d mode s) := by
  classical
  by_cases he : (master d mode s).Nonempty
  · obtain ⟨z, hz⟩ := master_attained d mode s he
    obtain ⟨q, hq⟩ := hz.1.2.1
    obtain ⟨p, hp⟩ := projection_attained d h q ⟨s.seed, hs⟩
    exact ⟨.project ⟨z, q, p, hz, hq, hp⟩⟩
  · exact ⟨.empty he⟩

theorem selector_nonempty (d : Data n m l) (h : Analytic d) (mode : Mode) :
    Nonempty (Selector d mode) :=
  ⟨fun s hs => Classical.choice (decision_nonempty d h mode s hs)⟩

end Chapter03.FPSearch
