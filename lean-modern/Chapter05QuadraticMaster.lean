module

public import Chapter05QuadraticScale

@[expose] public section

/-! Finite matched histories of actual safely scaled quadratic cuts.
The retained base is literal in all three sets. Coefficients belong to fixed
anchor indices, so extending the history retains each old row unchanged.
This is only a static relaxation/dominance consumer: no attainment, all-fiber
exactness, optimizer-set equality, execution, or finite-return claim is made. -/
noncomputable section
open Set
namespace Chapter05.Quadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I J : Type*}

structure MasterData (E I J : Type*) where
  f : E → ℝ
  g : J → E → ℝ
  anchor : I → E
  objectiveScale : I → ℝ
  constraintScale : I → J → ℝ
  base : Set E

structure MasterRegularity (d : MasterData E I J) : Prop where
  objective_convex : ConvexOn ℝ univ d.f
  objective_C2 : ContDiff ℝ 2 d.f
  constraint_convex : ∀ j, ConvexOn ℝ univ (d.g j)
  constraint_C2 : ∀ j, ContDiff ℝ 2 (d.g j)

def SafeHistory (d : MasterData E I J) (H : Finset I) : Prop :=
  ∀ i ∈ H, (0 ≤ d.objectiveScale i ∧
    d.objectiveScale i ≤ safeScale d.f (d.anchor i) d.base) ∧
    ∀ j, 0 ≤ d.constraintScale i j ∧
      d.constraintScale i j ≤ safeScale (d.g j) (d.anchor i) d.base

def trueEpigraph (d : MasterData E I J) : Set (E × ℝ) :=
  {p | p.1 ∈ d.base ∧ (∀ j, d.g j p.1 ≤ 0) ∧ d.f p.1 ≤ p.2}

def quadraticMaster (d : MasterData E I J) (H : Finset I) : Set (E × ℝ) :=
  {p | p.1 ∈ d.base ∧
    (∀ i ∈ H, cut d.f (d.anchor i) (d.objectiveScale i) p.1 ≤ p.2) ∧
    ∀ i ∈ H, ∀ j, cut (d.g j) (d.anchor i) (d.constraintScale i j) p.1 ≤ 0}

def linearMaster (d : MasterData E I J) (H : Finset I) : Set (E × ℝ) :=
  {p | p.1 ∈ d.base ∧
    (∀ i ∈ H, tangent d.f (d.anchor i) p.1 ≤ p.2) ∧
    ∀ i ∈ H, ∀ j, tangent (d.g j) (d.anchor i) p.1 ≤ 0}

theorem trueEpigraph_subset_quadraticMaster {d : MasterData E I J} {H : Finset I}
    (hr : MasterRegularity d) (hs : SafeHistory d H) :
    trueEpigraph d ⊆ quadraticMaster d H := by
  rintro p ⟨hB,hg,hf⟩
  refine ⟨hB,?_,?_⟩
  · intro i hi
    exact (cut_le_of_safeScale hr.objective_convex hr.objective_C2
      (d.anchor i) d.base (hs i hi).1.2 p.1 hB).trans hf
  · intro i hi j
    exact (cut_le_of_safeScale (hr.constraint_convex j) (hr.constraint_C2 j)
      (d.anchor i) d.base ((hs i hi).2 j).2 p.1 hB).trans (hg j)

theorem quadraticMaster_subset_linearMaster {d : MasterData E I J} {H : Finset I}
    (hr : MasterRegularity d) (hs : SafeHistory d H) :
    quadraticMaster d H ⊆ linearMaster d H := by
  rintro p ⟨hB,hf,hg⟩
  refine ⟨hB,?_,?_⟩
  · intro i hi
    exact (tangent_le_cut hr.objective_convex hr.objective_C2
      (d.anchor i) (hs i hi).1.1 p.1).trans (hf i hi)
  · intro i hi j
    exact (tangent_le_cut (hr.constraint_convex j) (hr.constraint_C2 j)
      (d.anchor i) ((hs i hi).2 j).1 p.1).trans (hg i hi j)

theorem master_inclusions {d : MasterData E I J} {H : Finset I}
    (hr : MasterRegularity d) (hs : SafeHistory d H) :
    trueEpigraph d ⊆ quadraticMaster d H ∧
      quadraticMaster d H ⊆ linearMaster d H :=
  ⟨trueEpigraph_subset_quadraticMaster hr hs,
    quadraticMaster_subset_linearMaster hr hs⟩

theorem quadratic_master_lower_bound {d : MasterData E I J} {H : Finset I}
    (hr : MasterRegularity d) (hs : SafeHistory d H) {q : E × ℝ}
    (hq : Chapter02.IsMinimizer (quadraticMaster d H) Prod.snd q) :
    Chapter02.IsLowerBound (trueEpigraph d) Prod.snd q.2 :=
  Chapter02.lowerBound_of_relaxation (trueEpigraph_subset_quadraticMaster hr hs)
    (Chapter02.minimizer_is_lowerBound hq)

theorem quadratic_master_objective_lower_bound {d : MasterData E I J} {H : Finset I}
    (hr : MasterRegularity d) (hs : SafeHistory d H) {q : E × ℝ}
    (hq : Chapter02.IsMinimizer (quadraticMaster d H) Prod.snd q)
    {x : E} (hx : x ∈ d.base) (hg : ∀ j, d.g j x ≤ 0) : q.2 ≤ d.f x :=
  quadratic_master_lower_bound hr hs hq (x,d.f x) ⟨hx,hg,le_rfl⟩

theorem quadratic_linear_minima_order {d : MasterData E I J} {H : Finset I}
    (hr : MasterRegularity d) (hs : SafeHistory d H) {l q : E × ℝ}
    (hl : Chapter02.IsMinimizer (linearMaster d H) Prod.snd l)
    (hq : Chapter02.IsMinimizer (quadraticMaster d H) Prod.snd q) : l.2 ≤ q.2 :=
  Chapter02.nested_minima_monotone (quadraticMaster_subset_linearMaster hr hs) hl hq

/-- Pure row retention: every coefficient is fixed by its anchor index. -/
theorem quadraticMaster_antitone (d : MasterData E I J) {H K : Finset I}
    (hHK : H ⊆ K) : quadraticMaster d K ⊆ quadraticMaster d H := by
  rintro p ⟨hB,hf,hg⟩
  exact ⟨hB,fun i hi => hf i (hHK hi),fun i hi j => hg i (hHK hi) j⟩

theorem quadratic_master_values_monotone (d : MasterData E I J) {H K : Finset I}
    (hHK : H ⊆ K) {p q : E × ℝ}
    (hp : Chapter02.IsMinimizer (quadraticMaster d H) Prod.snd p)
    (hq : Chapter02.IsMinimizer (quadraticMaster d K) Prod.snd q) : p.2 ≤ q.2 :=
  Chapter02.nested_minima_monotone (quadraticMaster_antitone d hHK) hp hq

/-- The source has finitely many nonlinear rows and a joint dimension n+p.
The more general supporting definitions make no finiteness-based inference. -/
theorem source_joint_master_inclusions {n p m : ℕ} {I : Type*}
    {d : MasterData (Chapter02.RealVector (n+p)) I (Fin m)} {H : Finset I}
    (hr : MasterRegularity d) (hs : SafeHistory d H) :
    trueEpigraph d ⊆ quadraticMaster d H ∧
      quadraticMaster d H ⊆ linearMaster d H :=
  master_inclusions hr hs

end Chapter05.Quadratic
