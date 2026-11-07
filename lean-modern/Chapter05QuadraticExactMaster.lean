module

public import Chapter05QuadraticExact

@[expose] public section

/-! A complete nonempty unit history is exactly the original epigraph when
the objective and every represented constraint have explicit quadratic data.
The retained base carries all hard, domain and integrality restrictions unchanged.
Minimizer transport assumes an actual exact minimizer and does not assert a solve. -/
noncomputable section
open Set
namespace Chapter05.Quadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I J : Type*}

structure QuadraticRepresentations (d : MasterData E I J) where
  objective : QuadraticFormData E
  objective_eq : d.f = objective.eval
  constraint : J → QuadraticFormData E
  constraint_eq : ∀ j, d.g j = (constraint j).eval

def UnitHistory (d : MasterData E I J) (H : Finset I) : Prop :=
  ∀ i ∈ H, d.objectiveScale i = 1 ∧ ∀ j, d.constraintScale i j = 1

def originalFeasible (d : MasterData E I J) : Set E :=
  {x | x ∈ d.base ∧ ∀ j, d.g j x ≤ 0}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem trueEpigraph_eq_epigraphLift (d : MasterData E I J) :
    trueEpigraph d = Chapter02.EpigraphLift (originalFeasible d) d.f := by
  ext p
  simp only [trueEpigraph, Chapter02.EpigraphLift, originalFeasible,
    mem_setOf_eq, and_assoc]

theorem quadraticMaster_eq_trueEpigraph {d : MasterData E I J} {H : Finset I}
    (hr : QuadraticRepresentations d) (hne : H.Nonempty) (hu : UnitHistory d H) :
    quadraticMaster d H = trueEpigraph d := by
  have hf (a x : E) : cut d.f a 1 x = d.f x := by
    rw [hr.objective_eq]
    exact hr.objective.cut_one_eq a x
  have hg (j : J) (a x : E) : cut (d.g j) a 1 x = d.g j x := by
    rw [hr.constraint_eq j]
    exact (hr.constraint j).cut_one_eq a x
  rcases hne with ⟨i0,hi0⟩
  ext p
  constructor
  · rintro ⟨hB,hf',hg'⟩
    refine ⟨hB,?_,?_⟩
    · intro j
      simpa only [(hu i0 hi0).2 j, hg] using hg' i0 hi0 j
    · simpa only [(hu i0 hi0).1, hf] using hf' i0 hi0
  · rintro ⟨hB,hg',hf'⟩
    refine ⟨hB,?_,?_⟩
    · intro i hi
      simpa only [(hu i hi).1, hf] using hf'
    · intro i hi j
      simpa only [(hu i hi).2 j, hg] using hg' j

/-- A complete singleton anchor gives the exact same epigraph. -/
theorem singleton_master_exact {d : MasterData E I J}
    (hr : QuadraticRepresentations d) (i : I)
    (hf : d.objectiveScale i = 1) (hg : ∀ j, d.constraintScale i j = 1) :
    quadraticMaster d {i} = trueEpigraph d := by
  classical
  apply quadraticMaster_eq_trueEpigraph hr (Finset.singleton_nonempty i)
  intro k hk
  have hki : k = i := Finset.mem_singleton.mp hk
  subst k
  exact ⟨hf,hg⟩

theorem exact_master_minimizer_recovery {d : MasterData E I J} {H : Finset I}
    (hr : QuadraticRepresentations d) (hne : H.Nonempty) (hu : UnitHistory d H)
    {p : E × ℝ} (hp : Chapter02.IsMinimizer (quadraticMaster d H) Prod.snd p) :
    p.2 = d.f p.1 ∧ p.1 ∈ originalFeasible d ∧
      Chapter02.IsMinimizer (originalFeasible d) d.f p.1 := by
  rw [quadraticMaster_eq_trueEpigraph hr hne hu, trueEpigraph_eq_epigraphLift] at hp
  exact ⟨Chapter02.epigraph_tight_at_minimizer hp, hp.1.1,
    Chapter02.epigraph_project_minimizer hp⟩

theorem original_minimizer_lifts_exact_master {d : MasterData E I J} {H : Finset I}
    (hr : QuadraticRepresentations d) (hne : H.Nonempty) (hu : UnitHistory d H)
    {x : E} (hx : Chapter02.IsMinimizer (originalFeasible d) d.f x) :
    Chapter02.IsMinimizer (quadraticMaster d H) Prod.snd (x,d.f x) := by
  rw [quadraticMaster_eq_trueEpigraph hr hne hu, trueEpigraph_eq_epigraphLift]
  exact Chapter02.epigraph_lift_minimizer hx

theorem exact_master_nonempty_iff {d : MasterData E I J} {H : Finset I}
    (hr : QuadraticRepresentations d) (hne : H.Nonempty) (hu : UnitHistory d H) :
    (quadraticMaster d H).Nonempty ↔ (originalFeasible d).Nonempty := by
  rw [quadraticMaster_eq_trueEpigraph hr hne hu, trueEpigraph_eq_epigraphLift]
  exact Chapter02.epigraph_feasible_iff _ _

/-- The omitted nonemptiness premise changes the literal master. -/
theorem empty_history_master (d : MasterData E I J) :
    quadraticMaster d ∅ = {p | p.1 ∈ d.base} := by
  ext p
  simp [quadraticMaster]

end Chapter05.Quadratic
