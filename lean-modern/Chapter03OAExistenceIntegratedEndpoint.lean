module

public import Chapter03OAExistenceIntegratedRegularity
public import Chapter03OAExistenceAvailability

@[expose] public section

/-! An inhabited article-scoped source package for the integrated control.
The final result invokes the new availability endpoint and retains the exact
universal execution equality established in the sealed first stage. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.OAExec.Integrated

theorem fixed_licq (y : IntVector 1) (hy : y∈IntegerBox model.lo model.hi)
    (x : V) (hm : IsMinimizer (fiber model (intCast y))
      (fiberObjective objective (intCast y)) x) :
    FixedLICQ model x (intCast y) (Dg (x,intCast y)) := by
  change LinearIndepOn ℝ
    (Sum.elim (fun j => restrict (Dg (x,intCast y) j))
      (fiberLinearRow model))
    {i | fixedRows model (intCast y) i x=0}
  have hset : {i | fixedRows model (intCast y) i x=0} =
      {i : Fin 1 ⊕ Fin 1 | Sum.elim (fun j => soft model (intCast y) j x)
        (fun k => hard model (intCast y) k x) i=0} := by
    ext i
    cases i <;> rfl
  rw [hset]
  exact all_minima_LICQ y hy x hm

theorem domain_eq_article : spec.domain=articleDomain bounds spec :=
  domain_eq_base.trans (articleDomain_eq_base bounds spec encoding).symm

theorem source_package : AvailabilityAssumptions spec :=
  article_availability_assumptions bounds spec encoding analytic domain_eq_article
    relaxation_bounded fixed_licq

/-- Every exact initializer and every legal selector returns the same original
solution, for every nonnegative tolerance. The package supplies those choices;
the actual execution performs two masters, two fixed solves and one restoration. -/
theorem complete_control (epsilon : ℝ) (heps : 0≤epsilon) :
    Nonempty (Initialization spec) ∧
    (∀ seed, SeedValid spec seed → LocalAvailability spec seed epsilon) ∧
    Nonempty (InitializedSelectors spec epsilon) ∧
    ∀ (choose : InitializedSelectors spec epsilon) (initial : Initialization spec),
      execute spec epsilon choose initial =
        some ⟨.solution solution,2,2,1⟩ ∧
      ReturnCertificate spec epsilon (.solution solution) := by
  obtain ⟨hi,hl,hs,hr⟩ := article_source_initialized_finite_return
    bounds spec encoding analytic domain_eq_article relaxation_bounded fixed_licq heps
  refine ⟨hi,hl,hs,?_⟩
  intro choose initial
  have hex := every_initialized_run epsilon heps choose initial
  refine ⟨hex,?_⟩
  obtain ⟨out,he,hc,_,_,_⟩ := hr choose initial
  have ho : out = ⟨.solution solution,2,2,1⟩ := Option.some.inj (he.symm.trans hex)
  subst out
  exact hc

/-- The new zero-tolerance endpoint gives actual original global optimality. -/
theorem solution_minimum : IsMinimizer spec.original spec.f solution := by
  obtain ⟨initial⟩ := source_package.initialization_nonempty
  obtain ⟨choose⟩ := source_package.selectors_nonempty 0
  obtain ⟨out,he,hm,_,_,_⟩ := source_initialized_zero_return source_package choose initial
  have ho : out = ⟨.solution solution,2,2,1⟩ :=
    Option.some.inj (he.symm.trans (every_initialized_run 0 (le_refl 0) choose initial))
  subst out
  exact hm

end Chapter03.OAExec.Integrated
