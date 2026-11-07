module

public import Chapter03OAExistenceArticleSources

@[expose] public section

/-! Complete source packages for explicit hard-domain adaptations of G, T,
EmptyInitial and IntegralF. All source models, objective functions and tangent
fields are unchanged. The accepted Set.univ-support Data values are distinct. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article.Source

theorem Empty_source_domain : EmptySource.domain = articleDomain (interval (-1) 1) EmptySource :=
  (articleDomain_eq_base (interval (-1) 1) EmptySource (boxEncoding (-1) 1 (xSquareRow (-1)))).symm

def Empty_source_encoding : HardBoundEncoding (interval (-1) 1) EmptySource.model :=
  boxEncoding (-1) 1 (xSquareRow (-1))

theorem Empty_source_analytic : Analytic EmptySource := onHardDomain_analytic EmptyData Empty_analytic rfl

theorem Empty_source_bounded : Bornology.IsBounded EmptySource.relaxation :=
  box_relaxation_bounded (-1) 1 (xSquareRow (-1))

theorem Empty_source_C1 : ContDiff ℝ 1 EmptySource.f ∧ ∀ j, ContDiff ℝ 1 (EmptySource.model.g j) :=
  ⟨quadratic_C1 (1/2),fun _ => xSquareRow_C1 (-1)⟩

theorem Empty_source_assumptions : AvailabilityAssumptions EmptySource := by
  apply article_availability_assumptions (interval (-1) 1) EmptySource Empty_source_encoding
    Empty_source_analytic Empty_source_domain Empty_source_bounded
  intro y hy x hm
  exact (Empty_fiber_empty (intCast y) ⟨x,hm.1⟩).elim

/-- Actual invocation of the new source endpoint, for every admitted initializer
and every admitted selector. The bound is the same two-assignment box. -/
theorem Empty_source_return {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (Initialization EmptySource) ∧
    (∀ seed, SeedValid EmptySource seed → LocalAvailability EmptySource seed epsilon) ∧
    Nonempty (InitializedSelectors EmptySource epsilon) ∧
    ∀ (choose : InitializedSelectors EmptySource epsilon) (initial : Initialization EmptySource),
      ∃ out, execute EmptySource epsilon choose initial = some out ∧
        ReturnCertificate EmptySource epsilon out.result ∧
        out.masters ≤ 3 ∧ out.fixed ≤ 3 ∧ out.restorations ≤ 2 := by
  have hb : EmptySource.box.card = 2 := G_box_card
  simpa only [hb,show 2+1=3 by rfl] using
    source_initialized_finite_return Empty_source_assumptions heps

theorem Integral_source_domain : IntegralSource.domain = articleDomain (interval (-1) 1) IntegralSource :=
  (articleDomain_eq_base (interval (-1) 1) IntegralSource (boxEncoding (-1) 1 (xSquareRow 4))).symm

def Integral_source_encoding : HardBoundEncoding (interval (-1) 1) IntegralSource.model :=
  boxEncoding (-1) 1 (xSquareRow 4)

theorem Integral_source_analytic : Analytic IntegralSource := onHardDomain_analytic IntegralData Integral_analytic rfl

theorem Integral_source_bounded : Bornology.IsBounded IntegralSource.relaxation :=
  box_relaxation_bounded (-1) 1 (xSquareRow 4)

theorem Integral_source_C1 : ContDiff ℝ 1 IntegralSource.f ∧ ∀ j, ContDiff ℝ 1 (IntegralSource.model.g j) :=
  ⟨quadratic_C1 0,fun _ => xSquareRow_C1 4⟩

theorem Integral_source_assumptions : AvailabilityAssumptions IntegralSource := by
  apply article_availability_assumptions (interval (-1) 1) IntegralSource Integral_source_encoding
    Integral_source_analytic Integral_source_domain Integral_source_bounded
  intro y hy x hm
  exact Integral_all_minimizer_LICQ (intCast y) x hm

/-- Actual invocation of the new source endpoint, for every admitted initializer
and every admitted selector. The bound is the same two-assignment box. -/
theorem Integral_source_return {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (Initialization IntegralSource) ∧
    (∀ seed, SeedValid IntegralSource seed → LocalAvailability IntegralSource seed epsilon) ∧
    Nonempty (InitializedSelectors IntegralSource epsilon) ∧
    ∀ (choose : InitializedSelectors IntegralSource epsilon) (initial : Initialization IntegralSource),
      ∃ out, execute IntegralSource epsilon choose initial = some out ∧
        ReturnCertificate IntegralSource epsilon out.result ∧
        out.masters ≤ 3 ∧ out.fixed ≤ 3 ∧ out.restorations ≤ 2 := by
  have hb : IntegralSource.box.card = 2 := G_box_card
  simpa only [hb,show 2+1=3 by rfl] using
    source_initialized_finite_return Integral_source_assumptions heps

/-- Every initializer reply is genuinely empty; no loop choice is inspected. -/
theorem Empty_source_all_executions (epsilon : ℝ)
    (choose : InitializedSelectors EmptySource epsilon) (initial : Initialization EmptySource) :
    execute EmptySource epsilon choose initial = some ⟨.infeasible,0,0,0⟩ := by
  cases initial with
  | empty he => rfl
  | minimum seed hm hd => exact (empty_initializer_relaxation ⟨seed,hm.1⟩).elim

/-- Every actual relaxed minimum is (0,0); every initializer/selector therefore
returns that original minimizer with no master, fixed or restoration decisions. -/
theorem Integral_source_all_executions (epsilon : ℝ)
    (choose : InitializedSelectors IntegralSource epsilon)
    (initial : Initialization IntegralSource) :
    execute IntegralSource epsilon choose initial = some ⟨.solution (pt 0 0),0,0,0⟩ ∧
    IsMinimizer IntegralSource.original IntegralSource.f (pt 0 0) := by
  refine ⟨?_,Chapter03.OAExec.integral_initializer_minimum
    (d := IntegralSource) Article.integral_initializer_minimum integral_zero⟩
  cases initial with
  | empty he =>
    have hp : pt 0 0 ∈ IntegralSource.relaxation := Article.integral_initializer_minimum.1
    rw [he] at hp
    exact hp.elim
  | minimum seed hm hd =>
    have hs := Integral_minimum_unique seed hm
    subst seed
    simp only [execute,dif_pos integral_zero]


end Chapter03.OAExec.Article.Source

#print axioms Chapter03.OAExec.Article.Source.Empty_source_return
#print axioms Chapter03.OAExec.Article.Source.Integral_source_return
