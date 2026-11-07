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

theorem G_source_domain : Gsource.domain = articleDomain (interval (-1) 1) Gsource :=
  (articleDomain_eq_base (interval (-1) 1) Gsource (boxEncoding (-1) 1 (xSquareRow 4))).symm

def G_source_encoding : HardBoundEncoding (interval (-1) 1) Gsource.model :=
  boxEncoding (-1) 1 (xSquareRow 4)

theorem G_source_analytic : Analytic Gsource := onHardDomain_analytic Gdata G_analytic rfl

theorem G_source_bounded : Bornology.IsBounded Gsource.relaxation :=
  box_relaxation_bounded (-1) 1 (xSquareRow 4)

theorem G_source_C1 : ContDiff ℝ 1 Gsource.f ∧ ∀ j, ContDiff ℝ 1 (Gsource.model.g j) :=
  ⟨quadratic_C1 (1/2),fun _ => xSquareRow_C1 4⟩

theorem G_source_assumptions : AvailabilityAssumptions Gsource := by
  apply article_availability_assumptions (interval (-1) 1) Gsource G_source_encoding
    G_source_analytic G_source_domain G_source_bounded
  intro y hy x hm
  exact G_all_minimizer_LICQ (intCast y) x hm

/-- Actual invocation of the new source endpoint, for every admitted initializer
and every admitted selector. The bound is the same two-assignment box. -/
theorem G_source_return {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (Initialization Gsource) ∧
    (∀ seed, SeedValid Gsource seed → LocalAvailability Gsource seed epsilon) ∧
    Nonempty (InitializedSelectors Gsource epsilon) ∧
    ∀ (choose : InitializedSelectors Gsource epsilon) (initial : Initialization Gsource),
      ∃ out, execute Gsource epsilon choose initial = some out ∧
        ReturnCertificate Gsource epsilon out.result ∧
        out.masters ≤ 3 ∧ out.fixed ≤ 3 ∧ out.restorations ≤ 2 := by
  have hb : Gsource.box.card = 2 := G_box_card
  simpa only [hb,show 2+1=3 by rfl] using
    source_initialized_finite_return G_source_assumptions heps

def G_source_initialization : Initialization Gsource :=
  exact_initialization Gsource G_source_assumptions.domain_base (pt 0 (1/2)) G_initial_minimum

theorem G_source_fractional_seed : SeedValid Gsource (pt 0 (1/2)) :=
  ⟨G_initial_minimum,G_source_assumptions.every_exact_initialization _ G_initial_minimum,
    G_seed_valid.2.2⟩

theorem G_actual_source_execution {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : InitializedSelectors Gsource epsilon) :
    ∃ out, execute Gsource epsilon choose G_source_initialization = some out ∧
      ReturnCertificate Gsource epsilon out.result ∧
      out.masters ≤ 3 ∧ out.fixed ≤ 3 ∧ out.restorations ≤ 2 :=
  (G_source_return heps).2.2.2 choose G_source_initialization


end Chapter03.OAExec.Article.Source

#print axioms Chapter03.OAExec.Article.Source.G_source_return
