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

theorem T_source_domain : Tsource.domain = articleDomain (interval 0 1) Tsource :=
  (articleDomain_eq_base (interval 0 1) Tsource (boxEncoding 0 1 (xSquareRow 2))).symm

def T_source_encoding : HardBoundEncoding (interval 0 1) Tsource.model :=
  boxEncoding 0 1 (xSquareRow 2)

theorem T_source_analytic : Analytic Tsource := onHardDomain_analytic Tdata T_analytic rfl

theorem T_source_bounded : Bornology.IsBounded Tsource.relaxation :=
  box_relaxation_bounded 0 1 (xSquareRow 2)

theorem T_source_C1 : ContDiff ℝ 1 Tsource.f ∧ ∀ j, ContDiff ℝ 1 (Tsource.model.g j) :=
  ⟨linearQuadratic_C1 (1/4),fun _ => xSquareRow_C1 2⟩

theorem T_source_assumptions : AvailabilityAssumptions Tsource := by
  apply article_availability_assumptions (interval 0 1) Tsource T_source_encoding
    T_source_analytic T_source_domain T_source_bounded
  intro y hy x hm
  exact T_all_minimizer_LICQ (intCast y) x hm

/-- Actual invocation of the new source endpoint, for every admitted initializer
and every admitted selector. The bound is the same two-assignment box. -/
theorem T_source_return {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (Initialization Tsource) ∧
    (∀ seed, SeedValid Tsource seed → LocalAvailability Tsource seed epsilon) ∧
    Nonempty (InitializedSelectors Tsource epsilon) ∧
    ∀ (choose : InitializedSelectors Tsource epsilon) (initial : Initialization Tsource),
      ∃ out, execute Tsource epsilon choose initial = some out ∧
        ReturnCertificate Tsource epsilon out.result ∧
        out.masters ≤ 3 ∧ out.fixed ≤ 3 ∧ out.restorations ≤ 2 := by
  have hb : Tsource.box.card = 2 := T_box_card
  simpa only [hb,show 2+1=3 by rfl] using
    source_initialized_finite_return T_source_assumptions heps

def T_source_initialization : Initialization Tsource :=
  exact_initialization Tsource T_source_assumptions.domain_base (pt 0 (1/4)) T_initial_minimum

theorem T_source_fractional_seed : SeedValid Tsource (pt 0 (1/4)) :=
  ⟨T_initial_minimum,T_source_assumptions.every_exact_initialization _ T_initial_minimum,
    T_seed_valid.2.2⟩

theorem T_actual_source_execution {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : InitializedSelectors Tsource epsilon) :
    ∃ out, execute Tsource epsilon choose T_source_initialization = some out ∧
      ReturnCertificate Tsource epsilon out.result ∧
      out.masters ≤ 3 ∧ out.fixed ≤ 3 ∧ out.restorations ≤ 2 :=
  (T_source_return heps).2.2.2 choose T_source_initialization


end Chapter03.OAExec.Article.Source

#print axioms Chapter03.OAExec.Article.Source.T_source_return
