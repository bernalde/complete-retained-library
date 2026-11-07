module

public import Chapter03OAExistenceArticleShared

@[expose] public section

/-! Complete source packages for explicit hard-domain adaptations of G, T,
EmptyInitial and IntegralF. All source models, objective functions and tangent
fields are unchanged. The accepted Set.univ-support Data values are distinct. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article.Source

def Gsource := onHardDomain Gdata
def Tsource := onHardDomain Tdata
def EmptySource := onHardDomain EmptyData
def IntegralSource := onHardDomain IntegralData

theorem old_data_no_source_package : ¬ AvailabilityAssumptions Gdata ∧
    ¬ AvailabilityAssumptions Tdata ∧ ¬ AvailabilityAssumptions EmptyData ∧
    ¬ AvailabilityAssumptions IntegralData :=
  ⟨fun h => original_domains_mismatch.1 h.domain_base,
   fun h => original_domains_mismatch.2.1 h.domain_base,
   fun h => original_domains_mismatch.2.2.1 h.domain_base,
   fun h => original_domains_mismatch.2.2.2 h.domain_base⟩

theorem Empty_analytic : Analytic EmptyData where
  convex_f := quadratic_convex _
  convex_g _ := xSquareRow_convex _
  original_domain _ _ := Set.mem_univ _
  derivative_f _ _ := quadratic_derivative _ _
  derivative_g _ _ _ := xSquareRow_derivative _ _

theorem Integral_analytic : Analytic IntegralData where
  convex_f := quadratic_convex _
  convex_g _ := xSquareRow_convex _
  original_domain _ _ := Set.mem_univ _
  derivative_f _ _ := quadratic_derivative _ _
  derivative_g _ _ _ := xSquareRow_derivative _ _

theorem Empty_fiber_empty (y : V) : ¬ (fiber EmptyInitial y).Nonempty := by
  rintro ⟨x,hx⟩
  have hg := hx.2 0
  change (x 0)^2 - (-1) ≤ 0 at hg
  nlinarith [sq_nonneg (x 0)]


end Chapter03.OAExec.Article.Source
