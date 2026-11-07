module

public import Chapter03OAExistenceAvailability
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Boundary control: no continuous coordinates, no soft rows, no hard rows.
Y=[0,1] and f(y)=y. Empty row/active families are intentional and explicitly
recorded; the actual initializer is unique and immediately integral. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec.ZeroBoundary

def pt (t : ℝ) : Point 0 1 := (0,fun _ => t)
def cy : Point 0 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.snd ℝ (RealVector 0) (RealVector 1))
def objective (p : Point 0 1) : ℝ := p.2 0
def model : ModelData 0 1 0 0 where
  g := Fin.elim0
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := 0
  c2 := 0
  lo := 0
  hi := 1
def domain : Set (Point 0 1) := {p | 0≤p.2 0 ∧ p.2 0≤1}
def spec : Data 0 1 0 0 where
  model := model
  f := objective
  Df _ := cy
  Dg _ := Fin.elim0
  domain := domain
def bounds : Bounds 0 where
  lower := Fin.elim0
  upper := Fin.elim0

def encoding : HardBoundEncoding bounds model where
  valid := by intro i; exact Fin.elim0 i
  side := Fin.elim0
  injective := by intro i; exact Fin.elim0 i
  lower_cover := by intro i; exact Fin.elim0 i
  upper_cover := by intro i; exact Fin.elim0 i
  row_spec := by intro i; exact Fin.elim0 i

theorem bounds_region : bounds.region=Set.univ := by
  ext x
  simp [Bounds.region]

theorem unique_continuous_point (x : RealVector 0) : x=0 :=
  Subsingleton.elim _ _

theorem domain_eq_article : spec.domain=articleDomain bounds spec := by
  ext p
  simp [articleDomain,bounds_region,spec,model,domain,Fin.forall_fin_one]

theorem domain_eq_base : spec.domain=(asFP spec).base :=
  domain_eq_article.trans (articleDomain_eq_base bounds spec encoding)

theorem domain_closed : IsClosed domain := by
  change IsClosed spec.domain
  rw [domain_eq_base]
  exact Chapter03.FP.base_closed _

theorem domain_convex : Convex ℝ domain := by
  change Convex ℝ spec.domain
  rw [domain_eq_base]
  exact Chapter03.FP.base_convex _

theorem relaxation (p : Point 0 1) : p∈spec.relaxation ↔ p∈domain := by
  rw [relaxation_mem_iff]
  simp [spec,model,ModelData.linearRegion,domain,Fin.forall_fin_one]

theorem objective_C1 : ContDiff ℝ 1 objective := cy.contDiff

theorem objective_derivative (p : Point 0 1) :
    HasFDerivAt objective cy p := cy.hasFDerivAt

theorem row_C1 (j : Fin 0) : ContDiff ℝ 1 (model.g j) := Fin.elim0 j

theorem nonlinear_empty : spec.nonlinear=∅ := by
  ext j
  exact Fin.elim0 j

theorem analytic : Analytic spec where
  convex_f := cy.toLinearMap.convexOn domain_convex
  convex_g j := Fin.elim0 j
  original_domain p hp := (relaxation p).mp (original_subset_relaxation spec hp)
  derivative_f p _ := objective_derivative p
  derivative_g _ _ j := Fin.elim0 j

theorem relaxation_bounded : Bornology.IsBounded spec.relaxation := by
  apply (isCompact_Icc : IsCompact (Set.Icc (pt 0) (pt 1))).isBounded.subset
  intro p hp
  have h := (relaxation p).mp hp
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; exact Fin.elim0 i
  · intro i; fin_cases i; exact h.1
  · intro i; exact Fin.elim0 i
  · intro i; fin_cases i; exact h.2

theorem initial_minimum : IsMinimizer spec.relaxation spec.f (pt 0) := by
  refine ⟨(relaxation _).mpr (by norm_num [domain,pt]),?_⟩
  intro p hp
  exact ((relaxation p).mp hp).1

theorem initial_unique {p : Point 0 1}
    (hm : IsMinimizer spec.relaxation spec.f p) : p=pt 0 := by
  have hp := (relaxation p).mp hm.1
  have hv := hm.2 (pt 0) initial_minimum.1
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · funext i
    fin_cases i
    exact le_antisymm hv hp.1

theorem initial_integral : integral (pt 0) := by
  refine ⟨0,?_⟩
  funext i
  simp [pt,intCast]

theorem no_fractional_seed : ¬ ∃ seed, SeedValid spec seed := by
  rintro ⟨seed,hm,_,hi⟩
  have hs := initial_unique hm
  subst seed
  exact hi initial_integral

theorem fiber_univ (y : RealVector 1) : fiber model y=Set.univ := by
  ext x
  simp [fiber,ModelData.linearRegion,model]

theorem fixed_minimum (y : RealVector 1) :
    IsMinimizer (fiber model y) (fiberObjective objective y) 0 := by
  refine ⟨?_,?_⟩
  · rw [fiber_univ]
    exact Set.mem_univ _
  · intro x _
    exact le_rfl

theorem active_empty (x : RealVector 0) (y : RealVector 1) :
    {i : Fin 0 ⊕ Fin 0 | fixedRows model y i x=0}=∅ := by
  ext i
  cases i with
  | inl j => exact Fin.elim0 j
  | inr k => exact Fin.elim0 k

/-- LICQ is vacuous because both the soft and hard row index types are empty. -/
theorem fixed_licq (y : IntVector 1) (_hy : y∈IntegerBox model.lo model.hi)
    (x : RealVector 0) (_hm : IsMinimizer (fiber model (intCast y))
      (fiberObjective objective (intCast y)) x) :
    FixedLICQ model x (intCast y) (spec.Dg (x,intCast y)) := by
  exact linearIndependent_empty_type

theorem source_package : AvailabilityAssumptions spec :=
  article_availability_assumptions bounds spec encoding analytic domain_eq_article
    relaxation_bounded fixed_licq

theorem every_initialized_run (epsilon : ℝ) (choose : InitializedSelectors spec epsilon)
    (initial : Initialization spec) :
    execute spec epsilon choose initial=some ⟨.solution (pt 0),0,0,0⟩ := by
  cases initial with
  | empty he =>
    have h := initial_minimum.1
    rw [he] at h
    exact False.elim h
  | minimum seed hm hd =>
    have hs := initial_unique hm
    subst seed
    simp only [execute,dif_pos initial_integral]

/-- The source endpoint supplies inhabited choices; every initializer follows
the actual immediate integral branch, with no loop decision or restoration. -/
theorem complete_control (epsilon : ℝ) (heps : 0≤epsilon) :
    Nonempty (Initialization spec) ∧
    (∀ seed, SeedValid spec seed → LocalAvailability spec seed epsilon) ∧
    Nonempty (InitializedSelectors spec epsilon) ∧
    ∀ (choose : InitializedSelectors spec epsilon) (initial : Initialization spec),
      execute spec epsilon choose initial=some ⟨.solution (pt 0),0,0,0⟩ ∧
      ReturnCertificate spec epsilon (.solution (pt 0)) := by
  obtain ⟨hi,hl,hs,hr⟩ := article_source_initialized_finite_return
    bounds spec encoding analytic domain_eq_article relaxation_bounded fixed_licq heps
  refine ⟨hi,hl,hs,?_⟩
  intro choose initial
  have hex := every_initialized_run epsilon choose initial
  refine ⟨hex,?_⟩
  obtain ⟨out,he,hc,_,_,_⟩ := hr choose initial
  have ho : out=⟨.solution (pt 0),0,0,0⟩ := Option.some.inj (he.symm.trans hex)
  subst out
  exact hc

end Chapter03.OAExec.ZeroBoundary
