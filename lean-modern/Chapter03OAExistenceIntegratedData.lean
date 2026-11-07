module

public import Chapter03OAExistenceAnalytic
public import Chapter03OAExecControlCases
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Integrated article-style control. X is the unbounded half-line x ≤ 1/2;
Y=[0,1]. The single nonlinear row stays soft in restoration, and the upper
x-bound is the single hard row. No integer bound is inserted into g. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Integrated

def objective (p : P) : ℝ := (p.1 0-1)^2+p.2 0
def Df (p : P) : P →L[ℝ] ℝ := (2*(p.1 0-1)) • cx+cy
def model : ModelData 1 1 1 1 where
  g _ p := (p.1 0)^2+7/16-p.2 0
  A _ := scalar 1
  B _ := scalar 0
  rhs := scalar (1/2)
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1
def Dg (p : P) (_ : Fin 1) : P →L[ℝ] ℝ := (2*p.1 0) • cx-cy
def domain : Set P := {p | p.1 0≤1/2 ∧ 0≤p.2 0 ∧ p.2 0≤1}
def spec : Data 1 1 1 1 where
  model := model
  f := objective
  Df := Df
  Dg := Dg
  domain := domain

def bounds : Bounds 1 where
  lower _ := .negInfinity
  upper _ := .finite (1/2)

def encoding : HardBoundEncoding bounds model where
  valid := by intro i; constructor <;> simp [bounds]
  side j := .inr j
  injective := Sum.inr_injective
  lower_cover := by intro i a h; simp [bounds] at h
  upper_cover := by intro i a h; exact ⟨i,rfl⟩
  row_spec := by
    intro j
    refine ⟨1/2,rfl,?_⟩
    intro p
    fin_cases j
    simp [linearResidual,model,LinearForm,scalar,Fin.sum_univ_one]

theorem hard_region (p : P) : p∈model.linearRegion ↔ p.1 0≤1/2 := by
  simp [ModelData.linearRegion,model,LinearForm,scalar,Fin.forall_fin_one,Fin.sum_univ_one]

theorem bounds_region (x : V) : x∈bounds.region ↔ x 0≤1/2 := by
  simp [Bounds.region,bounds,ExtendedBound.lowerHolds,ExtendedBound.upperHolds,
    Fin.forall_fin_one]

theorem domain_eq_base : spec.domain=(asFP spec).base := by
  ext p
  rw [asFP_base_iff]
  change (p.1 0≤1/2 ∧ 0≤p.2 0 ∧ p.2 0≤1) ↔
    p∈model.linearRegion ∧ ∀j,model.lo j≤p.2 j ∧ p.2 j≤model.hi j
  rw [hard_region]
  simp [model,scalar,Fin.forall_fin_one]

theorem domain_closed : IsClosed domain := by
  change IsClosed spec.domain
  rw [domain_eq_base]
  exact Chapter03.FP.base_closed _

theorem domain_convex : Convex ℝ domain := by
  change Convex ℝ spec.domain
  rw [domain_eq_base]
  exact Chapter03.FP.base_convex _

theorem objective_derivative (p : P) : HasFDerivAt objective (Df p) p := by
  change HasFDerivAt (fun q : P => (q.1 0-1)^2+q.2 0) (Df p) p
  simpa [Df,sub_eq_add_neg] using
    (affine_square_derivative cx (-1) p).fun_add cy.hasFDerivAt

theorem row_derivative (p : P) (j : Fin 1) : HasFDerivAt (model.g j) (Dg p j) p :=
  ((square_derivative p).add_const (7/16)).sub cy.hasFDerivAt

theorem objective_C1 : ContDiff ℝ 1 objective :=
  ((cx.contDiff.sub contDiff_const).pow 2).add cy.contDiff

theorem row_C1 (j : Fin 1) : ContDiff ℝ 1 (model.g j) :=
  ((cx.contDiff.pow 2).add contDiff_const).sub cy.contDiff

theorem objective_convex : ConvexOn ℝ Set.univ objective := by
  change ConvexOn ℝ Set.univ (fun p : P => (p.1 0-1)^2+p.2 0)
  simpa [Pi.add_def,sub_eq_add_neg] using
    (affine_square_convex cx (-1)).add (cy.toLinearMap.convexOn convex_univ)

theorem row_convex (j : Fin 1) : ConvexOn ℝ Set.univ (model.g j) :=
  (square_convex.add_const (7/16)).sub (cy.toLinearMap.concaveOn convex_univ)

theorem row_nonaffine (j : Fin 1) : ¬ AffineRow (model.g j) := by
  intro h
  have hh := affine_second_difference h
  norm_num [model,pt,scalar] at hh

theorem nonlinear_exact : spec.nonlinear=Set.univ := by
  ext j
  simp [Data.nonlinear,spec,row_nonaffine]

theorem relaxation (p : P) : p∈spec.relaxation ↔
    p.1 0≤1/2 ∧ 0≤p.2 0 ∧ p.2 0≤1 ∧ (p.1 0)^2+7/16≤p.2 0 := by
  rw [relaxation_mem_iff]
  change ((∀j : Fin 1, (p.1 0)^2+7/16-p.2 0≤0) ∧ p∈model.linearRegion ∧
    ∀i : Fin 1,0≤p.2 i ∧ p.2 i≤1) ↔ _
  rw [hard_region]
  simp only [Fin.forall_fin_one]
  constructor <;> intro h <;> constructor <;> try tauto
  · exact ⟨h.2.2.1,h.2.2.2,by linarith [h.1]⟩
  · linarith [h.2.2.2]

theorem analytic : Analytic spec where
  convex_f := objective_convex.subset (Set.subset_univ _) domain_convex
  convex_g j := (row_convex j).subset (Set.subset_univ _) domain_convex
  original_domain := by
    intro p hp
    have h := (relaxation p).mp (original_subset_relaxation spec hp)
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  derivative_f p _ := objective_derivative p
  derivative_g p _ j := row_derivative p j

theorem relaxation_bounded : Bornology.IsBounded spec.relaxation := by
  apply (isCompact_Icc : IsCompact (Set.Icc (pt (-1) 0) (pt 1 1))).isBounded.subset
  intro p hp
  obtain ⟨hx,hy0,hy1,hg⟩ := (relaxation p).mp hp
  have hx0 : -1≤p.1 0 := by nlinarith [sq_nonneg (p.1 0+1)]
  have hx1 : p.1 0≤1 := by linarith
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> intro i <;> fin_cases i
  · exact hx0
  · exact hy0
  · exact hx1
  · exact hy1

theorem domain_unbounded : ¬ Bornology.IsBounded domain := by
  intro hb
  obtain ⟨R,hR⟩ := hb.exists_norm_le
  let T : ℝ := max R 0+1
  have hT : 0<T := by dsimp [T]; have := le_max_right R 0; linarith
  have hp : pt (-T) 0∈domain := by
    change -T≤1/2 ∧ 0≤(0:ℝ) ∧ (0:ℝ)≤1
    exact ⟨(neg_nonpos.mpr hT.le).trans (by norm_num),by norm_num,by norm_num⟩
  have hn : ‖(pt (-T) 0).1 0‖≤‖pt (-T) 0‖ :=
    (norm_le_pi_norm (pt (-T) 0).1 0).trans (norm_fst_le _)
  have hnT : T≤R := by
    have h := hn.trans (hR _ hp)
    simpa [pt,scalar,Real.norm_eq_abs,abs_neg,abs_of_pos hT] using h
  have := le_max_left R 0
  dsimp [T] at hnT
  linarith

def seed : P := pt (1/2) (11/16)
def solution : P := pt (1/2) 1

theorem seed_minimum : IsMinimizer spec.relaxation spec.f seed := by
  refine ⟨(relaxation seed).mpr (by norm_num [seed,pt,scalar]),?_⟩
  intro p hp
  have hg := ((relaxation p).mp hp).2.2.2
  norm_num [spec,objective,seed,pt,scalar]
  nlinarith [sq_nonneg (p.1 0-1/2)]

theorem seed_unique {p : P} (hp : IsMinimizer spec.relaxation spec.f p) : p=seed := by
  have hg := ((relaxation p).mp hp.1).2.2.2
  have hm := hp.2 seed seed_minimum.1
  norm_num [spec,objective,seed,pt,scalar] at hm
  have hx : p.1 0=1/2 := by nlinarith [sq_nonneg (p.1 0-1/2)]
  apply point_ext
  · simpa [seed,pt,scalar] using hx
  · norm_num [seed,pt,scalar]
    rw [hx] at hg hm
    norm_num at hg hm
    linarith

theorem seed_valid : SeedValid spec seed :=
  ⟨seed_minimum,by norm_num [spec,domain,seed,pt,scalar],
    fractional_not_integral (1/2) (11/16) (by norm_num) (by norm_num)⟩

theorem fiber_membership (x : V) (y : ℝ) : x∈fiber model (scalar y) ↔
    x 0≤1/2 ∧ (x 0)^2+7/16≤y := by
  change ((x,scalar y)∈model.linearRegion ∧ ∀j : Fin 1,(x 0)^2+7/16-y≤0) ↔ _
  rw [hard_region]
  simp only [Fin.forall_fin_one]
  exact and_congr_right fun _ => sub_nonpos

theorem zero_fiber_empty : ¬ (fiber model (scalar 0)).Nonempty := by
  rintro ⟨x,hx⟩
  have h := ((fiber_membership x 0).mp hx).2
  nlinarith [sq_nonneg (x 0)]

theorem fixed_minimum :
    IsMinimizer (fiber model (scalar 1)) (fiberObjective objective (scalar 1)) (scalar (1/2)) := by
  refine ⟨(fiber_membership _ _).mpr (by norm_num [scalar]),?_⟩
  intro x hx
  have h := ((fiber_membership x 1).mp hx).1
  norm_num [fiberObjective,objective,scalar]
  nlinarith [sq_nonneg (x 0-1/2)]

theorem fixed_unique {x : V}
    (hx : IsMinimizer (fiber model (scalar 1)) (fiberObjective objective (scalar 1)) x) :
    x=scalar (1/2) := by
  have h := ((fiber_membership x 1).mp hx.1).1
  have hm := hx.2 _ fixed_minimum.1
  norm_num [fiberObjective,objective,scalar] at hm
  apply scalar_ext
  change x 0=1/2
  nlinarith [sq_nonneg (x 0-1/2)]

end Chapter03.OAExec.Integrated
