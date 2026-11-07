module

public import Chapter03PumpOAAvailability
public import Chapter03OAExistenceIntegratedEndpoint

@[expose] public section

/-! Full article-style source package for a surviving failed-projection row.
The accepted Integrated hard domain and every original constraint are unchanged.
Only the objective becomes (x-1)^2+4y. Fixed objectives differ by a constant,
so the accepted all-minimizer LICQ proof applies to exactly the same minima. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.PumpOA.Retained

abbrev model := OAExec.Integrated.model
abbrev domain := OAExec.Integrated.domain
abbrev Dg := OAExec.Integrated.Dg
abbrev bounds := OAExec.Integrated.bounds
def objective (p : P) : ℝ := (p.1 0-1)^2+4*p.2 0
def Df (p : P) : P →L[ℝ] ℝ := (2*(p.1 0-1)) • cx+(4:ℝ) • cy
def spec : OAExec.Data 1 1 1 1 where
  model := model
  f := objective
  Df := Df
  Dg := Dg
  domain := domain
def pump : FP.Data 1 1 1 1 := asFPDelta spec 0
def seed : P := pt (1/5) (191/400)
def projection : P := pt 0 (7/16)
def solution : P := OAExec.Integrated.solution

theorem objective_shift (p : P) :
    objective p=OAExec.Integrated.objective p+3*p.2 0 := by
  dsimp [objective,OAExec.Integrated.objective]
  ring

theorem objective_derivative (p : P) : HasFDerivAt objective (Df p) p := by
  change HasFDerivAt (fun q : P => (q.1 0-1)^2+4*q.2 0) (Df p) p
  simpa [Df,sub_eq_add_neg] using
    (affine_square_derivative cx (-1) p).fun_add ((4:ℝ) • cy).hasFDerivAt

theorem objective_convex : ConvexOn ℝ Set.univ objective := by
  change ConvexOn ℝ Set.univ (fun p : P => (p.1 0-1)^2+4*p.2 0)
  simpa [Pi.add_def,sub_eq_add_neg] using
    (affine_square_convex cx (-1)).add
      (((4:ℝ) • cy).toLinearMap.convexOn convex_univ)

theorem analytic : OAExec.Analytic spec where
  convex_f := objective_convex.subset (Set.subset_univ _) OAExec.Integrated.domain_convex
  convex_g := OAExec.Integrated.analytic.convex_g
  original_domain := OAExec.Integrated.analytic.original_domain
  derivative_f p _ := objective_derivative p
  derivative_g := OAExec.Integrated.analytic.derivative_g

theorem fixed_minimum_transport (y : RealVector 1) (x : V)
    (hm : IsMinimizer (fiber model y) (fiberObjective objective y) x) :
    IsMinimizer (fiber model y) (fiberObjective OAExec.Integrated.objective y) x := by
  refine ⟨hm.1,?_⟩
  intro z hz
  have h := hm.2 z hz
  dsimp [fiberObjective] at h ⊢
  rw [objective_shift,objective_shift] at h
  linarith

theorem fixed_licq (y : IntVector 1) (hy : y∈IntegerBox model.lo model.hi)
    (x : V) (hm : IsMinimizer (fiber model (intCast y))
      (fiberObjective objective (intCast y)) x) :
    FixedLICQ model x (intCast y) (Dg (x,intCast y)) :=
  OAExec.Integrated.fixed_licq y hy x (fixed_minimum_transport _ _ hm)

def encoding : HardBoundEncoding bounds model := OAExec.Integrated.encoding

theorem domain_article : spec.domain=OAExec.articleDomain bounds spec :=
  OAExec.Integrated.domain_eq_article

theorem source_package : OAExec.AvailabilityAssumptions spec :=
  OAExec.article_availability_assumptions bounds spec encoding analytic domain_article
    OAExec.Integrated.relaxation_bounded fixed_licq

theorem pump_analytic : FP.Analytic pump := asFPDelta_analytic source_package (le_refl 0)

theorem relaxation (p : P) : p∈pump.relaxation ↔
    p.1 0≤1/2 ∧ 0≤p.2 0 ∧ p.2 0≤1 ∧ (p.1 0)^2+7/16≤p.2 0 :=
  OAExec.Integrated.relaxation p

theorem seed_minimum : IsMinimizer pump.relaxation pump.f seed := by
  refine ⟨(relaxation seed).mpr (by norm_num [seed,pt,scalar]),?_⟩
  intro p hp
  have hg := ((relaxation p).mp hp).2.2.2
  change objective seed≤objective p
  norm_num [objective,seed,pt,scalar]
  nlinarith [sq_nonneg (p.1 0-1/5)]

theorem seed_valid : OAExec.SeedValid spec seed :=
  ⟨seed_minimum,by norm_num [spec,domain,OAExec.Integrated.domain,seed,pt,scalar],
    fractional_not_integral (1/5) (191/400) (by norm_num) (by norm_num)⟩

theorem seed_not_original : seed∉pump.original := by
  intro hp
  obtain ⟨_,_,_,y,_,hy⟩ := (source_feasible_iff model Set.univ seed).mp hp
  exact seed_valid.2.2 ⟨y,hy⟩

theorem box_card : spec.box.card=2 := OAExec.Integrated.box_card

theorem values : objective seed=51/20 ∧ objective solution=17/4 := by
  norm_num [objective,seed,solution,OAExec.Integrated.solution,pt,scalar]

theorem fixed_minimum : IsMinimizer (pump.fiber target1) pump.f solution := by
  refine ⟨⟨(relaxation solution).mpr ?_,?_⟩,?_⟩
  · norm_num [solution,OAExec.Integrated.solution,pt,scalar]
  · funext j; fin_cases j; norm_num [solution,OAExec.Integrated.solution,pt,scalar,FP.intCast,target1]
  · intro p hp
    have hx := ((relaxation p).mp hp.1).1
    have hy : p.2 0=1 := by simpa [FP.intCast,target1] using congrFun hp.2 0
    change objective solution≤objective p
    norm_num [objective,solution,OAExec.Integrated.solution,pt,scalar,hy]
    nlinarith [sq_nonneg (p.1 0-1/2)]

theorem distance (y : IntVector 1) (p : P) : FP.distance y p=((y 0:ℝ)-p.2 0)^2 := by
  simp [FP.distance,FP.intY,FP.intCast,Chapter03.yMap,PiLp.norm_sq_eq_of_L2,
    Fin.sum_univ_one,Real.norm_eq_abs,sq_abs]

theorem projection0_minimum : IsMinimizer (pump.region none) (FP.distance target0) projection := by
  refine ⟨⟨(relaxation projection).mpr (by norm_num [projection,pt,scalar]),trivial⟩,?_⟩
  intro p hp
  have hg := ((relaxation p).mp hp.1).2.2.2
  have hy : 7/16≤p.2 0 := by nlinarith [sq_nonneg (p.1 0)]
  rw [distance,distance]
  norm_num [target0,projection,pt,scalar]
  nlinarith [sq_nonneg (p.2 0-7/16)]

theorem projection1_minimum : IsMinimizer (pump.region none) (FP.distance target1) solution := by
  refine ⟨⟨fixed_minimum.1.1,trivial⟩,?_⟩
  intro p _
  rw [distance,distance]
  norm_num [target1,solution,OAExec.Integrated.solution,pt,scalar]
  exact sq_nonneg _

end Chapter03.PumpOA.Retained
