module

public import Chapter03OAExecHistory
public import Chapter03OAExecControlBase
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-! One concrete origin-domain countercontrol for the thesis's all-soft restoration.
The first no-good set is interpreted as empty (the source initializes C⁰ but
references C¹ at its first master). This is a pure subproblem/history certificate,
not an accepted RawStep: the actual restoration anchor violates EventValid's
unchanged domain premise. The weak nonlinear residual ≥ 0 selection is literal
Algorithm 1; the adjacent strictly-positive prose is a different policy. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
open scoped BigOperators
namespace Chapter03.OAExec.RestorationOrigin

def objective (p : P) : ℝ := (p.1 0-2/5)^2+(p.2 0-61/250)^2
def Df (p : P) : P →L[ℝ] ℝ :=
  (2*(p.1 0-2/5)) • cx+(2*(p.2 0-61/250)) • cy
def model : ModelData 1 1 5 0 where
  g := ![fun p => 8*(p.1 0)^3+2*p.2 0-1,
    fun p => -p.1 0,fun p => p.1 0-2,
    fun p => -p.2 0,fun p => p.2 0-1]
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1

def Dg (p : P) : Fin 5 → P →L[ℝ] ℝ :=
  ![(24*(p.1 0)^2) • cx+2 • cy,-cx,cx,-cy,cy]
def domain : Set P := Set.Icc (pt 0 0) (pt 2 1)
def spec : Data 1 1 5 0 where
  model := model
  f := objective
  Df := Df
  Dg := Dg
  domain := domain

def seed : P := pt (2/5) (61/250)
def incumbent : P := pt 0 0
def initialChoice : P × ℝ := (pt 0 1,0)
def slack : RealVector 5 := ![0,1/2,0,0,0]
def badEvent : Event spec where
  target _ := 1
  target_mem := by intro i; norm_num [spec,model,scalar]
  x := scalar (-(1/2))
  restoration := some slack

@[simp] theorem anchor : badEvent.anchor=pt (-(1/2)) 1 := by
  ext i <;> simp [badEvent,Event.anchor,intCast,pt,scalar]

def boundRows : IntegerBoundRows model where
  lower _ := 3
  upper _ := 4
  lower_eq := by intro i p; fin_cases i; simp [model,scalar]
  upper_eq := by intro i p; fin_cases i; rfl

@[simp] theorem hard (p : P) : p∈model.linearRegion := by
  intro i; exact Fin.elim0 i

theorem domain_iff (p : P) : p∈domain ↔
    0≤p.1 0 ∧ p.1 0≤2 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  simp [domain,Set.mem_Icc,Prod.le_def,Pi.le_def,Fin.forall_fin_one,pt,scalar]
  tauto

theorem rows_iff (p : P) : (∀j,model.g j p≤0) ↔
    8*(p.1 0)^3+2*p.2 0-1≤0 ∧
    0≤p.1 0 ∧ p.1 0≤2 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  simp [model,Fin.forall_fin_succ]

theorem relaxation_iff (p : P) : p∈spec.relaxation ↔
    8*(p.1 0)^3+2*p.2 0-1≤0 ∧ p∈domain := by
  rw [thesis_relaxation_iff spec boundRows]
  change (∀j,model.g j p≤0) ↔ _
  rw [rows_iff,domain_iff]

theorem objective_derivative (p : P) : HasFDerivAt objective (Df p) p := by
  change HasFDerivAt (fun q : P => (q.1 0-2/5)^2+(q.2 0-61/250)^2) (Df p) p
  simpa [Df,sub_eq_add_neg] using
    (affine_square_derivative cx (-(2/5)) p).fun_add
      (affine_square_derivative cy (-(61/250)) p)

theorem cubic_derivative (p : P) : HasFDerivAt (model.g 0) (Dg p 0) p := by
  have h := ((((cx.hasFDerivAt (x:=p)).mul cx.hasFDerivAt).mul cx.hasFDerivAt).const_mul 8).add
    (cy.hasFDerivAt.const_mul 2)
  convert h.sub_const 1 using 1
  · funext z; simp [model]; ring
  · apply ContinuousLinearMap.ext
    intro z; simp [Dg]; ring

theorem row_derivative (p : P) (j : Fin 5) :
    HasFDerivAt (model.g j) (Dg p j) p := by
  fin_cases j
  · exact cubic_derivative p
  · exact cx.hasFDerivAt.neg
  · exact cx.hasFDerivAt.sub_const 2
  · exact cy.hasFDerivAt.neg
  · exact cy.hasFDerivAt.sub_const 1

theorem objective_C1 : ContDiff ℝ 1 objective :=
  ((cx.contDiff.sub contDiff_const).pow 2).add
    ((cy.contDiff.sub contDiff_const).pow 2)

theorem row_C1 (j : Fin 5) : ContDiff ℝ 1 (model.g j) := by
  fin_cases j
  · exact ((contDiff_const.mul (cx.contDiff.pow 3)).add (contDiff_const.mul cy.contDiff)).sub contDiff_const
  · exact cx.contDiff.neg
  · exact cx.contDiff.sub contDiff_const
  · exact cy.contDiff.neg
  · exact cy.contDiff.sub contDiff_const

theorem domain_convex : Convex ℝ domain := by
  intro p hp q hq a b ha hb hab
  rw [domain_iff] at hp hq ⊢
  change 0≤a*p.1 0+b*q.1 0 ∧ a*p.1 0+b*q.1 0≤2 ∧
    0≤a*p.2 0+b*q.2 0 ∧ a*p.2 0+b*q.2 0≤1
  obtain ⟨hp0,hp2,hpy0,hpy1⟩ := hp
  obtain ⟨hq0,hq2,hqy0,hqy1⟩ := hq
  constructor
  · exact add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0)
  constructor
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hp2),mul_nonneg hb (sub_nonneg.mpr hq2)]
  constructor
  · exact add_nonneg (mul_nonneg ha hpy0) (mul_nonneg hb hqy0)
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hpy1),mul_nonneg hb (sub_nonneg.mpr hqy1)]

theorem objective_convex : ConvexOn ℝ domain objective := by
  apply ConvexOn.subset _ (Set.subset_univ _) domain_convex
  change ConvexOn ℝ Set.univ (fun p : P => (p.1 0-2/5)^2+(p.2 0-61/250)^2)
  simpa [Pi.add_def,sub_eq_add_neg] using
    (affine_square_convex cx (-(2/5))).add (affine_square_convex cy (-(61/250)))

theorem row_convex (j : Fin 5) : ConvexOn ℝ domain (model.g j) := by
  have hc : ConvexOn ℝ domain (fun p : P => (p.1 0)^3) := by
    exact ((convexOn_pow (𝕜:=ℝ) 3).comp_linearMap cx.toLinearMap).subset
      (fun p hp => ((domain_iff p).mp hp).1) domain_convex
  fin_cases j
  · simpa [model,Pi.add_def,sub_eq_add_neg] using ((hc.smul (by norm_num : (0:ℝ)≤8)).add
      ((cy.toLinearMap.convexOn domain_convex).smul (by norm_num : (0:ℝ)≤2))).add_const (-1)
  · simpa [model,sub_eq_add_neg] using (affine_convex (-1) 0 0).subset
      (Set.subset_univ _) domain_convex
  · simpa [model,sub_eq_add_neg] using (affine_convex 1 0 (-2)).subset
      (Set.subset_univ _) domain_convex
  · simpa [model,sub_eq_add_neg] using (affine_convex 0 (-1) 0).subset
      (Set.subset_univ _) domain_convex
  · simpa [model,sub_eq_add_neg] using (affine_convex 0 1 (-1)).subset
      (Set.subset_univ _) domain_convex

theorem analytic : Analytic spec where
  convex_f := objective_convex
  convex_g := row_convex
  original_domain p hp := ((relaxation_iff p).mp (original_subset_relaxation spec hp)).2
  derivative_f p _ := objective_derivative p
  derivative_g p _ := row_derivative p

theorem relaxation_bounded : Bornology.IsBounded spec.relaxation :=
  (isCompact_Icc : IsCompact domain).isBounded.subset
    (fun p hp => ((relaxation_iff p).mp hp).2)

theorem seed_feasible : seed∈spec.relaxation := by
  rw [relaxation_iff,domain_iff]
  norm_num [seed,pt,scalar]

theorem seed_fractional : ¬ integral seed := by
  intro h
  obtain ⟨y,hy⟩ := h
  have hh := congrFun hy 0
  norm_num [seed,pt,scalar,intCast] at hh
  have hlo : (0:ℤ)<y 0 := by exact_mod_cast (show (0:ℝ)<(y 0:ℝ) by linarith)
  have hhi : y 0<(1:ℤ) := by exact_mod_cast (show (y 0:ℝ)<1 by linarith)
  omega

theorem seed_minimum : IsMinimizer spec.relaxation objective seed := by
  refine ⟨seed_feasible,?_⟩
  intro q _
  norm_num [objective,seed,pt,scalar]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem original_nonempty : incumbent∈spec.original := by
  rw [thesis_original_iff spec boundRows]
  constructor
  · change ∀j,model.g j incumbent≤0
    rw [rows_iff]; norm_num [incumbent,pt,scalar]
  · refine ⟨fun _ => 0,?_⟩
    ext i; simp [incumbent,pt,scalar,intCast]

theorem seed_objective_tangent (p : P) : objective seed+Df seed (p-seed)=0 := by
  norm_num [objective,Df,seed,pt,scalar]

theorem seed_cubic_tangent (p : P) :
    model.g 0 seed+Dg seed 0 (p-seed)=(96/25)*p.1 0+2*p.2 0-253/125 := by
  norm_num [model,Dg,seed,pt,scalar]
  ring

theorem seed_lower_x (p : P) : model.g 1 seed+Dg seed 1 (p-seed)= -p.1 0 := by
  simp [model,Dg,seed,pt,scalar]
  ring

theorem seed_lower_y (p : P) : model.g 3 seed+Dg seed 3 (p-seed)= -p.2 0 := by
  simp [model,Dg,seed,pt,scalar]
  ring

theorem first_master_minimum :
    IsMinimizer (master spec seed []) Prod.snd initialChoice := by
  constructor
  · rw [master_mem_iff]
    refine ⟨hard _,?_,?_,?_,?_,?_⟩
    · exact ⟨(fun _ => 1),(by intro i; norm_num [spec,model,scalar]),(by ext i; simp [initialChoice,pt,scalar])⟩
    · intro j; fin_cases j <;> norm_num [spec,model,Dg,initialChoice,seed,pt,scalar]
    · change objective seed+Df seed (initialChoice.1-seed) ≤ initialChoice.2
      rw [seed_objective_tangent]
      exact le_rfl
    · simp
    · simp [noGoods]
  · intro z hz
    have h := ((master_mem_iff spec seed [] z).mp hz).2.2.2.1
    change objective seed+Df seed (z.1-seed)≤z.2 at h
    rw [seed_objective_tangent] at h
    exact h

theorem chosen_assignment : initialChoice.1.2=intCast badEvent.target := by
  ext i
  simp [initialChoice,badEvent,intCast,pt,scalar]

theorem failed_fiber : ¬ (fiber model (scalar 1)).Nonempty := by
  rintro ⟨x,_,hg⟩
  have h0 := hg 0
  have h1 := hg 1
  norm_num [model,scalar] at h0 h1
  have hc : 0≤(x 0)^3 := pow_nonneg (by linarith) _
  linarith

theorem all_soft_restoration_iff (x : V) (s : RealVector 5) :
    weightedInsert x s∈restSet model (scalar 1) ↔
      (∀j,model.g j (x,scalar 1)≤s j) ∧ ∀j,0≤s j :=
  thesis_restoration_iff spec (scalar 1) x s

/-- Actual all-five-slack lower bound, with no box imposed on x. -/
theorem restoration_bound (x : V) (s : RealVector 5)
    (hg : ∀j,model.g j (x,scalar 1)≤s j) (hs : ∀j,0≤s j) :
    (1/2:ℝ)≤∑j,s j := by
  have h0 := hg 0
  have h1 := hg 1
  norm_num [model,scalar] at h0 h1
  have h01 : (1/2:ℝ)≤s 0+s 1 := by
    by_cases hx : x 0≤ -(1/2)
    · linarith [hs 0]
    · have hx0 : -(1/2)≤x 0 := by linarith
      by_cases hx1 : x 0≤0
      · have ha : 0≤2*x 0+1 := by linarith
        have hb : 0≤4*(x 0)^2-2*x 0+1/2 := by nlinarith [sq_nonneg (x 0)]
        have hc := mul_nonneg ha hb
        nlinarith
      · have hc : 0≤(x 0)^3 := pow_nonneg (by linarith) _
        linarith [hs 1]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change (1/2:ℝ)≤s 0+(s 1+(s 2+(s 3+s 4)))
  linarith [hs 2,hs 3,hs 4]

theorem restoration_minimum : IsMinimizer (restSet model (scalar 1)) restCost
    (weightedInsert (scalar (-(1/2))) slack) := by
  constructor
  · rw [restSet_insert_iff]
    refine ⟨(fun i => Fin.elim0 i),?_,?_⟩ <;>
      intro j <;> fin_cases j <;> norm_num [model,soft,slack,scalar]
  · intro q hq
    let x : V := weightedX (s:=5) q
    let s : RealVector 5 := weightedV (n:=1) q
    have he : weightedInsert x s=q := weightedInsert_project q
    rw [←he] at hq ⊢
    have hh := (restSet_insert_iff model (scalar 1) x s).mp hq
    have hb := restoration_bound x s hh.2.1 hh.2.2
    rw [restCost_insert,restCost_insert]
    simpa [slack,Fin.sum_univ_succ] using hb

theorem restoration_value : restCost (weightedInsert (scalar (-(1/2))) slack)=(1/2:ℝ) := by
  norm_num [restCost_insert,slack,Fin.sum_univ_succ]

theorem event_restoration_minimum :
    IsMinimizer (restSet spec.model (intCast badEvent.target)) restCost
      (weightedInsert badEvent.x slack) := by
  rw [←chosen_assignment]
  exact restoration_minimum

theorem cubic_nonaffine : ¬ AffineRow (model.g 0) := by
  rintro ⟨ax,ay,b,h⟩
  have h0 := h (pt 0 0)
  have h1 := h (pt 1 0)
  have h2 := h (pt 2 0)
  norm_num [model,LinearForm,pt,scalar,Fin.sum_univ_one] at h0 h1 h2
  linarith

theorem zero_residual : model.g 0 badEvent.anchor=0 := by
  norm_num [anchor,model,pt,scalar]

theorem weak_selected : (0:Fin 5)∈spec.selected badEvent.anchor :=
  ⟨cubic_nonaffine,zero_residual.symm.le⟩

theorem strict_not_selected : ¬ (0<model.g 0 badEvent.anchor) := by
  rw [zero_residual]; exact lt_irrefl 0

theorem exterior_origin : badEvent.anchor∉spec.domain := by
  change badEvent.anchor∉domain
  rw [anchor,domain_iff]
  norm_num [pt,scalar]

theorem event_invalid : ¬ EventValid spec badEvent := fun h => exterior_origin h.1

theorem bad_tangent (p : P) :
    model.g 0 badEvent.anchor+Dg badEvent.anchor 0 (p-badEvent.anchor)=
      6*p.1 0+2*p.2 0+1 := by
  norm_num [anchor,model,Dg,pt,scalar]
  ring

theorem tangent_excludes_original :
    0<model.g 0 badEvent.anchor+Dg badEvent.anchor 0 (incumbent-badEvent.anchor) := by
  rw [bad_tangent]
  norm_num [incumbent,pt,scalar]

theorem next_epigraph_empty : epigraph spec seed [badEvent]=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨_,_,hseed,_,hev⟩ := (epigraph_mem_iff spec seed [badEvent] z).mp hz
  have hx := hseed 1
  have hy := hseed 3
  change model.g 1 seed+Dg seed 1 (z.1-seed)≤0 at hx
  change model.g 3 seed+Dg seed 3 (z.1-seed)≤0 at hy
  rw [seed_lower_x] at hx
  rw [seed_lower_y] at hy
  have hb := (hev badEvent (by simp)).2 0 weak_selected
  change model.g 0 badEvent.anchor+Dg badEvent.anchor 0 (z.1-badEvent.anchor)≤0 at hb
  rw [bad_tangent] at hb
  linarith

theorem next_master_empty : master spec seed [badEvent]=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have h := hz.1
  rw [next_epigraph_empty] at h
  exact h

theorem noGood_preserves_original : ∀p∈spec.original,noGoods [badEvent] p := by
  intro p hp e he _ hy
  have heq : e=badEvent := List.mem_singleton.mp he
  subst e
  have hy' : p.2=scalar 1 := hy.trans chosen_assignment.symm
  have hg := ((thesis_original_iff spec boundRows p).mp hp).1
  apply failed_fiber
  refine ⟨p.1,hard _,?_⟩
  intro j
  simpa only [spec,←hy',Prod.eta] using hg j

/-- The duplicated integer box in the reused pure carrier is already enforced
by the source's all-row seed; it does not harden the restoration problem. -/
theorem source_master_correspondence (H : List (Event spec)) (z : P × ℝ) :
    z∈master spec seed H ↔
      z∈sourceMaster model objective (family spec seed H) (familyDf spec seed H) ∧
      noGoods H z.1 :=
  thesis_master_iff spec boundRows analytic seed H
    ((relaxation_iff seed).mp seed_feasible).2 z

/-- One bounded source-local countercontrol; all clauses are proved, not oracle
fields. The event is deliberately outside the accepted valid execution relation. -/
theorem all_soft_origin_countercontrol :
    Analytic spec ∧ ContDiff ℝ 1 objective ∧ (∀j,ContDiff ℝ 1 (model.g j)) ∧
    (∀p,HasFDerivAt objective (Df p) p ∧ ∀j,HasFDerivAt (model.g j) (Dg p j) p) ∧
    Bornology.IsBounded spec.relaxation ∧
    IsMinimizer spec.relaxation objective seed ∧ ¬ integral seed ∧
    IsMinimizer (master spec seed []) Prod.snd initialChoice ∧
    initialChoice.1.2=intCast badEvent.target ∧
    ¬ (fiber model (scalar 1)).Nonempty ∧
    IsMinimizer (restSet model (scalar 1)) restCost
      (weightedInsert (scalar (-(1/2))) slack) ∧
    restCost (weightedInsert (scalar (-(1/2))) slack)=(1/2:ℝ) ∧
    model.g 0 badEvent.anchor=0 ∧ (0:Fin 5)∈spec.selected badEvent.anchor ∧
    ¬ EventValid spec badEvent ∧ incumbent∈spec.original ∧
    0<model.g 0 badEvent.anchor+Dg badEvent.anchor 0 (incumbent-badEvent.anchor) ∧
    (∀p∈spec.original,noGoods [badEvent] p) ∧
    epigraph spec seed [badEvent]=∅ ∧ master spec seed [badEvent]=∅ ∧
    (∀H z,z∈master spec seed H ↔
      z∈sourceMaster model objective (family spec seed H) (familyDf spec seed H) ∧
      noGoods H z.1) :=
  ⟨analytic,objective_C1,row_C1,(fun p => ⟨objective_derivative p,row_derivative p⟩),
    relaxation_bounded,seed_minimum,seed_fractional,
    first_master_minimum,chosen_assignment,failed_fiber,restoration_minimum,restoration_value,
    zero_residual,weak_selected,
    event_invalid,original_nonempty,tangent_excludes_original,noGood_preserves_original,
    next_epigraph_empty,next_master_empty,source_master_correspondence⟩

end Chapter03.OAExec.RestorationOrigin
