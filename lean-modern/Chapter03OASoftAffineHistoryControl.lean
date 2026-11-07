module

public import Chapter03OASoftMasterBounds
public import Chapter03OAExecHistory
public import Chapter03OAExecControlBase

@[expose] public section

/-! One article-domain affine-history control. Selected seed rows are soft,
weights are stored per generated occurrence, successful fibers are not excluded,
and the incumbent uses the intended minimum update. This is a concrete family of
exact finite prefixes, not a hard RawStep, software trace or generic driver. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec Chapter03.OAExec.Controls
namespace Chapter03.OASoftMaster.AffineHistory

def objective (p : P) : ℝ := (p.1 0)^2+(p.2 0-1/2)^2
def Df (p : P) : P →L[ℝ] ℝ := (2*p.1 0) • cx+(2*(p.2 0-1/2)) • cy
def model : ModelData 1 1 1 2 where
  g _ p := p.2 0-3/4-p.1 0
  A := ![scalar (-1),scalar 1]
  B _ := scalar 0
  rhs := ![1,1]
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1
def Dg (_ : P) (_ : Fin 1) : P →L[ℝ] ℝ := cy-cx
def domain : Set P := Set.Icc (pt (-1) 0) (pt 1 1)
def spec : Data 1 1 1 2 where
  model := model
  f := objective
  Df := Df
  Dg := Dg
  domain := domain
def seed : P := pt 0 (1/2)
def solveX (b : ℝ) : ℝ := if b=0 then 0 else 1/4
def solution (b : ℝ) : P := pt (solveX b) b
def multiplier (b : ℝ) : ℝ := if b=0 then 0 else 1/2
def choice : P := pt (-(3/8)) 1

theorem hard_iff (p : P) : p∈model.linearRegion ↔ -1≤p.1 0 ∧ p.1 0≤1 := by
  simp [ModelData.linearRegion,LinearForm,model,Fin.forall_fin_two,Fin.sum_univ_one,scalar]
  intro _; constructor <;> intro h <;> linarith

theorem domain_iff (p : P) : p∈domain ↔
    -1≤p.1 0 ∧ p.1 0≤1 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  simp [domain,Set.mem_Icc,Prod.le_def,Pi.le_def,Fin.forall_fin_one,pt,scalar]
  tauto

theorem relaxation_iff (p : P) : p∈spec.relaxation ↔
    p.2 0-3/4-p.1 0≤0 ∧ p∈domain := by
  rw [relaxation_mem_iff,domain_iff]
  change (∀j : Fin 1, p.2 0-3/4-p.1 0≤0) ∧ p∈model.linearRegion ∧
    (∀i : Fin 1, 0≤p.2 i ∧ p.2 i≤1) ↔ _
  simp only [Fin.forall_fin_one,hard_iff]
  tauto

theorem original_iff (p : P) : p∈spec.original ↔
    p.2 0-3/4-p.1 0≤0 ∧ (-1≤p.1 0 ∧ p.1 0≤1) ∧ (p.2 0=0 ∨ p.2 0=1) := by
  rw [Data.original,source_feasible_iff]
  change (p∈Set.univ ∧ (∀j : Fin 1,p.2 0-3/4-p.1 0≤0) ∧ p∈model.linearRegion ∧
    (∃z : IntVector 1,z∈IntegerBox (scalar 0) (scalar 1) ∧ p.2=fun i => (z i : ℝ))) ↔ _
  rw [integer_binary,hard_iff]
  simp [DICOPT.Binary,Fin.forall_fin_one]

theorem fiber_iff_scalar (x : V) (b : ℝ) : x∈fiber model (scalar b) ↔
    (-1≤x 0 ∧ x 0≤1) ∧ b-3/4-x 0≤0 := by
  change ((x,scalar b)∈model.linearRegion ∧ (∀j : Fin 1,b-3/4-x 0≤0)) ↔ _
  rw [hard_iff]; simp [Fin.forall_fin_one]

theorem objective_derivative (p : P) : HasFDerivAt objective (Df p) p := by
  change HasFDerivAt (fun q : P => (q.1 0)^2+(q.2 0-1/2)^2) (Df p) p
  simpa [Df,sub_eq_add_neg] using
    (square_derivative p).fun_add (affine_square_derivative cy (-(1/2)) p)

theorem row_derivative (p : P) (j : Fin 1) :
    HasFDerivAt (model.g j) (Dg p j) p :=
  (cy.hasFDerivAt.sub_const (3/4)).sub cx.hasFDerivAt

theorem objective_C1 : ContDiff ℝ 1 objective :=
  (cx.contDiff.pow 2).add ((cy.contDiff.sub contDiff_const).pow 2)

theorem row_C1 (j : Fin 1) : ContDiff ℝ 1 (model.g j) :=
  (cy.contDiff.sub contDiff_const).sub cx.contDiff

theorem objective_convex : ConvexOn ℝ Set.univ objective := by
  change ConvexOn ℝ Set.univ (fun q : P => (q.1 0)^2+(q.2 0-1/2)^2)
  simpa [Pi.add_def,sub_eq_add_neg] using
    square_convex.add (affine_square_convex cy (-(1/2)))

theorem row_convex (j : Fin 1) : ConvexOn ℝ Set.univ (model.g j) := by
  convert affine_convex (-1) 1 (-(3/4)) using 1
  funext p; simp [model]; ring

theorem row_affine (j : Fin 1) : AffineRow (model.g j) := by
  refine ⟨scalar (-1),scalar 1,3/4,?_⟩
  intro p; simp [model,LinearForm,scalar,Fin.sum_univ_one]; ring

theorem selected_empty (p : P) : spec.selected p=∅ := by
  ext j
  simp [Data.selected,Data.nonlinear,spec,row_affine]

theorem objective_nonlinear : ¬AffineRow objective := by
  intro h
  have hh := affine_second_difference h
  norm_num [objective,pt,scalar] at hh

theorem domain_convex : Convex ℝ domain := by
  intro p hp q hq a b ha hb hab
  rw [domain_iff] at hp hq ⊢
  change -1≤a*p.1 0+b*q.1 0 ∧ a*p.1 0+b*q.1 0≤1 ∧
    0≤a*p.2 0+b*q.2 0 ∧ a*p.2 0+b*q.2 0≤1
  obtain ⟨hp0,hp1,hpy0,hpy1⟩ := hp
  obtain ⟨hq0,hq1,hqy0,hqy1⟩ := hq
  constructor
  · nlinarith [mul_nonneg ha (show 0≤p.1 0+1 by linarith),mul_nonneg hb (show 0≤q.1 0+1 by linarith)]
  constructor
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hp1),mul_nonneg hb (sub_nonneg.mpr hq1)]
  constructor
  · exact add_nonneg (mul_nonneg ha hpy0) (mul_nonneg hb hqy0)
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hpy1),mul_nonneg hb (sub_nonneg.mpr hqy1)]

theorem analytic : Analytic spec where
  convex_f := objective_convex.subset (Set.subset_univ _) domain_convex
  convex_g j := (row_convex j).subset (Set.subset_univ _) domain_convex
  original_domain p hp := ((relaxation_iff p).mp (original_subset_relaxation spec hp)).2
  derivative_f p _ := objective_derivative p
  derivative_g p _ := row_derivative p

theorem relaxation_compact : IsCompact spec.relaxation := by
  have he : spec.relaxation=domain∩{p | model.g 0 p≤0} := by
    ext p; rw [relaxation_iff]; simp [model,and_comm]
  rw [he]
  exact (isCompact_Icc : IsCompact domain).inter_right
    (isClosed_le (row_C1 0).continuous continuous_const)

theorem seed_minimum : IsMinimizer spec.relaxation objective seed := by
  constructor
  · rw [relaxation_iff,domain_iff]; norm_num [seed,pt,scalar]
  · intro p _; norm_num [objective,seed,pt,scalar]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem seed_unique (p : P) (hp : IsMinimizer spec.relaxation objective p) : p=seed := by
  have h := hp.2 seed seed_minimum.1
  norm_num [objective,seed,pt,scalar] at h
  apply point_ext
  · change p.1 0=0; nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.2 0-1/2)]
  · change p.2 0=1/2; nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.2 0-1/2)]

theorem seed_fractional : ¬integral seed := by
  rintro ⟨y,hy⟩
  have hh := congrFun hy 0
  norm_num [seed,pt,scalar,intCast] at hh
  have hlo : (0:ℤ)<y 0 := by exact_mod_cast (show (0:ℝ)<(y 0:ℝ) by linarith)
  have hhi : y 0<(1:ℤ) := by exact_mod_cast (show (y 0:ℝ)<1 by linarith)
  omega

/-- Actual joint rows include g and both sides of X and Y. -/
def jointRows : Fin 5 → P → ℝ :=
  ![model.g 0,fun p => -1-p.1 0,fun p => p.1 0-1,fun p => -p.2 0,fun p => p.2 0-1]
def jointD : Fin 5 → P →L[ℝ] ℝ := ![cy-cx,-cx,cx,-cy,cy]
def seedMultiplier (_ : Fin 5) : ℝ := 0

theorem joint_rows_exact (p : P) : (∀j,jointRows j p≤0) ↔ p∈spec.relaxation := by
  rw [relaxation_iff,domain_iff]
  simp [jointRows,model,Fin.forall_fin_succ]

theorem joint_derivative (p : P) (j : Fin 5) : HasFDerivAt (jointRows j) (jointD j) p := by
  fin_cases j
  · exact row_derivative p 0
  · exact cx.hasFDerivAt.const_sub (-1)
  · exact cx.hasFDerivAt.sub_const 1
  · exact cy.hasFDerivAt.neg
  · exact cy.hasFDerivAt.sub_const 1

theorem joint_seed_strict (j : Fin 5) : jointRows j seed<0 := by
  fin_cases j <;> norm_num [jointRows,model,seed,pt,scalar]

theorem seed_LICQ : LinearIndependent ℝ
    (fun i : {j : Fin 5 // jointRows j seed=0} => jointD i.1) := by
  have : IsEmpty {j : Fin 5 // jointRows j seed=0} :=
    ⟨fun j => (ne_of_lt (joint_seed_strict j.1)) j.2⟩
  exact linearIndependent_empty_type

theorem seed_zero_KKT :
    (∀j : Fin 5,seedMultiplier j=0 ∧ 0≤seedMultiplier j ∧ seedMultiplier j*jointRows j seed=0) ∧
    Df seed+(∑j : Fin 5,seedMultiplier j • jointD j)=0 := by
  constructor
  · simp [seedMultiplier]
  · apply ContinuousLinearMap.ext
    intro p; norm_num [Df,seed,pt,scalar,seedMultiplier]

theorem fixed_minimum (b : ℝ) (hb : b=0 ∨ b=1) :
    IsMinimizer (fiber model (scalar b)) (fiberObjective objective (scalar b))
      (scalar (solveX b)) := by
  rcases hb with rfl|rfl
  · constructor
    · rw [fiber_iff_scalar]; norm_num [solveX,scalar]
    · intro x _
      norm_num [fiberObjective,objective,solveX,scalar]
      exact sq_nonneg _
  · constructor
    · rw [fiber_iff_scalar]; norm_num [solveX,scalar]
    · intro x hx
      rw [fiber_iff_scalar] at hx
      norm_num [fiberObjective,objective,solveX,scalar]
      nlinarith [sq_nonneg (x 0-1/4)]

theorem fixed_unique (b : ℝ) (hb : b=0 ∨ b=1) (x : V)
    (hx : IsMinimizer (fiber model (scalar b)) (fiberObjective objective (scalar b)) x) :
    x=scalar (solveX b) := by
  have hh := hx.2 _ (fixed_minimum b hb).1
  have hf := (fiber_iff_scalar x b).mp hx.1
  apply scalar_ext
  rcases hb with rfl|rfl
  · norm_num [fiberObjective,objective,solveX,scalar] at hh ⊢
    nlinarith [sq_nonneg (x 0)]
  · norm_num [fiberObjective,objective,solveX,scalar] at hh ⊢
    nlinarith [sq_nonneg (x 0-1/4)]

def fixedKKT (b : ℝ) (hb : b=0 ∨ b=1) :
    FixedKKT model objective (scalar (solveX b)) (scalar b) where
  Df := Df (solution b)
  Dg := Dg (solution b)
  lambda _ := multiplier b
  mu _ := 0
  primal := (fixed_minimum b hb).1
  derivative_f := objective_derivative _
  derivative_g := row_derivative _
  lambda_nonneg := by intro j; rcases hb with rfl|rfl <;> norm_num [multiplier]
  mu_nonneg := by simp
  soft_compl := by intro j; rcases hb with rfl|rfl <;> norm_num [multiplier,soft,model,solveX,scalar]
  hard_compl := by simp
  stationarity := by
    ext v
    rcases hb with rfl|rfl <;>
      norm_num [Df,Dg,solution,solveX,multiplier,pt,scalar,Fin.sum_univ_one]

def fixedActive (b : ℝ) : Set (Fin 1 ⊕ Fin 2) :=
  {i | Sum.elim (fun j => soft model (scalar b) j (scalar (solveX b)))
    (fun j => hard model (scalar b) j (scalar (solveX b))) i=0}
def fixedNormal (b : ℝ) : (Fin 1 ⊕ Fin 2) → V →L[ℝ] ℝ :=
  Sum.elim (fun j => restrict (Dg (solution b) j)) (fiberLinearRow model)

theorem fixed_active_zero : fixedActive 0=∅ := by
  ext i; cases i with
  | inl j => fin_cases j; norm_num [fixedActive,soft,model,solveX,scalar]
  | inr j => fin_cases j <;> norm_num [fixedActive,hard,linearResidual,model,solveX,scalar,LinearForm,Fin.sum_univ_one]

theorem fixed_active_one : fixedActive 1={Sum.inl 0} := by
  ext i; cases i with
  | inl j => fin_cases j; norm_num [fixedActive,soft,model,solveX,scalar]
  | inr j => fin_cases j <;> norm_num [fixedActive,hard,linearResidual,model,solveX,scalar,LinearForm,Fin.sum_univ_one] <;> simp

theorem fixed_LICQ (b : ℝ) (hb : b=0 ∨ b=1) :
    LinearIndependent ℝ (fun i : fixedActive b => fixedNormal b i.1) := by
  change LinearIndepOn ℝ (fixedNormal b) (fixedActive b)
  rcases hb with rfl|rfl
  · rw [fixed_active_zero]; exact linearIndepOn_empty ℝ _
  · rw [fixed_active_one,linearIndepOn_singleton_iff]
    intro h
    have hh := congrArg (fun L : V →L[ℝ] ℝ => L (scalar 1)) h
    norm_num [fixedNormal,Dg,scalar] at hh

theorem original_minimum : IsMinimizer spec.original objective (solution 0) := by
  constructor
  · rw [original_iff]; norm_num [solution,solveX,pt,scalar]
  · intro p hp
    have hh := (original_iff p).mp hp
    rcases hh.2.2 with hy|hy <;>
      norm_num [objective,solution,solveX,pt,scalar,hy] <;> exact sq_nonneg _

def event : Event spec where
  target _ := 1
  target_mem := by intro i; norm_num [spec,model,scalar]
  x := scalar (1/4)
  restoration := none

@[simp] theorem event_anchor : event.anchor=solution 1 := by
  ext i <;> simp [event,Event.anchor,solution,solveX,intCast,pt,scalar]

theorem event_valid : EventValid spec event := by
  constructor
  · change event.anchor∈domain
    rw [event_anchor,domain_iff]; norm_num [solution,solveX,pt,scalar]
  · have hi : intCast event.target=scalar 1 := by ext i; simp [intCast,event,scalar]
    rw [show event.restoration=none from rfl,hi]
    change IsMinimizer (fiber model (scalar 1)) (fiberObjective objective (scalar 1))
      (scalar (1/4)) ∧ Nonempty (FixedKKT model objective (scalar (1/4)) (scalar 1))
    constructor
    · simpa [solveX] using fixed_minimum 1 (Or.inr rfl)
    · have h : Nonempty (FixedKKT model objective (scalar (solveX 1)) (scalar 1)) :=
        ⟨fixedKKT 1 (Or.inr rfl)⟩
      simpa [solveX] using h

def history (n : ℕ) : List (Event spec) := List.replicate n event
def tangents (n : ℕ) := family spec seed (history n)
def objectiveTangents (n : ℕ) := familyDf spec seed (history n)

theorem history_valid (n : ℕ) : ValidHistory spec seed (history n) := by
  constructor
  · change seed∈domain; rw [domain_iff]; norm_num [seed,pt,scalar]
  · intro e he
    have hh : e=event := (List.mem_replicate.mp he).2
    subst e; exact event_valid

theorem keep_true (n : ℕ) (p : P) : noGoods (history n) p := by
  intro e he hn
  have hh : e=event := (List.mem_replicate.mp he).2
  subst e; exact False.elim (hn rfl)

theorem selected_iff (n : ℕ) (i : Fin ((history n).length+1)) (j : Fin 1) :
    j∈(tangents n).selected i ↔ i=0 := by
  refine Fin.cases ?_ ?_ i
  · simp [tangents,family]
  · intro k
    simp [tangents,family,selected_empty]

def storedMultiplier (n : ℕ) (i : Fin ((history n).length+1)) : ℝ :=
  if i=0 then seedMultiplier 0 else (fixedKKT 1 (Or.inr rfl)).lambda 0
def weight (n : ℕ) (a : Occurrence (tangents n)) : ℝ :=
  1000*|storedMultiplier n a.1.1|

theorem weight_zero (n : ℕ) (a : Occurrence (tangents n)) : weight n a=0 := by
  have hi := (selected_iff n a.1.1 a.1.2).mp a.2
  simp [weight,storedMultiplier,seedMultiplier,hi]

def seedOccurrence (n : ℕ) : Occurrence (tangents n) :=
  ⟨(0,0),(selected_iff n 0 0).mpr rfl⟩

theorem sole_occurrence (n : ℕ) (a : Occurrence (tangents n)) : a=seedOccurrence n := by
  apply Subtype.ext
  apply Prod.ext
  · exact (selected_iff n a.1.1 a.1.2).mp a.2
  · exact Subsingleton.elim _ _

theorem stored_multiplier_exact (n : ℕ) :
    storedMultiplier n 0=seedMultiplier 0 ∧
    ∀i : Fin (history n).length,
      storedMultiplier n i.succ=(fixedKKT 1 (Or.inr rfl)).lambda 0 := by
  simp [storedMultiplier]

def selectedChoice (n : ℕ) : Candidate (tangents n) := (choice,0,fun _ => 5/8)
def softMaster (n : ℕ) := OASoftMaster.master model objective (tangents n)
  (objectiveTangents n) (noGoods (history n))

theorem seed_tangent (p : P) : objective seed+Df seed (p-seed)=0 := by
  norm_num [objective,Df,seed,pt,scalar]

theorem next_tangent (p : P) :
    objective (solution 1)+Df (solution 1) (p-solution 1)=p.1 0/2+p.2 0-13/16 := by
  norm_num [objective,Df,solution,solveX,pt,scalar]
  ring

theorem chosen_feasible (n : ℕ) : selectedChoice n∈softMaster n := by
  refine ⟨?_,?_,keep_true n choice,?_,?_,?_⟩
  · rw [hard_iff]; norm_num [selectedChoice,choice,pt,scalar]
  · refine ⟨(fun _ => 1),?_,?_⟩
    · intro i; norm_num [model,scalar]
    · ext i; simp [selectedChoice,choice,pt,scalar]
  · intro a; norm_num [selectedChoice]
  · intro i
    refine Fin.cases ?_ ?_ i
    · change objective seed+Df seed (choice-seed)≤0
      rw [seed_tangent]
    · intro k
      have he : ((history n).get k)=event := by
        have hk : ((history n).get k) ∈ List.replicate n event := by
          change ((history n).get k) ∈ history n
          exact List.get_mem _ _
        exact List.eq_of_mem_replicate hk
      change objective ((history n).get k).anchor+
        Df ((history n).get k).anchor (choice-((history n).get k).anchor)≤0
      rw [he,event_anchor,next_tangent]
      norm_num [choice,pt,scalar]
  · intro a
    change model.g a.1.2 ((tangents n).origin a.1.1)+
      Dg ((tangents n).origin a.1.1) a.1.2 (choice-(tangents n).origin a.1.1)≤5/8
    rw [affine_tangent (row_affine _) (row_derivative _ _)]
    norm_num [model,choice,pt,scalar]

theorem cost_eq_alpha (n : ℕ) (z : Candidate (tangents n)) : cost (weight n) z=z.2.1 := by
  simp [cost,penalty,weight_zero]

theorem uncovered_multiplier (n : ℕ) :
    weight n (seedOccurrence n)=0 ∧
    1000*|(fixedKKT 1 (Or.inr rfl)).lambda 0|=500 ∧
    (fixedKKT 1 (Or.inr rfl)).lambda 0*(selectedChoice n).2.2 (seedOccurrence n)=5/16 := by
  norm_num [weight_zero,fixedKKT,multiplier,selectedChoice]

theorem chosen_minimum (n : ℕ) :
    IsMinimizer (softMaster n) (cost (weight n)) (selectedChoice n) := by
  refine ⟨chosen_feasible n,?_⟩
  intro z hz
  have hh := hz.2.2.2.2.1 0
  change objective seed+Df seed (z.1-seed)≤z.2.1 at hh
  rw [seed_tangent] at hh
  simpa [cost_eq_alpha,selectedChoice] using hh

/-- The stripped alpha of the exhibited exact master optimizer. -/
def lowerBound (n : ℕ) : ℝ := (selectedChoice n).2.1
def upperBound : ℕ → WithTop ℝ
  | 0 => ⊤
  | n+1 => min (upperBound n) (objective (solution 1))

theorem intended_upper (n : ℕ) : upperBound (n+1)=(5/16:ℝ) := by
  induction n with
  | zero => norm_num [upperBound,objective,solution,solveX,pt,scalar]
  | succ n ih => rw [upperBound,ih]; norm_num [objective,solution,solveX,pt,scalar]

theorem exact_prefix (n : ℕ) :
    ValidHistory spec seed (history n) ∧
    IsMinimizer (softMaster n) (cost (weight n)) (selectedChoice n) ∧
    (selectedChoice n).1.2=intCast event.target ∧
    history (n+1)=history n++[event] ∧ EventValid spec event ∧
    (∀p,noGoods (history n) p) ∧
    cost (weight n) (selectedChoice n)=0 ∧ (selectedChoice n).2.1=lowerBound n ∧
    lowerBound (n+1)=(selectedChoice n).2.1 ∧
    upperBound (n+1)=min (upperBound n) (objective event.anchor) ∧
    upperBound (n+1)=(5/16:ℝ) ∧
    (lowerBound (n+1):WithTop ℝ)<upperBound (n+1) := by
  refine ⟨history_valid n,chosen_minimum n,?_,?_,event_valid,keep_true n,?_,rfl,rfl,?_,intended_upper n,?_⟩
  · ext i; simp [selectedChoice,choice,event,intCast,pt,scalar]
  · simp [history,List.replicate_succ']
  · rw [cost_eq_alpha]; rfl
  · rw [event_anchor]; rfl
  · rw [intended_upper]; norm_num [lowerBound,selectedChoice]

/-- One qualified control: all concrete source premises and exact finite-prefix
choices. The interpretation is recorded above; no universal tie rule is claimed. -/
theorem qualified_soft_affine_history_countercontrol :
    ContDiff ℝ 1 objective ∧ (∀j,ContDiff ℝ 1 (model.g j)) ∧
    ConvexOn ℝ Set.univ objective ∧ (∀j,ConvexOn ℝ Set.univ (model.g j)) ∧
    (∀p,HasFDerivAt objective (Df p) p) ∧
    (∀p j,HasFDerivAt (model.g j) (Dg p j) p) ∧
    Analytic spec ∧ IsCompact spec.relaxation ∧
    (IntegerBox model.lo model.hi).Finite ∧
    ¬AffineRow objective ∧ (∀j,AffineRow (model.g j)) ∧
    IsMinimizer spec.relaxation objective seed ∧ ¬integral seed ∧
    (∀p,IsMinimizer spec.relaxation objective p → p=seed) ∧
    (∀p,(∀j,jointRows j p≤0) ↔ p∈spec.relaxation) ∧
    (∀p j,HasFDerivAt (jointRows j) (jointD j) p) ∧
    (∀j,jointRows j seed<0) ∧
    ((∀j : Fin 5,seedMultiplier j=0 ∧ 0≤seedMultiplier j ∧ seedMultiplier j*jointRows j seed=0) ∧
      Df seed+(∑j : Fin 5,seedMultiplier j • jointD j)=0) ∧
    LinearIndependent ℝ (fun i : {j : Fin 5 // jointRows j seed=0} => jointD i.1) ∧
    (∀b,b=0 ∨ b=1 →
      IsMinimizer (fiber model (scalar b)) (fiberObjective objective (scalar b)) (scalar (solveX b)) ∧
      (∀x,IsMinimizer (fiber model (scalar b)) (fiberObjective objective (scalar b)) x → x=scalar (solveX b)) ∧
      Nonempty (FixedKKT model objective (scalar (solveX b)) (scalar b)) ∧
      LinearIndependent ℝ (fun i : fixedActive b => fixedNormal b i.1)) ∧
    IsMinimizer spec.original objective (solution 0) ∧
    objective (solution 0)=1/4 ∧ objective (solution 1)=5/16 ∧
    model.g 0 choice=5/8 ∧ multiplier 1=1/2 ∧
    (∀p,spec.selected p=∅) ∧
    (∀n a,weight n a=0) ∧
    (∀n a,a=seedOccurrence n) ∧
    (∀n,storedMultiplier n 0=seedMultiplier 0 ∧ ∀i : Fin (history n).length,
      storedMultiplier n i.succ=(fixedKKT 1 (Or.inr rfl)).lambda 0) ∧
    (∀n,weight n (seedOccurrence n)=0 ∧
      1000*|(fixedKKT 1 (Or.inr rfl)).lambda 0|=500 ∧
      (fixedKKT 1 (Or.inr rfl)).lambda 0*(selectedChoice n).2.2 (seedOccurrence n)=5/16) ∧
    lowerBound 0=objective seed ∧ (lowerBound 0:WithTop ℝ)<upperBound 0 ∧
    (∀n,ValidHistory spec seed (history n) ∧
      IsMinimizer (softMaster n) (cost (weight n)) (selectedChoice n) ∧
      (selectedChoice n).1.2=intCast event.target ∧
      history (n+1)=history n++[event] ∧ EventValid spec event ∧
      (∀p,noGoods (history n) p) ∧
      cost (weight n) (selectedChoice n)=0 ∧ (selectedChoice n).2.1=lowerBound n ∧
      lowerBound (n+1)=(selectedChoice n).2.1 ∧
      upperBound (n+1)=min (upperBound n) (objective event.anchor) ∧
      upperBound (n+1)=(5/16:ℝ) ∧
      (lowerBound (n+1):WithTop ℝ)<upperBound (n+1)) := by
  refine ⟨objective_C1,row_C1,objective_convex,row_convex,objective_derivative,row_derivative,
    analytic,relaxation_compact,integerBox_finite _ _,objective_nonlinear,row_affine,seed_minimum,seed_fractional,
    seed_unique,joint_rows_exact,joint_derivative,joint_seed_strict,seed_zero_KKT,seed_LICQ,
    ?_,original_minimum,?_,?_,?_,?_,selected_empty,weight_zero,sole_occurrence,
    stored_multiplier_exact,uncovered_multiplier,?_,?_,exact_prefix⟩
  · intro b hb
    exact ⟨fixed_minimum b hb,fixed_unique b hb,⟨fixedKKT b hb⟩,fixed_LICQ b hb⟩
  · norm_num [objective,solution,solveX,pt,scalar]
  · norm_num [objective,solution,solveX,pt,scalar]
  · norm_num [model,choice,pt,scalar]
  · norm_num [multiplier]
  · norm_num [lowerBound,selectedChoice,objective,seed,pt,scalar]
  · simp [upperBound,lowerBound,selectedChoice]

end Chapter03.OASoftMaster.AffineHistory
