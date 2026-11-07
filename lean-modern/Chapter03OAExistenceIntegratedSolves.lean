module

public import Chapter03OAExistenceIntegratedData

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Integrated

def fixedKKT : FixedKKT model objective (scalar (1/2)) (scalar 1) where
  Df := Df solution
  Dg := Dg solution
  lambda := scalar 0
  mu := scalar 1
  primal := fixed_minimum.1
  derivative_f := objective_derivative _
  derivative_g := row_derivative _
  lambda_nonneg := by simp [scalar]
  mu_nonneg := by simp [scalar]
  soft_compl := by simp [scalar]
  hard_compl := by
    intro i; fin_cases i
    norm_num [hard,linearResidual,model,LinearForm,scalar,Fin.sum_univ_one]
  stationarity := by
    ext v
    norm_num [Df,solution,restrict_apply,pt,scalar,Fin.sum_univ_one,
      fiberLinearRow_apply,LinearForm,model]

def active : Set (Fin 1 ⊕ Fin 1) :=
  {i | Sum.elim (fun j => soft model (scalar 1) j (scalar (1/2)))
      (fun k => hard model (scalar 1) k (scalar (1/2))) i=0}

theorem active_exact : active={Sum.inr 0} := by
  ext i
  cases i with
  | inl j => fin_cases j; norm_num [active,soft,model,scalar]
  | inr k => fin_cases k
             norm_num [active,hard,linearResidual,model,LinearForm,scalar,Fin.sum_univ_one]

theorem fixed_LICQ : LinearIndependent ℝ
    (fun i : active => Sum.elim (fun j => restrict (Dg solution j))
      (fun k => fiberLinearRow model k) i.1) := by
  change LinearIndepOn ℝ (fun i : Fin 1 ⊕ Fin 1 =>
    Sum.elim (fun j => restrict (Dg solution j)) (fun k => fiberLinearRow model k) i) active
  rw [active_exact,linearIndepOn_singleton_iff]
  intro h
  have hh := congrArg (fun L : V →L[ℝ] ℝ => L (scalar 1)) h
  norm_num [fiberLinearRow_apply,LinearForm,model,scalar,Fin.sum_univ_one] at hh

theorem hard_normal (v : V) : fiberLinearRow model 0 v=v 0 := by
  simp [fiberLinearRow_apply,LinearForm,model,scalar,Fin.sum_univ_one]

theorem fixed_residuals : model.g 0 solution=-(5/16:ℝ) ∧
    hard model (scalar 1) 0 (scalar (1/2))=0 := by
  norm_num [model,solution,pt,scalar,hard,linearResidual,LinearForm,Fin.sum_univ_one]

def slack : RealVector 1 := scalar (7/16)

theorem restoration_primal : weightedInsert (scalar 0) slack∈restSet model (scalar 0) := by
  rw [restSet_insert_iff]
  refine ⟨?_,?_,?_⟩ <;> intro j <;> fin_cases j <;>
    norm_num [hard,soft,linearResidual,model,LinearForm,scalar,slack,Fin.sum_univ_one]

theorem restoration_minimum :
    IsMinimizer (restSet model (scalar 0)) (restCost (n:=1) (l:=1))
      (weightedInsert (scalar 0) slack) := by
  refine ⟨restoration_primal,?_⟩
  intro q hq
  have hq' : weightedInsert (weightedX (n:=1) (s:=1) q)
      (weightedV (n:=1) (s:=1) q)∈restSet model (scalar 0) := by
    rw [weightedInsert_project]; exact hq
  have hg := ((restSet_insert_iff model (scalar 0) _ _).mp hq').2.1 0
  change (weightedX (n:=1) (s:=1) q 0)^2+7/16-0≤weightedV (n:=1) (s:=1) q 0 at hg
  change weightedLiftObjective (n:=1) (fun _ : Fin 1 => 1) _ ≤
    weightedLiftObjective (n:=1) (fun _ : Fin 1 => 1) q
  simp only [weightedLiftObjective_apply,Fin.sum_univ_one,weightedV_insert,
    scalar,slack,one_mul]
  nlinarith [sq_nonneg (weightedX (n:=1) (s:=1) q 0)]

theorem restoration_unique {x : V} {s : RealVector 1}
    (hm : IsMinimizer (restSet model (scalar 0)) (restCost (n:=1) (l:=1))
      (weightedInsert x s)) : x=scalar 0 ∧ s=slack := by
  have hg := ((restSet_insert_iff model (scalar 0) x s).mp hm.1).2.1 0
  have hh := hm.2 _ restoration_primal
  rw [restCost_insert,restCost_insert] at hh
  norm_num [soft,model,scalar,slack,Fin.sum_univ_one] at hg hh
  have hx : x 0=0 := by nlinarith [sq_nonneg (x 0)]
  refine ⟨scalar_ext hx,scalar_ext ?_⟩
  change s 0=7/16
  nlinarith [sq_nonneg (x 0)]

theorem restoration_positive : 0<restCost (weightedInsert (scalar 0) slack) := by
  rw [restCost_insert]; norm_num [slack,scalar,Fin.sum_univ_one]

def event0 : Event spec where
  target := target0
  target_mem := target0_mem
  x := scalar 0
  restoration := some slack

def event1 : Event spec where
  target := target1
  target_mem := target1_mem
  x := scalar (1/2)
  restoration := none

@[simp] theorem event0_anchor : event0.anchor=pt 0 0 := by
  simp [Event.anchor,event0,pt]
@[simp] theorem event1_anchor : event1.anchor=solution := by
  simp [Event.anchor,event1,solution,pt]

theorem event0_valid : EventValid spec event0 := by
  refine ⟨by norm_num [spec,domain,event0_anchor,pt,scalar],?_⟩
  change ¬ (fiber model (intCast target0)).Nonempty ∧
    IsMinimizer (restSet model (intCast target0)) restCost (weightedInsert (scalar 0) slack)
  rw [cast_target0]
  exact ⟨zero_fiber_empty,restoration_minimum⟩

theorem event1_valid : EventValid spec event1 := by
  refine ⟨by norm_num [spec,domain,event1_anchor,solution,pt,scalar],?_⟩
  change IsMinimizer (fiber model (intCast target1)) (fiberObjective objective (intCast target1))
    (scalar (1/2)) ∧ Nonempty (FixedKKT model objective (scalar (1/2)) (intCast target1))
  rw [cast_target1]
  exact ⟨fixed_minimum,⟨fixedKKT⟩⟩

theorem valid_event_cases {e : Event spec} (he : EventValid spec e) : e=event0 ∨ e=event1 := by
  rcases target_cases e.target e.target_mem with ht|ht
  · cases hr : e.restoration with
    | none =>
      have hm := event_fixed_minimum he hr
      exfalso
      apply zero_fiber_empty
      exact ⟨e.x,by simpa [spec,ht] using hm.1⟩
    | some s =>
      have hm := event_restoration_minimum he hr
      have hu := restoration_unique (by simpa [spec,ht] using hm)
      exact Or.inl (event_ext ht hu.1 (by simpa [hu.2,event0] using hr))
  · have hr : e.restoration=none := by
      by_contra hn
      apply event_empty he hn
      exact ⟨scalar (1/2),by simpa [spec,ht] using fixed_minimum.1⟩
    have hm := event_fixed_minimum he hr
    have hx := fixed_unique (by simpa [spec,ht] using hm)
    exact Or.inr (event_ext ht hx hr)

theorem seed_objective_tangent (q : P) :
    objective seed+Df seed (q-seed)=-q.1 0+q.2 0+3/4 := by
  norm_num [objective,Df,seed,pt,scalar]; ring

theorem seed_constraint_tangent (q : P) (j : Fin 1) :
    model.g j seed+Dg seed j (q-seed)=q.1 0-q.2 0+3/16 := by
  norm_num [model,Dg,seed,pt,scalar]; ring

theorem event0_rows (z : P×ℝ) : event0.rows z ↔
    1-2*z.1.1 0+z.1.2 0≤z.2 ∧ 7/16-z.1.2 0≤0 := by
  unfold Event.rows
  rw [event0_anchor]
  change (objective (pt 0 0)+Df (pt 0 0) (z.1-pt 0 0)≤z.2 ∧
    ∀j, (¬ AffineRow (model.g j) ∧ 0≤model.g j (pt 0 0)) →
      model.g j (pt 0 0)+Dg (pt 0 0) j (z.1-pt 0 0)≤0) ↔ _
  simp only [row_nonaffine,true_and]
  norm_num [objective,Df,model,Dg,pt,scalar,Fin.forall_fin_one]
  intro h
  constructor <;> intro h <;> linarith

theorem event1_rows (z : P×ℝ) : event1.rows z ↔ -z.1.1 0+z.1.2 0+3/4≤z.2 := by
  unfold Event.rows
  rw [event1_anchor]
  change (objective solution+Df solution (z.1-solution)≤z.2 ∧
    ∀j, (¬ AffineRow (model.g j) ∧ 0≤model.g j solution) →
      model.g j solution+Dg solution j (z.1-solution)≤0) ↔ _
  norm_num [objective,Df,model,Dg,solution,pt,scalar]
  constructor <;> intro h <;> linarith

end Chapter03.OAExec.Integrated
