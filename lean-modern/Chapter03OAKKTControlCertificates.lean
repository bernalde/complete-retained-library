module

public import Chapter03OAKKTSource
public import Chapter03OAKKTControlActive

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples
open scoped BigOperators
namespace Chapter03.OAKKT.Controls

def finalFixed : FixedKKT finalModel positiveF (scalar (1/2)) (scalar 1) where
  Df := positiveDf (pt (1/2) 1)
  Dg := finalDg (pt (1/2) 1)
  lambda := scalar 0
  mu := ![1,0]
  primal := by
    refine ⟨(final_hard _).mpr (by norm_num [scalar]),?_⟩
    intro j
    norm_num [finalModel,positiveG,scalar]
  derivative_f := positiveF_derivative _
  derivative_g := final_derivative _
  lambda_nonneg := by simp [scalar]
  mu_nonneg := by intro i; fin_cases i <;> norm_num
  soft_compl := by simp [scalar]
  hard_compl := by
    intro i; fin_cases i <;>
      norm_num [hard,linearResidual,finalModel,LinearForm,scalar,Fin.sum_univ_one]
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    norm_num [restrict_apply,positiveDf,pt,scalar,Fin.sum_univ_two,Fin.sum_univ_one,
      fiberLinearRow_apply,LinearForm,finalModel]

def thesisFixed : FixedKKT thesisModel positiveF (scalar (1/2)) (scalar 1) where
  Df := positiveDf (pt (1/2) 1)
  Dg := thesisDg (pt (1/2) 1)
  lambda := ![0,1,0,0,0]
  mu := Fin.elim0
  primal := by
    refine ⟨thesis_hard _,?_⟩
    rw [thesis_rows]
    norm_num [scalar]
  derivative_f := positiveF_derivative _
  derivative_g := thesis_derivative _
  lambda_nonneg := by intro i; fin_cases i <;> norm_num
  mu_nonneg i := Fin.elim0 i
  soft_compl := by
    intro i; fin_cases i <;>
      norm_num [soft,thesisModel,positiveG,scalar]
  hard_compl i := Fin.elim0 i
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    norm_num [restrict_apply,positiveDf,thesisDg,pt,scalar,Fin.sum_univ_succ]

def finalRestoration : SumKKT finalModel (scalar (1/2)) (scalar 0) (scalar (1/4)) where
  Dg := finalDg (pt (1/2) 0)
  lambda := scalar 1
  nu := scalar 0
  mu := ![1,0]
  primal := by
    rw [restSet_insert_iff]
    norm_num [hard,soft,linearResidual,finalModel,LinearForm,positiveG,scalar,
      Fin.sum_univ_one,Fin.forall_fin_two]
  derivative_g := final_derivative _
  lambda_nonneg := by simp [scalar]
  nu_nonneg := by simp [scalar]
  mu_nonneg := by intro i; fin_cases i <;> norm_num
  soft_compl := by norm_num [soft,finalModel,positiveG,scalar]
  slack_compl := by simp [scalar]
  slack_stationarity := by simp [scalar]
  hard_compl := by
    intro i; fin_cases i <;>
      norm_num [hard,linearResidual,finalModel,LinearForm,scalar,Fin.sum_univ_one]
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    norm_num [restrict_apply,positiveDg,finalDg,pt,scalar,Fin.sum_univ_two,
      Fin.sum_univ_one,fiberLinearRow_apply,LinearForm,finalModel]

def thesisRestoration : SumKKT thesisModel (scalar (1/2)) (scalar 0) thesisSlack where
  Dg := thesisDg (pt (1/2) 0)
  lambda := thesisLambda
  nu := thesisNu
  mu := Fin.elim0
  primal := by
    rw [restSet_insert_iff]
    exact ⟨fun i => Fin.elim0 i,thesis_slack_feasible.2,thesis_slack_feasible.1⟩
  derivative_g := thesis_derivative _
  lambda_nonneg := thesis_scalar_kkt.1
  nu_nonneg := thesis_scalar_kkt.2.1
  mu_nonneg i := Fin.elim0 i
  soft_compl := thesis_scalar_kkt.2.2.2.1
  slack_compl := thesis_scalar_kkt.2.2.2.2.1
  slack_stationarity := thesis_scalar_kkt.2.2.1
  hard_compl i := Fin.elim0 i
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    norm_num [restrict_apply,positiveDg,thesisDg,thesisLambda,pt,scalar,Fin.sum_univ_succ]

theorem final_fiber_minimum :
    IsMinimizer (fiber finalModel (scalar 1)) (fiberObjective positiveF (scalar 1))
      (scalar (1/2)) := by
  refine ⟨finalFixed.primal,?_⟩
  intro x hx
  have hl := ((final_hard _).mp hx.1).1
  norm_num [fiberObjective,positiveF,scalar]
  nlinarith [sq_nonneg (x 0-1/2)]

theorem thesis_fiber_minimum :
    IsMinimizer (fiber thesisModel (scalar 1)) (fiberObjective positiveF (scalar 1))
      (scalar (1/2)) := by
  refine ⟨thesisFixed.primal,?_⟩
  intro x hx
  have hl := ((thesis_rows _).mp hx.2).2.1
  norm_num [fiberObjective,positiveF,scalar]
  nlinarith [sq_nonneg (x 0-1/2)]

theorem final_zero_fiber_empty : ¬(fiber finalModel (scalar 0)).Nonempty := by
  rintro ⟨x,hx⟩
  have hl := ((final_hard _).mp hx.1).1
  have hg := hx.2 0
  norm_num [finalModel,positiveG,scalar] at hg
  nlinarith [sq_nonneg (x 0-1/2)]

theorem thesis_zero_fiber_empty : ¬(fiber thesisModel (scalar 0)).Nonempty := by
  rintro ⟨x,hx⟩
  obtain ⟨hg,hl,hu,hy0,hy1⟩ := (thesis_rows _).mp hx.2
  norm_num [scalar] at hg
  nlinarith [sq_nonneg (x 0-1/2)]

theorem final_restoration_minimum :
    IsMinimizer (restSet finalModel (scalar 0)) (restCost (n:=1) (l:=1))
      (weightedInsert (scalar (1/2)) (scalar (1/4))) := by
  refine ⟨finalRestoration.primal,?_⟩
  intro q hq
  have hq' : weightedInsert (weightedX (n:=1) (s:=1) q) (weightedV (n:=1) (s:=1) q)∈restSet finalModel (scalar 0) := by
    rw [weightedInsert_project (n:=1) (s:=1)]
    exact hq
  obtain ⟨hh,hg,hs⟩ := (restSet_insert_iff finalModel (scalar 0) _ _).mp hq'
  have hl := hh 0
  change linearResidual finalModel 0 (weightedX (n:=1) (s:=1) q,scalar 0)≤0 at hl
  change LinearForm (finalModel.A 0) (finalModel.B 0) (weightedX (n:=1) (s:=1) q,scalar 0)-
    finalModel.rhs 0≤0 at hl
  rw [final_lower_identity] at hl
  have hb := final_restoration_bound (weightedX (n:=1) (s:=1) q) (weightedV (n:=1) (s:=1) q) (by linarith) hg
  change weightedLiftObjective (n:=1) (fun _ : Fin 1 => 1) _ ≤
    weightedLiftObjective (n:=1) (fun _ : Fin 1 => 1) q
  rw [weightedLiftObjective_apply (n:=1) (s:=1),
    weightedLiftObjective_apply (n:=1) (s:=1)]
  simpa only [weightedV_insert,one_mul,Fin.sum_univ_one,scalar] using hb

theorem thesis_restoration_minimum :
    IsMinimizer (restSet thesisModel (scalar 0)) (restCost (n:=1) (l:=5))
      (weightedInsert (scalar (1/2)) thesisSlack) := by
  refine ⟨thesisRestoration.primal,?_⟩
  intro q hq
  have hq' : weightedInsert (weightedX (n:=1) (s:=5) q) (weightedV (n:=1) (s:=5) q)∈restSet thesisModel (scalar 0) := by
    rw [weightedInsert_project (n:=1) (s:=5)]
    exact hq
  obtain ⟨hh,hg,hs⟩ := (restSet_insert_iff thesisModel (scalar 0) _ _).mp hq'
  have hb := thesis_restoration_bound (weightedX (n:=1) (s:=5) q) (weightedV (n:=1) (s:=5) q) hg hs
  change weightedLiftObjective (n:=1) (fun _ : Fin 5 => 1) _ ≤
    weightedLiftObjective (n:=1) (fun _ : Fin 5 => 1) q
  rw [weightedLiftObjective_apply (n:=1) (s:=5),
    weightedLiftObjective_apply (n:=1) (s:=5)]
  rw [weightedV_insert (n:=1) (s:=5)]
  simpa [one_mul,thesisSlack,Fin.sum_univ_succ] using hb

def activeFixed : FixedKKT activeModel activeF (scalar 1) (scalar 1) where
  Df := activeDf
  Dg := activeDg (pt 1 1)
  lambda := ![1/2,0,0]
  mu := Fin.elim0
  primal := by
    refine ⟨active_hard _,?_⟩
    intro j; fin_cases j <;> norm_num [activeModel,positiveG,scalar]
  derivative_f := activeF_derivative _
  derivative_g := active_derivative _
  lambda_nonneg := by intro i; fin_cases i <;> norm_num
  mu_nonneg i := Fin.elim0 i
  soft_compl := by
    intro j; fin_cases j <;> norm_num [soft,activeModel,positiveG,scalar]
  hard_compl i := Fin.elim0 i
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    norm_num [restrict_apply,activeDf,activeDg,positiveDg,pt,scalar,Fin.sum_univ_succ]
    ring

theorem active_fiber_minimum :
    IsMinimizer (fiber activeModel (scalar 1)) (fiberObjective activeF (scalar 1))
      (scalar 1) := by
  refine ⟨activeFixed.primal,?_⟩
  intro x hx
  exact active_fixed_value_bound (x,scalar 1) rfl (hx.2 0)

theorem active_positive_nonlinear_multiplier :
    activeFixed.lambda 0=(1/2:ℝ) ∧ 0<activeFixed.lambda 0 ∧
    activeModel.g 0 (pt 1 1)=0 ∧ activeF (pt 1 1)=0 := by
  norm_num [activeFixed,activeModel,positiveG,activeF,pt,scalar]

end Chapter03.OAKKT.Controls
