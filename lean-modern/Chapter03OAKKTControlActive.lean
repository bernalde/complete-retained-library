module

public import Chapter03OAKKTControlData

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT Chapter02DICOPTExamples
open scoped BigOperators
namespace Chapter03.OAKKT.Controls

def activeF (p : P) : ℝ := -p.1 0+p.2 0
def activeDf : P →L[ℝ] ℝ := -cx+cy
def activeModel : ModelData 1 1 3 0 where
  g := ![positiveG,fun p => -p.2 0,fun p => p.2 0-1]
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1
def activeDg (p : P) : Fin 3 → P →L[ℝ] ℝ := ![positiveDg p,-cy,cy]

theorem activeF_derivative (p : P) : HasFDerivAt activeF activeDf p :=
  cx.hasFDerivAt.neg.add cy.hasFDerivAt

theorem active_objective_tangent (a q : P) :
    activeF a+activeDf (q-a)=activeF q := by
  simp [activeF,activeDf]
  ring

theorem active_current_row_tangent (q : P) :
    positiveG (pt 1 1)+positiveDg (pt 1 1) (q-pt 1 1)=2*q.1 0-q.2 0-1 := by
  norm_num [positiveG,positiveDg,pt,scalar]
  ring

theorem active_derivative (p : P) (j : Fin 3) :
    HasFDerivAt (activeModel.g j) (activeDg p j) p := by
  fin_cases j
  · exact positiveG_derivative p
  · exact cy.hasFDerivAt.neg
  · exact cy.hasFDerivAt.sub_const 1

@[simp] theorem active_hard (p : P) : p∈activeModel.linearRegion := by
  intro i
  exact Fin.elim0 i

theorem active_relaxation (p : P) : p∈activeModel.relaxationOn Set.univ ↔
    (p.1 0)^2≤p.2 0 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  change ((p∈Set.univ ∧ ∀ j, activeModel.g j p≤0) ∧
    p∈activeModel.linearRegion ∧ ∀ i, activeModel.lo i≤p.2 i ∧ p.2 i≤activeModel.hi i) ↔ _
  simp only [active_hard,Set.mem_univ,true_and]
  simp [activeModel,positiveG,scalar,Fin.forall_fin_succ,and_assoc]

theorem active_relaxed_seed :
    IsMinimizer (activeModel.relaxationOn Set.univ) activeF (pt (1/2) (1/4)) := by
  refine ⟨(active_relaxation _).mpr (by norm_num [pt,scalar]),?_⟩
  intro q hq
  obtain ⟨hg,hy0,hy1⟩ := (active_relaxation q).mp hq
  norm_num [activeF,pt,scalar]
  nlinarith [sq_nonneg (q.1 0-1/2)]

theorem active_fixed_value_bound (p : P) (hy : p.2=scalar 1)
    (hg : activeModel.g 0 p≤0) : activeF (pt 1 1)≤activeF p := by
  norm_num [activeModel,positiveG,hy,scalar] at hg
  norm_num [activeF,pt,hy,scalar]
  have hx := le_trans (le_abs_self (p.1 0)) hg
  linarith

theorem active_integer_lower_identity (p : P) :
    activeModel.g 1 p=activeModel.lo 0-p.2 0 := by simp [activeModel,scalar]

theorem active_integer_upper_identity (p : P) :
    activeModel.g 2 p=p.2 0-activeModel.hi 0 := rfl

end Chapter03.OAKKT.Controls
