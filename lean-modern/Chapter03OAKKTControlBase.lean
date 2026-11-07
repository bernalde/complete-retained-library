module

public import Chapter02DICOPTSupplementalControls
public import Chapter06

@[expose] public section

/-! Analytic control data for the qualified Chapter 3 KKT source bridge.
The positiveData y=0 cases are static: their genuine fractional relaxed seed
already excludes that fiber. No OA visit, driver execution or LICQ is claimed. -/
noncomputable section
open Chapter02 Chapter02.DICOPT Chapter02DICOPTExamples
open scoped BigOperators
namespace Chapter03.OAKKT.Controls

abbrev P := Point 1 1
def pt (x y : ℝ) : P := (scalar x,scalar y)
def cx : P →L[ℝ] ℝ := coord.comp (ContinuousLinearMap.fst ℝ V V)
def cy : P →L[ℝ] ℝ := coord.comp (ContinuousLinearMap.snd ℝ V V)
@[simp] theorem pt_x (x y : ℝ) : (pt x y).1 0=x := rfl
@[simp] theorem pt_y (x y : ℝ) : (pt x y).2 0=y := rfl
@[simp] theorem cx_apply (p : P) : cx p=p.1 0 := rfl
@[simp] theorem cy_apply (p : P) : cy p=p.2 0 := rfl

def positiveF (p : P) : ℝ := (p.1 0)^2+p.2 0
def positiveG (p : P) : ℝ := (p.1 0)^2-p.2 0
def positiveDf (p : P) : P →L[ℝ] ℝ := (2*p.1 0) • cx+cy
def positiveDg (p : P) : P →L[ℝ] ℝ := (2*p.1 0) • cx-cy

theorem square_derivative (p : P) :
    HasFDerivAt (fun z : P => (z.1 0)^2) ((2*p.1 0) • cx) p := by
  simpa only [cx,ContinuousLinearMap.smul_comp,Function.comp_def] using
    (Chapter02DICOPTExamples.derivative_square p.1).comp p
      (ContinuousLinearMap.fst ℝ V V).hasFDerivAt

theorem positiveF_derivative (p : P) : HasFDerivAt positiveF (positiveDf p) p :=
  (square_derivative p).add cy.hasFDerivAt

theorem positiveG_derivative (p : P) : HasFDerivAt positiveG (positiveDg p) p :=
  (square_derivative p).sub cy.hasFDerivAt

theorem positive_objective_identity (p : P) :
    positiveF p=pointObjective Chapter02DICOPTSupplemental.positiveData p := by
  simp [positiveF,pointObjective,Chapter02DICOPTSupplemental.positive_objective]
  ring

theorem positive_objective_tangent (b : ℝ) (q : P) :
    positiveF (pt (1/2) b)+positiveDf (pt (1/2) b) (q-pt (1/2) b)=
      q.1 0+q.2 0-1/4 := by
  norm_num [positiveF,positiveDf,pt,scalar]
  ring

theorem positive_row_tangent (b : ℝ) (q : P) :
    positiveG (pt (1/2) b)+positiveDg (pt (1/2) b) (q-pt (1/2) b)=
      q.1 0-q.2 0-1/4 := by
  norm_num [positiveG,positiveDg,pt,scalar]
  ring

def finalModel : ModelData 1 1 1 2 where
  g _ := positiveG
  A := ![scalar (-1),scalar 1]
  B _ := scalar 0
  rhs := ![-(1/2),1]
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1

def thesisModel : ModelData 1 1 5 0 where
  g := ![positiveG,fun p => 1/2-p.1 0,fun p => p.1 0-1,
    fun p => -p.2 0,fun p => p.2 0-1]
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1

def finalDg (p : P) (_ : Fin 1) : P →L[ℝ] ℝ := positiveDg p
def thesisDg (p : P) : Fin 5 → P →L[ℝ] ℝ :=
  ![positiveDg p,-cx,cx,-cy,cy]

theorem final_derivative (p : P) (j : Fin 1) :
    HasFDerivAt (finalModel.g j) (finalDg p j) p := positiveG_derivative p

theorem thesis_derivative (p : P) (j : Fin 5) :
    HasFDerivAt (thesisModel.g j) (thesisDg p j) p := by
  fin_cases j
  · exact positiveG_derivative p
  · exact cx.hasFDerivAt.const_sub (1/2)
  · exact cx.hasFDerivAt.sub_const 1
  · exact cy.hasFDerivAt.neg
  · exact cy.hasFDerivAt.sub_const 1

theorem thesis_integer_lower_identity (p : P) :
    thesisModel.g 3 p=thesisModel.lo 0-p.2 0 := by simp [thesisModel,scalar]

theorem thesis_integer_upper_identity (p : P) :
    thesisModel.g 4 p=p.2 0-thesisModel.hi 0 := rfl

theorem final_lower_identity (p : P) :
    LinearForm (finalModel.A 0) (finalModel.B 0) p-finalModel.rhs 0=1/2-p.1 0 := by
  simp [LinearForm,finalModel,scalar,Fin.sum_univ_one]
  ring

theorem final_upper_identity (p : P) :
    LinearForm (finalModel.A 1) (finalModel.B 1) p-finalModel.rhs 1=p.1 0-1 := by
  simp [LinearForm,finalModel,scalar,Fin.sum_univ_one]

@[simp] theorem final_hard (p : P) : p∈finalModel.linearRegion ↔
    (1/2:ℝ)≤p.1 0 ∧ p.1 0≤1 := by
  simp [ModelData.linearRegion,LinearForm,finalModel,Fin.forall_fin_two,
    Fin.sum_univ_one,scalar]

@[simp] theorem thesis_hard (p : P) : p∈thesisModel.linearRegion := by
  intro i
  exact Fin.elim0 i

@[simp] theorem thesis_rows (p : P) : (∀j,thesisModel.g j p≤0) ↔
    (p.1 0)^2≤p.2 0 ∧ (1/2:ℝ)≤p.1 0 ∧ p.1 0≤1 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  simp [thesisModel,positiveG,Fin.forall_fin_succ]


end Chapter03.OAKKT.Controls
