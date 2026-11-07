module

public import Chapter03OASoftMasterBounds
public import Chapter03OAKKTControlConvexity

@[expose] public section

/-! Uncounted reuse control for the hard-objective source master. The weight is
rho=2, not the historical 1000-times-multiplier policy. All calculus, original
minima and the positive first AP minimum are reused from accepted controls. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02.DICOPT Chapter02DICOPTExamples
open Chapter03.OAKKT.Controls
namespace Chapter03.OASoftMaster.Control

def history : TangentFamily 1 1 1 1 where
  origin _ := pt (1/2) (1/4)
  selected _ := Set.univ
  derivative _ _ := positiveDg (pt (1/2) (1/4))

def objectiveDerivative (_ : Fin 1) := positiveDf (pt (1/2) (1/4))
def occurrence : Occurrence history := ⟨(0,0), Set.mem_univ _⟩

def rho (_ : Occurrence history) : ℝ := 2
def chosen : Candidate history := (pt (1/2) 0, 1/4, fun _ => 1/4)
abbrev sourceMaster := master finalModel positiveF history objectiveDerivative (fun _ => True)

theorem master_scalar (z : Candidate history) : z ∈ sourceMaster ↔
    (1/2:ℝ) ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1 ∧ Binary z.1.2 ∧
    0 ≤ z.2.2 occurrence ∧ z.1.1 0 + z.1.2 0 - 1/4 ≤ z.2.1 ∧
    z.1.1 0 - z.1.2 0 - 1/4 ≤ z.2.2 occurrence := by
  constructor
  · intro h
    have hx := (final_hard z.1).mp h.1
    have hy := integer_binary z.1.2 |>.mp h.2.1
    have hf := h.2.2.2.2.1 0
    have hg := h.2.2.2.2.2 occurrence
    change positiveF (pt (1/2) (1/4)) +
      positiveDf (pt (1/2) (1/4)) (z.1-pt (1/2) (1/4)) ≤ z.2.1 at hf
    change positiveG (pt (1/2) (1/4)) +
      positiveDg (pt (1/2) (1/4)) (z.1-pt (1/2) (1/4)) ≤ z.2.2 occurrence at hg
    rw [positive_objective_tangent] at hf
    rw [positive_row_tangent] at hg
    exact ⟨hx.1,hx.2,hy,h.2.2.2.1 occurrence,hf,hg⟩
  · rintro ⟨hl,hu,hy,hs,hf,hg⟩
    refine ⟨(final_hard _).mpr ⟨hl,hu⟩,(integer_binary _).mpr hy,trivial,?_,?_,?_⟩
    · intro a; simpa only [Subsingleton.elim a occurrence] using hs
    · intro i
      change positiveF (pt (1/2) (1/4)) +
        positiveDf (pt (1/2) (1/4)) (z.1-pt (1/2) (1/4)) ≤ z.2.1
      rwa [positive_objective_tangent]
    · intro a
      rw [Subsingleton.elim a occurrence]
      change positiveG (pt (1/2) (1/4)) +
        positiveDg (pt (1/2) (1/4)) (z.1-pt (1/2) (1/4)) ≤ z.2.2 occurrence
      rwa [positive_row_tangent]

/-- Absorb c*y into the new alpha and fix the old objective slack to zero. -/
def oldPoint (z : Candidate history) :
    MasterPoint Chapter02DICOPTSupplemental.positiveData
      [Chapter02DICOPTSupplemental.positiveInitial] where
  x := z.1.1
  y := z.1.2
  alpha := z.2.1-z.1.2 0
  s _ := 0
  p _ := Fin.elim0
  q _ _ := z.2.2 occurrence

theorem oldPoint_feasible (z : Candidate history) (hz : z ∈ sourceMaster) :
    oldPoint z ∈ masterFeasible Chapter02DICOPTSupplemental.positiveData
      [Chapter02DICOPTSupplemental.positiveInitial] ∅ := by
  obtain ⟨hl,hu,hy,hs,hf,hg⟩ := (master_scalar z).mp hz
  refine ⟨⟨⟨?_,fun i => Fin.elim0 i⟩,hy,by simp⟩,?_,?_,?_,?_,?_,?_⟩
  · exact scalar_Icc.mpr ⟨hl,hu⟩
  · intro i; exact le_rfl
  · intro i j; exact Fin.elim0 j
  · intro i j; exact hs
  · intro i; fin_cases i
    change objTangent _ Chapter02DICOPTSupplemental.positiveInitial.kkt.jet _-_ ≤ 0
    rw [Chapter02DICOPTSupplemental.positive_objective_tangent]
    change z.1.1 0-1/4-(z.2.1-z.1.2 0) ≤ 0
    linarith
  · intro i j; exact Fin.elim0 j
  · intro i j; fin_cases i
    change ineqTangent _ Chapter02DICOPTSupplemental.positiveInitial.kkt.jet j _ _ ≤ _
    rw [Chapter02DICOPTSupplemental.positive_inequality_tangent]
    change z.1.1 0-1/4-z.1.2 0 ≤ z.2.2 occurrence
    linarith

theorem master_correspondence (z : Candidate history) : z ∈ sourceMaster ↔
    oldPoint z ∈ masterFeasible Chapter02DICOPTSupplemental.positiveData
      [Chapter02DICOPTSupplemental.positiveInitial] ∅ := by
  refine ⟨oldPoint_feasible z,?_⟩
  intro h
  apply (master_scalar z).mpr
  have hx := scalar_Icc.mp h.1.1.1
  have hf := h.2.2.2.2.1 (0:Fin 1)
  have hg := h.2.2.2.2.2.2 (0:Fin 1) (0:Fin 1)
  change objTangent _ Chapter02DICOPTSupplemental.positiveInitial.kkt.jet _-_ ≤ 0 at hf
  change ineqTangent _ Chapter02DICOPTSupplemental.positiveInitial.kkt.jet _ _ _ ≤ _ at hg
  rw [Chapter02DICOPTSupplemental.positive_objective_tangent] at hf
  rw [Chapter02DICOPTSupplemental.positive_inequality_tangent] at hg
  refine ⟨hx.1,hx.2,h.1.2.1,h.2.2.2.1 (0:Fin 1) (0:Fin 1),?_,?_⟩
  · change z.1.1 0-1/4-(z.2.1-z.1.2 0) ≤ 0 at hf
    linarith
  · change z.1.1 0-1/4-z.1.2 0 ≤ z.2.2 occurrence at hg
    linarith

theorem cost_scalar (z : Candidate history) : cost rho z = z.2.1+2*z.2.2 occurrence := by
  classical
  letI : Unique (Occurrence history) := ⟨⟨occurrence⟩,fun _ => Subsingleton.elim _ _⟩
  simp only [cost,penalty,rho,Fintype.sum_unique]
  rw [Subsingleton.elim (default : Occurrence history) occurrence]

theorem oldPoint_cost (z : Candidate history) :
    masterObjective Chapter02DICOPTSupplemental.positiveData
      [Chapter02DICOPTSupplemental.positiveInitial] (oldPoint z) = cost rho z := by
  rw [Chapter02DICOPTSupplemental.first_master_value,cost_scalar]
  dsimp [oldPoint]
  ring

theorem chosen_old : oldPoint chosen = Chapter02DICOPTSupplemental.firstMaster := by
  simp only [oldPoint,chosen,Chapter02DICOPTSupplemental.firstMaster,pt,scalar,sub_zero]
  rfl

theorem chosen_minimum : IsMinimizer sourceMaster (cost rho) chosen := by
  refine ⟨(master_correspondence chosen).mpr ?_,?_⟩
  · rw [chosen_old]; exact Chapter02DICOPTSupplemental.first_master_feasible
  · intro z hz
    have h := Chapter02DICOPTSupplemental.first_master_minimum.2
      (oldPoint z) (oldPoint_feasible z hz)
    rw [← chosen_old,oldPoint_cost,oldPoint_cost] at h
    exact h

/-- Full bound-theorem premises are inhabited, and its conclusion is applied.
This positive-slack reuse control adds no independent headline credit. -/
theorem source_hard_objective_positive_control :
    IsMinimizer sourceMaster (cost rho) chosen ∧
    IsMinimizer (finalModel.relaxationOn Set.univ) positiveF (pt (1/2) (1/4)) ∧
    IsMinimizer (finalModel.feasibleOn Set.univ) positiveF (pt (1/2) 1) ∧
    chosen.2.1 = (1/4:ℝ) ∧ cost rho chosen = (3/4:ℝ) ∧
    positiveF (pt (1/2) 1) = (5/4:ℝ) ∧ chosen.2.2 occurrence = (1/4:ℝ) ∧
    chosen.2.1 < cost rho chosen ∧ cost rho chosen < positiveF (pt (1/2) 1) ∧
    (∀ p ∈ remaining finalModel (fun _ => True),
      embed positiveF history p ∈ sourceMaster ∧
      cost rho (embed positiveF history p) = positiveF p) ∧
    IsLowerBound (remaining finalModel (fun _ => True)) positiveF (cost rho chosen) ∧
    IsLowerBound (remaining finalModel (fun _ => True)) positiveF chosen.2.1 := by
  have bound := source_soft_master_bounds finalModel positiveF history objectiveDerivative
    (fun _ => True) Set.univ (fun _ => positiveG_convex) positiveF_convex
    (fun _ => Set.mem_univ _) (fun _ _ _ => positiveG_derivative _)
    (fun _ => positiveF_derivative _) (fun _ _ => Set.mem_univ _)
    rho (fun _ => by norm_num [rho]) chosen chosen_minimum
  have hc : cost rho chosen = (3/4:ℝ) := by norm_num [cost_scalar,chosen]
  have hf : positiveF (pt (1/2) 1) = (5/4:ℝ) := by norm_num [positiveF,pt,scalar]
  refine ⟨chosen_minimum,final_relaxed_seed,final_original_minimum,rfl,hc,hf,rfl,
    ?_,?_,bound.1,bound.2.2.2.1,bound.2.2.2.2⟩
  · rw [hc]; norm_num [chosen]
  · rw [hc,hf]; norm_num

end Chapter03.OASoftMaster.Control
