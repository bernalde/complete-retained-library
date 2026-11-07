module

public import Chapter02DICOPTSigns

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
open scoped BigOperators
namespace Chapter02DICOPTExamples

def mixedData : Data 1 1 0 1 0 where
  f _ := 0
  h := Fin.elim0
  g _ _ := 0
  A := Fin.elim0
  B _ := scalar 1
  C := Fin.elim0
  D := Fin.elim0
  rhs := Fin.elim0
  xL := scalar 0
  xU := scalar 0
  c := scalar (-2)

def mixedJet : Jet mixedData (scalar 0) where
  Df := 0
  Dh := Fin.elim0
  Dg _ := 0
  fderiv := hasFDerivAt_const _ _
  hderiv := by intro i; exact Fin.elim0 i
  gderiv _ := hasFDerivAt_const _ _

def mixedKKT : FixedKKT mixedData (scalar 0) (scalar 0) where
  jet := mixedJet
  alpha := 0
  sigma := 1
  lambda := Fin.elim0
  mu := scalar 0
  nu := Fin.elim0
  xLower := scalar 0
  xUpper := scalar 0
  feasible := by
    norm_num [Data.Feasible,Data.Hard,Data.xBox,Data.ineqRow,mixedData,Pi.le_def,
      Fin.forall_fin_one]
  alphaFeasible := le_rfl
  sigmaNonneg := by norm_num
  muNonneg := by simp
  nuNonneg := by intro i; exact Fin.elim0 i
  lowerNonneg := by simp
  upperNonneg := by simp
  alphaComp := by simp [mixedData]
  ineqComp := by simp
  affineComp := by intro i; exact Fin.elim0 i
  lowerComp := by simp
  upperComp := by simp
  alphaStationarity := by norm_num
  stationarity := by simp [mixedJet]

def mixedAnchor : Anchor mixedData where
  x := scalar 0
  y := scalar 0
  kkt := mixedKKT
  convex := {
    objective := by simpa [mixedData,Data.xBox] using
      convex_affine_on (convex_Icc (scalar (0:ℝ)) (scalar (0:ℝ))) 0 0
    inequalities := by
      intro i
      simpa [mixedData,Data.xBox] using
        convex_affine_on (convex_Icc (scalar (0:ℝ)) (scalar (0:ℝ))) 0 0
    equalities := by intro i; exact Fin.elim0 i }
  weights := {
    obj := 2
    eq := Fin.elim0
    ineq := scalar 1
    obj_gt := by norm_num [mixedKKT]
    eq_gt := by intro i; exact Fin.elim0 i
    ineq_gt := by simp [mixedKKT] }

def mixedPoint : MasterPoint mixedData [mixedAnchor] where
  x := scalar 0
  y := scalar 1
  alpha := 0
  s _ := 0
  p _ := Fin.elim0
  q _ := scalar 1

theorem mixed_original_singleton : mixedData.original={(scalar 0,scalar 0)} := by
  ext z
  constructor
  · intro hz
    have hx : z.1=scalar 0 := le_antisymm hz.1.1.1.2 hz.1.1.1.1
    have hy := hz.1.2.2 0
    simp [Data.ineqRow,mixedData] at hy
    rcases hz.2 0 with h0|h1
    · exact Prod.ext hx (scalar_ext h0)
    · linarith
  · intro hz
    have he := Set.mem_singleton_iff.mp hz
    rw [he]
    exact ⟨mixedKKT.feasible,by intro i; exact Or.inl rfl⟩

theorem mixed_original_minimum :
    IsMinimizer mixedData.original (fun z => mixedData.objective z.1 z.2)
      (scalar 0,scalar 0) := by
  rw [mixed_original_singleton]
  exact ⟨rfl,by intro z hz; rw [Set.mem_singleton_iff.mp hz]⟩

theorem mixed_point_feasible : mixedPoint ∈ masterFeasible mixedData [mixedAnchor] ∅ := by
  refine ⟨⟨?_,?_,by simp⟩,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨⟨le_rfl,le_rfl⟩,by intro i; exact Fin.elim0 i⟩
  · intro i; exact Or.inr rfl
  · intro k; exact le_rfl
  · intro k i; exact Fin.elim0 i
  · intro k i; norm_num [mixedPoint]
  · intro k; fin_cases k
    dsimp [objTangent,mixedPoint,mixedAnchor,mixedKKT,mixedJet,mixedData]
    norm_num
  · intro k i; exact Fin.elim0 i
  · intro k i; fin_cases k; fin_cases i
    dsimp [ineqTangent,mixedPoint,mixedAnchor,mixedKKT,mixedJet,mixedData]
    norm_num

theorem mixed_point_minimum :
    IsMinimizer (masterFeasible mixedData [mixedAnchor] ∅)
      (masterObjective mixedData [mixedAnchor]) mixedPoint := by
  refine ⟨mixed_point_feasible,?_⟩
  intro z hz
  have hs := hz.2.1 (0:Fin 1)
  have hq := hz.2.2.2.1 (0:Fin 1) (0:Fin 1)
  have hf := hz.2.2.2.2.1 (0:Fin 1)
  have hg := hz.2.2.2.2.2.2 (0:Fin 1) (0:Fin 1)
  simp [objTangent,mixedAnchor,mixedKKT,mixedJet,mixedData] at hf
  simp [ineqTangent,mixedAnchor,mixedKKT,mixedJet,mixedData] at hg
  simp [masterObjective,mixedPoint,mixedData,mixedAnchor,Fin.sum_univ_succ]
  rcases hz.1.2.1 0 with hy|hy <;> dsimp at hy <;> linarith

theorem mixed_positive_slack_and_gap :
    mixedPoint.q (0:Fin 1) 0=1 ∧
    masterObjective mixedData [mixedAnchor] mixedPoint = -1 ∧
    mixedData.objective (scalar 0) (scalar 0)=0 ∧
    mixedAnchor.weights.ineq 0 > |mixedAnchor.kkt.mu 0| := by
  refine ⟨rfl,?_,by norm_num [mixedData,Data.objective],mixedAnchor.weights.ineq_gt 0⟩
  have hw : ∀ k : Fin [mixedAnchor].length, ([mixedAnchor].get k).weights.ineq 0=1 := by
    intro k
    fin_cases k
    rfl
  norm_num [masterObjective,mixedPoint,mixedData,Fin.sum_univ_succ,hw]

end Chapter02DICOPTExamples
