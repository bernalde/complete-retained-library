module

public import Chapter02DICOPTProcedure
public import Chapter02DICOPTExampleData

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT Chapter02DICOPTExamples
open scoped BigOperators
namespace Chapter02DICOPTSupplemental

def positiveData : Data 1 1 0 1 0 where
  f x := (x 0)^2
  h := Fin.elim0
  g _ x := (x 0)^2
  A := Fin.elim0
  B _ := scalar (-1)
  C := Fin.elim0
  D := Fin.elim0
  rhs := Fin.elim0
  xL := scalar (1/2)
  xU := scalar 1
  c := scalar 1

@[simp] theorem positive_objective (x y : V) :
    positiveData.objective x y=y 0+(x 0)^2 := by
  simp [Data.objective,positiveData,dot,Fin.sum_univ_one]

@[simp] theorem positive_feasible (x y : V) : positiveData.Feasible x y ↔
    (1/2:ℝ)≤x 0 ∧ x 0≤1 ∧ (x 0)^2≤y 0 := by
  simp [Data.Feasible,Data.Hard,Data.xBox,positiveData,scalar_Icc,
    Data.ineqRow,dot,Fin.forall_fin_one,and_assoc,Pi.le_def]

def positiveJet (x : V) : Jet positiveData x where
  Df := (2*x 0) • coord
  Dh := Fin.elim0
  Dg _ := (2*x 0) • coord
  fderiv := derivative_square x
  hderiv i := Fin.elim0 i
  gderiv _ := derivative_square x

def positiveKKT (b mu : ℝ) (hb : (1/4:ℝ)≤b) (hm : 0≤mu)
    (hc : mu*(1/4-b)=0) : FixedKKT positiveData (scalar (1/2)) (scalar b) where
  jet := positiveJet (scalar (1/2))
  alpha := 1/4
  sigma := 1
  lambda := Fin.elim0
  mu := scalar mu
  nu := Fin.elim0
  xLower := scalar (1+mu)
  xUpper := scalar 0
  feasible := (positive_feasible _ _).mpr (by norm_num; exact hb)
  alphaFeasible := by norm_num [positiveData]
  sigmaNonneg := by norm_num
  muNonneg := fun _ => hm
  nuNonneg i := Fin.elim0 i
  lowerNonneg := by intro i; dsimp; linarith
  upperNonneg := by simp
  alphaComp := by norm_num [positiveData]
  ineqComp := by
    intro i
    norm_num [Data.ineqRow,positiveData,dot,Fin.sum_univ_one]
    rcases mul_eq_zero.mp hc with hm|he
    · exact Or.inl hm
    · exact Or.inr (by linarith)
  affineComp i := Fin.elim0 i
  lowerComp := by simp [positiveData]
  upperComp := by simp
  alphaStationarity := by norm_num
  stationarity := by
    intro w
    norm_num [positiveJet,Fin.sum_univ_one]
    ring

theorem positive_signed {x y : V} (k : FixedKKT positiveData x y) : SignedConvex positiveData k := by
  constructor
  · exact convex_square_on (convex_Icc _ _)
  · intro i; exact convex_square_on (convex_Icc _ _)
  · intro i; exact Fin.elim0 i

def initialKKT := positiveKKT (1/4) 1 (by norm_num) (by norm_num) (by norm_num)
def oneKKT := positiveKKT 1 0 (by norm_num) (by norm_num) (by norm_num)

def initialJoint : JointKKT positiveData (scalar (1/2)) (scalar (1/4)) where
  toFixedKKT := initialKKT
  yFeasible := by constructor <;> intro i <;> norm_num [Data.yBox,scalar]
  yLower := scalar 0
  yUpper := scalar 0
  yLowerNonneg := by simp
  yUpperNonneg := by simp
  yLowerComp := by simp
  yUpperComp := by simp
  yStationarity := by simp [positiveData,initialKKT,positiveKKT,dot,Fin.sum_univ_one]

def positiveRelaxed : RelaxedAnchor positiveData :=
  ⟨scalar (1/2),scalar (1/4),initialJoint,positive_signed _,canonicalWeights initialKKT⟩
def positiveInitial : Anchor positiveData := positiveRelaxed.toAnchor
def positiveInitialization : Initialization positiveData :=
  .fractional positiveRelaxed (by intro h; have hh:=h 0; norm_num [positiveRelaxed] at hh)

theorem positive_relaxed_minimum :
    IsMinimizer positiveData.relaxed (pointObjective positiveData) (scalar (1/2),scalar (1/4)) :=
  initialJoint.global_min (positive_signed _)

theorem positive_zero_fiber_empty : ¬(positiveData.fiber (scalar 0)).Nonempty := by
  rintro ⟨x,hx⟩
  have hh := (positive_feasible _ _).mp hx
  norm_num at hh
  nlinarith [sq_nonneg (x 0-1/2)]

theorem positive_original_y {z : V×V} (hz : z∈positiveData.original) : z.2=scalar 1 := by
  rcases hz.2 0 with hy|hy
  · have hf := (positive_feasible _ _).mp hz.1
    rw [hy] at hf
    exfalso
    nlinarith [sq_nonneg (z.1 0-1/2)]
  · exact scalar_ext hy

theorem positive_original_minimum :
    IsMinimizer positiveData.original (pointObjective positiveData) (scalar (1/2),scalar 1) := by
  refine ⟨⟨oneKKT.feasible,fun _ => Or.inr rfl⟩,?_⟩
  intro z hz
  have hy:=positive_original_y hz
  have hx:=((positive_feasible _ _).mp hz.1).1
  simp only [pointObjective,positive_objective,scalar_apply,hy]
  nlinarith [sq_nonneg (z.1 0-1/2)]

theorem positive_unique_minimum (z : V×V)
    (hz : IsMinimizer positiveData.original (pointObjective positiveData) z) :
    z=(scalar (1/2),scalar 1) := by
  have hy:=positive_original_y hz.1
  have hx:=((positive_feasible _ _).mp hz.1.1).1
  have hh:=hz.2 (scalar (1/2),scalar 1) positive_original_minimum.1
  simp only [pointObjective,positive_objective,hy,scalar_apply] at hh
  have he : z.1 0=1/2 := by nlinarith [sq_nonneg (z.1 0-1/2)]
  exact Prod.ext (scalar_ext he) hy

theorem positive_fiber_regularity : FiberRegularity positiveData := by
  intro b hb
  cases he:b 0 with
  | false =>
    have hy : realBinary b=scalar 0 := by ext i; fin_cases i; simp [realBinary,he]
    rw [hy] at hb
    exact False.elim (positive_zero_fiber_empty hb)
  | true =>
    have hy : realBinary b=scalar 1 := by ext i; fin_cases i; simp [realBinary,he]
    rw [hy]
    exact ⟨scalar (1/2),oneKKT,positive_signed _⟩

theorem positive_joint_regularity : JointRegularity positiveData :=
  fun _ => ⟨scalar (1/2),scalar (1/4),initialJoint,positive_signed _⟩

theorem positive_procedure_all_choices : Nonempty (Initialization positiveData) ∧
    Nonempty (Selector positiveData) ∧
    ∀ initial : Initialization positiveData, ∀ choose : Selector positiveData, ∃ output,
      procedure positiveData initial choose=some output ∧
      output.result=.solution (scalar (1/2),scalar 1) ∧
      output.binarySolves≤2 ∧ output.masterDecisions≤3 ∧
      ReturnCertificate positiveData output.result := by
  have hh:=qualified_source_procedure positiveData positive_joint_regularity positive_fiber_regularity
  refine ⟨hh.1,hh.2.1,?_⟩
  intro initial choose
  obtain ⟨out,hout,hb,hm,ht,hcert⟩ := hh.2.2 initial choose
  exact ⟨out,hout,certificate_solution_of_unique positiveData out.result hcert
    _ positive_original_minimum positive_unique_minimum,by simpa using hb,by simpa using hm,hcert⟩

theorem positive_objective_tangent (x : V) :
    objTangent positiveData positiveInitial.kkt.jet x=x 0-1/4 := by
  change (1/2:ℝ)^2+((2*(1/2:ℝ)) • coord) (x-scalar (1/2))=x 0-1/4
  norm_num
  ring

theorem positive_inequality_tangent (x y : V) (i : Fin 1) :
    ineqTangent positiveData positiveInitial.kkt.jet i x y=x 0-1/4-y 0 := by
  change dot (scalar (-1)) y+(1/2:ℝ)^2+((2*(1/2:ℝ)) • coord) (x-scalar (1/2))=_
  norm_num [dot,Fin.sum_univ_one]
  ring

def firstMaster : MasterPoint positiveData [positiveInitial] where
  x := scalar (1/2)
  y := scalar 0
  alpha := 1/4
  s _ := 0
  p _ := Fin.elim0
  q _ := scalar (1/4)

theorem first_master_feasible : firstMaster ∈ masterFeasible positiveData [positiveInitial] ∅ := by
  refine ⟨⟨?_,fun _ => Or.inl rfl,by simp⟩,?_,?_,?_,?_,?_,?_⟩
  · constructor
    · norm_num [Data.xBox,positiveData,Pi.le_def,firstMaster]
    · intro i; exact Fin.elim0 i
  · intro k; exact le_rfl
  · intro k i; exact Fin.elim0 i
  · intro k i; norm_num [firstMaster]
  · intro k; fin_cases k
    change objTangent positiveData positiveInitial.kkt.jet _-_≤_
    rw [positive_objective_tangent]; norm_num [firstMaster]
  · intro k i; exact Fin.elim0 i
  · intro k i; fin_cases k
    change ineqTangent positiveData positiveInitial.kkt.jet i _ _≤_
    rw [positive_inequality_tangent]; norm_num [firstMaster]

theorem first_master_value (z : MasterPoint positiveData [positiveInitial]) :
    masterObjective positiveData [positiveInitial] z=z.y 0+z.alpha+2*z.s (0:Fin 1)+2*z.q (0:Fin 1) 0 := by
  unfold masterObjective
  change dot positiveData.c z.y+z.alpha+
    (∑ k : Fin 1,([positiveInitial].get k).weights.obj*z.s k)+
    (∑ k : Fin 1,∑ i : Fin 0,([positiveInitial].get k).weights.eq i*z.p k i)+
    (∑ k : Fin 1,∑ i : Fin 1,([positiveInitial].get k).weights.ineq i*z.q k i)=_
  simp only [Fin.sum_univ_one,Fin.sum_univ_zero,add_zero]
  change dot positiveData.c z.y+z.alpha+positiveInitial.weights.obj*z.s (0:Fin 1)+
    positiveInitial.weights.ineq 0*z.q (0:Fin 1) 0=_
  change dot positiveData.c z.y+z.alpha+(|(1:ℝ)|+1)*z.s (0:Fin 1)+
    (|(1:ℝ)|+1)*z.q (0:Fin 1) 0=_
  norm_num [dot,positiveData,Fin.sum_univ_one]

theorem first_master_lower_bounds (z : MasterPoint positiveData [positiveInitial])
    (hz : z ∈ masterFeasible positiveData [positiveInitial] ∅) :
    (3/4:ℝ) ≤ masterObjective positiveData [positiveInitial] z ∧
      (z.y 0=1 → (5/4:ℝ)≤masterObjective positiveData [positiveInitial] z) := by
  have hx:=hz.1.1.1.1 0
  change (1/2:ℝ)≤z.x 0 at hx
  have hs:=hz.2.1 (0:Fin 1)
  have hq:=hz.2.2.2.1 (0:Fin 1) (0:Fin 1)
  have hf:=hz.2.2.2.2.1 (0:Fin 1)
  have hg:=hz.2.2.2.2.2.2 (0:Fin 1) (0:Fin 1)
  change objTangent positiveData positiveInitial.kkt.jet _-_≤_ at hf
  change ineqTangent positiveData positiveInitial.kkt.jet _ _ _≤_ at hg
  rw [positive_objective_tangent] at hf
  rw [positive_inequality_tangent] at hg
  rw [first_master_value]
  constructor
  · have hb : z.y 0=0 ∨ z.y 0=1 := hz.1.2.1 0
    rcases hb with hy|hy <;> rw [hy] at hg ⊢ <;> linarith
  · intro hy; rw [hy]; linarith

theorem first_master_minimum : IsMinimizer (masterFeasible positiveData [positiveInitial] ∅)
    (masterObjective positiveData [positiveInitial]) firstMaster := by
  refine ⟨first_master_feasible,?_⟩
  intro z hz
  have hv : masterObjective positiveData [positiveInitial] firstMaster=3/4 := by
    norm_num [first_master_value,firstMaster]
  rw [hv]
  exact (first_master_lower_bounds z hz).1

theorem positive_nonaffine : ¬∃ a b : ℝ, ∀ x∈positiveData.xBox,
    positiveData.f x=a*x 0+b := by
  rintro ⟨a,b,h⟩
  have h1:=h (scalar (1/2)) (by norm_num [Data.xBox,positiveData,scalar_Icc,Pi.le_def,scalar])
  have h2:=h (scalar (3/4)) (by norm_num [Data.xBox,positiveData,scalar_Icc,Pi.le_def,scalar])
  have h3:=h (scalar 1) (by norm_num [Data.xBox,positiveData,scalar_Icc,Pi.le_def,scalar])
  norm_num [positiveData] at h1 h2 h3
  linarith

def zeroBinary : BVector 1 := fun _ => false

def positiveEmptyReply : FiberReply positiveData where
  binary := zeroBinary
  anchor := none
  same_y := by simp
  empty := fun _ => by
    have he : realBinary zeroBinary = scalar 0 := by ext i; rfl
    rw [he]
    exact positive_zero_fiber_empty

def positiveAfterEmpty : State positiveData :=
  append positiveData (initialState positiveInitial) positiveEmptyReply

theorem positive_actual_first_step :
    Continue positiveData (initialState positiveInitial) positiveAfterEmpty ∧
    positiveAfterEmpty.incumbent=none ∧
    zeroBinary∈positiveAfterEmpty.seen ∧
    positiveAfterEmpty.history=[positiveInitial] ∧
    ¬(positiveData.fiber (realBinary zeroBinary)).Nonempty := by
  refine ⟨?_,rfl,?_,rfl,positiveEmptyReply.empty rfl⟩
  · exact .step first_master_minimum (by intro u hu; cases hu) rfl
  · change zeroBinary∈(append positiveData (initialState positiveInitial) positiveEmptyReply).seen
    rw [seen_append]
    exact Finset.mem_insert_self _ _

def positiveFirstSelector (fallback : Selector positiveData) : Selector positiveData := by
  classical
  intro s hs
  by_cases he:s=initialState positiveInitial
  · subst s
    exact .next _ positive_actual_first_step.1
  · exact fallback s hs

theorem positive_first_run (fallback : Selector positiveData) :
    run positiveData (positiveFirstSelector fallback) 3 (initialState positiveInitial)
      (initial_invariant positiveInitial) =
    (run positiveData (positiveFirstSelector fallback) 2 positiveAfterEmpty
      (continue_invariant positiveData (initial_invariant positiveInitial)
        positive_actual_first_step.1)).map (fun out => (out.1,out.2+1)) := by
  rw [run]
  simp [positiveFirstSelector]

theorem positive_procedure_first_step (fallback : Selector positiveData) :
    procedure positiveData positiveInitialization (positiveFirstSelector fallback) =
    (run positiveData (positiveFirstSelector fallback) 2 positiveAfterEmpty
      (continue_invariant positiveData (initial_invariant positiveInitial)
        positive_actual_first_step.1)).map (fun out => ⟨out.1,out.2+1,out.2+2⟩) := by
  change (run positiveData (positiveFirstSelector fallback) (Fintype.card (BVector 1)+1) (initialState positiveInitial)
    (initial_invariant positiveInitial)).map (fun out => (⟨out.1,out.2,out.2+1⟩ : Output 1 1))=_
  rw [binary_configuration_count]
  norm_num only [pow_one, Nat.reduceAdd]
  rw [positive_first_run,Option.map_map]
  rfl

theorem positive_first_execution_exists : ∃ choose : Selector positiveData,
    (procedure positiveData positiveInitialization choose =
      (run positiveData choose 2 positiveAfterEmpty
        (continue_invariant positiveData (initial_invariant positiveInitial)
          positive_actual_first_step.1)).map (fun out => ⟨out.1,out.2+1,out.2+2⟩)) ∧
    ∃ output,procedure positiveData positiveInitialization choose=some output ∧
      output.result=.solution (scalar (1/2),scalar 1) ∧
      output.binarySolves≤2 ∧ output.masterDecisions≤3 ∧
      ReturnCertificate positiveData output.result := by
  obtain ⟨fallback⟩:=positive_procedure_all_choices.2.1
  exact ⟨positiveFirstSelector fallback,positive_procedure_first_step fallback,
    positive_procedure_all_choices.2.2 positiveInitialization (positiveFirstSelector fallback)⟩

theorem first_every_minimum_positive_slack (z : MasterPoint positiveData [positiveInitial])
    (hz : IsMinimizer (masterFeasible positiveData [positiveInitial] ∅)
      (masterObjective positiveData [positiveInitial]) z) :
    z.y 0=0 ∧ (1/4:ℝ)≤z.q (0:Fin 1) 0 := by
  have hvalue:=hz.2 firstMaster first_master_feasible
  have hupper : masterObjective positiveData [positiveInitial] z≤3/4 := by
    have hv : masterObjective positiveData [positiveInitial] firstMaster=3/4 := by
      norm_num [first_master_value,firstMaster]
    rw [hv] at hvalue
    exact hvalue
  have hy:z.y 0=0 := by
    rcases hz.1.1.2.1 0 with h|h
    · exact h
    · have hh:=(first_master_lower_bounds z hz.1).2 h
      linarith
  refine ⟨hy,?_⟩
  have hx:=hz.1.1.1.1.1 0
  change (1/2:ℝ)≤z.x 0 at hx
  have hg:=hz.1.2.2.2.2.2.2 (0:Fin 1) (0:Fin 1)
  change ineqTangent positiveData positiveInitial.kkt.jet _ _ _≤_ at hg
  rw [positive_inequality_tangent,hy] at hg
  linarith

/-- Empty relaxation with genuine nonlinear objective and inequality. -/
def emptyData : Data 1 1 0 1 0 where
  f x := (x 0)^2
  h := Fin.elim0
  g _ x := (x 0)^2+1
  A := Fin.elim0
  B _ := scalar 0
  C := Fin.elim0
  D := Fin.elim0
  rhs := Fin.elim0
  xL := scalar 0
  xU := scalar 1
  c := scalar 0

def emptyJet (x : V) : Jet emptyData x where
  Df := (2*x 0) • coord
  Dh := Fin.elim0
  Dg _ := (2*x 0) • coord
  fderiv := derivative_square x
  hderiv i := Fin.elim0 i
  gderiv _ := (derivative_square x).add_const 1

theorem empty_convex : ConvexOn ℝ emptyData.xBox emptyData.f ∧
    ∀ i,ConvexOn ℝ emptyData.xBox (emptyData.g i) := by
  refine ⟨convex_square_on (convex_Icc _ _),?_⟩
  intro i
  exact (convex_square_on (convex_Icc _ _)).add_const 1

theorem empty_not_feasible (x y : V) : ¬emptyData.Feasible x y := by
  intro h
  have hg:=h.2.2 0
  norm_num [Data.ineqRow,emptyData,dot,Fin.sum_univ_one] at hg
  nlinarith [sq_nonneg (x 0)]

theorem empty_relaxation : ¬emptyData.relaxed.Nonempty := by
  rintro ⟨z,hz⟩
  exact empty_not_feasible z.1 z.2 hz.1

theorem empty_original : ¬emptyData.original.Nonempty := by
  rintro ⟨z,hz⟩
  exact empty_not_feasible z.1 z.2 hz.1

/-- Certificate regularity is vacuous here because the actual sets are empty. -/
theorem empty_joint_regularity : JointRegularity emptyData :=
  fun h => False.elim (empty_relaxation h)

theorem empty_fiber_regularity : FiberRegularity emptyData := by
  intro b hb
  obtain ⟨x,hx⟩:=hb
  exact False.elim (empty_not_feasible x (realBinary b) hx)

def emptyInitialization : Initialization emptyData := .empty empty_relaxation

theorem empty_procedure_all_choices : Nonempty (Initialization emptyData) ∧
    Nonempty (Selector emptyData) ∧
    ∀ choose : Selector emptyData,
      procedure emptyData emptyInitialization choose=some ⟨.infeasible,0,0⟩ ∧
      ReturnCertificate emptyData (.infeasible : Result 1 1) := by
  have h:=qualified_source_procedure emptyData empty_joint_regularity empty_fiber_regularity
  exact ⟨h.1,h.2.1,fun _ => ⟨rfl,empty_original⟩⟩

/-- Source-bound nonvacuity and exact initial/continuation paths, uncounted support. -/
structure SupplementalControls : Prop where
  positiveDerivatives : ∀ x,Nonempty (Jet positiveData x)
  objectiveNonaffine : ¬∃ a b : ℝ,∀ x∈positiveData.xBox,positiveData.f x=a*x 0+b
  inequalityNonaffine : ¬∃ a b : ℝ,∀ x∈positiveData.xBox,positiveData.g 0 x=a*x 0+b
  positiveConvex : ConvexOn ℝ positiveData.xBox positiveData.f ∧
    ∀ i,ConvexOn ℝ positiveData.xBox (positiveData.g i)
  actualJointKKT : Nonempty (JointKKT positiveData (scalar (1/2)) (scalar (1/4)))
  actualOneFiberKKT : Nonempty (FixedKKT positiveData (scalar (1/2)) (scalar 1))
  initialFractional : ¬Binary positiveRelaxed.y
  relaxedMinimum : IsMinimizer positiveData.relaxed (pointObjective positiveData)
    (scalar (1/2),scalar (1/4))
  originalMinimum : IsMinimizer positiveData.original (pointObjective positiveData)
    (scalar (1/2),scalar 1)
  objectiveValues : pointObjective positiveData (scalar (1/2),scalar (1/4))=1/2 ∧
    pointObjective positiveData (scalar (1/2),scalar 1)=5/4
  emptyFiber : ¬(positiveData.fiber (scalar 0)).Nonempty
  firstMasterMinimum : IsMinimizer (masterFeasible positiveData [positiveInitial] ∅)
    (masterObjective positiveData [positiveInitial]) firstMaster
  firstMasterValues : masterObjective positiveData [positiveInitial] firstMaster=3/4 ∧
    firstMaster.q (0:Fin 1) 0=1/4 ∧ firstMaster.s (0:Fin 1)=0
  everyFirstMinimumSlack : ∀ z,IsMinimizer (masterFeasible positiveData [positiveInitial] ∅)
    (masterObjective positiveData [positiveInitial]) z → z.y 0=0 ∧ (1/4:ℝ)≤z.q (0:Fin 1) 0
  actualContinuation : Continue positiveData (initialState positiveInitial) positiveAfterEmpty
  unchangedIncumbent : positiveAfterEmpty.incumbent=none
  retainedNoGood : zeroBinary∈positiveAfterEmpty.seen
  retainedHistory : positiveAfterEmpty.history=[positiveInitial]
  positiveAllSelectors : Nonempty (Initialization positiveData) ∧ Nonempty (Selector positiveData) ∧
    ∀ initial : Initialization positiveData,∀ choose : Selector positiveData,∃ output,
      procedure positiveData initial choose=some output ∧
      output.result=.solution (scalar (1/2),scalar 1) ∧ output.binarySolves≤2 ∧
      output.masterDecisions≤3 ∧ ReturnCertificate positiveData output.result
  positiveExecutedFirstStep : ∃ choose : Selector positiveData,
    (procedure positiveData positiveInitialization choose =
      (run positiveData choose 2 positiveAfterEmpty
        (continue_invariant positiveData (initial_invariant positiveInitial)
          positive_actual_first_step.1)).map (fun out => ⟨out.1,out.2+1,out.2+2⟩)) ∧
    ∃ output,procedure positiveData positiveInitialization choose=some output ∧
      output.result=.solution (scalar (1/2),scalar 1) ∧ output.binarySolves≤2 ∧
      output.masterDecisions≤3 ∧ ReturnCertificate positiveData output.result
  emptyDerivatives : ∀ x,Nonempty (Jet emptyData x)
  emptyConvex : ConvexOn ℝ emptyData.xBox emptyData.f ∧ ∀ i,ConvexOn ℝ emptyData.xBox (emptyData.g i)
  emptyRelaxation : ¬emptyData.relaxed.Nonempty
  emptyOriginal : ¬emptyData.original.Nonempty
  emptyInitialReturn : Nonempty (Initialization emptyData) ∧ Nonempty (Selector emptyData) ∧
    ∀ choose : Selector emptyData,
      procedure emptyData emptyInitialization choose=some ⟨.infeasible,0,0⟩ ∧
      ReturnCertificate emptyData (.infeasible : Result 1 1)

theorem supplemental_controls : SupplementalControls where
  positiveDerivatives := fun x => ⟨positiveJet x⟩
  objectiveNonaffine := positive_nonaffine
  inequalityNonaffine := positive_nonaffine
  positiveConvex := ⟨(positive_signed initialKKT).objective,(positive_signed initialKKT).inequalities⟩
  actualJointKKT := ⟨initialJoint⟩
  actualOneFiberKKT := ⟨oneKKT⟩
  initialFractional := by intro h; have hh:=h 0; norm_num [positiveRelaxed] at hh
  relaxedMinimum := positive_relaxed_minimum
  originalMinimum := positive_original_minimum
  objectiveValues := by norm_num [pointObjective]
  emptyFiber := positive_zero_fiber_empty
  firstMasterMinimum := first_master_minimum
  firstMasterValues := by norm_num [first_master_value,firstMaster]
  everyFirstMinimumSlack := first_every_minimum_positive_slack
  actualContinuation := positive_actual_first_step.1
  unchangedIncumbent := positive_actual_first_step.2.1
  retainedNoGood := positive_actual_first_step.2.2.1
  retainedHistory := positive_actual_first_step.2.2.2.1
  positiveAllSelectors := positive_procedure_all_choices
  positiveExecutedFirstStep := positive_first_execution_exists
  emptyDerivatives := fun x => ⟨emptyJet x⟩
  emptyConvex := empty_convex
  emptyRelaxation := empty_relaxation
  emptyOriginal := empty_original
  emptyInitialReturn := empty_procedure_all_choices

end Chapter02DICOPTSupplemental
