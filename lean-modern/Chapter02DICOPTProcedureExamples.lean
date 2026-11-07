module

public import Chapter02DICOPTProcedure
public import Chapter02DICOPTInfeasible

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
open scoped BigOperators
namespace Chapter02DICOPTExamples

theorem nonlinear_fiber_regularity : FiberRegularity nonlinearData := by
  intro b hb
  cases he : b 0 with
  | false =>
    have hy : realBinary b=scalar 0 := by ext i; fin_cases i; simp [realBinary,he]
    rw [hy]
    exact ⟨scalar 0,nonlinearZero.kkt,nonlinearZero.convex⟩
  | true =>
    have hy : realBinary b=scalar 1 := by ext i; fin_cases i; simp [realBinary,he]
    rw [hy]
    exact ⟨scalar 1,nonlinearOne.kkt,nonlinearOne.convex⟩

theorem nonlinear_joint_regularity : JointRegularity nonlinearData :=
  fun _ => ⟨scalar (5/6),scalar (55/72),nonlinearJoint,nonlinearInitial.convex⟩

def nonlinearRelaxedAnchor : RelaxedAnchor nonlinearData :=
  ⟨scalar (5/6),scalar (55/72),nonlinearJoint,nonlinearInitial.convex,nonlinearInitial.weights⟩
def nonlinearInitialization : Initialization nonlinearData :=
  .fractional nonlinearRelaxedAnchor (by
    intro h
    have hh := h 0
    norm_num [nonlinearRelaxedAnchor] at hh)

theorem nonlinear_unique_minimum (q : V×V)
    (hq : IsMinimizer nonlinearData.original (pointObjective nonlinearData) q) :
    q=(scalar 1,scalar 1) := by
  rcases (nonlinear_original_points _ _).mp hq.1 with ⟨hx,hy⟩|⟨hx,hy⟩
  · have hh := hq.2 (scalar 1,scalar 1) nonlinear_original_minimum.1
    norm_num [pointObjective,hx,hy] at hh
  · exact Prod.ext hx hy

theorem nonlinear_procedure_all_choices : Nonempty (Selector nonlinearData) ∧
    ∀ choose : Selector nonlinearData, ∃ output,
      procedure nonlinearData nonlinearInitialization choose=some output ∧
      output.result=.solution (scalar 1,scalar 1) ∧
      output.binarySolves≤2 ∧ output.masterDecisions≤3 ∧
      ReturnCertificate nonlinearData output.result := by
  have hh := qualified_source_procedure nonlinearData nonlinear_joint_regularity nonlinear_fiber_regularity
  refine ⟨hh.2.1,?_⟩
  intro choose
  obtain ⟨out,hout,hb,hm,ht,hcert⟩ := hh.2.2 nonlinearInitialization choose
  refine ⟨out,hout,?_,by simpa using hb,by simpa using hm,hcert⟩
  exact certificate_solution_of_unique nonlinearData out.result hcert
    (scalar 1,scalar 1) nonlinear_original_minimum nonlinear_unique_minimum

theorem infeasible_fiber_regularity : FiberRegularity infeasibleData := by
  intro b hb
  exact False.elim (infeasible_binary_fiber_empty _ (realBinary_binary b) hb)

theorem infeasible_joint_regularity : JointRegularity infeasibleData :=
  fun _ => ⟨scalar 0,scalar (1/2),infeasibleJoint,infeasibleInitial.convex⟩

def infeasibleRelaxedAnchor : RelaxedAnchor infeasibleData :=
  ⟨scalar 0,scalar (1/2),infeasibleJoint,infeasibleInitial.convex,infeasibleInitial.weights⟩
def infeasibleInitialization : Initialization infeasibleData :=
  .fractional infeasibleRelaxedAnchor (by
    intro h
    have hh := h 0
    norm_num [infeasibleRelaxedAnchor] at hh)

theorem infeasible_procedure_all_choices : Nonempty (Selector infeasibleData) ∧
    ∀ choose : Selector infeasibleData, ∃ output,
      procedure infeasibleData infeasibleInitialization choose=some output ∧
      output.result=.infeasible ∧ output.binarySolves≤2 ∧ output.masterDecisions≤3 ∧
      ReturnCertificate infeasibleData output.result := by
  have hh := qualified_source_procedure infeasibleData infeasible_joint_regularity infeasible_fiber_regularity
  refine ⟨hh.2.1,?_⟩
  intro choose
  obtain ⟨out,hout,hb,hm,ht,hcert⟩ := hh.2.2 infeasibleInitialization choose
  refine ⟨out,hout,?_,by simpa using hb,by simpa using hm,hcert⟩
  apply (certificate_infeasible_iff infeasibleData out.result hcert).mpr
  simp [infeasible_original_empty]

def infeasibleReply (b : BVector 1) : FiberReply infeasibleData where
  binary := b
  anchor := none
  same_y := by simp
  empty := fun _ => infeasible_binary_fiber_empty _ (realBinary_binary b)

def infeasibleMaster (b : BVector 1) : MasterPoint infeasibleData [infeasibleInitial] where
  x := scalar 0
  y := realBinary b
  alpha := 0
  s _ := 0
  p _ := scalar 0
  q _ := Fin.elim0

theorem infeasible_master_feasible (b : BVector 1) :
    infeasibleMaster b ∈ masterFeasible infeasibleData [infeasibleInitial] ∅ := by
  refine ⟨⟨?_,realBinary_binary b,by simp⟩,?_,?_,?_,?_,?_,?_⟩
  · constructor
    · norm_num [Data.xBox,infeasibleData,Pi.le_def,Fin.forall_fin_one,infeasibleMaster]
    · intro i; exact Fin.elim0 i
  · intro k; exact le_rfl
  · intro k i; exact le_rfl
  · intro k i; exact Fin.elim0 i
  · intro k; fin_cases k
    dsimp [objTangent,infeasibleMaster,infeasibleInitial,infeasibleKKT,infeasibleJet,infeasibleData]
    norm_num
  · intro k i; fin_cases k; fin_cases i
    dsimp [eqTangent,infeasibleMaster,infeasibleInitial,infeasibleKKT,infeasibleJet,infeasibleData]
    norm_num [signReal]
  · intro k i; exact Fin.elim0 i

theorem infeasible_master_minimum (b : BVector 1) :
    IsMinimizer (masterFeasible infeasibleData [infeasibleInitial] ∅)
      (masterObjective infeasibleData [infeasibleInitial]) (infeasibleMaster b) := by
  refine ⟨infeasible_master_feasible b,?_⟩
  intro z hz
  have hs := hz.2.1 (0:Fin 1)
  have hp := hz.2.2.1 (0:Fin 1) (0:Fin 1)
  have hf := hz.2.2.2.2.1 (0:Fin 1)
  simp [objTangent,infeasibleInitial,infeasibleKKT,infeasibleJet,infeasibleData] at hf
  simp [masterObjective,infeasibleMaster,infeasibleData,infeasibleInitial,Fin.sum_univ_succ]
  linarith

theorem infeasible_actual_first_step (b : BVector 1) :
    Continue infeasibleData (initialState infeasibleInitial)
      (append infeasibleData (initialState infeasibleInitial) (infeasibleReply b)) ∧
    (append infeasibleData (initialState infeasibleInitial) (infeasibleReply b)).incumbent=none ∧
    b ∈ (append infeasibleData (initialState infeasibleInitial) (infeasibleReply b)).seen := by
  refine ⟨?_,rfl,?_⟩
  · exact .step (infeasible_master_minimum b) (by intro u hu; cases hu) rfl
  · rw [seen_append]
    exact Finset.mem_insert_self _ _

def emptyFirstSelector (b : BVector 1) (fallback : Selector infeasibleData) :
    Selector infeasibleData := by
  classical
  intro s hs
  by_cases he : s=initialState infeasibleInitial
  · subst s
    exact .next _ (infeasible_actual_first_step b).1
  · exact fallback s hs

theorem infeasible_actual_first_run (b : BVector 1) :
    ∃ choose : Selector infeasibleData,
      run infeasibleData choose 3 (initialState infeasibleInitial)
        (initial_invariant infeasibleInitial) =
      (run infeasibleData choose 2
        (append infeasibleData (initialState infeasibleInitial) (infeasibleReply b))
        (continue_invariant infeasibleData (initial_invariant infeasibleInitial)
          (infeasible_actual_first_step b).1)).map (fun out => (out.1,out.2+1)) := by
  obtain ⟨fallback⟩ := infeasible_procedure_all_choices.1
  refine ⟨emptyFirstSelector b fallback,?_⟩
  rw [run]
  simp [emptyFirstSelector]

end Chapter02DICOPTExamples
