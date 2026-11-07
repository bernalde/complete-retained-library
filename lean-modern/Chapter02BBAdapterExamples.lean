module

public import Chapter02BBSimulation
public import Chapter02BBDriver
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Tactic

@[expose] public section

/-! Original-coordinate controls for the bounded-polyhedral adapter. Coordinates
0 and2 are integral; coordinate1 remains continuous at the fractional value1/2.
The objective is genuinely quadratic, with actual affine/nonlinear coupling. -/
noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02BBAdapterExamples

def indices : Finset (Fin 3) := {0, 2}
def firstInteger : {i : Fin 3 // i ∈ indices} := ⟨0, by simp [indices]⟩

def partition : BBPartition indices 1 2 where
  continuousEquiv :=
    { toFun := fun _ => 0
      invFun := fun _ => ⟨1, by simp [indices]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        have hi := i.property
        simp only [indices, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hi
        apply Fin.ext
        have hlt := i.val.isLt
        dsimp at hi ⊢
        omega
      right_inv := by intro i; fin_cases i; rfl }
  integerEquiv :=
    { toFun := fun i => if i.val = 0 then 0 else 1
      invFun := fun j => if j = 0 then ⟨0, by simp [indices]⟩ else ⟨2, by simp [indices]⟩
      left_inv := by
        rintro ⟨i, hi⟩
        apply Subtype.ext
        fin_cases i <;> simp_all [indices]
        all_goals exact False.elim ((by decide : (1 : Fin 3) ∉ indices) hi)
      right_inv := by intro j; fin_cases j <;> simp }

def point (a b c : ℝ) : RealVector 3 := ![a, b, c]
def rootPoint (a : ℝ) := point a (1/2) 0
def leftPoint := point 0 (1/2) 0
def rightPoint := point 1 (1/2) 0

def data (a : ℝ) : BBPolyData 3 1 7 where
  coefficient := ![![-1,0,0], ![1,0,0], ![0,-1,0], ![0,1,0],
    ![0,0,-1], ![0,0,1], ![1,1,1]]
  rhs := ![0,1,0,1,0,1,3/2]
  c := fun z _ => z 0 + (z 1)^2 - 5/4
  f := fun z => (z 0-a)^2 + (z 1-1/2)^2 + (z 2)^2

theorem split_coordinates (z : RealVector 3) :
    partition.split z = (fun _ => z 1, ![z 0, z 2]) := by
  apply Prod.ext
  · funext i; fin_cases i; simp [BBPartition.split, partition]
  · funext i; fin_cases i <;> simp [BBPartition.split, partition]

theorem join_coordinates (p : Point 1 2) :
    partition.join p = point (p.2 0) (p.1 0) (p.2 1) := by
  funext i
  fin_cases i <;> rfl

theorem polyhedron_iff (a : ℝ) (z : RealVector 3) :
    z ∈ (data a).polyhedron ↔
      (0 ≤ z 0 ∧ z 0 ≤ 1) ∧ (0 ≤ z 1 ∧ z 1 ≤ 1) ∧
      (0 ≤ z 2 ∧ z 2 ≤ 1) ∧ z 0 + z 1 + z 2 ≤ 3/2 := by
  simp [BBPolyData.polyhedron, data, Fin.forall_fin_succ, Fin.sum_univ_succ,
    and_assoc, add_assoc]

theorem polyhedron_bounded (a : ℝ) : Bornology.IsBounded (data a).polyhedron := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : RealVector 3) 1)).isBounded.subset
  intro z hz
  obtain ⟨h0,h1,h2,hs⟩ := (polyhedron_iff a z).mp hz
  constructor <;> intro i <;> fin_cases i <;> simp_all

theorem enclosing_bound (a : ℝ) : (data a).Encloses (3/2) := by
  refine ⟨by norm_num, ?_⟩
  intro z hz i
  obtain ⟨h0,h1,h2,hs⟩ := (polyhedron_iff a z).mp hz
  apply abs_le.mpr
  fin_cases i <;> dsimp <;> constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2]

theorem objective_c2 (a : ℝ) : ContDiff ℝ 2 (data a).f := by
  dsimp [data]
  fun_prop

theorem constraints_c2 (a : ℝ) : ContDiff ℝ 2 (data a).c := by
  dsimp [data]
  fun_prop

theorem shifted_square_convex (i : Fin 3) (a : ℝ) :
    ConvexOn ℝ Set.univ (fun z : RealVector 3 => (z i-a)^2) := by
  have hs : ConvexOn ℝ Set.univ (fun x : ℝ => x^2) := (by decide : Even 2).convexOn_pow
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy s t hs0 ht0 hst
  have hh := hs.2 (Set.mem_univ (x i-a)) (Set.mem_univ (y i-a)) hs0 ht0 hst
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh ⊢
  have heq : s*x i + t*y i-a = s*(x i-a)+t*(y i-a) := by
    calc
      _ = s*x i+t*y i-(s+t)*a := by rw [hst]; ring
      _ = _ := by ring
  simpa only [heq] using hh

theorem objective_convex (a : ℝ) : ConvexOn ℝ Set.univ (data a).f := by
  apply (((shifted_square_convex 0 a).add
    (shifted_square_convex 1 (1/2))).add (shifted_square_convex 2 0)).congr
  intro z hz
  simp [data, Pi.add_apply]

theorem constraints_convex (a : ℝ) : ConvexOn ℝ Set.univ (data a).c := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy s t hs ht hst j
  have hh := (shifted_square_convex 1 0).2 hx hy hs ht hst
  simp only [data, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_zero] at hh ⊢
  nlinarith [hst]

def root : BBExternalNode indices := BBExtendedNode.root
def left : BBExternalNode indices := root.left firstInteger (2/5)
def right : BBExternalNode indices := root.right firstInteger (2/5)

theorem fractional (a : ℝ) (ha : 0 < a) (hb : a < 1) : BBFractional a := by
  rintro ⟨z,hz⟩
  rw [← hz] at ha hb
  have h0 : (0 : ℤ) < z := by exact_mod_cast ha
  have h1 : z < (1 : ℤ) := by exact_mod_cast hb
  omega

theorem root_member (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1) :
    rootPoint a ∈ (data a).relaxation root := by
  refine ⟨(polyhedron_iff _ _).2 ?_, ?_, BBExtendedNode.holds_root _⟩
  · simp only [rootPoint,point,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    norm_num
    exact ⟨⟨ha,hb⟩, by linarith⟩
  · intro j
    dsimp [data,rootPoint,point]
    norm_num
    linarith

theorem root_minimum (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1) :
    IsMinimizer ((data a).relaxation root) (data a).f (rootPoint a) := by
  refine ⟨root_member a ha hb, ?_⟩
  intro z hz
  dsimp [data,rootPoint,point]
  nlinarith [sq_nonneg (z 0-a),sq_nonneg (z 1-1/2),sq_nonneg (z 2)]

theorem left_holds_iff (z : RealVector 3) : left.Holds (fun i => z i) ↔ z 0 ≤ 0 := by
  constructor
  · intro h
    have hh := (h firstInteger).2
    norm_num [left,root,BBExtendedNode.left,BBExtendedNode.root,firstInteger] at hh
    exact hh
  · intro h i
    constructor
    · exact bot_le
    · by_cases hi : i = firstInteger
      · subst i
        norm_num [left,root,BBExtendedNode.left,BBExtendedNode.root,firstInteger]
        exact h
      · dsimp only [left,root,BBExtendedNode.left,BBExtendedNode.root]
        simp [Function.update,hi]

theorem right_holds_iff (z : RealVector 3) : right.Holds (fun i => z i) ↔ 1 ≤ z 0 := by
  constructor
  · intro h
    have hh := (h firstInteger).1
    norm_num [right,root,BBExtendedNode.right,BBExtendedNode.root,firstInteger] at hh
    exact hh
  · intro h i
    constructor
    · by_cases hi : i = firstInteger
      · subst i
        norm_num [right,root,BBExtendedNode.right,BBExtendedNode.root,firstInteger]
        exact h
      · dsimp only [right,root,BBExtendedNode.right,BBExtendedNode.root]
        simp [Function.update,hi]
    · exact le_top

theorem left_member (a : ℝ) : leftPoint ∈ (data a).relaxation left := by
  refine ⟨(polyhedron_iff _ _).2 ?_, ?_, (left_holds_iff _).2 ?_⟩ <;>
    norm_num [leftPoint,point,data,Matrix.cons_val_two]

theorem right_member (a : ℝ) : rightPoint ∈ (data a).relaxation right := by
  refine ⟨(polyhedron_iff _ _).2 ?_, ?_, (right_holds_iff _).2 ?_⟩ <;>
    norm_num [rightPoint,point,data,Matrix.cons_val_two]

theorem left_minimum (a : ℝ) :
    IsMinimizer ((data a).relaxation left) (data a).f leftPoint := by
  refine ⟨left_member a, ?_⟩
  intro z hz
  have h0 := ((polyhedron_iff a z).mp hz.1).1.1
  have h1 := (left_holds_iff z).mp hz.2.2
  have heq : z 0 = 0 := le_antisymm h1 h0
  dsimp [data,leftPoint,point]
  rw [heq]
  nlinarith [sq_nonneg (z 1-1/2),sq_nonneg (z 2)]

theorem right_minimum (a : ℝ) :
    IsMinimizer ((data a).relaxation right) (data a).f rightPoint := by
  refine ⟨right_member a, ?_⟩
  intro z hz
  have h0 := ((polyhedron_iff a z).mp hz.1).1.2
  have h1 := (right_holds_iff z).mp hz.2.2
  have heq : z 0 = 1 := le_antisymm h0 h1
  dsimp [data,rightPoint,point]
  rw [heq]
  nlinarith [sq_nonneg (z 1-1/2),sq_nonneg (z 2)]

theorem left_integral : bbExternalInteger indices leftPoint := by
  rintro ⟨i,hi⟩
  fin_cases i <;> simp_all [indices,leftPoint,point,Matrix.cons_val_two]
  all_goals exact False.elim ((by decide : (1 : Fin 3) ∉ indices) hi)

theorem right_integral : bbExternalInteger indices rightPoint := by
  rintro ⟨i,hi⟩
  fin_cases i <;> simp_all [indices,rightPoint,point,Matrix.cons_val_two]
  all_goals exact False.elim ((by decide : (1 : Fin 3) ∉ indices) hi)

def afterBranch : BBExternalState indices := ⟨[left,right],none⟩
def afterInferior : BBExternalState indices := ⟨[left],some rightPoint⟩
def final : BBExternalState indices := ⟨[],some leftPoint⟩

theorem step_root : BBExternalProcess (data (2/5)) indices
    (bbExternalInitial indices) afterBranch := by
  simpa [bbExternalInitial,afterBranch,left,right,root,rootPoint,point,firstInteger] using
    (BBExternalProcess.branch (D := data (2/5)) (pre := []) (post := []) (inc := none)
      firstInteger (root_minimum (2/5) (by norm_num) (by norm_num))
      (by simp [bbExternalUpper]) (fractional (2/5) (by norm_num) (by norm_num)))

theorem step_inferior : BBExternalProcess (data (2/5)) indices afterBranch afterInferior := by
  exact BBExternalProcess.integral (pre := [left]) (post := []) (right_minimum (2/5))
    (by simp [bbExternalUpper]) right_integral

theorem step_best : BBExternalProcess (data (2/5)) indices afterInferior final := by
  exact BBExternalProcess.integral (pre := []) (post := []) (left_minimum (2/5))
    (by norm_num [bbExternalUpper,data,rightPoint,leftPoint,point,Matrix.cons_val_two]) left_integral

theorem inferior_first_trace : BBExternalTrace (data (2/5)) indices
    (bbExternalInitial indices) 3 final :=
  .step (.step (.step (.refl _) step_root) step_inferior) step_best

theorem inferior_not_global :
    ¬ IsMinimizer ((data (2/5)).feasible indices) (data (2/5)).f rightPoint := by
  intro h
  have hl : leftPoint ∈ (data (2/5)).feasible indices :=
    ⟨(left_member (2/5)).1,(left_member (2/5)).2.1,left_integral⟩
  have hv := h.2 leftPoint hl
  norm_num [data,leftPoint,rightPoint,point,Matrix.cons_val_two] at hv

theorem values_and_active_rows :
    (data (2/5)).f (rootPoint (2/5)) = 0 ∧
    (data (2/5)).f rightPoint = 9/25 ∧ (data (2/5)).f leftPoint = 4/25 ∧
    rightPoint 0 + rightPoint 1 + rightPoint 2 = 3/2 ∧ (data (2/5)).c rightPoint 0 = 0 := by
  norm_num [data,rootPoint,rightPoint,leftPoint,point,Matrix.cons_val_two]

theorem explicit_root_rank_weight :
    (bbRootNode ((data (2/5)).model partition (3/2))).rank = 8 ∧
    (bbRootNode ((data (2/5)).model partition (3/2))).weight = 511 := by
  norm_num [bbRootNode,BBPolyData.model,BBNode.rank,BBNode.span,BBNode.weight,Fin.sum_univ_succ]

theorem final_global_optimal :
    IsMinimizer ((data (2/5)).feasible indices) (data (2/5)).f leftPoint := by
  exact bb_external_reachable_correct (data (2/5)) partition (3/2) (enclosing_bound _)
    (polyhedron_bounded _) (constraints_c2 _).continuous (objective_c2 _).continuous.continuousOn
    ⟨3,inferior_first_trace⟩ rfl

theorem trace_transports_to_engine :
    ∃ s, BBTrace ((data (2/5)).model partition (3/2)) ((data (2/5)).objective partition)
      .belottiAlgorithm 3 (bbInitial ((data (2/5)).model partition (3/2)) none) s ∧
      BBStatesRelated partition (3/2) final s :=
  bb_simulate_trace_forward (data (2/5)) partition (3/2) (enclosing_bound _) inferior_first_trace
    (bb_sim_initial (data (2/5)) partition (3/2))

theorem all_selectors_with_discharged_source_premises
    (choose : BBExternalSelector (data (2/5)) indices) :
    ∃ (s : BBExternalState indices) (out : Option (RealVector 3)) (j : ℕ),
      j ≤ 511 ∧ BBExternalTrace (data (2/5)) indices (bbExternalInitial indices) j s ∧
      s.live = [] ∧ out = s.incumbent ∧
      bbExternalRun (data (2/5)) indices choose 512 = .stopped s out ∧
      BBExternalOutcome (data (2/5)) indices out := by
  have h := bb_belotti_every_selector_exact_return (data (2/5)) partition (3/2)
    (enclosing_bound _) (polyhedron_bounded _) (constraints_c2 _) (objective_c2 _)
    (constraints_convex _) (objective_convex _) choose
  simpa only [explicit_root_rank_weight.2] using h

theorem tie_children : root.left firstInteger (1/2) = left ∧
    root.right firstInteger (1/2) = right := by
  norm_num [left,right,root,BBExtendedNode.left,BBExtendedNode.right]

theorem tie_step_root : BBExternalProcess (data (1/2)) indices
    (bbExternalInitial indices) afterBranch := by
  have h := BBExternalProcess.branch (D := data (1/2)) (pre := []) (post := []) (inc := none)
    firstInteger (root_minimum (1/2) (by norm_num) (by norm_num))
    (by simp [bbExternalUpper]) (fractional (1/2) (by norm_num) (by norm_num))
  change BBExternalProcess (data (1/2)) indices ⟨[root],none⟩
    ⟨[root.left firstInteger (1/2),root.right firstInteger (1/2)],none⟩ at h
  rw [tie_children.1,tie_children.2] at h
  exact h

theorem tie_step_right : BBExternalProcess (data (1/2)) indices afterBranch afterInferior :=
  BBExternalProcess.integral (pre := [left]) (post := []) (right_minimum (1/2))
    (by simp [bbExternalUpper]) right_integral

theorem tie_step_left_replaces : BBExternalProcess (data (1/2)) indices afterInferior final :=
  BBExternalProcess.integral (pre := []) (post := []) (left_minimum (1/2))
    (by norm_num [bbExternalUpper,data,rightPoint,leftPoint,point,Matrix.cons_val_two]) left_integral

theorem tie_trace : BBExternalTrace (data (1/2)) indices
    (bbExternalInitial indices) 3 final :=
  .step (.step (.step (.refl _) tie_step_root) tie_step_right) tie_step_left_replaces

theorem tie_update_policy_difference :
    bbUpdate .source ((data (1/2)).objective partition) (some (partition.split rightPoint))
      (partition.split leftPoint) = some (partition.split rightPoint) ∧
    bbUpdate .belottiAlgorithm ((data (1/2)).objective partition) (some (partition.split rightPoint))
      (partition.split leftPoint) = some (partition.split leftPoint) ∧
    partition.split rightPoint ≠ partition.split leftPoint := by
  constructor
  · norm_num [bbUpdate,show BBPolicy.source ≠ BBPolicy.belottiAlgorithm by decide,BBPolyData.objective_split,data,rightPoint,leftPoint,point,Matrix.cons_val_two]
  constructor
  · norm_num [bbUpdate,show BBPolicy.source ≠ BBPolicy.belottiAlgorithm by decide,BBPolyData.objective_split,data,rightPoint,leftPoint,point,Matrix.cons_val_two]
  · intro h
    have hh := congrArg (fun p : Point 1 2 => p.2 0) h
    norm_num [split_coordinates,rightPoint,leftPoint,point] at hh

def emptyPartition : BBPartition (∅ : Finset (Fin 3)) 3 0 where
  continuousEquiv :=
    { toFun := fun i => i.val
      invFun := fun i => ⟨i,by simp⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  integerEquiv :=
    { toFun := fun i => False.elim (Finset.notMem_empty _ i.property)
      invFun := Fin.elim0
      left_inv := fun i => False.elim (Finset.notMem_empty _ i.property)
      right_inv := fun i => Fin.elim0 i }

def fullPartition : BBPartition (Finset.univ : Finset (Fin 3)) 0 3 where
  continuousEquiv :=
    { toFun := fun i => False.elim (i.property (Finset.mem_univ _))
      invFun := Fin.elim0
      left_inv := fun i => False.elim (i.property (Finset.mem_univ _))
      right_inv := fun i => Fin.elim0 i }
  integerEquiv :=
    { toFun := fun i => i.val
      invFun := fun i => ⟨i,Finset.mem_univ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def emptyIndicesFinal : BBExternalState (∅ : Finset (Fin 3)) :=
  ⟨[],some (rootPoint (2/5))⟩

theorem empty_indices_root_minimum :
    IsMinimizer ((data (2/5)).relaxation (BBExtendedNode.root : BBExternalNode ∅))
      (data (2/5)).f (rootPoint (2/5)) := by
  refine ⟨?_,?_⟩
  · exact ⟨(root_member (2/5) (by norm_num) (by norm_num)).1,
      (root_member (2/5) (by norm_num) (by norm_num)).2.1,BBExtendedNode.holds_root _⟩
  · intro z hz
    exact (root_minimum (2/5) (by norm_num) (by norm_num)).2 z
      ⟨hz.1,hz.2.1,BBExtendedNode.holds_root _⟩

theorem empty_indices_trace : BBExternalTrace (data (2/5)) (∅ : Finset (Fin 3))
    (bbExternalInitial ∅) 1 emptyIndicesFinal := by
  apply BBExternalTrace.step (.refl _)
  exact BBExternalProcess.integral (pre := []) (post := []) empty_indices_root_minimum
    (by simp [bbExternalUpper]) (by intro i; exact False.elim (Finset.notMem_empty _ i.property))

theorem empty_indices_endpoint :
    IsMinimizer ((data (2/5)).feasible ∅) (data (2/5)).f (rootPoint (2/5)) ∧
    (bbRootNode ((data (2/5)).model emptyPartition (3/2))).weight = 1 := by
  constructor
  · exact bb_external_reachable_correct (data (2/5)) emptyPartition (3/2) (enclosing_bound _)
      (polyhedron_bounded _) (constraints_c2 _).continuous (objective_c2 _).continuous.continuousOn
      ⟨1,empty_indices_trace⟩ rfl
  · simp [BBNode.weight,BBNode.rank]

def fullData : BBPolyData 3 1 7 :=
  { data 0 with f := fun z => (z 0)^2+(z 1)^2+(z 2)^2 }
def zeroPoint := point 0 0 0
def fullIndicesFinal : BBExternalState (Finset.univ : Finset (Fin 3)) := ⟨[],some zeroPoint⟩

theorem full_source_premises : Bornology.IsBounded fullData.polyhedron ∧
    fullData.Encloses (3/2) ∧ ContDiff ℝ 2 fullData.c ∧ ContDiff ℝ 2 fullData.f ∧
    ConvexOn ℝ Set.univ fullData.c ∧ ConvexOn ℝ Set.univ fullData.f := by
  refine ⟨polyhedron_bounded 0,enclosing_bound 0,constraints_c2 0,?_,constraints_convex 0,?_⟩
  · dsimp [fullData]; fun_prop
  · apply (((shifted_square_convex 0 0).add
      (shifted_square_convex 1 0)).add (shifted_square_convex 2 0)).congr
    intro z hz
    simp [fullData, Pi.add_apply]

theorem full_indices_minimum :
    IsMinimizer (fullData.relaxation (BBExtendedNode.root : BBExternalNode Finset.univ))
      fullData.f zeroPoint := by
  refine ⟨⟨?_,?_,BBExtendedNode.holds_root _⟩,?_⟩
  · apply (polyhedron_iff 0 zeroPoint).2
    norm_num [zeroPoint,point,Matrix.cons_val_two]
  · intro j
    norm_num [fullData,data,zeroPoint,point]
  · intro z hz
    dsimp [fullData,zeroPoint,point]
    nlinarith [sq_nonneg (z 0),sq_nonneg (z 1),sq_nonneg (z 2)]

theorem full_indices_trace : BBExternalTrace fullData (Finset.univ : Finset (Fin 3))
    (bbExternalInitial Finset.univ) 1 fullIndicesFinal := by
  apply BBExternalTrace.step (.refl _)
  apply BBExternalProcess.integral (pre := []) (post := []) full_indices_minimum
    (by simp [bbExternalUpper])
  intro i
  refine ⟨0,?_⟩
  rcases i with ⟨i,hi⟩
  fin_cases i <;> norm_num [zeroPoint,point,Matrix.cons_val_two]

theorem full_indices_endpoint : IsMinimizer (fullData.feasible Finset.univ) fullData.f zeroPoint := by
  exact bb_external_reachable_correct fullData fullPartition (3/2) full_source_premises.2.1
    full_source_premises.1 full_source_premises.2.2.1.continuous
    full_source_premises.2.2.2.1.continuous.continuousOn ⟨1,full_indices_trace⟩ rfl

def emptyData : BBPolyData 3 1 7 := { data 0 with rhs := fun _ => -1 }
def emptyPolyFinal : BBExternalState indices := ⟨[],none⟩

theorem empty_polyhedron : emptyData.polyhedron = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have h0 := hz 0
  have h1 := hz 1
  norm_num [BBPolyData.polyhedron,emptyData,data,Fin.sum_univ_succ] at h0 h1
  linarith

theorem empty_source_premises : Bornology.IsBounded emptyData.polyhedron ∧
    emptyData.Encloses (3/2) ∧ ContDiff ℝ 2 emptyData.c ∧ ContDiff ℝ 2 emptyData.f ∧
    ConvexOn ℝ Set.univ emptyData.c ∧ ConvexOn ℝ Set.univ emptyData.f := by
  refine ⟨?_,?_,constraints_c2 0,objective_c2 0,constraints_convex 0,objective_convex 0⟩
  · rw [empty_polyhedron]; exact isCompact_empty.isBounded
  · refine ⟨by norm_num,?_⟩
    intro z hz
    simp [empty_polyhedron] at hz

theorem empty_poly_root : emptyData.relaxation (BBExtendedNode.root : BBExternalNode indices) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hx := hz.1
  simp [empty_polyhedron] at hx

theorem empty_poly_trace : BBExternalTrace emptyData indices
    (bbExternalInitial indices) 1 emptyPolyFinal :=
  .step (.refl _) (BBExternalProcess.empty (pre := []) (post := []) empty_poly_root)

theorem empty_poly_endpoint : emptyData.feasible indices = ∅ :=
  bb_external_reachable_correct emptyData partition (3/2) empty_source_premises.2.1
    empty_source_premises.1 empty_source_premises.2.2.1.continuous
    empty_source_premises.2.2.2.1.continuous.continuousOn ⟨1,empty_poly_trace⟩ rfl

/-- Internal policy comparison: before any incumbent, the two strict-pruning
policies make identical state changes. This is used on the actual tie prefix. -/
theorem no_incumbent_policy_transfer {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) {s t : BBState n m}
    (h : BBProcess d f .belottiAlgorithm s t) (hnone : s.incumbent = none) :
    BBProcess d f .source s t := by
  cases h with
  | empty h => exact .empty h
  | unbounded h => exact .unbounded h
  | unattained hn hb hh => exact .unattained hn hb hh
  | @prune pre post b inc q hq hp =>
    change inc = none at hnone
    simp [hnone,bbPrunable] at hp
  | @integral pre post b inc q hq hk hi =>
    change inc = none at hnone
    subst inc
    simpa [bbUpdate] using
      (BBProcess.integral (policy := .source) (pre := pre) (post := post) (inc := none)
        hq (by simp [bbPrunable]) hi)
  | @branch pre post b inc q i hq hk hi =>
    change inc = none at hnone
    subst inc
    exact BBProcess.branch i hq (by simp [bbPrunable]) hi

theorem strict_tie_engine_trace :
    BBTrace ((data (1/2)).model partition (3/2)) ((data (1/2)).objective partition) .source 3
      (bbInitial ((data (1/2)).model partition (3/2)) none)
      ⟨[],some (partition.split rightPoint)⟩ := by
  obtain ⟨s1,hs1,hr1⟩ := bb_simulate_process_forward (data (1/2)) partition (3/2)
    (enclosing_bound _) tie_step_root (bb_sim_initial (data (1/2)) partition (3/2))
  obtain ⟨s2,hs2,hr2⟩ := bb_simulate_process_forward (data (1/2)) partition (3/2)
    (enclosing_bound _) tie_step_right hr1
  have h1 := no_incumbent_policy_transfer _ _ hs1 rfl
  have hn1 : s1.incumbent = none := by simpa [afterBranch] using hr1.2
  have h2 := no_incumbent_policy_transfer _ _ hs2 hn1
  rcases s2 with ⟨live,inc⟩
  have hi : inc = some (partition.split rightPoint) := by simpa [afterInferior] using hr2.2
  subst inc
  have hh : List.Forall₂ (fun B b => b.node = B.clamp partition.integerEquiv (3/2)) [left] live := hr2.1
  cases hh with
  | @cons a b as bs hb htail =>
    cases htail
    have hm : IsMinimizer (b.node.region ((data (1/2)).model partition (3/2)))
        ((data (1/2)).objective partition) (partition.split leftPoint) := by
      rw [hb]
      exact ((data (1/2)).minimizer_iff partition (3/2) (enclosing_bound _) left leftPoint).mp
        (left_minimum (1/2))
    have hk : ¬ bbPrunable .source ((data (1/2)).objective partition)
        (some (partition.split rightPoint)) ((data (1/2)).objective partition (partition.split leftPoint)) := by
      norm_num [bbPrunable,show BBPolicy.source ≠ BBPolicy.weak by decide,
        BBPolyData.objective_split,data,leftPoint,rightPoint,point,Matrix.cons_val_two]
    have hf : BBProcess ((data (1/2)).model partition (3/2)) ((data (1/2)).objective partition)
        .source ⟨[b],some (partition.split rightPoint)⟩ ⟨[],some (partition.split rightPoint)⟩ := by
      have hp := BBProcess.integral (policy := .source) (pre := []) (post := []) hm hk
        ((partition.integral_iff leftPoint).mp left_integral)
      simpa only [tie_update_policy_difference.1,List.nil_append] using hp
    exact .cons h1 (.cons h2 (.cons hf (.nil _)))

theorem tie_transport_and_distinct_outputs :
    (∃ s, BBTrace ((data (1/2)).model partition (3/2)) ((data (1/2)).objective partition)
      .belottiAlgorithm 3 (bbInitial ((data (1/2)).model partition (3/2)) none) s ∧
      s.live = [] ∧ s.incumbent = some (partition.split leftPoint)) ∧
    partition.split rightPoint ≠ partition.split leftPoint := by
  obtain ⟨s,hs,hr⟩ := bb_simulate_trace_forward (data (1/2)) partition (3/2)
    (enclosing_bound _) tie_trace (bb_sim_initial (data (1/2)) partition (3/2))
  refine ⟨⟨s,hs,(bb_sim_empty_live_iff partition (3/2) hr).mp rfl,?_⟩,
    tie_update_policy_difference.2.2⟩
  simpa [final] using hr.2

def capIndices : Finset (Fin 1) := Finset.univ
def capIndex : {i : Fin 1 // i ∈ capIndices} := ⟨0,Finset.mem_univ _⟩
def capPartition : BBPartition capIndices 0 1 where
  continuousEquiv :=
    { toFun := fun i => False.elim (i.property (Finset.mem_univ _))
      invFun := Fin.elim0
      left_inv := fun i => False.elim (i.property (Finset.mem_univ _))
      right_inv := fun i => Fin.elim0 i }
  integerEquiv :=
    { toFun := fun i => i.val
      invFun := fun i => ⟨i,Finset.mem_univ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def capData : BBPolyData 1 0 2 where
  coefficient := ![fun _ => -1,fun _ => 1]
  rhs := ![0,3/2]
  c := fun _ => Fin.elim0
  f := fun _ => 0
def capRoot : BBExternalNode capIndices := BBExtendedNode.root
def capLeft := capRoot.left capIndex (6/5)
def capRight := capRoot.right capIndex (6/5)
def capAfter : BBExternalState capIndices := ⟨[capLeft,capRight],none⟩
def capLast : BBExternalState capIndices := ⟨[capRight],some (fun _ => 0)⟩
def capFinal : BBExternalState capIndices := ⟨[],some (fun _ => 0)⟩

theorem cap_poly_iff (z : RealVector 1) : z ∈ capData.polyhedron ↔ 0 ≤ z 0 ∧ z 0 ≤ 3/2 := by
  simp [capData,BBPolyData.polyhedron,Fin.forall_fin_succ,Fin.sum_univ_succ]

theorem cap_source_premises : Bornology.IsBounded capData.polyhedron ∧
    capData.Encloses (3/2) ∧ ContDiff ℝ 2 capData.c ∧ ContDiff ℝ 2 capData.f ∧
    ConvexOn ℝ Set.univ capData.c ∧ ConvexOn ℝ Set.univ capData.f := by
  refine ⟨?_,?_,?_,contDiff_const,?_,convexOn_const 0 convex_univ⟩
  · apply (isCompact_Icc : IsCompact (Set.Icc (0 : RealVector 1) (fun _ => 3/2))).isBounded.subset
    intro z hz
    have hh := (cap_poly_iff z).mp hz
    constructor <;> intro i <;> fin_cases i <;> simp_all
  · refine ⟨by norm_num,?_⟩
    intro z hz i
    have hh := (cap_poly_iff z).mp hz
    fin_cases i
    change |z 0| ≤ 3/2
    simpa only [abs_of_nonneg hh.1] using hh.2
  · exact contDiff_pi.mpr (fun i => Fin.elim0 i)
  · refine ⟨convex_univ,?_⟩
    intro _ _ _ _ _ _ _ _ _ i
    exact Fin.elim0 i

theorem cap_root_minimum : IsMinimizer (capData.relaxation capRoot) capData.f (fun _ => 6/5) := by
  refine ⟨⟨(cap_poly_iff _).2 (by norm_num),?_,BBExtendedNode.holds_root _⟩,?_⟩
  · intro i; exact Fin.elim0 i
  · intro _ _; exact le_rfl

theorem cap_left_minimum : IsMinimizer (capData.relaxation capLeft) capData.f (fun _ => 0) := by
  refine ⟨⟨(cap_poly_iff _).2 (by norm_num),?_,?_⟩,?_⟩
  · intro i; exact Fin.elim0 i
  · intro i
    have hi : i = capIndex := by apply Subtype.ext; exact Subsingleton.elim _ _
    subst i
    norm_num [capLeft,capRoot,BBExtendedNode.left,BBExtendedNode.root]
  · intro _ _; exact le_rfl

theorem cap_right_empty : capData.relaxation capRight = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hu := ((cap_poly_iff z).mp hz.1).2
  have hl := (hz.2.2 capIndex).1
  norm_num [capRight,capRoot,BBExtendedNode.right,BBExtendedNode.root,capIndex] at hl
  have hl' : (2 : ℝ) ≤ z 0 := WithBot.coe_le_coe.mp hl
  linarith

theorem cap_branch_step : BBExternalProcess capData capIndices
    (bbExternalInitial capIndices) capAfter :=
  BBExternalProcess.branch (pre := []) (post := []) capIndex cap_root_minimum
    (by simp [bbExternalUpper]) (by
      rintro ⟨z,hz⟩
      have h1 : (1 : ℝ) < (z : ℝ) := by rw [hz]; norm_num
      have h2 : (z : ℝ) < (2 : ℝ) := by rw [hz]; norm_num
      have hz1 : (1 : ℤ) < z := by exact_mod_cast h1
      have hz2 : z < (2 : ℤ) := by exact_mod_cast h2
      omega)

theorem cap_trace : BBExternalTrace capData capIndices
    (bbExternalInitial capIndices) 3 capFinal := by
  have hleft : BBExternalProcess capData capIndices capAfter capLast :=
    BBExternalProcess.integral (pre := []) (post := [capRight]) cap_left_minimum
      (by simp [bbExternalUpper]) (fun _ => ⟨0,by norm_num⟩)
  have hright : BBExternalProcess capData capIndices capLast capFinal :=
    BBExternalProcess.empty (pre := []) (post := []) cap_right_empty
  exact .step (.step (.step (.refl _) cap_branch_step) hleft) hright

theorem cap_outward_clamp_empty :
    (capRight.clamp capPartition.integerEquiv (3/2)).lower 0 = 2 ∧
    (capRight.clamp capPartition.integerEquiv (3/2)).upper 0 = 3/2 ∧
    (capRight.clamp capPartition.integerEquiv (3/2)).box (n := 0) = ∅ := by
  have hl : (capRight.clamp capPartition.integerEquiv (3/2)).lower 0 = 2 := by
    norm_num [capRight,capRoot,capPartition,capIndex,BBExtendedNode.clamp,BBExtendedNode.right,
      BBExtendedNode.root,BBExtendedNode.clampLower]
    change max (-(3/2 : ℝ)) 2 = 2
    norm_num
  have hu : (capRight.clamp capPartition.integerEquiv (3/2)).upper 0 = 3/2 := rfl
  refine ⟨hl,hu,?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := hp 0
  rw [hl,hu] at h
  linarith [h.1,h.2]

theorem cap_endpoint : IsMinimizer (capData.feasible capIndices) capData.f (fun _ => 0) :=
  bb_external_reachable_correct capData capPartition (3/2) cap_source_premises.2.1
    cap_source_premises.1 cap_source_premises.2.2.1.continuous
    cap_source_premises.2.2.2.1.continuous.continuousOn ⟨3,cap_trace⟩ rfl

end Chapter02BBAdapterExamples




/- Transitive axiom inventory for every named control theorem. -/
#print axioms Chapter02BBAdapterExamples.split_coordinates
#print axioms Chapter02BBAdapterExamples.join_coordinates
#print axioms Chapter02BBAdapterExamples.polyhedron_iff
#print axioms Chapter02BBAdapterExamples.polyhedron_bounded
#print axioms Chapter02BBAdapterExamples.enclosing_bound
#print axioms Chapter02BBAdapterExamples.objective_c2
#print axioms Chapter02BBAdapterExamples.constraints_c2
#print axioms Chapter02BBAdapterExamples.shifted_square_convex
#print axioms Chapter02BBAdapterExamples.objective_convex
#print axioms Chapter02BBAdapterExamples.constraints_convex
#print axioms Chapter02BBAdapterExamples.fractional
#print axioms Chapter02BBAdapterExamples.root_member
#print axioms Chapter02BBAdapterExamples.root_minimum
#print axioms Chapter02BBAdapterExamples.left_holds_iff
#print axioms Chapter02BBAdapterExamples.right_holds_iff
#print axioms Chapter02BBAdapterExamples.left_member
#print axioms Chapter02BBAdapterExamples.right_member
#print axioms Chapter02BBAdapterExamples.left_minimum
#print axioms Chapter02BBAdapterExamples.right_minimum
#print axioms Chapter02BBAdapterExamples.left_integral
#print axioms Chapter02BBAdapterExamples.right_integral
#print axioms Chapter02BBAdapterExamples.step_root
#print axioms Chapter02BBAdapterExamples.step_inferior
#print axioms Chapter02BBAdapterExamples.step_best
#print axioms Chapter02BBAdapterExamples.inferior_first_trace
#print axioms Chapter02BBAdapterExamples.inferior_not_global
#print axioms Chapter02BBAdapterExamples.values_and_active_rows
#print axioms Chapter02BBAdapterExamples.explicit_root_rank_weight
#print axioms Chapter02BBAdapterExamples.final_global_optimal
#print axioms Chapter02BBAdapterExamples.trace_transports_to_engine
#print axioms Chapter02BBAdapterExamples.all_selectors_with_discharged_source_premises
#print axioms Chapter02BBAdapterExamples.tie_children
#print axioms Chapter02BBAdapterExamples.tie_step_root
#print axioms Chapter02BBAdapterExamples.tie_step_right
#print axioms Chapter02BBAdapterExamples.tie_step_left_replaces
#print axioms Chapter02BBAdapterExamples.tie_trace
#print axioms Chapter02BBAdapterExamples.tie_update_policy_difference
#print axioms Chapter02BBAdapterExamples.empty_indices_root_minimum
#print axioms Chapter02BBAdapterExamples.empty_indices_trace
#print axioms Chapter02BBAdapterExamples.empty_indices_endpoint
#print axioms Chapter02BBAdapterExamples.full_source_premises
#print axioms Chapter02BBAdapterExamples.full_indices_minimum
#print axioms Chapter02BBAdapterExamples.full_indices_trace
#print axioms Chapter02BBAdapterExamples.full_indices_endpoint
#print axioms Chapter02BBAdapterExamples.empty_polyhedron
#print axioms Chapter02BBAdapterExamples.empty_source_premises
#print axioms Chapter02BBAdapterExamples.empty_poly_root
#print axioms Chapter02BBAdapterExamples.empty_poly_trace
#print axioms Chapter02BBAdapterExamples.empty_poly_endpoint
#print axioms Chapter02BBAdapterExamples.no_incumbent_policy_transfer
#print axioms Chapter02BBAdapterExamples.strict_tie_engine_trace
#print axioms Chapter02BBAdapterExamples.tie_transport_and_distinct_outputs
#print axioms Chapter02BBAdapterExamples.cap_poly_iff
#print axioms Chapter02BBAdapterExamples.cap_source_premises
#print axioms Chapter02BBAdapterExamples.cap_root_minimum
#print axioms Chapter02BBAdapterExamples.cap_left_minimum
#print axioms Chapter02BBAdapterExamples.cap_right_empty
#print axioms Chapter02BBAdapterExamples.cap_branch_step
#print axioms Chapter02BBAdapterExamples.cap_trace
#print axioms Chapter02BBAdapterExamples.cap_outward_clamp_empty
#print axioms Chapter02BBAdapterExamples.cap_endpoint
