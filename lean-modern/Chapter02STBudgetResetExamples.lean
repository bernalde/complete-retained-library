module

public import Chapter02STBudget
public import Chapter02STSourceExamples
public import Mathlib.Tactic

@[expose] public section

/-! A genuine fixed-integer initialized budget-reset control. Four complete
processes spend both sibling allowances and then reset only the selected one.
Fractional objective tangents are retained, so their actual height floor is zero.
This replaces the planning trace's incompatible fractional-root initialization;
no assertion about a twelve-process adopted trace is made. -/
noncomputable section
open Chapter02 Chapter02STSourceExamples
namespace Chapter02STBudgetResetExamples

abbrev Tag := STBudgetNode c7I
abbrev State := STBudgetState c7I

def seed (a : ℝ × ℝ) : RealVector 3 := c7Point a.1 0 a.2

def state (S H : List (ℝ × ℝ)) (live : List Tag) : State :=
  ⟨S.map seed,H.map (fun a => c7Batch a.1 a.2),some (c7Point 1 (5/16) 1),live,none⟩

def lp (S : List (ℝ × ℝ)) (B : C7Node) : Set (RealVector 3 × ℝ) :=
  stSourceLP c7Data B (S.map seed ++ [(c7Batch 1 1).anchor]) (.gap (1/256)) (some (25/256))

theorem seed_rows (a : ℝ × ℝ) (q : RealVector 3) :
    stSourceRows c7Data (seed a) q ↔ c7Row a.1 a.2 q≤0 := by
  unfold stSourceRows
  simp_rw [(c7_row_derivative _ _).fderiv]
  simp only [Fin.forall_fin_one]
  simp [seed,c7Data,c7Point,c7Coord,c7Row]
  constructor <;> intro h <;> nlinarith

theorem seed_objective_tangent (a : ℝ × ℝ) (q : RealVector 3) :
    stTangent c7Data.f (seed a) q=0 := by
  rw [stTangent,(c7_objective_derivative _).fderiv]
  simp [seed,c7Data,c7Point]

theorem lp_iff (S : List (ℝ × ℝ)) (B : C7Node) (q : RealVector 3 × ℝ) :
    q∈lp S B ↔ (∀ i,0≤q.1 i ∧ q.1 i≤1) ∧ B.Holds (fun i => q.1 i) ∧
      (∀ a∈S,c7Row a.1 a.2 q.1≤0) ∧ c7Row 1 1 q.1≤0 ∧
      (∀ a∈S,(0:ℝ)≤q.2) ∧ (5/8)*q.1 1-25/256≤q.2 ∧ q.2≤24/256 := by
  rw [lp,st_source_lp_mem_iff,c7_polyhedron]
  constructor
  · rintro ⟨hX,hB,hr,ho,hc⟩
    refine ⟨hX,hB,?_,?_,?_,?_,?_⟩
    · intro a ha
      exact (seed_rows a q.1).mp (hr _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩))))
    · exact (c7_rows 1 1 q.1).mp (hr _ (by simp))
    · intro a ha
      simpa only [seed_objective_tangent] using
        ho _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩)))
    · simpa only [c7_objective_tangent] using ho (c7Batch 1 1).anchor (by simp)
    · norm_num [STSourcePolicy.Admits] at hc ⊢
      exact hc
  · rintro ⟨hX,hB,hs,hr,hos,ho,hc⟩
    refine ⟨hX,hB,?_,?_,?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
        exact (seed_rows b q.1).mpr (hs b hb)
      · rw [List.mem_singleton.mp ha]
        exact (c7_rows 1 1 q.1).mpr hr
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
        simpa only [seed_objective_tangent] using hos b hb
      · rw [List.mem_singleton.mp ha]
        simpa only [c7_objective_tangent] using ho
    · norm_num [STSourcePolicy.Admits]
      linarith

theorem left_minimum : IsMinimizer (lp [] c7Left) Prod.snd
    (c7Point 0 0 (1/2),-25/256) := by
  refine ⟨?_,?_⟩
  · rw [lp_iff,c7_node_holds]
    constructor
    · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
    · norm_num [c7Point,c7Left,c7Root,c7Y,c7Z,BBExtendedNode.left,BBExtendedNode.root,
        c7Row,Function.update,Fin.ext_iff]
  · intro q hq
    have hh := (lp_iff [] c7Left q).mp hq
    have ht := (hh.1 1).1
    dsimp
    linarith [hh.2.2.2.2.2.1]

theorem right_minimum : IsMinimizer (lp [(0,1/2)] c7Right) Prod.snd
    (c7Point 1 0 (1/2),0) := by
  refine ⟨?_,?_⟩
  · rw [lp_iff,c7_node_holds]
    constructor
    · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
    · norm_num [c7Point,c7Right,c7Root,c7Y,c7Z,BBExtendedNode.right,BBExtendedNode.root,
        c7Row,Function.update,Fin.ext_iff]
  · intro q hq
    exact ((lp_iff [(0,1/2)] c7Right q).mp hq).2.2.2.2.1 (0,1/2) (by simp)

theorem callback_minimum : IsMinimizer (lp [(0,1/2),(1,1/2)] c7Right) Prod.snd
    (c7Point 1 (1/16) 0,0) := by
  refine ⟨?_,?_⟩
  · rw [lp_iff,c7_node_holds]
    constructor
    · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
    · norm_num [c7Point,c7Right,c7Root,c7Y,c7Z,BBExtendedNode.right,BBExtendedNode.root,
        c7Row,Function.update,Fin.ext_iff]
  · intro q hq
    exact ((lp_iff [(0,1/2),(1,1/2)] c7Right q).mp hq).2.2.2.2.1 (0,1/2) (by simp)

def s0 : State := state [] [(1,1)] [⟨c7Root,1⟩]
def s1 : State := state [] [(1,1)] [⟨c7Left,1⟩,⟨c7Right,1⟩]
def s2 : State := state [(0,1/2)] [(1,1)] [⟨c7Left,0⟩,⟨c7Right,1⟩]
def s3 : State := state [(0,1/2),(1,1/2)] [(1,1)] [⟨c7Right,0⟩,⟨c7Left,0⟩]
def s4 : State := state [(0,1/2),(1,1/2)] [(1,1),(1,0)] [⟨c7Right,1⟩,⟨c7Left,0⟩]
def callbackWorking : State :=
  ⟨[seed (0,1/2),seed (1,1/2)],[c7Batch 1 1],some (c7Point 1 (5/16) 1),
    [⟨c7Left,0⟩],some ⟨c7Right,0⟩⟩

theorem initialization : STBudgetInitialize c7Data c7I (fun _ => 1) 1 (some s0) := by
  have hb := c7_batch_valid 1 1 (Or.inr rfl) (Or.inr rfl)
  have ha := st_source_batch_anchor_polyhedron c7Data c7I (fun _ => 1) (c7Batch 1 1) hb
  have hh := STBudgetInitialize.seeded (cap := 1) (c7Batch 1 1).anchor (c7Batch 1 1) ha hb.1 hb
    (fun _ => rfl)
  simpa [s0,state,stBudgetInitial,c7Root,stSourceBatchInc,c7Batch,stSourceBest] using hh

theorem root_branch : STBudgetProcess c7Data c7I (fun _ => 1) (.gap (1/256)) 1 s0 s1 := by
  refine ⟨_,STBudgetSelect.choose [] [c7Batch 1 1] (some (c7Point 1 (5/16) 1)) [] [] ⟨c7Root,1⟩,?_⟩
  have hf : BBFractional ((c7Point (1/2) 0 (1/2)) c7Y) := by
    change ¬∃k:ℤ,(k:ℝ)=(1/2:ℝ)
    rintro ⟨k,hk⟩
    have hl : (0:ℤ)<k := by exact_mod_cast (show (0:ℝ)<(k:ℝ) by linarith)
    have hu : k<(1:ℤ) := by exact_mod_cast (show (k:ℝ)<(1:ℝ) by linarith)
    omega
  exact STBudgetResolve.branch (seeds := []) (H := [c7Batch 1 1])
    (inc := some (c7Point 1 (5/16) 1)) (live := []) (B := ⟨c7Root,1⟩)
    c7Y c7_min_root hf

theorem left_cut : STBudgetProcess c7Data c7I (fun _ => 1) (.gap (1/256)) 1 s1 s2 := by
  refine ⟨_,STBudgetSelect.choose [] [c7Batch 1 1] (some (c7Point 1 (5/16) 1)) []
    [⟨c7Right,1⟩] ⟨c7Left,1⟩,?_⟩
  have hf : BBFractional ((c7Point 0 0 (1/2)) c7Z) := by
    change ¬∃k:ℤ,(k:ℝ)=(1/2:ℝ)
    rintro ⟨k,hk⟩
    have hl : (0:ℤ)<k := by exact_mod_cast (show (0:ℝ)<(k:ℝ) by linarith)
    have hu : k<(1:ℤ) := by exact_mod_cast (show (k:ℝ)<(1:ℝ) by linarith)
    omega
  apply STBudgetResolve.cut (seeds := []) (H := [c7Batch 1 1])
    (inc := some (c7Point 1 (5/16) 1)) (live := [⟨c7Right,1⟩]) (B := ⟨c7Left,1⟩)
    (q := (c7Point 0 0 (1/2),-25/256)) c7Z _ hf (by norm_num)
  simpa [lp,show c7Data.f (c7Point 1 (5/16) 1)=(25/256:ℝ) from by norm_num [c7Data,c7Point]] using left_minimum

theorem right_cut : STBudgetProcess c7Data c7I (fun _ => 1) (.gap (1/256)) 1 s2 s3 := by
  refine ⟨_,STBudgetSelect.choose [seed (0,1/2)] [c7Batch 1 1] (some (c7Point 1 (5/16) 1))
    [⟨c7Left,0⟩] [] ⟨c7Right,1⟩,?_⟩
  have hf : BBFractional ((c7Point 1 0 (1/2)) c7Z) := by
    change ¬∃k:ℤ,(k:ℝ)=(1/2:ℝ)
    rintro ⟨k,hk⟩
    have hl : (0:ℤ)<k := by exact_mod_cast (show (0:ℝ)<(k:ℝ) by linarith)
    have hu : k<(1:ℤ) := by exact_mod_cast (show (k:ℝ)<(1:ℝ) by linarith)
    omega
  apply STBudgetResolve.cut (seeds := [seed (0,1/2)]) (H := [c7Batch 1 1])
    (inc := some (c7Point 1 (5/16) 1)) (live := [⟨c7Left,0⟩]) (B := ⟨c7Right,1⟩)
    (q := (c7Point 1 0 (1/2),0)) c7Z _ hf (by norm_num)
  simpa [lp,show c7Data.f (c7Point 1 (5/16) 1)=(25/256:ℝ) from by norm_num [c7Data,c7Point]] using right_minimum

theorem callback_selection : STBudgetSelect s3 callbackWorking :=
  .choose _ _ _ [] [⟨c7Left,0⟩] ⟨c7Right,0⟩

theorem callback_resolution : STBudgetResolve c7Data c7I (fun _ => 1) (.gap (1/256)) 1
    callbackWorking s4 := by
  have hm : IsMinimizer (stSourceLP c7Data c7Right
      ([seed (0,1/2),seed (1,1/2)] ++ [c7Batch 1 1].map STSourceBatch.anchor)
      (.gap (1/256)) ((some (c7Point 1 (5/16) 1)).map c7Data.f)) Prod.snd
      (c7Point 1 (1/16) 0,0) := by
    simpa [lp,show c7Data.f (c7Point 1 (5/16) 1)=(25/256:ℝ) from by norm_num [c7Data,c7Point]] using callback_minimum
  have hh := STBudgetResolve.callback (cap := 1) (B := ⟨c7Right,0⟩) (live := [⟨c7Left,0⟩])
    (seeds := [seed (0,1/2),seed (1,1/2)]) (H := [c7Batch 1 1])
    (inc := some (c7Point 1 (5/16) 1)) hm
    (c7_integral 1 0 (Or.inr rfl) (Or.inl rfl) (1/16))
    (c7_batch_valid 1 0 (Or.inr rfl) (Or.inl rfl)) (c7_same_fiber 1 0 (1/16))
  simpa [callbackWorking,s4,state,stSourceBatchInc,c7Batch,stSourceBest,c7Data,c7Point] using hh

theorem four_process_trace : STBudgetTrace c7Data c7I (fun _ => 1) (.gap (1/256)) 1 4 s0 s4 :=
  .cons root_branch (.cons left_cut (.cons right_cut
    (.cons ⟨callbackWorking,callback_selection,callback_resolution⟩ (.nil _))))

theorem eight_microsteps : STBudgetMicroTrace c7Data c7I (fun _ => 1) (.gap (1/256)) 1 8 s0 s4 :=
  st_budget_trace_micro c7Data (fun _ => 1) (.gap (1/256)) 1 four_process_trace

theorem actual_reset_only_working : callbackWorking.working=some ⟨c7Right,0⟩ ∧
    callbackWorking.live=[⟨c7Left,0⟩] ∧ s4.live=[⟨c7Right,1⟩,⟨c7Left,0⟩] ∧
    s4.history=callbackWorking.history++[c7Batch 1 0] ∧ s4.seeds=callbackWorking.seeds := by
  simp [callbackWorking,s4,state]

def globalResetTarget : State :=
  state [(0,1/2),(1,1/2)] [(1,1),(1,0)] [⟨c7Right,1⟩,⟨c7Left,1⟩]

theorem global_reset_differs : globalResetTarget≠s4 := by
  intro h
  have hh := congrArg (fun s : State => (s.live.map STBudgetNode.allowance)) h
  norm_num [globalResetTarget,s4,state] at hh

theorem waiting_occurrence_retained {s t : State}
    (h : STBudgetResolve c7Data c7I (fun _ => 1) (.gap (1/256)) 1 s t)
    (B : Tag) (hB : B∈s.live) : B∈t.live := by
  cases h <;> simp_all

theorem global_reset_not_legal : ¬ STBudgetResolve c7Data c7I (fun _ => 1) (.gap (1/256)) 1
    callbackWorking globalResetTarget := by
  intro h
  have hh := waiting_occurrence_retained h ⟨c7Left,0⟩ (by simp [callbackWorking])
  have hm : 0∈globalResetTarget.live.map STBudgetNode.allowance :=
    List.mem_map.mpr ⟨⟨c7Left,0⟩,hh,rfl⟩
  norm_num [globalResetTarget,state] at hm


theorem left_cut_removes_trial : (c7Point 0 0 (1/2),-25/256)∉lp [(0,1/2)] c7Left := by
  intro h
  have hh := ((lp_iff _ _ _).mp h).2.2.1 (0,1/2) (by simp)
  norm_num [c7Row,c7Point] at hh

theorem right_cut_removes_trial : (c7Point 1 0 (1/2),0)∉lp [(0,1/2),(1,1/2)] c7Right := by
  intro h
  have hh := ((lp_iff _ _ _).mp h).2.2.1 (1,1/2) (by simp)
  norm_num [c7Row,c7Point] at hh

theorem callback_fiber_unseen : ∀ b∈callbackWorking.history,
    b.anchor c7Z≠(c7Batch 1 0).anchor c7Z := by
  intro b hb
  have he : b=c7Batch 1 1 := by simpa [callbackWorking] using hb
  rw [he]
  norm_num [c7Batch,c7Point,c7Z,Fin.ext_iff]

theorem prefix_invariant : STBudgetInvariant c7Data c7I (fun _ => 1) (.gap (1/256)) 1 s4 := by
  have hi := (st_budget_initialization_invariant c7Data (fun _ => 1) (.gap (1/256)) 1 initialization).1
  exact st_budget_trace_invariant c7Data (fun _ => 1) (.gap (1/256)) 1
    c7_convex.1 (c7_C2.1.differentiable (by norm_num)) c7_convex.2
    (fun j => ((contDiff_apply ℝ (fun _ => ℝ) j).comp c7_C2.2).differentiable (by norm_num)) hi four_process_trace

theorem every_continuation_returns (choose : STBudgetSelector c7Data c7I (fun _ => 1) (.gap (1/256)) 1) :
    ∃ s out steps, stBudgetRun c7Data c7I (fun _ => 1) (.gap (1/256)) 1 choose s4 steps =
      .stopped s out ∧ STSourceReturnCertificate c7Data c7I (.gap (1/256)) out := by
  have hdf : Differentiable ℝ c7Data.f := c7_C2.1.differentiable (by norm_num)
  have hdiff : ∀j,Differentiable ℝ (fun z => c7Data.c z j) :=
    fun j => ((contDiff_apply ℝ (fun _ => ℝ) j).comp c7_C2.2).differentiable (by norm_num)
  have hp : STSourcePolicy.gap (1/256) = .strict ∨
      ∃ epsilon,STSourcePolicy.gap (1/256) = .gap epsilon ∧ 0<epsilon :=
    Or.inr ⟨1/256,rfl,by norm_num⟩
  obtain ⟨s,out,he⟩ := st_budget_every_selector_finite_return c7Data (fun _ => 1) (.gap (1/256)) 1
    c7P 1 c7_enclosing (by intro; norm_num) hp c7_convex.1 hdf c7_convex.2 hdiff c7_fiber_CQ
    choose s4 prefix_invariant
  have hh := st_budget_run_invariant c7Data (fun _ => 1) (.gap (1/256)) 1
    c7_convex.1 hdf c7_convex.2 hdiff choose s4 prefix_invariant
    (stBudgetPhasePotential c7P 1 1 s4+1)
  rw [he] at hh
  obtain ⟨k,hk,ht,hs,hstop⟩ := hh
  exact ⟨s,out,_,he,st_budget_stop_sound c7Data (fun _ => 1) (.gap (1/256)) 1 hs hstop⟩

theorem full_model_initialized_reset : Bornology.IsBounded c7Data.polyhedron ∧
    ContDiff ℝ 2 c7Data.f ∧ ContDiff ℝ 2 c7Data.c ∧ ConvexOn ℝ Set.univ c7Data.f ∧
    (∀ j,ConvexOn ℝ Set.univ (fun z => c7Data.c z j)) ∧ STSourceFiberSlater c7Data c7I ∧
    STBudgetInitialize c7Data c7I (fun _ => 1) 1 (some s0) ∧
    STBudgetTrace c7Data c7I (fun _ => 1) (.gap (1/256)) 1 4 s0 s4 ∧
    callbackWorking.working=some ⟨c7Right,0⟩ ∧ callbackWorking.live=[⟨c7Left,0⟩] ∧
    s4.live=[⟨c7Right,1⟩,⟨c7Left,0⟩] :=
  ⟨c7_bounded,c7_C2.1,c7_C2.2,c7_convex.1,c7_convex.2,c7_fiber_CQ,
    initialization,four_process_trace,actual_reset_only_working.1,
    actual_reset_only_working.2.1,actual_reset_only_working.2.2.1⟩

end Chapter02STBudgetResetExamples

#print axioms Chapter02STBudgetResetExamples.seed_rows
#print axioms Chapter02STBudgetResetExamples.seed_objective_tangent
#print axioms Chapter02STBudgetResetExamples.lp_iff
#print axioms Chapter02STBudgetResetExamples.left_minimum
#print axioms Chapter02STBudgetResetExamples.right_minimum
#print axioms Chapter02STBudgetResetExamples.callback_minimum
#print axioms Chapter02STBudgetResetExamples.initialization
#print axioms Chapter02STBudgetResetExamples.root_branch
#print axioms Chapter02STBudgetResetExamples.left_cut
#print axioms Chapter02STBudgetResetExamples.right_cut
#print axioms Chapter02STBudgetResetExamples.callback_selection
#print axioms Chapter02STBudgetResetExamples.callback_resolution
#print axioms Chapter02STBudgetResetExamples.four_process_trace
#print axioms Chapter02STBudgetResetExamples.eight_microsteps
#print axioms Chapter02STBudgetResetExamples.actual_reset_only_working
#print axioms Chapter02STBudgetResetExamples.global_reset_differs
#print axioms Chapter02STBudgetResetExamples.waiting_occurrence_retained
#print axioms Chapter02STBudgetResetExamples.global_reset_not_legal
#print axioms Chapter02STBudgetResetExamples.left_cut_removes_trial
#print axioms Chapter02STBudgetResetExamples.right_cut_removes_trial
#print axioms Chapter02STBudgetResetExamples.callback_fiber_unseen
#print axioms Chapter02STBudgetResetExamples.prefix_invariant
#print axioms Chapter02STBudgetResetExamples.every_continuation_returns
#print axioms Chapter02STBudgetResetExamples.full_model_initialized_reset
