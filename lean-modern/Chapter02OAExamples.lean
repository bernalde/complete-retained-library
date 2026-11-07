module

public import Chapter02KKTSelectionExamples
public import Chapter02MultiplierEdgeExamples
public import Chapter02OAState
public import Chapter02OADriver

@[expose] public section

/-! Exact source-model controls for the S007 retained-history OA procedure.
Candidate examples: source status and independent acceptance are recorded
outside this module. No numerical solver behavior is asserted. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02Examples
namespace Chapter02OAExamples

def pt (x y : ℝ) : Point 1 1 := (fun _ => x, fun _ => y)
def coordY : Point 1 1 →L[ℝ] ℝ := Chapter02KKTExamples.coordY

def traceModel : ModelData 1 1 1 2 where
  g := fun _ p => (p.1 0)^2 + 1 - 2*p.2 0
  A := fun row _ => if row = 0 then 1 else -1
  B := fun _ _ => 0
  rhs := fun _ => 2
  c1 := fun _ => 0
  c2 := fun _ => 1
  lo := fun _ => 0
  hi := fun _ => 1

theorem trace_objective (p : Point 1 1) : traceModel.objective p = p.2 0 := by
  simp [traceModel, ModelData.objective, LinearForm, Fin.sum_univ_one]

theorem trace_linear_iff (p : Point 1 1) :
    p ∈ traceModel.linearRegion ↔ -2 ≤ p.1 0 ∧ p.1 0 ≤ 2 := by
  simp [ModelData.linearRegion, traceModel, LinearForm, Fin.forall_fin_succ, Fin.sum_univ_one]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem trace_base_compact :
    IsCompact (traceModel.linearRegion ∩ IntegerCylinder (n := 1) traceModel.lo traceModel.hi) :=
  Chapter02KKTSelectionExamples.selection_base_compact

theorem trace_convex : ∀ j, ConvexOn ℝ Set.univ (traceModel.g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t hs ht hst
  have hx : 0 ≤ s*t*(p.1 0-q.1 0)^2 :=
    mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
  simp [traceModel, smul_eq_mul]
  nlinarith [sq_nonneg (p.1 0-q.1 0)]

theorem trace_smooth : ∀ j, ContDiff ℝ 1 (traceModel.g j) := by
  intro j
  exact ((((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).add
    contDiff_const).sub (contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd))

theorem trace_diff : ∀ j, Differentiable ℝ (traceModel.g j) :=
  fun j => (trace_smooth j).differentiable (by norm_num)

theorem trace_anchor_derivative (y : ℝ) (j : Fin 1) :
    HasFDerivAt (traceModel.g j) ((-2 : ℝ) • coordY) (pt 0 y) := by
  have h := (((hasDerivAt_pow 2 (0 : ℝ)).comp_hasFDerivAt (pt 0 y)
    coordX.hasFDerivAt).add_const 1).sub (coordY.hasFDerivAt.const_mul 2)
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_zero, zero_smul, zero_sub] at h
  convert h using 1 <;>
  ext p <;>
    simp [traceModel, coordX, coordY, Chapter02KKTExamples.coordY, Function.comp_def, neg_smul]

theorem trace_bad_fiber : ¬ (traceModel.fixedNonlinearFiber (pt 0 0).2).Nonempty := by
  rintro ⟨p, hp⟩
  have hy : p.2 0 = 0 := by simpa [pt] using congrFun hp.1.2 0
  have hg := hp.2 (0 : Fin 1)
  change (p.1 0)^2 + 1 - 2*p.2 0 ≤ 0 at hg
  rw [hy] at hg
  nlinarith [sq_nonneg (p.1 0)]

theorem trace_restoration_minimum :
    IsMinimizer (RestorationPairs (traceModel.fixedLinearFiber (pt 0 0).2) traceModel.g)
      Prod.snd (pt 0 0, 1) := by
  refine ⟨⟨⟨(trace_linear_iff _).mpr (by norm_num [pt]), rfl⟩,
    fun _ => by norm_num [traceModel, pt]⟩, ?_⟩
  intro q hq
  have hy : q.1.2 0 = 0 := by simpa [pt] using congrFun hq.1.2 0
  have hg := hq.2 (0 : Fin 1)
  change (q.1.1 0)^2 + 1 - 2*q.1.2 0 ≤ q.2 at hg
  rw [hy] at hg
  change 1 ≤ q.2
  nlinarith [sq_nonneg (q.1.1 0)]

theorem trace_fixed_minimum :
    IsMinimizer (traceModel.fixedNonlinearFiber (pt 0 1).2) traceModel.objective (pt 0 1) := by
  refine ⟨⟨⟨(trace_linear_iff _).mpr (by norm_num [pt]), rfl⟩,
    fun _ => by norm_num [traceModel, pt]⟩, ?_⟩
  intro q hq
  have hy := congrFun hq.1.2 0
  simpa [trace_objective, pt] using le_of_eq hy.symm

theorem trace_fiber_slater :
    ∀ y ∈ IntegerBox traceModel.lo traceModel.hi,
      (traceModel.fixedNonlinearFiber (fun i => (y i : ℝ))).Nonempty →
      ∃ z ∈ traceModel.fixedLinearFiber (fun i => (y i : ℝ)), ∀ j, traceModel.g j z < 0 := by
  intro y hy ⟨p, hp⟩
  have hpy : p.2 0 = (y 0 : ℝ) := congrFun hp.1.2 0
  have hg := hp.2 (0 : Fin 1)
  change (p.1 0)^2 + 1 - 2*p.2 0 ≤ 0 at hg
  rw [hpy] at hg
  have hypos : (0 : ℝ) < (y 0 : ℝ) := by nlinarith [sq_nonneg (p.1 0)]
  have hyint : (0 : ℤ) < y 0 := by exact_mod_cast hypos
  have hyone : (1 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hyint
  refine ⟨(0, fun i => (y i : ℝ)), ⟨(trace_linear_iff _).mpr (by norm_num), rfl⟩, ?_⟩
  intro j
  change 0^2 + 1 - 2*(y 0 : ℝ) < 0
  nlinarith

def traceBad : OABatch 1 1 := ⟨fun _ => 0, pt 0 0, some 1⟩
def traceGood : OABatch 1 1 := ⟨fun _ => 1, pt 0 1, none⟩

theorem trace_bad_valid : oaBatchValid traceModel traceBad := by
  refine ⟨?_, by ext i; norm_num [traceBad, Chapter02.oaIntCast, pt], ?_⟩
  · intro i
    norm_num [traceModel, traceBad]
  · change ¬ (traceModel.fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => 0))).Nonempty ∧
      IsMinimizer (RestorationPairs (traceModel.fixedLinearFiber (Chapter02.oaIntCast (fun _ => 0))) traceModel.g)
        Prod.snd (pt 0 0, 1)
    have hc : Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)) = (pt 0 0).2 := by
      ext i
      norm_num [Chapter02.oaIntCast, pt]
    rw [hc]
    exact ⟨trace_bad_fiber, trace_restoration_minimum⟩

theorem trace_good_valid : oaBatchValid traceModel traceGood := by
  refine ⟨?_, by ext i; norm_num [traceGood, Chapter02.oaIntCast, pt], ?_⟩
  · intro i
    norm_num [traceModel, traceGood]
  · change IsMinimizer (traceModel.fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => 1)))
      traceModel.objective (pt 0 1)
    have hc : Chapter02.oaIntCast (fun _ : Fin 1 => (1 : ℤ)) = (pt 0 1).2 := by
      ext i
      norm_num [Chapter02.oaIntCast, pt]
    rw [hc]
    exact trace_fixed_minimum

theorem trace_bad_cuts (q : Point 1 1) :
    oaBatchCuts traceModel traceBad q ↔ 1 - 2*q.2 0 ≤ 0 := by
  have hd : oaBatchDerivative traceModel traceBad = fun _ => (-2 : ℝ) • coordY := by
    funext j
    exact (trace_anchor_derivative 0 j).fderiv
  unfold oaBatchCuts SelectedOARows tangentRow
  rw [hd]
  simp [oaBatchRows, traceBad,
    traceModel, pt, coordY, Chapter02KKTExamples.coordY]

theorem trace_good_cuts (q : Point 1 1) :
    oaBatchCuts traceModel traceGood q ↔ 1 - 2*q.2 0 ≤ 0 := by
  have hd : oaBatchDerivative traceModel traceGood = fun _ => (-2 : ℝ) • coordY := by
    funext j
    exact (trace_anchor_derivative 1 j).fderiv
  unfold oaBatchCuts SelectedOARows tangentRow
  rw [hd]
  simp only [oaBatchRows, traceGood,
    Set.mem_univ, forall_true_left]
  simp [traceModel, pt, coordY, Chapter02KKTExamples.coordY]
  constructor <;> intro h <;> linarith

theorem trace_cylinder (x : ℝ) (y : ℤ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    pt x (y : ℝ) ∈ IntegerCylinder (n := 1) traceModel.lo traceModel.hi := by
  refine ⟨fun _ => y, ?_, rfl⟩
  intro i
  constructor
  · change (0 : ℝ) ≤ (y : ℝ)
    exact_mod_cast h0
  · change (y : ℝ) ≤ 1
    exact_mod_cast h1

theorem trace_initial_master :
    IsMinimizer (oaMaster traceModel []) traceModel.objective (pt 2 0) := by
  refine ⟨(oa_master_mem_iff _ _ _).mpr ⟨(trace_linear_iff _).mpr (by norm_num [pt]),
    by simpa [traceModel] using trace_cylinder 2 0 (by norm_num) (by norm_num), by simp⟩, ?_⟩
  intro q hq
  obtain ⟨y,hy,hqy⟩ := ((oa_master_mem_iff _ _ _).mp hq).2.1
  have h0 := (hy 0).1
  rw [trace_objective, trace_objective]
  change 0 ≤ q.2 0
  rw [hqy]
  exact h0

theorem trace_later_master (H : List (OABatch 1 1))
    (hbad : traceBad ∈ H) (hrows : ∀ b ∈ H, b = traceBad ∨ b = traceGood) :
    IsMinimizer (oaMaster traceModel H) traceModel.objective (pt 2 1) := by
  refine ⟨(oa_master_mem_iff _ _ _).mpr ⟨(trace_linear_iff _).mpr (by norm_num [pt]),
    by simpa using trace_cylinder 2 1 (by norm_num) (by norm_num), ?_⟩, ?_⟩
  · intro b hb
    rcases hrows b hb with rfl | rfl
    · exact (trace_bad_cuts _).mpr (by norm_num [pt])
    · exact (trace_good_cuts _).mpr (by norm_num [pt])
  · intro q hq
    have hm := (oa_master_mem_iff _ _ _).mp hq
    have hc := (trace_bad_cuts q).mp (hm.2.2 traceBad hbad)
    obtain ⟨y,hy,hqy⟩ := hm.2.1
    have hval : q.2 0 = (y 0 : ℝ) := congrFun hqy 0
    have hpos : (0 : ℝ) < (y 0 : ℝ) := by rw [hval] at hc; linarith
    have hint : (0 : ℤ) < y 0 := by exact_mod_cast hpos
    have hone : (1 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hint
    simpa [trace_objective, pt, hval] using hone

def traceS0 : OAState 1 1 := oaInit none
def traceS1 : OAState 1 1 := oaAppend traceModel traceS0 traceBad
def traceS2 : OAState 1 1 := oaAppend traceModel traceS1 traceGood

theorem trace_first_continue : OAContinue traceModel 0 traceS0 traceS1 := by
  exact OAContinue.step trace_initial_master (by simp [oaCompetitive, traceS0, oaInit])
    trace_bad_valid (by ext i; norm_num [pt, Chapter02.oaIntCast, traceBad])

theorem trace_second_continue : OAContinue traceModel 0 traceS1 traceS2 := by
  apply OAContinue.step (q := pt 2 1)
  · exact trace_later_master [traceBad] (by simp) (by simp)
  · simp [oaCompetitive, traceS1, traceS0, oaAppend, oaInit, traceBad]
  · exact trace_good_valid
  · ext i
    norm_num [pt, Chapter02.oaIntCast, traceGood]

theorem trace_final_stop : OAStop traceModel 0 traceS2 (.solution (pt 0 1)) := by
  apply OAStop.gap (q := pt 2 1)
  · exact trace_later_master [traceBad,traceGood] (by simp) (by simp)
  · rfl
  · norm_num [trace_objective, pt]

theorem trace_master_choices_infeasible :
    pt 2 0 ∉ traceModel.feasibleOn Set.univ ∧ pt 2 1 ∉ traceModel.feasibleOn Set.univ := by
  constructor <;> intro h
  all_goals
    have hg := ((source_feasible_iff traceModel Set.univ _).mp h).2.1 (0 : Fin 1)
    norm_num [traceModel, pt] at hg

theorem two_branch_trace :
    IsCompact (traceModel.linearRegion ∩ IntegerCylinder (n := 1) traceModel.lo traceModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (traceModel.g j)) ∧
    (∀ j, Differentiable ℝ (traceModel.g j)) ∧ OAFiberSlater traceModel ∧
    OAInvariant traceModel traceS0 ∧
    OAContinue traceModel 0 traceS0 traceS1 ∧ OAContinue traceModel 0 traceS1 traceS2 ∧
    OAStop traceModel 0 traceS2 (.solution (pt 0 1)) ∧
    traceS2.history.length = 2 ∧
    pt 2 0 ∉ traceModel.feasibleOn Set.univ ∧ pt 2 1 ∉ traceModel.feasibleOn Set.univ := by
  exact ⟨trace_base_compact, trace_convex, trace_diff, trace_fiber_slater,
    oa_init_invariant traceModel none (by simp), trace_first_continue,
    trace_second_continue, trace_final_stop, rfl, trace_master_choices_infeasible⟩

#print axioms two_branch_trace

/-! A second complete model exercises warm and cold positive-tolerance
returns. Its two fibers have different true optima. -/
def toleranceModel : ModelData 1 1 1 2 :=
  { traceModel with
    g := fun _ p => (p.1 0 + 2*p.2 0)^2 - 1
    c1 := fun _ => 1
    c2 := fun _ => 0 }

theorem tolerance_objective (p : Point 1 1) : toleranceModel.objective p = p.1 0 := by
  simp [toleranceModel, ModelData.objective, LinearForm, Fin.sum_univ_one]

theorem tolerance_linear_iff (p : Point 1 1) :
    p ∈ toleranceModel.linearRegion ↔ -2 ≤ p.1 0 ∧ p.1 0 ≤ 2 := trace_linear_iff p

theorem tolerance_convex : ∀ j, ConvexOn ℝ Set.univ (toleranceModel.g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t hs ht hst
  have hx : 0 ≤ s*t*((p.1 0+2*p.2 0)-(q.1 0+2*q.2 0))^2 :=
    mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
  simp [toleranceModel, smul_eq_mul]
  nlinarith

theorem tolerance_smooth : ∀ j, ContDiff ℝ 1 (toleranceModel.g j) := by
  intro j
  change ContDiff ℝ 1 (fun p : Point 1 1 => (p.1 0+2*p.2 0)^2-1)
  fun_prop

theorem tolerance_diff : ∀ j, Differentiable ℝ (toleranceModel.g j) :=
  fun j => (tolerance_smooth j).differentiable (by norm_num)

theorem tolerance_slater : OAFiberSlater toleranceModel := by
  intro y hy _
  let z : Point 1 1 := (fun _ => -2*(y 0 : ℝ), Chapter02.oaIntCast y)
  have hy0 := hy 0
  change 0 ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 1 at hy0
  refine ⟨z, ⟨(tolerance_linear_iff _).mpr ?_, rfl⟩, ?_⟩
  · change -2 ≤ -2*(y 0 : ℝ) ∧ -2*(y 0 : ℝ) ≤ 2
    constructor <;> linarith [hy0.1, hy0.2]
  · intro j
    change (-2*(y 0 : ℝ)+2*(y 0 : ℝ))^2-1<0
    ring_nf
    norm_num

theorem tolerance_feasible (x : ℝ) (y : ℤ) (hx : -2 ≤ x ∧ x ≤ 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hg : (x+2*(y:ℝ))^2-1≤0) :
    pt x (y : ℝ) ∈ toleranceModel.feasibleOn Set.univ := by
  apply (source_feasible_iff _ _ _).mpr
  exact ⟨Set.mem_univ _, fun _ => hg, (tolerance_linear_iff _).mpr hx,
    trace_cylinder x y hy0 hy1⟩

theorem tolerance_initial_master :
    IsMinimizer (oaMaster toleranceModel []) toleranceModel.objective (pt (-2) 0) := by
  refine ⟨(oa_master_mem_iff _ _ _).mpr ⟨(tolerance_linear_iff _).mpr (by norm_num [pt]),
    by simpa [traceModel,toleranceModel] using trace_cylinder (-2) 0 (by norm_num) (by norm_num), by simp⟩, ?_⟩
  intro q hq
  have hx := ((tolerance_linear_iff q).mp ((oa_master_mem_iff _ _ _).mp hq).1).1
  simpa only [tolerance_objective, pt] using hx

theorem tolerance_fixed_minimum :
    IsMinimizer (toleranceModel.fixedNonlinearFiber (pt (-1) 0).2)
      toleranceModel.objective (pt (-1) 0) := by
  refine ⟨⟨⟨(tolerance_linear_iff _).mpr (by norm_num [pt]), rfl⟩,
    fun _ => by norm_num [toleranceModel, pt]⟩, ?_⟩
  intro q hq
  have hy : q.2 0 = 0 := by simpa [pt] using congrFun hq.1.2 0
  have hg := hq.2 (0 : Fin 1)
  change (q.1 0+2*q.2 0)^2-1≤0 at hg
  rw [hy] at hg
  simp only [tolerance_objective, pt]
  nlinarith [sq_nonneg (q.1 0 + 1)]

def sumCoord : Point 1 1 →L[ℝ] ℝ := coordX + (2:ℝ) • coordY

theorem tolerance_anchor_derivative (j : Fin 1) :
    HasFDerivAt (toleranceModel.g j) ((-2 : ℝ) • sumCoord) (pt (-1) 0) := by
  have h := ((hasDerivAt_pow 2 (sumCoord (pt (-1) 0))).comp_hasFDerivAt (pt (-1) 0)
    sumCoord.hasFDerivAt).sub_const 1
  convert h using 1 <;>
  ext p <;>
    simp [toleranceModel, sumCoord, coordX, coordY, Chapter02KKTExamples.coordY, pt,
      Function.comp_def, neg_smul]

def toleranceBatch : OABatch 1 1 := ⟨fun _ => 0, pt (-1) 0, none⟩

theorem tolerance_batch_valid : oaBatchValid toleranceModel toleranceBatch := by
  refine ⟨?_, by ext i; norm_num [toleranceBatch, Chapter02.oaIntCast, pt], ?_⟩
  · intro i
    norm_num [toleranceModel, traceModel, toleranceBatch]
  · change IsMinimizer (toleranceModel.fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => 0)))
      toleranceModel.objective (pt (-1) 0)
    have hc : Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)) = (pt (-1) 0).2 := by
      ext i
      norm_num [Chapter02.oaIntCast, pt]
    rw [hc]
    exact tolerance_fixed_minimum

theorem tolerance_batch_cuts (q : Point 1 1) :
    oaBatchCuts toleranceModel toleranceBatch q ↔ -2*q.1 0-4*q.2 0-2≤0 := by
  have hd : oaBatchDerivative toleranceModel toleranceBatch = fun _ => (-2 : ℝ) • sumCoord := by
    funext j
    exact (tolerance_anchor_derivative j).fderiv
  unfold oaBatchCuts SelectedOARows tangentRow
  rw [hd]
  simp [oaBatchRows, toleranceBatch, toleranceModel, sumCoord, pt, coordX, coordY,
    Chapter02KKTExamples.coordY]
  constructor <;> intro h <;> linarith

theorem tolerance_later_master :
    IsMinimizer (oaMaster toleranceModel [toleranceBatch]) toleranceModel.objective (pt (-2) 1) := by
  refine ⟨(oa_master_mem_iff _ _ _).mpr ⟨(tolerance_linear_iff _).mpr (by norm_num [pt]),
    by simpa [traceModel,toleranceModel] using trace_cylinder (-2) 1 (by norm_num) (by norm_num), ?_⟩, ?_⟩
  · intro b hb
    have hbe : b = toleranceBatch := by simpa using hb
    subst b
    exact (tolerance_batch_cuts _).mpr (by norm_num [pt])
  · intro q hq
    have hx := ((tolerance_linear_iff q).mp ((oa_master_mem_iff _ _ _).mp hq).1).1
    simpa only [tolerance_objective, pt] using hx

def toleranceWarm : OAState 1 1 := oaInit (some (pt 1 0))
def toleranceCold1 : OAState 1 1 := oaAppend toleranceModel (oaInit none) toleranceBatch

theorem warm_tolerance_nonoptimal_return :
    OAInvariant toleranceModel toleranceWarm ∧
    OAStop toleranceModel 3 toleranceWarm (.solution (pt 1 0)) ∧
    ¬ IsMinimizer (toleranceModel.feasibleOn Set.univ) toleranceModel.objective (pt 1 0) := by
  have hu : pt 1 0 ∈ toleranceModel.feasibleOn Set.univ := by
    simpa using tolerance_feasible 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hv : pt (-2) 1 ∈ toleranceModel.feasibleOn Set.univ := by
    simpa using tolerance_feasible (-2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨oa_init_invariant _ _ ?_, OAStop.gap tolerance_initial_master rfl ?_, ?_⟩
  · intro u he
    cases Option.some.inj he
    exact hu
  · norm_num [tolerance_objective, pt]
  · intro hm
    have hn := hm.2 _ hv
    norm_num [tolerance_objective, pt] at hn

theorem cold_tolerance_nonoptimal_return :
    OAContinue toleranceModel 1 (oaInit none) toleranceCold1 ∧
    OAStop toleranceModel 1 toleranceCold1 (.solution (pt (-1) 0)) ∧
    ¬ IsMinimizer (toleranceModel.feasibleOn Set.univ) toleranceModel.objective (pt (-1) 0) := by
  refine ⟨OAContinue.step tolerance_initial_master (by simp [oaCompetitive, oaInit])
    tolerance_batch_valid (by ext i; norm_num [pt, toleranceBatch, Chapter02.oaIntCast]),
    OAStop.gap tolerance_later_master rfl ?_, ?_⟩
  · norm_num [tolerance_objective, pt]
  · intro hm
    have hv : pt (-2) 1 ∈ toleranceModel.feasibleOn Set.univ := by
      simpa using tolerance_feasible (-2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hn := hm.2 _ hv
    norm_num [tolerance_objective, pt] at hn

theorem tolerance_controls_assumptions :
    IsCompact (toleranceModel.linearRegion ∩ IntegerCylinder (n := 1)
      toleranceModel.lo toleranceModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (toleranceModel.g j)) ∧
    (∀ j, Differentiable ℝ (toleranceModel.g j)) ∧ OAFiberSlater toleranceModel :=
  ⟨trace_base_compact, tolerance_convex, tolerance_diff, tolerance_slater⟩

#print axioms warm_tolerance_nonoptimal_return
#print axioms cold_tolerance_nonoptimal_return
#print axioms tolerance_controls_assumptions

/-! The accepted missing-CQ source model now drives an actual unbounded
sequence of raw exact OA steps. No derivative or progress premise is supplied. -/
abbrev cqModel := Chapter02KKTExamples.zeroMarginModel
def cqBatch : OABatch 1 1 := ⟨fun _ => 0, pt 0 0, none⟩

theorem cq_objective (p : Point 1 1) : cqModel.objective p = p.1 0 := by
  simp [ModelData.objective, cqModel, Chapter02KKTExamples.zeroMarginModel,
    LinearForm, Fin.sum_univ_one]

theorem cq_batch_valid : oaBatchValid cqModel cqBatch := by
  refine ⟨?_, by ext i; norm_num [cqBatch, Chapter02.oaIntCast, pt], ?_⟩
  · intro i
    norm_num [cqBatch, cqModel, Chapter02KKTExamples.zeroMarginModel]
  · change IsMinimizer (cqModel.fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => 0)))
      cqModel.objective (pt 0 0)
    have hc : Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)) = (fun _ => 0) := by
      ext i
      norm_num [Chapter02.oaIntCast]
    rw [hc]
    exact Chapter02KKTExamples.zeroMargin_fixed_optimum

theorem cq_cuts (q : Point 1 1) : oaBatchCuts cqModel cqBatch q ↔ 0 ≤ q.2 0 := by
  have hd : oaBatchDerivative cqModel cqBatch = fun _ => -coordY := by
    funext j
    have h := Chapter02KKTExamples.zeroMargin_derivative (pt 0 0) j
    simpa [oaBatchDerivative,cqModel,cqBatch,pt,coordY] using h.fderiv
  unfold oaBatchCuts SelectedOARows tangentRow
  rw [hd]
  simp [oaBatchRows, cqBatch, cqModel, Chapter02KKTExamples.zeroMarginModel,
    pt, coordY, Chapter02KKTExamples.coordY]

theorem cq_master (H : List (OABatch 1 1)) (hH : ∀ b ∈ H, b = cqBatch) :
    IsMinimizer (oaMaster cqModel H) cqModel.objective (pt (-1) 0) := by
  refine ⟨(oa_master_mem_iff _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (Chapter02KKTExamples.zeroMargin_linear_iff _).mpr (by norm_num [pt])
  · refine ⟨fun _ => 0, ?_, by ext i; simp [pt]⟩
    intro i
    norm_num [cqModel, Chapter02KKTExamples.zeroMarginModel]
  · intro b hb
    rw [hH b hb]
    exact (cq_cuts _).mpr (by norm_num [pt])
  · intro q hq
    have hx := ((Chapter02KKTExamples.zeroMargin_linear_iff q).mp
      ((oa_master_mem_iff _ _ _).mp hq).1).1
    simpa only [cq_objective, pt] using hx

def cqState : ℕ → OAState 1 1
  | 0 => oaInit none
  | k+1 => oaAppend cqModel (cqState k) cqBatch

theorem cq_state_history (k : ℕ) : ∀ b ∈ (cqState k).history, b = cqBatch := by
  induction k with
  | zero => simp [cqState, oaInit]
  | succ k ih =>
    intro b hb
    simp only [cqState, oaAppend, List.mem_append, List.mem_singleton] at hb
    exact hb.elim (ih b) id

theorem cq_state_incumbent (k : ℕ) :
    (cqState k).incumbent = none ∨ (cqState k).incumbent = some (pt 0 0) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    right
    rcases ih with h | h <;>
      simp [cqState, oaAppend, cqBatch, oaBest, h]

theorem cq_repeats (k : ℕ) : OAContinue cqModel 0 (cqState k) (cqState (k+1)) := by
  apply OAContinue.step (q := pt (-1) 0) (b := cqBatch)
  · exact cq_master _ (cq_state_history k)
  · intro u hu
    rcases cq_state_incumbent k with h | h
    · rw [h] at hu
      cases hu
    · rw [h] at hu
      cases Option.some.inj hu
      norm_num [cq_objective, pt]
  · exact cq_batch_valid
  · ext i
    norm_num [pt, Chapter02.oaIntCast, cqBatch]

theorem cq_invariant (k : ℕ) : OAInvariant cqModel (cqState k) := by
  induction k with
  | zero => exact oa_init_invariant _ none (by simp)
  | succ k ih => exact oa_continue_invariant _ ih (cq_repeats k)

theorem cq_history_length (k : ℕ) : (cqState k).history.length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [cqState, oaAppend] using congrArg Nat.succ ih

theorem cq_fiber_slater_fails : ¬ OAFiberSlater cqModel := by
  intro h
  have hy : (fun _ : Fin 1 => (0 : ℤ)) ∈ IntegerBox cqModel.lo cqModel.hi := by
    intro i
    norm_num [cqModel, Chapter02KKTExamples.zeroMarginModel]
  have hp : (cqModel.fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => (0:ℤ)))).Nonempty := by
    have hc : Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)) = (fun _ => 0) := by
      ext i
      norm_num [Chapter02.oaIntCast]
    rw [hc]
    exact Set.nonempty_of_mem Chapter02KKTExamples.zeroMargin_fixed_optimum.1
  obtain ⟨z,hz,hg⟩ := h (fun _ => 0) hy hp
  have hzy : z.2 0 = 0 := by simpa [Chapter02.oaIntCast] using congrFun hz.2 0
  have hg0 := hg (0 : Fin 1)
  change (z.1 0)^2-z.2 0<0 at hg0
  rw [hzy] at hg0
  nlinarith [sq_nonneg (z.1 0)]

theorem missing_cq_arbitrary_exact_repetition :
    IsCompact (cqModel.linearRegion ∩ IntegerCylinder (n := 1) cqModel.lo cqModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (cqModel.g j)) ∧
    (∀ j, ContDiff ℝ 1 (cqModel.g j)) ∧ ¬ OAFiberSlater cqModel ∧
    (∀ k, OAInvariant cqModel (cqState k)) ∧
    (∀ k, OAContinue cqModel 0 (cqState k) (cqState (k+1))) ∧
    (∀ k, (cqState k).history.length = k) :=
  ⟨Chapter02KKTExamples.zeroMargin_base_compact, Chapter02KKTExamples.zeroMargin_convex,
    Chapter02KKTExamples.zeroMargin_smooth, cq_fiber_slater_fails,
    cq_invariant, cq_repeats, cq_history_length⟩

#print axioms missing_cq_arbitrary_exact_repetition

def toleranceDeleted : OAState 1 1 := ⟨[],some (pt (-1) 0)⟩

theorem deleted_history_repeats_solved_fiber :
    OAContinue toleranceModel 0 (oaInit none) toleranceCold1 ∧
    pt (-2) 0 ∉ oaMaster toleranceModel toleranceCold1.history ∧
    OAContinue toleranceModel 0 toleranceDeleted (oaAppend toleranceModel toleranceDeleted toleranceBatch) ∧
    toleranceDeleted.incumbent = toleranceCold1.incumbent := by
  refine ⟨OAContinue.step tolerance_initial_master (by simp [oaCompetitive, oaInit])
    tolerance_batch_valid (by ext i; norm_num [pt, toleranceBatch, Chapter02.oaIntCast]), ?_, ?_, rfl⟩
  · intro h
    have hc := ((oa_master_mem_iff _ _ _).mp h).2.2 toleranceBatch (by simp [toleranceCold1, oaAppend, oaInit])
    have hn := (tolerance_batch_cuts _).mp hc
    norm_num [pt] at hn
  · apply OAContinue.step tolerance_initial_master
    · intro u hu
      have hu' : u = pt (-1) 0 := (Option.some.inj hu).symm
      subst u
      norm_num [tolerance_objective, pt]
    · exact tolerance_batch_valid
    · ext i
      norm_num [pt, toleranceBatch, Chapter02.oaIntCast]

#print axioms deleted_history_repeats_solved_fiber

/-! The alternate relation below is deliberately the incorrect strict-gap
policy. It otherwise uses the same exact masters, batches and append operation.
The witness keeps the chosen master original-infeasible, so the optional
feasible-master return cannot rescue this particular execution. -/
def WrongStrictContinue (d : ModelData 1 1 1 2) (s t : OAState 1 1) : Prop :=
  ∃ q b, IsMinimizer (oaMaster d s.history) d.objective q ∧
    (∀ u, s.incumbent = some u → ¬ d.objective u < d.objective q) ∧
    oaBatchValid d b ∧ q.2 = Chapter02.oaIntCast b.integer ∧ t = oaAppend d s b

def guardModel : ModelData 1 1 1 2 := { toleranceModel with c1 := fun _ => 0 }
def guardBatch : OABatch 1 1 := ⟨fun _ => 0, pt 0 0, none⟩

theorem guard_objective (p : Point 1 1) : guardModel.objective p = 0 := by
  simp [guardModel, toleranceModel, ModelData.objective, LinearForm]

theorem guard_batch_valid : oaBatchValid guardModel guardBatch := by
  refine ⟨?_, by ext i; norm_num [guardBatch, Chapter02.oaIntCast, pt], ?_⟩
  · intro i
    norm_num [guardBatch, guardModel, toleranceModel, traceModel]
  · change IsMinimizer (guardModel.fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => 0)))
      guardModel.objective (pt 0 0)
    refine ⟨⟨⟨(tolerance_linear_iff _).mpr (by norm_num [pt]), ?_⟩, ?_⟩, ?_⟩
    · ext i
      norm_num [Chapter02.oaIntCast, pt]
    · intro j
      norm_num [guardModel, toleranceModel, pt]
    · intro q hq
      simp [guard_objective]

theorem guard_cuts (q : Point 1 1) : oaBatchCuts guardModel guardBatch q := by
  have hd : oaBatchDerivative guardModel guardBatch = fun _ => 0 := by
    funext j
    have h := ((hasDerivAt_pow 2 (sumCoord (pt 0 0))).comp_hasFDerivAt (pt 0 0)
      sumCoord.hasFDerivAt).sub_const 1
    have hg : HasFDerivAt (guardModel.g j) (0 : Point 1 1 →L[ℝ] ℝ) (pt 0 0) := by
      convert h using 1 <;>
      ext p <;>
        simp [guardModel, toleranceModel, sumCoord, coordX, coordY,
          Chapter02KKTExamples.coordY, pt, Function.comp_def, neg_smul]
    exact hg.fderiv
  unfold oaBatchCuts SelectedOARows tangentRow
  rw [hd]
  intro j hj
  norm_num [guardModel, guardBatch, toleranceModel, pt]

theorem guard_master (H : List (OABatch 1 1)) (hH : ∀ b∈H, b=guardBatch) :
    IsMinimizer (oaMaster guardModel H) guardModel.objective (pt 2 0) := by
  refine ⟨(oa_master_mem_iff _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (tolerance_linear_iff _).mpr (by norm_num [pt])
  · simpa [traceModel,guardModel,toleranceModel] using trace_cylinder 2 0 (by norm_num) (by norm_num)
  · intro b hb
    rw [hH b hb]
    exact guard_cuts _
  · intro q hq
    simp [guard_objective]

def guardState : ℕ → OAState 1 1
  | 0 => oaInit (some (pt 0 0))
  | k+1 => oaAppend guardModel (guardState k) guardBatch

theorem guard_state_history (k : ℕ) : ∀b∈(guardState k).history,b=guardBatch := by
  induction k with
  | zero => simp [guardState, oaInit]
  | succ k ih =>
    intro b hb
    simp only [guardState, oaAppend, List.mem_append, List.mem_singleton] at hb
    exact hb.elim (ih b) id

theorem guard_state_incumbent (k : ℕ) : (guardState k).incumbent = some (pt 0 0) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [guardState, oaAppend, guardBatch, oaBest, ih]

theorem guard_state_invariant (k : ℕ) : OAInvariant guardModel (guardState k) := by
  induction k with
  | zero =>
    apply oa_init_invariant
    intro u hu
    cases Option.some.inj hu
    exact oaBatch_feasible_original guardModel guardBatch guard_batch_valid rfl
  | succ k ih => exact oa_append_invariant _ ih guardBatch guard_batch_valid

theorem guard_wrong_repeat (k : ℕ) : WrongStrictContinue guardModel (guardState k) (guardState (k+1)) := by
  refine ⟨pt 2 0, guardBatch, guard_master _ (guard_state_history k), ?_, guard_batch_valid, ?_, rfl⟩
  · intro u hu
    simp [guard_objective]
  · ext i
    norm_num [guardBatch, Chapter02.oaIntCast, pt]

theorem guard_correct_stop (k : ℕ) : OAStop guardModel 0 (guardState k) (.solution (pt 0 0)) := by
  exact OAStop.gap (guard_master _ (guard_state_history k)) (guard_state_incumbent k)
    (by simp [guard_objective])

theorem guard_master_infeasible : pt 2 0 ∉ guardModel.feasibleOn Set.univ := by
  intro hp
  have hg := ((source_feasible_iff _ _ _).mp hp).2.1 (0 : Fin 1)
  norm_num [guardModel, toleranceModel, pt] at hg

theorem wrong_strict_guard_arbitrary_repetition :
    IsCompact (guardModel.linearRegion ∩ IntegerCylinder (n := 1) guardModel.lo guardModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (guardModel.g j)) ∧
    (∀ j, Differentiable ℝ (guardModel.g j)) ∧ OAFiberSlater guardModel ∧
    (∀ k, OAInvariant guardModel (guardState k)) ∧
    (∀ k, WrongStrictContinue guardModel (guardState k) (guardState (k+1))) ∧
    (∀ k, OAStop guardModel 0 (guardState k) (.solution (pt 0 0))) ∧
    pt 2 0 ∉ guardModel.feasibleOn Set.univ :=
  ⟨trace_base_compact, tolerance_convex, tolerance_diff, tolerance_slater,
    guard_state_invariant, guard_wrong_repeat, guard_correct_stop, guard_master_infeasible⟩

#print axioms wrong_strict_guard_arbitrary_repetition

/-! Global strict feasibility does not supply the required CQ on each
feasible integer fiber. This two-fiber model has a strictly feasible global
point and a better feasible point than the repeatedly returned NLP(0) anchor. -/
def globalCQModel : ModelData 1 1 1 2 :=
  { cqModel with c1 := fun _ => -1, c2 := fun _ => 1/2, hi := fun _ => 1 }

theorem globalCQ_objective (p : Point 1 1) :
    globalCQModel.objective p = -p.1 0 + (1/2)*p.2 0 := by
  simp [globalCQModel, ModelData.objective, LinearForm, Fin.sum_univ_one]

theorem globalCQ_linear_iff (p : Point 1 1) :
    p ∈ globalCQModel.linearRegion ↔ -1 ≤ p.1 0 ∧ p.1 0 ≤ 1 :=
  Chapter02KKTExamples.zeroMargin_linear_iff p

theorem globalCQ_base_compact :
    IsCompact (globalCQModel.linearRegion ∩ IntegerCylinder (n := 1)
      globalCQModel.lo globalCQModel.hi) := by
  have hc : IsClosed {p : Point 1 1 | -1 ≤ p.1 0 ∧ p.1 0 ≤ 1} :=
    (isClosed_le continuous_const coordX.continuous).inter
      (isClosed_le coordX.continuous continuous_const)
  have he : globalCQModel.linearRegion ∩ IntegerCylinder (n := 1)
      globalCQModel.lo globalCQModel.hi =
      (traceModel.linearRegion ∩ IntegerCylinder (n := 1) traceModel.lo traceModel.hi) ∩
      {p : Point 1 1 | -1 ≤ p.1 0 ∧ p.1 0 ≤ 1} := by
    ext p
    constructor
    · rintro ⟨hp,hint⟩
      have hx := (globalCQ_linear_iff p).mp hp
      exact ⟨⟨(trace_linear_iff p).mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩,hint⟩,hx⟩
    · rintro ⟨⟨_,hint⟩,hx⟩
      exact ⟨(globalCQ_linear_iff p).mpr hx,hint⟩
  rw [he]
  exact trace_base_compact.inter_right hc

theorem globalCQ_fixed_minimum :
    IsMinimizer (globalCQModel.fixedNonlinearFiber (fun _ => 0))
      globalCQModel.objective (pt 0 0) := by
  refine ⟨Chapter02KKTExamples.zeroMargin_fixed_optimum.1, ?_⟩
  intro q hq
  have he := (Chapter02KKTExamples.zeroMargin_fiber_iff q).mp hq
  rw [he]
  exact le_rfl

theorem globalCQ_batch_valid : oaBatchValid globalCQModel cqBatch := by
  refine ⟨?_, by ext i; norm_num [cqBatch, Chapter02.oaIntCast, pt], ?_⟩
  · intro i
    norm_num [cqBatch, globalCQModel, cqModel, Chapter02KKTExamples.zeroMarginModel]
  · change IsMinimizer (globalCQModel.fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => 0)))
      globalCQModel.objective (pt 0 0)
    have hc : Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)) = (fun _ => 0) := by
      ext i
      norm_num [Chapter02.oaIntCast]
    rw [hc]
    exact globalCQ_fixed_minimum

theorem globalCQ_master (H : List (OABatch 1 1)) (hH : ∀b∈H,b=cqBatch) :
    IsMinimizer (oaMaster globalCQModel H) globalCQModel.objective (pt 1 0) := by
  refine ⟨(oa_master_mem_iff _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (globalCQ_linear_iff _).mpr (by norm_num [pt])
  · simpa [traceModel,globalCQModel,cqModel,Chapter02KKTExamples.zeroMarginModel] using trace_cylinder 1 0 (by norm_num) (by norm_num)
  · intro b hb
    rw [hH b hb]
    exact (cq_cuts _).mpr (by norm_num [pt])
  · intro q hq
    have hm := (oa_master_mem_iff _ _ _).mp hq
    have hx := ((globalCQ_linear_iff q).mp hm.1).2
    obtain ⟨y,hy,hqy⟩ := hm.2.1
    have hy0 : 0 ≤ q.2 0 := by rw [hqy]; exact (hy 0).1
    simp only [globalCQ_objective, pt]
    linarith

def globalCQState : ℕ → OAState 1 1
  | 0 => oaInit none
  | k+1 => oaAppend globalCQModel (globalCQState k) cqBatch

theorem globalCQ_state_history (k : ℕ) : ∀ b∈(globalCQState k).history,b=cqBatch := by
  induction k with
  | zero => simp [globalCQState, oaInit]
  | succ k ih =>
    intro b hb
    simp only [globalCQState, oaAppend, List.mem_append, List.mem_singleton] at hb
    exact hb.elim (ih b) id

theorem globalCQ_state_incumbent (k : ℕ) :
    (globalCQState k).incumbent = none ∨ (globalCQState k).incumbent = some (pt 0 0) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    right
    rcases ih with h | h <;>
      simp [globalCQState, oaAppend, cqBatch, oaBest, h]

theorem globalCQ_repeats (k : ℕ) :
    OAContinue globalCQModel 0 (globalCQState k) (globalCQState (k+1)) := by
  apply OAContinue.step (q := pt 1 0) (b := cqBatch)
  · exact globalCQ_master _ (globalCQ_state_history k)
  · intro u hu
    rcases globalCQ_state_incumbent k with h | h
    · rw [h] at hu
      cases hu
    · rw [h] at hu
      cases Option.some.inj hu
      norm_num [globalCQ_objective, pt]
  · exact globalCQ_batch_valid
  · ext i
    norm_num [pt, Chapter02.oaIntCast, cqBatch]

theorem globalCQ_state_invariant (k : ℕ) : OAInvariant globalCQModel (globalCQState k) := by
  induction k with
  | zero => exact oa_init_invariant _ none (by simp)
  | succ k ih => exact oa_continue_invariant _ ih (globalCQ_repeats k)

theorem globalCQ_strict :
    pt 0 1 ∈ globalCQModel.linearRegion ∧
    pt 0 1 ∈ IntegerCylinder (n := 1) globalCQModel.lo globalCQModel.hi ∧
    ∀j, globalCQModel.g j (pt 0 1) < 0 := by
  refine ⟨(globalCQ_linear_iff _).mpr (by norm_num [pt]), ?_, ?_⟩
  · simpa [traceModel,globalCQModel,cqModel,Chapter02KKTExamples.zeroMarginModel] using trace_cylinder 0 1 (by norm_num) (by norm_num)
  · intro j
    norm_num [globalCQModel, cqModel, Chapter02KKTExamples.zeroMarginModel, pt]

theorem globalCQ_better :
    pt 1 1 ∈ globalCQModel.feasibleOn Set.univ ∧
    globalCQModel.objective (pt 1 1) < globalCQModel.objective (pt 0 0) := by
  constructor
  · apply (source_feasible_iff _ _ _).mpr
    refine ⟨Set.mem_univ _, ?_, (globalCQ_linear_iff _).mpr (by norm_num [pt]), ?_⟩
    · intro j
      norm_num [globalCQModel, cqModel, Chapter02KKTExamples.zeroMarginModel, pt]
    · exact ⟨fun _ => 1, by intro i; norm_num [globalCQModel,cqModel,Chapter02KKTExamples.zeroMarginModel],
        by funext i; norm_num [pt]⟩
  · norm_num [globalCQ_objective, pt]

theorem globalCQ_no_fiber_slater : ¬ OAFiberSlater globalCQModel := by
  intro h
  have hy : (fun _ : Fin 1 => (0 : ℤ)) ∈ IntegerBox globalCQModel.lo globalCQModel.hi := by
    intro i
    norm_num [globalCQModel, cqModel, Chapter02KKTExamples.zeroMarginModel]
  have hp : (globalCQModel.fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => (0:ℤ)))).Nonempty := by
    have hc : Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)) = (fun _ => 0) := by
      ext i
      norm_num [Chapter02.oaIntCast]
    rw [hc]
    exact Set.nonempty_of_mem globalCQ_fixed_minimum.1
  obtain ⟨z,hz,hg⟩ := h (fun _ => 0) hy hp
  have hzy : z.2 0 = 0 := by simpa [Chapter02.oaIntCast] using congrFun hz.2 0
  have hg0 := hg (0 : Fin 1)
  change (z.1 0)^2-z.2 0<0 at hg0
  rw [hzy] at hg0
  nlinarith [sq_nonneg (z.1 0)]

theorem global_slater_does_not_prevent_exact_repetition :
    IsCompact (globalCQModel.linearRegion ∩ IntegerCylinder (n := 1)
      globalCQModel.lo globalCQModel.hi) ∧
    (∀j,ConvexOn ℝ Set.univ (globalCQModel.g j)) ∧
    (∀j,ContDiff ℝ 1 (globalCQModel.g j)) ∧
    (pt 0 1 ∈ globalCQModel.linearRegion ∧
      pt 0 1 ∈ IntegerCylinder (n := 1) globalCQModel.lo globalCQModel.hi ∧
      ∀j,globalCQModel.g j (pt 0 1)<0) ∧
    ¬ OAFiberSlater globalCQModel ∧
    (∀k,OAInvariant globalCQModel (globalCQState k)) ∧
    (∀k,OAContinue globalCQModel 0 (globalCQState k) (globalCQState (k+1))) ∧
    (pt 1 1 ∈ globalCQModel.feasibleOn Set.univ ∧
      globalCQModel.objective (pt 1 1)<globalCQModel.objective (pt 0 0)) :=
  ⟨globalCQ_base_compact, Chapter02KKTExamples.zeroMargin_convex,
    Chapter02KKTExamples.zeroMargin_smooth, globalCQ_strict, globalCQ_no_fiber_slater,
    globalCQ_state_invariant, globalCQ_repeats, globalCQ_better⟩

#print axioms global_slater_does_not_prevent_exact_repetition

theorem trace_box_card : (oaBox traceModel).card = 2 := by
  classical
  have he : oaBox traceModel = {fun _ => (0 : ℤ), fun _ => (1 : ℤ)} := by
    ext y
    simp only [oaBox, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hy
      have hy0 : (0 : ℝ) ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 1 := hy 0
      have h0 : (0 : ℤ) ≤ y 0 := by exact_mod_cast hy0.1
      have h1 : y 0 ≤ (1 : ℤ) := by exact_mod_cast hy0.2
      have hy01 : y 0 = 0 ∨ y 0 = 1 := by omega
      rcases hy01 with h | h
      · left
        funext i
        fin_cases i
        exact h
      · right
        funext i
        fin_cases i
        exact h
    · rintro (rfl | rfl) i <;> norm_num [traceModel]
  rw [he]
  have hn : (fun _ : Fin 1 => (0 : ℤ)) ≠ (fun _ => 1) := by
    intro h
    have hv := congrFun h 0
    norm_num at hv
  simp [hn]

theorem trace_completed : OACompleted traceModel 0 traceS0 2 (.solution (pt 0 1)) :=
  ⟨traceS2, OAChain.cons trace_first_continue (OAChain.cons trace_second_continue
    (OAChain.nil traceS2)), trace_final_stop⟩

theorem two_branch_completed_sharp_bound :
    IsCompact (traceModel.linearRegion ∩ IntegerCylinder (n := 1) traceModel.lo traceModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (traceModel.g j)) ∧
    (∀ j, Differentiable ℝ (traceModel.g j)) ∧ OAFiberSlater traceModel ∧
    OAInvariant traceModel traceS0 ∧
    OACompleted traceModel 0 traceS0 2 (.solution (pt 0 1)) ∧
    (oaBox traceModel).card = 2 ∧
    OAReturnCertificate traceModel 0 (.solution (pt 0 1)) ∧
    IsMinimizer (traceModel.feasibleOn Set.univ) traceModel.objective (pt 0 1) := by
  have hi : OAInvariant traceModel traceS0 := oa_init_invariant traceModel none (by simp)
  exact ⟨trace_base_compact,trace_convex,trace_diff,trace_fiber_slater,hi,
    trace_completed,trace_box_card,
    oa_completed_sound traceModel trace_convex trace_diff (by norm_num) hi trace_completed,
    oa_completed_zero_optimal traceModel trace_convex trace_diff hi trace_completed⟩

/-- Deliberately altered policy: solves a fiber before testing the incumbent
gap. This records the actual exact reply and append, without a progress input. -/
def SolveBeforeGuard (d : ModelData 1 1 1 2) (s t : OAState 1 1) : Prop :=
  ∃ q b, IsMinimizer (oaMaster d s.history) d.objective q ∧ oaBatchValid d b ∧
    q.2 = Chapter02.oaIntCast b.integer ∧ t = oaAppend d s b

def traceS3 : OAState 1 1 := oaAppend traceModel traceS2 traceGood

theorem late_guard_extra_fiber_solve :
    SolveBeforeGuard traceModel traceS0 traceS1 ∧
    SolveBeforeGuard traceModel traceS1 traceS2 ∧
    SolveBeforeGuard traceModel traceS2 traceS3 ∧
    OAStop traceModel 0 traceS2 (.solution (pt 0 1)) ∧
    OAStop traceModel 0 traceS3 (.solution (pt 0 1)) ∧
    traceS3.history.length = 3 ∧ (oaBox traceModel).card < traceS3.history.length := by
  refine ⟨?_,?_,?_,trace_final_stop,?_,rfl,?_⟩
  · exact ⟨pt 2 0,traceBad,trace_initial_master,trace_bad_valid,
      by ext i; norm_num [pt,traceBad,Chapter02.oaIntCast],rfl⟩
  · exact ⟨pt 2 1,traceGood,trace_later_master [traceBad] (by simp) (by simp),trace_good_valid,
      by ext i; norm_num [pt,traceGood,Chapter02.oaIntCast],rfl⟩
  · exact ⟨pt 2 1,traceGood,trace_later_master [traceBad,traceGood] (by simp) (by simp),trace_good_valid,
      by ext i; norm_num [pt,traceGood,Chapter02.oaIntCast],rfl⟩
  · apply OAStop.gap (q := pt 2 1)
    · exact trace_later_master [traceBad,traceGood,traceGood] (by simp) (by simp)
    · simp [traceS3,traceS2,traceS1,traceS0,oaAppend,oaInit,traceBad,traceGood,oaBest]
    · norm_num [trace_objective,pt]
  · rw [trace_box_card]
    decide

#print axioms two_branch_completed_sharp_bound
#print axioms late_guard_extra_fiber_solve

end Chapter02OAExamples
