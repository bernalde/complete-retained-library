module

public import Chapter02GBDDriver
public import Chapter02OAEdgeExamples

@[expose] public section

/-! Dimension and empty-box controls use the literal projected GBD master.
All source assumptions are discharged jointly. Multipliers in the feasible
zero-dimensional example come from source existence at its actual optimum. -/
noncomputable section
namespace Chapter02
namespace GBDEdgeExamples
open OAEdgeExamples

theorem singleton_floor : GBDFloorValid singletonModel 0 := by
  intro p _
  simp [singleton_objective]

theorem singleton_fixed_minimum :
    IsMinimizer (singletonModel.fixedNonlinearFiber (oaIntCast (0 : IntVector 0)))
      singletonModel.objective 0 := by
  refine ⟨⟨⟨?_,Subsingleton.elim _ _⟩,?_⟩,?_⟩
  · intro i; exact Fin.elim0 i
  · intro j; norm_num [singletonModel]
  · intro p _; simp [singleton_objective]

theorem singleton_derived_reply :
    ∃ b : GBDBatch 0 0 1 0, gbdBatchValid singletonModel b ∧
      b.integer = 0 ∧ gbdBatchOptimalAnchor b = some 0 := by
  obtain ⟨lambda,mu,h⟩ := gbd_optimal_reply_of_minimum singletonModel 0
    (fun i => Fin.elim0 i) 0 (Subsingleton.elim _ _) singleton_fixed_minimum
    singleton_convex singleton_diff singleton_CQ
  exact ⟨⟨0,.optimal 0 lambda mu⟩,h,rfl,rfl⟩

theorem singleton_projected_minimum (H : List (GBDBatch 0 0 1 0))
    (hH : ∀ b ∈ H, gbdBatchValid singletonModel b) :
    IsMinimizer (gbdMaster singletonModel 0 H) Prod.snd (0,0) := by
  refine ⟨?_,?_⟩
  · have h := gbd_master_contains_feasible singletonModel 0 H hH singleton_floor
      singleton_convex 0 (singleton_feasible 0) 0 (Subsingleton.elim _ _)
    simpa only [singleton_objective] using h
  · intro z hz
    exact ((gbd_master_mem_iff singletonModel 0 H z).mp hz).2.1

/-- There is no continuous master point or feasible-master shortcut: this
cold projected run makes one true fixed-fiber decision, then the weak gap stops. -/
theorem singleton_actual_trace :
    ∃ b : GBDBatch 0 0 1 0, gbdBatchValid singletonModel b ∧
      gbdBatchOptimalAnchor b = some 0 ∧
      GBDContinue singletonModel 0 0 (gbdInit none)
        (gbdAppend singletonModel (gbdInit none) b) ∧
      GBDStop singletonModel 0 0 (gbdAppend singletonModel (gbdInit none) b)
        (.solution 0) ∧ GBDReturnCertificate singletonModel 0 (.solution 0) := by
  obtain ⟨b,hb,hi,ha⟩ := singleton_derived_reply
  have hstep : GBDContinue singletonModel 0 0 (gbdInit none)
      (gbdAppend singletonModel (gbdInit none) b) :=
    .step (singleton_projected_minimum [] (by simp))
      (by intro u h; cases h) hb hi.symm
  have hs := gbd_continue_invariant singletonModel
    (gbd_init_invariant singletonModel none (by intro u h; cases h)) hstep
  have hstop : GBDStop singletonModel 0 0
      (gbdAppend singletonModel (gbdInit none) b) (.solution 0) := by
    refine GBDStop.gap (z := (0,0))
      (singleton_projected_minimum [b] (by simpa using hb)) ?_ ?_
    · simp [gbdAppend,gbdInit,ha,oaBest]
    · simp [singleton_objective]
  exact ⟨b,hb,ha,hstep,hstop,gbd_stop_sound singletonModel singleton_floor singleton_convex hs hstop⟩

theorem singleton_joint_source_and_trace :
    IsCompact (singletonModel.linearRegion ∩ IntegerCylinder (n := 0)
      singletonModel.lo singletonModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (singletonModel.g j)) ∧
    (∀ j, Differentiable ℝ (singletonModel.g j)) ∧ OAFiberSlater singletonModel ∧
    GBDFloorValid singletonModel 0 ∧ (0 : ℝ) ≤ 0 ∧
    ∃ b : GBDBatch 0 0 1 0,
      GBDContinue singletonModel 0 0 (gbdInit none)
        (gbdAppend singletonModel (gbdInit none) b) ∧
      GBDStop singletonModel 0 0 (gbdAppend singletonModel (gbdInit none) b)
        (.solution 0) ∧ IsMinimizer (singletonModel.feasibleOn Set.univ)
          singletonModel.objective 0 := by
  obtain ⟨b,_,_,hst,hstop,hcert⟩ := singleton_actual_trace
  exact ⟨singleton_compact,singleton_convex,singleton_diff,singleton_CQ,
    singleton_floor,le_rfl,b,hst,hstop,gbd_certificate_zero_optimal singletonModel hcert⟩

theorem fractional_box_empty :
    IntegerBox fractionalBoxModel.lo fractionalBoxModel.hi = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact fractional_integer_impossible (y 0) (hy 0)

theorem fractional_projected_empty (floor : ℝ) (H : List (GBDBatch 0 1 0 0)) :
    gbdMaster fractionalBoxModel floor H = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hy := ((gbd_master_mem_iff fractionalBoxModel floor H z).mp hz).1
  rw [fractional_box_empty] at hy
  exact hy

theorem fractional_floor : GBDFloorValid fractionalBoxModel 0 := by
  intro p _
  simp [fractionalBoxModel,ModelData.objective,LinearForm]

theorem fractional_joint_immediate_return :
    IsCompact (fractionalBoxModel.linearRegion ∩ IntegerCylinder (n := 0)
      fractionalBoxModel.lo fractionalBoxModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (fractionalBoxModel.g j)) ∧
    (∀ j, Differentiable ℝ (fractionalBoxModel.g j)) ∧ OAFiberSlater fractionalBoxModel ∧
    GBDFloorValid fractionalBoxModel 0 ∧ (0 : ℝ) ≤ 0 ∧
    GBDStop fractionalBoxModel 0 0 (gbdInit none) .infeasible ∧
    GBDReturnCertificate fractionalBoxModel 0 .infeasible := by
  have hc : ∀ j, ConvexOn ℝ Set.univ (fractionalBoxModel.g j) := fun j => Fin.elim0 j
  have hs : GBDStop fractionalBoxModel 0 0 (gbdInit none) .infeasible :=
    .empty (fractional_projected_empty 0 [])
  refine ⟨?_,hc,(fun j => Fin.elim0 j),zero_rows_CQ _,fractional_floor,le_rfl,hs,?_⟩
  · rw [fractional_base_empty]; exact isCompact_empty
  · exact gbd_stop_sound fractionalBoxModel fractional_floor hc
      (gbd_init_invariant fractionalBoxModel none (by intro u h; cases h)) hs

/-- The sole zero-dimensional tuple has an empty affine fiber. The projected
master initially allows it; the exact empty-fiber exclusion removes it. -/
def emptyAffineModel : ModelData 0 0 1 1 where
  g := fun _ _ => -1
  A := 0
  B := 0
  rhs := fun _ => -1
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

theorem emptyAffine_linear_empty : emptyAffineModel.linearRegion = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := hp 0
  norm_num [emptyAffineModel,LinearForm] at h

theorem emptyAffine_fiber_empty (y : RealVector 0) :
    ¬ (emptyAffineModel.fixedLinearFiber y).Nonempty := by
  rintro ⟨p,hp⟩
  have h := hp.1
  rw [emptyAffine_linear_empty] at h
  exact h

theorem emptyAffine_base_compact : IsCompact
    (emptyAffineModel.linearRegion ∩ IntegerCylinder (n := 0)
      emptyAffineModel.lo emptyAffineModel.hi) := by
  rw [emptyAffine_linear_empty,Set.empty_inter]
  exact isCompact_empty

theorem emptyAffine_convex : ∀ j, ConvexOn ℝ Set.univ (emptyAffineModel.g j) := by
  intro j; exact convexOn_const (-1) convex_univ

theorem emptyAffine_diff : ∀ j, Differentiable ℝ (emptyAffineModel.g j) := by
  intro j; exact differentiable_const _

theorem emptyAffine_CQ : OAFiberSlater emptyAffineModel := by
  intro y _ h
  obtain ⟨p,hp⟩ := h
  exact False.elim (emptyAffine_fiber_empty _ ⟨p,hp.1⟩)

theorem emptyAffine_floor : GBDFloorValid emptyAffineModel 0 := by
  intro p _
  simp [emptyAffineModel,ModelData.objective,LinearForm]

def emptyAffineBatch : GBDBatch 0 0 1 1 := ⟨0,.emptyLinear⟩

theorem emptyAffine_batch_valid : gbdBatchValid emptyAffineModel emptyAffineBatch :=
  ⟨fun i => Fin.elim0 i,emptyAffine_fiber_empty _⟩

theorem emptyAffine_initial_minimum :
    IsMinimizer (gbdMaster emptyAffineModel 0 []) Prod.snd (0,0) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨fun i => Fin.elim0 i,le_rfl,by simp⟩,?_⟩
  intro z hz
  exact ((gbd_master_mem_iff _ _ _ _).mp hz).2.1

theorem emptyAffine_excluded_master :
    gbdMaster emptyAffineModel 0 [emptyAffineBatch] = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have he := ((gbd_master_mem_iff _ _ _ _).mp hz).2.2 emptyAffineBatch (by simp)
  exact he (Subsingleton.elim _ _)

theorem emptyAffine_actual_trace :
    GBDContinue emptyAffineModel 0 0 (gbdInit none)
      (gbdAppend emptyAffineModel (gbdInit none) emptyAffineBatch) ∧
    GBDStop emptyAffineModel 0 0
      (gbdAppend emptyAffineModel (gbdInit none) emptyAffineBatch) .infeasible ∧
    GBDReturnCertificate emptyAffineModel 0 .infeasible := by
  have hstep : GBDContinue emptyAffineModel 0 0 (gbdInit none)
      (gbdAppend emptyAffineModel (gbdInit none) emptyAffineBatch) :=
    .step emptyAffine_initial_minimum (by intro u h; cases h) emptyAffine_batch_valid rfl
  have hstop : GBDStop emptyAffineModel 0 0
      (gbdAppend emptyAffineModel (gbdInit none) emptyAffineBatch) .infeasible :=
    .empty emptyAffine_excluded_master
  exact ⟨hstep,hstop,gbd_stop_sound emptyAffineModel emptyAffine_floor emptyAffine_convex
    (gbd_continue_invariant emptyAffineModel
      (gbd_init_invariant emptyAffineModel none (by intro u h; cases h)) hstep) hstop⟩

theorem emptyAffine_joint_source_and_trace :
    IsCompact (emptyAffineModel.linearRegion ∩ IntegerCylinder (n := 0)
      emptyAffineModel.lo emptyAffineModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (emptyAffineModel.g j)) ∧
    (∀ j, Differentiable ℝ (emptyAffineModel.g j)) ∧ OAFiberSlater emptyAffineModel ∧
    GBDFloorValid emptyAffineModel 0 ∧ (0 : ℝ) ≤ 0 ∧
    GBDContinue emptyAffineModel 0 0 (gbdInit none)
      (gbdAppend emptyAffineModel (gbdInit none) emptyAffineBatch) ∧
    GBDStop emptyAffineModel 0 0
      (gbdAppend emptyAffineModel (gbdInit none) emptyAffineBatch) .infeasible ∧
    GBDReturnCertificate emptyAffineModel 0 .infeasible :=
  ⟨emptyAffine_base_compact,emptyAffine_convex,emptyAffine_diff,emptyAffine_CQ,
    emptyAffine_floor,le_rfl,emptyAffine_actual_trace⟩

theorem singleton_box_card : (oaBox singletonModel).card = 1 := by
  have he : oaBox singletonModel = {0} := by
    ext y
    simp only [oaBox,Set.Finite.mem_toFinset,Finset.mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _,fun _ i => Fin.elim0 i⟩
  rw [he,Finset.card_singleton]

theorem emptyAffine_box_card : (oaBox emptyAffineModel).card = 1 := by
  have he : oaBox emptyAffineModel = {0} := by
    ext y
    simp only [oaBox,Set.Finite.mem_toFinset,Finset.mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _,fun _ i => Fin.elim0 i⟩
  rw [he,Finset.card_singleton]

theorem fractional_box_card : (oaBox fractionalBoxModel).card = 0 := by
  simp [oaBox,fractional_box_empty]

theorem singleton_counted_trace :
    GBDCountedCompleted singletonModel 0 0 (gbdInit none) ⟨1,0,0⟩ (.solution 0) := by
  obtain ⟨b,hb,ha,hstep,hstop,_⟩ := singleton_actual_trace
  refine ⟨gbdAppend singletonModel (gbdInit none) b,[b],
    .cons hstep (.nil _),hstop,?_⟩
  cases he : b.payload with
  | optimal p lambda mu => simp [gbdCountHistory,gbdCountBatch,he,GBDCounts.add,GBDCounts.zero]
  | restoration p rho lambda mu => simp [gbdBatchOptimalAnchor,he] at ha
  | emptyLinear => simp [gbdBatchOptimalAnchor,he] at ha

theorem emptyAffine_counted_trace :
    GBDCountedCompleted emptyAffineModel 0 0 (gbdInit none) ⟨0,0,1⟩ .infeasible ∧
      (GBDCounts.mk 0 0 1).optimizations = 0 := by
  exact ⟨⟨_,[emptyAffineBatch],.cons emptyAffine_actual_trace.1 (.nil _),
    emptyAffine_actual_trace.2.1,rfl⟩,rfl⟩

theorem fractional_counted_trace :
    GBDCountedCompleted fractionalBoxModel 0 0 (gbdInit none) .zero .infeasible ∧
      GBDCounts.zero.fiber+1 = 1 := by
  exact ⟨⟨_,[],.nil _,.empty (fractional_projected_empty 0 []),rfl⟩,rfl⟩

/-- Joint source assumptions provide actual selectors, and every one returns
the unique feasible zero-dimensional point with at most one fiber decision. -/
theorem singleton_all_choices_return :
    Nonempty (GBDSelector singletonModel 0 0) ∧
    ∀ choose : GBDSelector singletonModel 0 0, ∃ counts,
      gbdRun singletonModel choose 2 (gbdInit none)
        (gbd_init_invariant singletonModel none (by intro u h; cases h)) =
          some (.solution 0,counts) ∧
      GBDCountedCompleted singletonModel 0 0 (gbdInit none) counts (.solution 0) ∧
      counts.fiber ≤ 1 ∧ GBDExactCertificate singletonModel (.solution 0) := by
  refine ⟨gbd_selector_exists singletonModel 0 0 singleton_compact singleton_convex
    singleton_diff singleton_CQ,?_⟩
  intro choose
  obtain ⟨result,c,hr,hcount,_,hb,_,_,hcert⟩ :=
    gbd_driver_exact_finite_return singletonModel singleton_floor singleton_convex
      choose none (by intro u h; cases h)
  rw [singleton_box_card] at hr hb
  cases result with
  | infeasible => exact False.elim (hcert ⟨0,singleton_feasible 0⟩)
  | solution p =>
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    exact ⟨c,hr,hcount,hb,hcert⟩

theorem emptyAffine_all_choices_return :
    Nonempty (GBDSelector emptyAffineModel 0 0) ∧
    ∀ choose : GBDSelector emptyAffineModel 0 0, ∃ counts,
      gbdRun emptyAffineModel choose 2 (gbdInit none)
        (gbd_init_invariant emptyAffineModel none (by intro u h; cases h)) =
          some (.infeasible,counts) ∧
      GBDCountedCompleted emptyAffineModel 0 0 (gbdInit none) counts .infeasible ∧
      counts.fiber ≤ 1 ∧ GBDExactCertificate emptyAffineModel .infeasible := by
  refine ⟨gbd_selector_exists emptyAffineModel 0 0 emptyAffine_base_compact emptyAffine_convex
    emptyAffine_diff emptyAffine_CQ,?_⟩
  intro choose
  obtain ⟨result,c,hr,hcount,_,hb,_,_,hcert⟩ :=
    gbd_driver_exact_finite_return emptyAffineModel emptyAffine_floor emptyAffine_convex
      choose none (by intro u h; cases h)
  rw [emptyAffine_box_card] at hr hb
  cases result with
  | infeasible => exact ⟨c,hr,hcount,hb,hcert⟩
  | solution p =>
    have hp := ((source_feasible_iff emptyAffineModel Set.univ p).mp hcert.1).2.2.1
    have he : p ∈ emptyAffineModel.linearRegion := hp
    rw [emptyAffine_linear_empty] at he
    exact False.elim he

theorem fractional_all_choices_return :
    Nonempty (GBDSelector fractionalBoxModel 0 0) ∧
    ∀ choose : GBDSelector fractionalBoxModel 0 0,
      gbdRun fractionalBoxModel choose 1 (gbdInit none)
        (gbd_init_invariant fractionalBoxModel none (by intro u h; cases h)) =
          some (.infeasible,GBDCounts.zero) ∧
      GBDCountedCompleted fractionalBoxModel 0 0 (gbdInit none) .zero .infeasible := by
  have hc : ∀ j, ConvexOn ℝ Set.univ (fractionalBoxModel.g j) := fun j => Fin.elim0 j
  have hbase : IsCompact (fractionalBoxModel.linearRegion ∩ IntegerCylinder (n := 0)
      fractionalBoxModel.lo fractionalBoxModel.hi) := by
    rw [fractional_base_empty]; exact isCompact_empty
  refine ⟨gbd_selector_exists fractionalBoxModel 0 0 hbase hc
    (fun j => Fin.elim0 j) (zero_rows_CQ _),?_⟩
  intro choose
  obtain ⟨result,c,hr,hcount,_,_,_,_,hcert⟩ :=
    gbd_driver_exact_finite_return fractionalBoxModel fractional_floor hc
      choose none (by intro u h; cases h)
  have hz := (gbd_empty_box_completed_counts fractionalBoxModel le_rfl fractional_box_card
    none (by intro u h; cases h) hcount).1
  subst c
  rw [fractional_box_card] at hr
  cases result with
  | infeasible => exact ⟨hr,hcount⟩
  | solution p =>
    obtain ⟨_,_,_,y,hy,_⟩ := (source_feasible_iff fractionalBoxModel Set.univ p).mp hcert.1
    exact False.elim (fractional_integer_impossible (y 0) (hy 0))

end GBDEdgeExamples
end Chapter02

#print axioms Chapter02.GBDEdgeExamples.singleton_floor
#print axioms Chapter02.GBDEdgeExamples.singleton_fixed_minimum
#print axioms Chapter02.GBDEdgeExamples.singleton_derived_reply
#print axioms Chapter02.GBDEdgeExamples.singleton_projected_minimum
#print axioms Chapter02.GBDEdgeExamples.singleton_actual_trace
#print axioms Chapter02.GBDEdgeExamples.singleton_joint_source_and_trace
#print axioms Chapter02.GBDEdgeExamples.fractional_box_empty
#print axioms Chapter02.GBDEdgeExamples.fractional_projected_empty
#print axioms Chapter02.GBDEdgeExamples.fractional_floor
#print axioms Chapter02.GBDEdgeExamples.fractional_joint_immediate_return
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_linear_empty
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_fiber_empty
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_base_compact
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_convex
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_diff
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_CQ
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_floor
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_batch_valid
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_initial_minimum
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_excluded_master
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_actual_trace
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_joint_source_and_trace
#print axioms Chapter02.GBDEdgeExamples.singleton_box_card
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_box_card
#print axioms Chapter02.GBDEdgeExamples.fractional_box_card
#print axioms Chapter02.GBDEdgeExamples.singleton_counted_trace
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_counted_trace
#print axioms Chapter02.GBDEdgeExamples.fractional_counted_trace
#print axioms Chapter02.GBDEdgeExamples.singleton_all_choices_return
#print axioms Chapter02.GBDEdgeExamples.emptyAffine_all_choices_return
#print axioms Chapter02.GBDEdgeExamples.fractional_all_choices_return
