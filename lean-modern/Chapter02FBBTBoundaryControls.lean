module

public import Chapter02FBBTTheorem
public import Chapter02AffinePropagationExamples

@[expose] public section

/-! Actual simultaneous-operator/LP boundary applications. These supporting
controls are uncounted; source acceptance remains with the complete frozen review.
The inconsistent rows reuse the previously accepted model and infeasibility proof. -/
noncomputable section
open Classical
open scoped BigOperators Topology
namespace Chapter02FBBTBoundary
open Chapter02FBBT

structure FixedInitialControl {n m} (A : Matrix n m) (q : JointBounds n m) : Prop where
  theory : SimultaneousTheory A q
  ordered : Ordered q
  actualFixed : rawF A q q = q
  allRunsNonempty : RunNonempty A q
  exactLimit : limitBounds A q = q
  conclusion : SimultaneousConclusion A q
  attained : LPFeasible A q (canonicalAssignment A q)
  maximum : ∀ p, LPFeasible A q p → LPObjective p ≤ LPObjective (canonicalAssignment A q)
  unique : ∀ p, LPFeasible A q p → LPObjective (canonicalAssignment A q) ≤ LPObjective p →
    p = canonicalAssignment A q

theorem fixed_initial_control {n m} (A : Matrix n m) (q : JointBounds n m)
    (ho : Ordered q) (hf : rawF A q q = q) : FixedInitialControl A q := by
  have ht := qualified_simultaneous_fbbt A q ho
  have hr := ht.runIffFixed.mpr ⟨q,ho,hf⟩
  have hc := ht.conditionalConclusion hr
  have he : limitBounds A q = q :=
    within_antisymm hc.limitWithinInitial (hc.greatestNonemptyFixed q ho hf)
  refine ⟨ht,ho,hf,hr,he,hc,?_,?_,?_⟩
  · simpa only [he] using hc.attainedLP
  · simpa only [he] using hc.globalWidthMaximum
  · simpa only [he] using hc.uniqueEntireAssignment

abbrev oldRow := Chapter02.AffinePropagationExamples.inconsistentRow

def inconsistentMatrix : Matrix 3 4 := fun i => (oldRow i).coefficient

def inconsistentBounds : JointBounds 3 4 :=
  (Sum.elim (fun _ => -1) (fun i => (oldRow i).lower),
   Sum.elim (fun _ => 1) (fun i => (oldRow i).upper))

theorem inconsistent_ordered : Ordered inconsistentBounds := by
  intro s
  cases s with
  | inl j => norm_num [inconsistentBounds]
  | inr i => fin_cases i <;> norm_num [inconsistentBounds,oldRow,
      Chapter02.AffinePropagationExamples.inconsistentRow]

theorem inconsistent_fixed : rawF inconsistentMatrix inconsistentBounds inconsistentBounds =
    inconsistentBounds := by
  apply (rawF_fixed_iff _ _ _).2
  refine ⟨within_refl _, (upward_fixed_iff _ _).2 ?_, (downward_fixed_iff _ _).2 ?_⟩
  · intro i
    fin_cases i <;> norm_num [imageLo,imageHi,productLo,productHi,inconsistentMatrix,
      inconsistentBounds,oldRow,Chapter02.AffinePropagationExamples.inconsistentRow,
      Chapter02.affineProductLo,Chapter02.affineProductHi,Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [inverseLo,inverseHi,restLo,restHi,productLo,productHi,inconsistentMatrix,
        inconsistentBounds,oldRow,Chapter02.AffinePropagationExamples.inconsistentRow,
        Chapter02.affineProductLo,Chapter02.affineProductHi,Finset.sum_erase_eq_sub,
        Fin.sum_univ_succ]

theorem inconsistent_no_graph : ¬ ∃ x, graph inconsistentMatrix x ∈ members inconsistentBounds := by
  rintro ⟨x,hx⟩
  apply Chapter02.AffinePropagationExamples.unchanged_infeasible_box_control.2.2
  refine ⟨x,?_,?_⟩
  · intro j
    exact hx (.inl j)
  · have hr (i : Fin 4) : (oldRow i).Holds x := by
      simpa [Chapter02.AffineIntervalRow.Holds,Chapter02.AffineIntervalRow.value,
        graph,inconsistentMatrix,inconsistentBounds,oldRow,
        Chapter02.AffinePropagationExamples.inconsistentRow] using hx (.inr i)
    intro r hrmem
    simp only [Chapter02.AffinePropagationExamples.inconsistentRows,
      List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hrmem
    rcases hrmem with rfl | rfl | rfl | rfl
    · exact hr 0
    · exact hr 1
    · exact hr 2
    · exact hr 3

structure InconsistentControl : Prop where
  actual : FixedInitialControl inconsistentMatrix inconsistentBounds
  cartesianNonempty : (members inconsistentBounds).Nonempty
  graphEmpty : ¬ ∃ x, graph inconsistentMatrix x ∈ members inconsistentBounds

theorem inconsistent_control : InconsistentControl :=
  ⟨fixed_initial_control _ _ inconsistent_ordered inconsistent_fixed,
   (members_nonempty_iff _).2 inconsistent_ordered,inconsistent_no_graph⟩

def noRowMatrix : Matrix 1 0 := fun i => Fin.elim0 i

def noRowBounds (l u : ℝ) : JointBounds 1 0 := (fun _ => l,fun _ => u)

theorem no_rows_fixed {n} (A : Matrix n 0) (q0 q : JointBounds n 0)
    (h : Within q q0) : rawF A q0 q = q := by
  apply (rawF_fixed_iff _ _ _).2
  exact ⟨h,(upward_fixed_iff _ _).2 (fun i => Fin.elim0 i),
    (downward_fixed_iff _ _).2 (fun i => Fin.elim0 i)⟩

structure CompetingBoxesControl : Prop where
  actual : FixedInitialControl noRowMatrix (noRowBounds 0 2)
  leftLP : LPFeasible noRowMatrix (noRowBounds 0 2)
    (canonicalAssignment noRowMatrix (noRowBounds 0 1))
  rightLP : LPFeasible noRowMatrix (noRowBounds 0 2)
    (canonicalAssignment noRowMatrix (noRowBounds 1 2))
  leftNotWithinRight : ¬ Within (noRowBounds 0 1) (noRowBounds 1 2)
  rightNotWithinLeft : ¬ Within (noRowBounds 1 2) (noRowBounds 0 1)
  wholeWidth : LPObjective (canonicalAssignment noRowMatrix (noRowBounds 0 2)) = 2
  leftWidth : LPObjective (canonicalAssignment noRowMatrix (noRowBounds 0 1)) = 1
  rightWidth : LPObjective (canonicalAssignment noRowMatrix (noRowBounds 1 2)) = 1

theorem competing_boxes_control : CompetingBoxesControl := by
  refine ⟨fixed_initial_control _ _ (by intro s; norm_num [noRowBounds])
    (no_rows_fixed _ _ _ (within_refl _)),?_,?_,?_,?_,?_,?_,?_⟩
  · exact (canonical_feasible_iff _ _ _).2 ⟨by intro s; norm_num [noRowBounds],
      no_rows_fixed _ _ _ (by intro s; norm_num [noRowBounds])⟩
  · exact (canonical_feasible_iff _ _ _).2 ⟨by intro s; norm_num [noRowBounds],
      no_rows_fixed _ _ _ (by intro s; norm_num [noRowBounds])⟩
  · intro h
    have h0 := h (.inl 0)
    norm_num [noRowBounds] at h0
  · intro h
    have h0 := h (.inl 0)
    norm_num [noRowBounds] at h0
  all_goals norm_num [LPObjective,canonicalAssignment,width,noRowBounds,
    Fintype.sum_sum_type,Fin.sum_univ_succ]

structure EmptyAfterOneControl {n m} (A : Matrix n m) (q : JointBounds n m) : Prop where
  theory : SimultaneousTheory A q
  initialNonempty : (publicRun A q 0).members.Nonempty
  initialNotEmpty : publicRun A q 0 ≠ .empty
  firstEmpty : publicRun A q 1 = .empty
  subsequentEmpty : ∀ k, publicRun A q (k+1) = .empty
  LPEmpty : ¬ ∃ p, LPFeasible A q p
  noGraph : ¬ ∃ x, graph A x ∈ members q

theorem empty_after_one_control {n m} (A : Matrix n m) (q : JointBounds n m)
    (ho : Ordered q) (hb : ¬ Ordered (rawF A q q)) : EmptyAfterOneControl A q := by
  have ht := qualified_simultaneous_fbbt A q ho
  have hi : (publicRun A q 0).members.Nonempty := by
    simpa only [publicRun,Function.iterate_zero_apply,public_members_ofBounds] using
      (members_nonempty_iff q).2 ho
  have he : publicRun A q 1 = .empty := by
    rw [ht.publicRawAgreement]
    apply (public_empty_iff _).2
    simpa only [rawRun,Function.iterate_one, id_eq] using hb
  have hlp : ¬ ∃ p, LPFeasible A q p := by
    intro hp
    have hr := ht.runIffFixed.mpr (ht.fixedIffLP.mpr hp)
    have h1 := hr 1
    rw [he] at h1
    exact Set.not_nonempty_empty h1
  refine ⟨ht,hi,?_,he,?_,hlp,ht.unconditionalInfeasibility hlp⟩
  · intro h
    rw [h] at hi
    exact Set.not_nonempty_empty hi
  · intro k
    induction k with
    | zero => exact he
    | succ k ih =>
      unfold publicRun
      rw [Function.iterate_succ_apply']
      change publicF A q (publicRun A q (k+1)) = .empty
      rw [ih]
      rfl

def immediateMatrix : Matrix 1 1 := fun _ _ => 1

def immediateBounds : JointBounds 1 1 :=
  (Sum.elim (fun _ => 0) (fun _ => 2),Sum.elim (fun _ => 1) (fun _ => 2))

theorem immediate_empty_control : EmptyAfterOneControl immediateMatrix immediateBounds := by
  apply empty_after_one_control
  · intro s
    cases s <;> norm_num [immediateBounds]
  · intro h
    have hb := h (.inr 0)
    norm_num [rawF,downward,upward,clip,immediateMatrix,immediateBounds,
      imageLo,imageHi,productLo,productHi,Chapter02.affineProductLo,
      Chapter02.affineProductHi,Fin.sum_univ_succ] at hb

/-- Ordered product X×B remains inhabited even when a zero row excludes zero. -/
def zeroMatrix (n : ℕ) : Matrix n 1 := fun _ _ => 0

def zeroRowBounds (n : ℕ) : JointBounds n 1 :=
  (Sum.elim (fun _ => 0) (fun _ => 1),Sum.elim (fun _ => 1) (fun _ => 1))

theorem zero_row_empty_control (n : ℕ) : EmptyAfterOneControl (zeroMatrix n) (zeroRowBounds n) := by
  apply empty_after_one_control
  · intro s
    cases s <;> norm_num [zeroRowBounds]
  · intro h
    have hb := h (.inr 0)
    norm_num [rawF,downward,upward,clip,zeroMatrix,zeroRowBounds,
      imageLo,imageHi,productLo,productHi,Chapter02.affineProductLo,
      Chapter02.affineProductHi] at hb

def emptyDimMatrix : Matrix 0 0 := fun i => Fin.elim0 i

def emptyDimBounds : JointBounds 0 0 := (fun c => Sum.elim Fin.elim0 Fin.elim0 c,
  fun c => Sum.elim Fin.elim0 Fin.elim0 c)

theorem empty_dimensions_control :
    FixedInitialControl emptyDimMatrix emptyDimBounds ∧
    (members emptyDimBounds).Nonempty ∧
    publicOfBounds emptyDimBounds ≠ .empty ∧
    LPObjective (canonicalAssignment emptyDimMatrix emptyDimBounds) = 0 := by
  have ho : Ordered emptyDimBounds := by intro c; cases c <;> exact Fin.elim0 ‹_›
  refine ⟨fixed_initial_control _ _ ho (no_rows_fixed _ _ _ (within_refl _)),
    (members_nonempty_iff _).2 ho,?_,?_⟩
  · exact fun h => (public_empty_iff _).1 h ho
  · simp [LPObjective,canonicalAssignment,width,Fintype.sum_sum_type]

theorem empty_dimensions_unique_bounds (q : JointBounds 0 0) : q = emptyDimBounds := by
  apply Prod.ext <;> funext c <;> cases c <;> exact Fin.elim0 ‹_›

structure BoundaryControls : Prop where
  inconsistent : InconsistentControl
  competing : CompetingBoxesControl
  immediateEmpty : EmptyAfterOneControl immediateMatrix immediateBounds
  zeroRow : ∀ n, EmptyAfterOneControl (zeroMatrix n) (zeroRowBounds n)
  zeroVariablesStillInitialNonempty : EmptyAfterOneControl (zeroMatrix 0) (zeroRowBounds 0)
  zeroVariablesAndRows : FixedInitialControl emptyDimMatrix emptyDimBounds
  zeroVariablesAndRowsNonempty : (members emptyDimBounds).Nonempty
  zeroVariablesAndRowsDistinctFromEmpty : publicOfBounds emptyDimBounds ≠ .empty
  zeroVariablesAndRowsUniqueBounds : ∀ q : JointBounds 0 0, q = emptyDimBounds
  zeroVariablesAndRowsWidth : LPObjective (canonicalAssignment emptyDimMatrix emptyDimBounds) = 0

theorem boundary_controls : BoundaryControls :=
  ⟨inconsistent_control,competing_boxes_control,immediate_empty_control,zero_row_empty_control,
    zero_row_empty_control 0,empty_dimensions_control.1,empty_dimensions_control.2.1,
    empty_dimensions_control.2.2.1,empty_dimensions_unique_bounds,empty_dimensions_control.2.2.2⟩

end Chapter02FBBTBoundary
