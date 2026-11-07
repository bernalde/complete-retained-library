module

public import Chapter08HullCompact

@[expose] public section

/-! Exact controls for the main hull and compactness interfaces. Residual
dimensions are 1,2,1. The branches are points 0,2,5 intersected with [0,2],
so the third branch is empty while the first two have a fractional midpoint. -/
noncomputable section
open scoped BigOperators
open Set

namespace Chapter08.HullControls
open ContinuousHull

def point (a : ℝ) : Vec 1 := fun _ => a

def data : Data (Fin 3) 1 where
  dim i := if i = 1 then 2 else 1
  map _ :=
    { toFun := fun x _ => x 0
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  offset i := fun _ => if i = 0 then 0 else if i = 1 then 2 else 5
  cone _ := {0}
  lower := point 0
  upper := point 2

@[simp] theorem data_map_apply (i : Fin 3) (x : Vec 1) (j : Fin (data.dim i)) :
    data.map i x j = x 0 := rfl

@[simp] theorem data_offset_apply (i : Fin 3) (j : Fin (data.dim i)) :
    data.offset i j = (if i = 0 then 0 else if i = 1 then 2 else 5) := rfl

theorem data_conic : Conic data where
  zero_mem _ := by rfl
  convex _ := convex_singleton 0
  smul_mem _ a _ z hz := by
    have hz' : z = 0 := Set.mem_singleton_iff.mp hz
    apply Set.mem_singleton_iff.mpr
    rw [hz']
    exact smul_zero a

theorem left_branch_member : point 0 ∈ branch data 0 := by
  constructor
  · intro j; norm_num [data, point]
  · apply Set.mem_singleton_iff.mpr
    ext j
    change (0 : ℝ) - 0 = 0
    norm_num

theorem right_branch_member : point 2 ∈ branch data 1 := by
  constructor
  · intro j; norm_num [data, point]
  · apply Set.mem_singleton_iff.mpr
    ext j
    change (2 : ℝ) - 2 = 0
    norm_num

theorem third_branch_empty : branch data 2 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hu := (hx.1 0).2
  have he := congrFun (Set.mem_singleton_iff.mp hx.2) 0
  change x 0 ≤ 2 at hu
  change x 0 - 5 = 0 at he
  linarith

def fractional : LiftPoint (Fin 3) 1 :=
  (![1/2, 1/2, 0], ![point 0, point 1, point 0])

theorem fractional_lift : fractional ∈ lift data := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [fractional]
  · norm_num [fractional, Fin.sum_univ_succ]
  · intro i
    apply Set.mem_singleton_iff.mpr
    ext j
    fin_cases i
    · change (0 : ℝ) - (1/2)*0 = 0
      norm_num
    · change (1 : ℝ) - (1/2)*2 = 0
      norm_num
    · change (0 : ℝ) - 0*5 = 0
      norm_num
  · intro i j
    fin_cases i <;> norm_num [data, fractional, point]

theorem fractional_fullLift : (point 1, fractional) ∈ fullLift data := by
  refine ⟨fractional_lift, ?_⟩
  ext j
  norm_num [fractional, point, Fin.sum_univ_succ]

theorem midpoint_in_projection : point 1 ∈ projection data :=
  ⟨fractional, fractional_lift, fractional_fullLift.2⟩

theorem midpoint_not_in_union : point 1 ∉ boundedUnion data := by
  intro hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have h := congrFun (Set.mem_singleton_iff.mp hi.2) 0
  change (1 : ℝ) - (if i = 0 then 0 else if i = 1 then 2 else 5) = 0 at h
  fin_cases i <;> norm_num at h

theorem fractional_hull_control :
    point 1 ∈ convexHull ℝ (boundedUnion data) ∧ point 1 ∉ boundedUnion data := by
  refine ⟨?_, midpoint_not_in_union⟩
  rw [← continuous_hull_exact data data_conic]
  exact midpoint_in_projection

theorem empty_branch_control : fractional.1 2 = 0 ∧ fractional.2 2 = 0 :=
  ⟨empty_branch_weight_zero data data_conic fractional_lift 2 third_branch_empty,
    empty_branch_block_zero data data_conic fractional_lift 2 third_branch_empty⟩

def endpoint : LiftPoint (Fin 3) 1 := (![1, 0, 0], fun _ => point 0)

theorem endpoint_lift : endpoint ∈ lift data := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [endpoint]
  · norm_num [endpoint, Fin.sum_univ_succ]
  · intro i
    apply Set.mem_singleton_iff.mpr
    ext j
    fin_cases i
    · change (0 : ℝ) - 1*0 = 0
      norm_num
    · change (0 : ℝ) - 0*2 = 0
      norm_num
    · change (0 : ℝ) - 0*5 = 0
      norm_num
  · intro i j
    fin_cases i <;> norm_num [data, endpoint, point]

theorem zero_weight_nonempty_branch_control :
    point 2 ∈ branch data 1 ∧ endpoint.1 1 = 0 ∧ endpoint.2 1 = 0 :=
  ⟨right_branch_member, by norm_num [endpoint],
    zero_block data endpoint_lift 1 (by norm_num [endpoint])⟩

def emptyData : Data (Fin 0) 1 where
  dim _ := 1
  map _ := 0
  offset _ := 0
  cone _ := {0}
  lower := point 0
  upper := point 2

theorem empty_disjunction_control : projection emptyData = ∅ :=
  projection_empty_index emptyData

theorem incompatible_box_control :
    projection {data with lower := point 3} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := projected_inBox {data with lower := point 3} hx 0
  norm_num [data, point] at h
  linarith [h.1, h.2]

theorem compact_fullLift_control : IsCompact (fullLift data) :=
  isCompact_fullLift data (fun _ => isClosed_singleton)

theorem closed_hull_control :
    closure (convexHull ℝ (boundedUnion data)) = projection data :=
  closed_hull_exact data data_conic (fun _ => isClosed_singleton)

end Chapter08.HullControls

#print axioms Chapter08.HullControls.data_map_apply
#print axioms Chapter08.HullControls.data_offset_apply
#print axioms Chapter08.HullControls.data_conic
#print axioms Chapter08.HullControls.left_branch_member
#print axioms Chapter08.HullControls.right_branch_member
#print axioms Chapter08.HullControls.third_branch_empty
#print axioms Chapter08.HullControls.fractional_lift
#print axioms Chapter08.HullControls.fractional_fullLift
#print axioms Chapter08.HullControls.midpoint_in_projection
#print axioms Chapter08.HullControls.midpoint_not_in_union
#print axioms Chapter08.HullControls.fractional_hull_control
#print axioms Chapter08.HullControls.empty_branch_control
#print axioms Chapter08.HullControls.endpoint_lift
#print axioms Chapter08.HullControls.zero_weight_nonempty_branch_control
#print axioms Chapter08.HullControls.empty_disjunction_control
#print axioms Chapter08.HullControls.incompatible_box_control
#print axioms Chapter08.HullControls.compact_fullLift_control
#print axioms Chapter08.HullControls.closed_hull_control
