module

public import Chapter03FPSearchModel
public import Chapter03FPSearchCQ
public import Chapter03FPSearchAnalytic
public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! A current-CQ countercontrol for the held Bonami2006 p7 extension to a
convex feasible region with nonconvex residuals. All five source inequalities
are actual g rows, with base = univ. Bonami's (integer x, continuous y) is
represented by (continuous u, integer t). This does not refute Theorem 1 with
convex residuals or target freshness. Requiring CQ at EVERY RETAINED ANCHOR,
INCLUDING THE SEED k=0, excludes this control. CQ only at computed FP-NLP
projection points i>=1 does not protect the comparison with the seed. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP Chapter03.FPUnboundedControls
namespace Chapter03.FPSearch.CQCounterexample

abbrev P := Point 1 1

def row : Fin 5 → P → ℝ := ![
  fun p => (p.2 0-1/2)^3 + (p.1 0)^2*(p.2 0-1/2),
  fun p => -p.2 0,
  fun p => p.2 0-1,
  fun p => -p.1 0-2,
  fun p => p.1 0-2]

def rowD (j : Fin 5) (p : P) : P →L[ℝ] ℝ := ![
  (3*(p.2 0-1/2)^2+(p.1 0)^2) • yc 1 +
    (2*p.1 0*(p.2 0-1/2)) • xc,
  -(yc 1), yc 1, -xc, xc] j

def data : Data 1 1 5 where
  base := Set.univ
  f p := (p.2 0-1/2)^2+(p.1 0)^2
  g := row
  Df p := (2*(p.2 0-1/2)) • yc 1 + (2*p.1 0) • xc
  Dg := rowD

def seed : P := xy 0 (1/2)
def current : P := xy 1 (1/2)
def masterOne : P := xy 0 1
def state : State 1 1 := initialState seed

theorem row_derivative (j : Fin 5) (p : P) : HasFDerivAt (row j) (rowD j p) p := by
  fin_cases j
  · have ht := ((yc 1).hasFDerivAt (x := p)).sub_const (1/2:ℝ)
    have hu := xc.hasFDerivAt (x := p)
    convert ((ht.mul ht).mul ht).add ((hu.mul hu).mul ht) using 1
    · funext v; simp [row]; ring
    · apply ContinuousLinearMap.ext
      intro v
      simp [rowD]
      ring
  · exact (yc 1).hasFDerivAt.neg
  · exact (yc 1).hasFDerivAt.sub_const 1
  · exact xc.hasFDerivAt.neg.sub_const 2
  · exact xc.hasFDerivAt.sub_const 2

theorem objective_derivative (p : P) : HasFDerivAt data.f (data.Df p) p := by
  simpa [data] using (square_derivative (yc 1) (1/2) p).fun_add
    (square_derivative xc 0 p)

theorem nonlinear_row_sign (p : P) : row 0 p ≤ 0 ↔ p.2 0 ≤ 1/2 := by
  change (p.2 0-1/2)^3+(p.1 0)^2*(p.2 0-1/2) ≤ 0 ↔ _
  constructor
  · intro h
    by_contra hn
    have ht : 0 < p.2 0-1/2 := sub_pos.mpr (lt_of_not_ge hn)
    have hcube : 0 < (p.2 0-1/2)^3 := pow_pos ht _
    have hprod : 0 ≤ (p.1 0)^2*(p.2 0-1/2) := mul_nonneg (sq_nonneg _) ht.le
    linarith
  · intro ht
    have hnonpos : p.2 0-1/2 ≤ 0 := sub_nonpos.mpr ht
    have hs : 0 ≤ (p.2 0-1/2)^2+(p.1 0)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have h := mul_nonpos_of_nonpos_of_nonneg hnonpos hs
    nlinarith only [h]

theorem relaxation_mem (p : P) : p ∈ data.relaxation ↔
    -2 ≤ p.1 0 ∧ p.1 0 ≤ 2 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1/2 := by
  constructor
  · rintro ⟨_,h⟩
    have h0 := (nonlinear_row_sign p).mp (h 0)
    have h1 := h 1; have h3 := h 3; have h4 := h 4
    change -p.2 0 ≤ 0 at h1
    change -p.1 0-2 ≤ 0 at h3
    change p.1 0-2 ≤ 0 at h4
    exact ⟨by linarith,by linarith,by linarith,h0⟩
  · rintro ⟨hu0,hu1,ht0,ht1⟩
    refine ⟨Set.mem_univ _,?_⟩
    intro j; fin_cases j
    · exact (nonlinear_row_sign p).mpr ht1
    · change -p.2 0 ≤ 0; linarith
    · change p.2 0-1 ≤ 0; linarith
    · change -p.1 0-2 ≤ 0; linarith
    · change p.1 0-2 ≤ 0; linarith

theorem relaxation_eq : data.relaxation = Set.Icc (xy (-2) 0) (xy 2 (1/2)) := by
  ext p
  rw [relaxation_mem]
  change _ ↔ ((fun _ : Fin 1 => (-2:ℝ)) ≤ p.1 ∧
    (fun _ : Fin 1 => (0:ℝ)) ≤ p.2) ∧
    (p.1 ≤ (fun _ : Fin 1 => (2:ℝ)) ∧ p.2 ≤ (fun _ : Fin 1 => (1/2:ℝ)))
  simp only [Pi.le_def,Fin.forall_fin_one]
  tauto

theorem relaxation_convex : Convex ℝ data.relaxation := by
  intro p hp q hq a b ha hb hab
  rw [relaxation_mem] at hp hq ⊢
  change -2 ≤ a*p.1 0+b*q.1 0 ∧ a*p.1 0+b*q.1 0 ≤ 2 ∧
    0 ≤ a*p.2 0+b*q.2 0 ∧ a*p.2 0+b*q.2 0 ≤ 1/2
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hp.1 ha,mul_le_mul_of_nonneg_left hq.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hp.2.1 ha,mul_le_mul_of_nonneg_left hq.2.1 hb]
  · exact add_nonneg (mul_nonneg ha hp.2.2.1) (mul_nonneg hb hq.2.2.1)
  · nlinarith [mul_le_mul_of_nonneg_left hp.2.2.2 ha,mul_le_mul_of_nonneg_left hq.2.2.2 hb]

theorem relaxation_compact : IsCompact data.relaxation := by
  rw [relaxation_eq]; exact isCompact_Icc

theorem initializer : IsMinimizer data.relaxation data.f seed := by
  refine ⟨(relaxation_mem _).mpr (by norm_num [seed]),?_⟩
  intro p _
  change ((1/2:ℝ)-1/2)^2+0^2 ≤ (p.2 0-1/2)^2+(p.1 0)^2
  nlinarith [sq_nonneg (p.2 0-1/2),sq_nonneg (p.1 0)]

def initialization : Initialization data := .minimum seed initializer

theorem seed_fractional : ¬Integral seed := by
  rintro ⟨q,hq⟩
  have he : (1/2:ℝ)=(q 0:ℝ) := congrFun hq 0
  have hl : (0:ℝ)<(q 0:ℝ) := by linarith
  have hu : (q 0:ℝ)<1 := by linarith
  have hl' : 0<q 0 := by exact_mod_cast hl
  have hu' : q 0<1 := by exact_mod_cast hu
  omega

theorem current_fractional : ¬Integral current := seed_fractional

theorem initial_rows (p : P) : (∀ j, tangent data seed j p ≤ 0) ↔
    0 ≤ p.2 0 ∧ p.2 0 ≤ 1 ∧ -2 ≤ p.1 0 ∧ p.1 0 ≤ 2 := by
  norm_num [tangent,data,row,rowD,seed,xy,Fin.forall_fin_succ]

theorem masterOne_target : masterOne.2=intCast (iv 1) := by
  funext j
  norm_num [masterOne,intCast,iv]

theorem first_master_mem : masterOne ∈ master data .basic state := by
  refine ⟨Set.mem_univ _,⟨iv 1,masterOne_target⟩,⟨?_,?_⟩,?_⟩
  · exact (initial_rows _).mpr (by norm_num [masterOne])
  · simp [state,initialState]
  · intro h; cases h

theorem first_master_minimum :
    IsMinimizer (master data .basic state) (masterCost state) masterOne := by
  refine ⟨first_master_mem,?_⟩
  intro p hp
  have hb := (initial_rows p).mp hp.2.2.1.1
  obtain ⟨k,hk⟩ := (scalar_integer p).mp hp.2.1
  have hi := binary_value (show 0≤(k:ℝ) by linarith [hb.1])
    (show (k:ℝ)≤1 by linarith [hb.2.1])
  simp only [masterCost,State.reference,state,initialState,List.getLast?_nil,
    Option.map_none,Option.getD_none,scalar_l1]
  rcases hi with rfl | rfl <;> norm_num [masterOne,seed,hk]

theorem current_projection :
    IsMinimizer data.relaxation (distance (iv 1)) current := by
  refine ⟨(relaxation_mem _).mpr (by norm_num [current]),?_⟩
  intro p hp
  have ht := ((relaxation_mem p).mp hp).2.2.2
  simp only [scalar_distance,iv_apply,Int.cast_one]
  change (1-(1/2:ℝ))^2 ≤ (1-p.2 0)^2
  nlinarith [sq_nonneg (p.2 0-1/2)]

/-- The held unsquared norm has exactly this same current projection minimizer. -/
theorem current_norm_projection :
    IsMinimizer data.relaxation (fun p => ‖intY (iv 1)-Chapter03.yMap 1 1 p‖) current := by
  exact (norm_projection_iff data.relaxation (iv 1) current).mpr current_projection

def firstStep : Step data .basic state :=
  ⟨masterOne,iv 1,current,first_master_minimum,masterOne_target,current_projection⟩

theorem active_seed : {j : Fin 5 | row j seed=0}={0} := by
  ext j; fin_cases j <;> norm_num [row,seed]

theorem active_current : {j : Fin 5 | row j current=0}={0} := by
  ext j; fin_cases j <;> norm_num [row,current]

theorem current_full_licq : JointLICQ row (fun j => rowD j current) current := by
  change LinearIndepOn ℝ (fun j => rowD j current) {j | row j current=0}
  rw [active_current,linearIndepOn_singleton_iff]
  intro hz
  have he := congrArg (fun L : P →L[ℝ] ℝ => L (xy 0 1)) hz
  norm_num [rowD,current] at he

theorem seed_not_licq : ¬JointLICQ row (fun j => rowD j seed) seed := by
  change ¬LinearIndepOn ℝ (fun j => rowD j seed) {j | row j seed=0}
  rw [active_seed,linearIndepOn_singleton_iff]
  push_neg
  apply ContinuousLinearMap.ext
  intro v
  simp [rowD,seed]

/-- The source-bound box already witnesses failure of convexity of the row. -/
theorem nonlinear_row_not_convex :
    ¬ConvexOn ℝ (Set.Icc (xy (-2) 0) (xy 2 1)) (row 0) := by
  intro h
  have hp : xy 0 0 ∈ Set.Icc (xy (-2) 0) (xy 2 1) := by
    constructor <;> constructor <;> intro i <;> fin_cases i <;> norm_num [xy]
  have hq : xy 0 (1/2) ∈ Set.Icc (xy (-2) 0) (xy 2 1) := by
    constructor <;> constructor <;> intro i <;> fin_cases i <;> norm_num [xy]
  have hh := h.2 hp hq (show (0:ℝ)≤1/2 by norm_num)
    (show (0:ℝ)≤1/2 by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
  norm_num [row,xy] at hh

theorem nonlinear_row_not_affine : ¬OAKKT.AffineRow (row 0) := by
  intro h
  have ht := OAKKT.affine_tangent h (row_derivative 0 seed) (xy 0 1)
  norm_num [row,rowD,seed] at ht

/-- Selection (3) of the held source retains every row at this initializer:
four convex affine bounds and the active nonlinear row. -/
theorem source_initial_row_selection (j : Fin 5) :
    ConvexOn ℝ Set.univ (row j) ∨ row j seed=0 := by
  fin_cases j
  · right; norm_num [row,seed]
  · left; exact FPTrace.linear_convex convex_univ (-(yc 1))
  · left
    simpa [row,Pi.add_def,sub_eq_add_neg] using
      (FPTrace.linear_convex convex_univ (yc 1)).add_const (-1)
  · left
    simpa [row,Pi.add_def,sub_eq_add_neg] using
      (FPTrace.linear_convex convex_univ (-xc)).add_const (-2)
  · left
    simpa [row,Pi.add_def,sub_eq_add_neg] using
      (FPTrace.linear_convex convex_univ xc).add_const (-2)

/-- Literal held selection (3) master at i=1: all bounds are original rows,
there is no hard base and there are no earlier projection-normal cuts. -/
def heldSelectedMaster : Set P :=
  {p | Integral p ∧ ∀ j : Fin 5,
    (ConvexOn ℝ Set.univ (row j) ∨ row j seed=0) → tangent data seed j p ≤ 0}

/-- Exact empty-history equality, not just a selection-membership observation. -/
theorem initial_master_eq_held : master data .basic state=heldSelectedMaster := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.2.1,fun j _ => hp.2.2.1.1 j⟩
  · rintro ⟨hi,hr⟩
    refine ⟨Set.mem_univ _,hi,⟨?_,?_⟩,?_⟩
    · intro j; exact hr j (source_initial_row_selection j)
    · simp [state,initialState]
    · intro h; cases h

theorem held_first_master_minimum :
    IsMinimizer heldSelectedMaster (masterCost state) masterOne := by
  rw [←initial_master_eq_held]
  exact first_master_minimum

/-- The nonconvex row is active at the initializer, so source selection(3)
retains it; the four bound rows are affine and remain exact tangent bounds. -/
theorem nonlinear_row_selected : selectedAt data seed 0 :=
  ⟨nonlinear_row_not_affine,by norm_num [data,row,seed]⟩

theorem repeated_integer_block : firstStep.projection.2=state.seed.2 := rfl

theorem different_full_points : firstStep.projection≠state.seed := by
  intro h
  have hh := congrArg (fun p : P => p.1 0) h
  norm_num [firstStep,current,state,initialState,seed] at hh

theorem original_feasible : xy 0 0 ∈ data.original := by
  refine ⟨(relaxation_mem _).mpr (by norm_num),⟨iv 0,?_⟩⟩
  funext j
  norm_num [intCast,iv]

/-- Self-contained source-premise package for the literal current-CQ reading.
CQ at every retained anchor INCLUDING seed k=0 would exclude this instance;
CQ only at FP-NLP points i>=1 does not protect the comparison with seed k=0. -/
theorem countercontrol :
    (∀ j p, HasFDerivAt (data.g j) (data.Dg j p) p) ∧
    (∀ p, HasFDerivAt data.f (data.Df p) p) ∧
    master data .basic state=heldSelectedMaster ∧
    IsMinimizer heldSelectedMaster (masterCost state) firstStep.point ∧
    IsMinimizer data.relaxation
      (fun p => ‖intY firstStep.target-Chapter03.yMap 1 1 p‖) firstStep.projection ∧
    ¬Integral firstStep.projection ∧
    ¬ConvexOn ℝ (Set.Icc (xy (-2) 0) (xy 2 1)) (data.g 0) ∧
    Convex ℝ data.relaxation ∧ IsCompact data.relaxation ∧
    IsMinimizer data.relaxation data.f state.seed ∧ ¬Integral state.seed ∧
    JointLICQ data.g (fun j => data.Dg j firstStep.projection) firstStep.projection ∧
    ¬JointLICQ data.g (fun j => data.Dg j state.seed) state.seed ∧
    firstStep.projection.2=state.seed.2 ∧ firstStep.projection≠state.seed := by
  exact ⟨row_derivative,objective_derivative,initial_master_eq_held,
    held_first_master_minimum,current_norm_projection,current_fractional,
    nonlinear_row_not_convex,relaxation_convex,relaxation_compact,
    initializer,seed_fractional,current_full_licq,seed_not_licq,
    repeated_integer_block,different_full_points⟩

end Chapter03.FPSearch.CQCounterexample
