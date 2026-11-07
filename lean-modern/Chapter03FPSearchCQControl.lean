module

public import Chapter03FPSearchBasic
public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! Nondegenerate joint-CQ application with a genuine nonlinear active row.
The original integer problem is infeasible, but the relaxation is a nonempty
compact interval. Every selectable projection minimum satisfies full LICQ,
including both actual hard-domain bound rows. Supporting control only. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FPUnboundedControls
open Chapter03.FP (distance l1 intCast intY)
namespace Chapter03.FPSearchCQControl
open Chapter03.FPSearch

abbrev P := Point 0 1

/-- Empty constraint families need neither a nonzero covector nor a positive
ambient dimension. This also applies to Point 0 0 without changing its space. -/
theorem empty_family_licq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Fin 0 → E → ℝ) (A : Fin 0 → E →L[ℝ] ℝ) (p : E) :
    JointLICQ c A p := linearIndependent_empty_type

theorem empty_family_mfcq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Fin 0 → E → ℝ) (A : Fin 0 → E →L[ℝ] ℝ) (p : E) :
    JointMFCQ c A p := joint_mfcq_of_licq c A p (empty_family_licq c A p)

def data : Data 0 1 1 where
  base := Set.Icc (pt 0) (pt 1)
  f p := (p.2 0 - 1/2)^2
  g _ p := (p.2 0 - 1/2)^2 - 1/16
  Df p := (2*(p.2 0-1/2)) • yc 0
  Dg _ p := (2*(p.2 0-1/2)) • yc 0

theorem base_mem (p : P) : p ∈ data.base ↔ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  change (pt 0 ≤ p ∧ p ≤ pt 1) ↔ _
  constructor
  · rintro ⟨h0,h1⟩; exact ⟨h0.2 0,h1.2 0⟩
  · rintro ⟨h0,h1⟩
    constructor
    · constructor
      · intro i; exact Fin.elim0 i
      · intro j; fin_cases j; exact h0
    · constructor
      · intro i; exact Fin.elim0 i
      · intro j; fin_cases j; exact h1

theorem relaxation_mem (p : P) :
    p ∈ data.relaxation ↔ (1/4:ℝ) ≤ p.2 0 ∧ p.2 0 ≤ 3/4 := by
  change (p ∈ data.base ∧ ∀ j : Fin 1, (p.2 0-1/2)^2-1/16≤0) ↔ _
  rw [base_mem]
  simp only [Fin.forall_fin_one]
  constructor
  · rintro ⟨hb,hg⟩
    constructor <;> nlinarith
  · rintro ⟨ha,hb⟩
    refine ⟨⟨by linarith,by linarith⟩,?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

theorem base_convex : Convex ℝ data.base := by
  have he : data.base = (yc 0) ⁻¹' Set.Icc (0:ℝ) 1 := by
    ext p; exact base_mem p
  rw [he]
  exact (convex_Icc (0:ℝ) 1).linear_preimage (yc 0).toLinearMap

theorem analytic : Analytic data := by
  refine ⟨isClosed_Icc, base_convex, ?_, ?_, ?_, ?_, ?_, by norm_num [Data.toUnbounded]⟩
  · exact square_convex base_convex (yc 0) (1/2)
  · intro j
    simpa [data,Data.toUnbounded,Pi.add_def,sub_eq_add_neg] using
      (square_convex base_convex (yc 0) (1/2)).add_const (-(1/16))
  · intro p _
    exact square_derivative (yc 0) (1/2) p
  · intro j p _
    exact (square_derivative (yc 0) (1/2) p).sub_const (1/16)
  · exact (isCompact_Icc : IsCompact (Set.Icc (pt 0) (pt 1))).isBounded.subset
      (fun p hp => hp.1)

def baseRows : BaseRows data 2 where
  linear i := if i=0 then -(yc 0) else yc 0
  offset i := if i=0 then 0 else -1
  exact_base p := by
    rw [base_mem]
    simp only [Fin.forall_fin_two]
    norm_num

theorem original_empty : ¬data.original.Nonempty := by
  rintro ⟨p,hp,hi⟩
  obtain ⟨k,hk⟩ := (scalar_integer p).mp hi
  obtain ⟨ha,hb⟩ := (relaxation_mem p).mp hp
  have h0 : (0:ℝ) < k := by linarith
  have h1 : (k:ℝ) < 1 := by linarith
  have : 0 < k := by exact_mod_cast h0
  have : k < 1 := by exact_mod_cast h1
  omega

theorem initializer : IsMinimizer data.relaxation data.f (pt (1/2)) := by
  refine ⟨(relaxation_mem _).mpr (by norm_num),?_⟩
  intro p _
  change ((1/2:ℝ)-1/2)^2 ≤ (p.2 0-1/2)^2
  norm_num only [sub_self,zero_pow,ne_eq,OfNat.ofNat_ne_zero]
  exact sq_nonneg _

theorem projection_zero :
    IsMinimizer data.relaxation (distance (iv 0)) (pt (1/4)) := by
  refine ⟨(relaxation_mem _).mpr (by norm_num),?_⟩
  intro p hp
  have h := (relaxation_mem p).mp hp
  simp only [scalar_distance, iv_apply, Int.cast_zero, pt_snd]
  nlinarith

theorem projection_one :
    IsMinimizer data.relaxation (distance (iv 1)) (pt (3/4)) := by
  refine ⟨(relaxation_mem _).mpr (by norm_num),?_⟩
  intro p hp
  have h := (relaxation_mem p).mp hp
  simp only [scalar_distance, iv_apply, Int.cast_one, pt_snd]
  nlinarith

theorem projection_zero_unique (p : P)
    (hp : IsMinimizer data.relaxation (distance (iv 0)) p) : p=pt (1/4) := by
  have hb := (relaxation_mem p).mp hp.1
  have hm := hp.2 (pt (1/4)) projection_zero.1
  simp only [scalar_distance,iv_apply,Int.cast_zero,pt_snd] at hm
  have hy : p.2 0=1/4 := by nlinarith
  rw [←pt_eta p,hy]

theorem projection_one_unique (p : P)
    (hp : IsMinimizer data.relaxation (distance (iv 1)) p) : p=pt (3/4) := by
  have hb := (relaxation_mem p).mp hp.1
  have hm := hp.2 (pt (3/4)) projection_one.1
  simp only [scalar_distance,iv_apply,Int.cast_one,pt_snd] at hm
  have hy : p.2 0=3/4 := by nlinarith
  rw [←pt_eta p,hy]

/-- Both bound residuals remain indexed, but are strictly inactive here. -/
theorem active_exact (a : ℝ) (ha : a=1/4 ∨ a=3/4) :
    {i : Fin 2 ⊕ Fin 1 | jointRows data baseRows i (pt a)=0} = {Sum.inr 0} := by
  ext i
  cases i with
  | inl i =>
    fin_cases i <;> rcases ha with rfl | rfl <;>
      norm_num [jointRows,BaseRows.residual,baseRows] <;> simp
  | inr j =>
    fin_cases j
    rcases ha with rfl | rfl <;> norm_num [jointRows,data]

theorem endpoint_licq (a : ℝ) (ha : a=1/4 ∨ a=3/4) :
    JointLICQ (jointRows data baseRows) (jointRowD data baseRows (pt a)) (pt a) := by
  change LinearIndepOn ℝ (jointRowD data baseRows (pt a))
    {i | jointRows data baseRows i (pt a)=0}
  rw [active_exact a ha,linearIndepOn_singleton_iff]
  intro hz
  have he := congrArg (fun L : P →L[ℝ] ℝ => L (pt 1)) hz
  rcases ha with rfl | rfl <;> norm_num [jointRowD,data] at he

def targets : Finset (IntVector 1) := {iv 0,iv 1}

theorem targets_card : targets.card = 2 := by
  have h : iv 0 ≠ iv 1 := by
    intro he
    have hh := congrFun he 0
    norm_num [iv] at hh
  simp [targets,h]

theorem positive_projection_distances :
    distance (iv 0) (pt (1/4)) = 1/16 ∧
    distance (iv 1) (pt (3/4)) = 1/16 := by
  norm_num [scalar_distance]

theorem uniform_projection_licq : ProjectionLICQ data baseRows targets := by
  intro q hq p hp
  simp only [targets,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · rw [projection_zero_unique p hp]
    exact endpoint_licq (1/4) (Or.inl rfl)
  · rw [projection_one_unique p hp]
    exact endpoint_licq (3/4) (Or.inr rfl)

theorem target_bound (mode : Mode) : TargetBound data mode targets := by
  intro s _ p hp q hq
  obtain ⟨ha,hb⟩ := (base_mem p).mp hp.1
  have he : p.2 0=(q 0:ℝ) := congrFun hq 0
  have hq01 := binary_value (show 0≤(q 0:ℝ) by linarith)
    (show (q 0:ℝ)≤1 by linarith)
  have heta : q=iv (q 0) := by funext i; fin_cases i; rfl
  rcases hq01 with h0 | h1
  · rw [heta,h0]; simp [targets]
  · rw [heta,h1]; simp [targets]

theorem derived_basic_normal : NormalLaw data .basic targets :=
  basic_normal_law data baseRows analytic targets uniform_projection_licq

/-- The assessed endpoint is instantiated with proved analytics and uniform CQ;
there is no supplied progress or optimizer-existence assumption. -/
theorem all_selectors_return :
    Nonempty (Selector data .basic) ∧
    ∀ choose : Selector data .basic,
      ∃ out, procedureWithFuel data .basic (.minimum (pt (1/2)) initializer)
          choose (targets.card+1) = some out ∧
        out.Correct data ∧ out.Counts targets.card := by
  obtain ⟨_, hs, hf⟩ := qualified_basic_first_feasibility data baseRows analytic
    targets (target_bound .basic) uniform_projection_licq
  exact ⟨hs, fun choose => hf (.minimum (pt (1/2)) initializer) choose⟩

def eventZero : Event 0 1 := ⟨iv 0,pt (1/4)⟩
def eventOne : Event 0 1 := ⟨iv 1,pt (3/4)⟩
def stateZero : State 0 1 := initialState (pt (1/2))
def stateOne : State 0 1 := append stateZero eventZero
def stateTwo : State 0 1 := append stateOne eventOne

theorem fractional_of_relaxation {p : P} (hp : p ∈ data.relaxation) : ¬Integral p := by
  intro hi
  exact original_empty ⟨p,hp,hi⟩

theorem integer_base_cases (p : P) (hb : p ∈ data.base) (hi : Integral p) :
    p=pt 0 ∨ p=pt 1 := by
  obtain ⟨k,hk⟩ := (scalar_integer p).mp hi
  obtain ⟨h0,h1⟩ := (base_mem p).mp hb
  have hh := binary_value (show 0≤(k:ℝ) by linarith) (show (k:ℝ)≤1 by linarith)
  rcases hh with rfl | rfl
  · left; rw [←pt_eta p,hk]; norm_num
  · right; rw [←pt_eta p,hk]; norm_num

theorem initial_master_mem (a : ℝ) (ha : a=0 ∨ a=1) :
    pt a ∈ master data .basic stateZero := by
  rcases ha with rfl | rfl <;>
    refine ⟨(base_mem _).mpr (by norm_num),?_,⟨?_,?_⟩,?_⟩
  · exact ⟨iv 0,by funext j; norm_num [pt,intCast,iv]⟩
  · intro j; fin_cases j; norm_num [tangent,data,stateZero,initialState]
  · simp [stateZero,initialState]
  · intro h; cases h
  · exact ⟨iv 1,by funext j; norm_num [pt,intCast,iv]⟩
  · intro j; fin_cases j; norm_num [tangent,data,stateZero,initialState]
  · simp [stateZero,initialState]
  · intro h; cases h

theorem initial_master_min :
    IsMinimizer (master data .basic stateZero) (masterCost stateZero) (pt 0) := by
  refine ⟨initial_master_mem 0 (Or.inl rfl),?_⟩
  intro p hp
  rcases integer_base_cases p hp.1 hp.2.1 with rfl | rfl <;>
    norm_num [masterCost,State.reference,stateZero,initialState,scalar_l1]

theorem nonlinear_row : ¬OAKKT.AffineRow (data.g 0) :=
  scalar_square_not_affine (1/2) (1/16)

theorem event_zero_selected : selectedAt data eventZero.projection 0 := by
  exact ⟨nonlinear_row,by norm_num [data,eventZero]⟩

theorem event_one_selected : selectedAt data eventOne.projection 0 := by
  exact ⟨nonlinear_row,by norm_num [data,eventOne]⟩

theorem second_master_mem : pt 1 ∈ master data .basic stateOne := by
  refine ⟨(base_mem _).mpr (by norm_num),⟨iv 1,by funext j; norm_num [pt,intCast,iv]⟩,⟨?_,?_⟩,?_⟩
  · intro j; fin_cases j; norm_num [tangent,data,stateOne,append,stateZero,initialState]
  · intro e he j _
    have he' : e=eventZero := by simpa [stateOne,append,stateZero,initialState] using he
    subst e; fin_cases j
    norm_num [tangent,data,eventZero]
  · intro h; cases h

theorem second_master_only (p : P) (hp : p ∈ master data .basic stateOne) : p=pt 1 := by
  rcases integer_base_cases p hp.1 hp.2.1 with rfl | he
  · have ht := hp.2.2.1.2 eventZero
      (by simp [stateOne,append,stateZero,initialState]) 0 event_zero_selected
    norm_num [tangent,data,eventZero] at ht
  · exact he

theorem second_master_min :
    IsMinimizer (master data .basic stateOne) (masterCost stateOne) (pt 1) := by
  refine ⟨second_master_mem,?_⟩
  intro p hp
  rw [second_master_only p hp]

theorem final_master_empty : ¬(master data .basic stateTwo).Nonempty := by
  rintro ⟨p,hp⟩
  have hp1 := master_append_subset data .basic stateOne eventOne hp
  have he := second_master_only p hp1
  subst p
  have ht := hp.2.2.1.2 eventOne
    (by simp [stateTwo,append]) 0 event_one_selected
  norm_num [tangent,data,eventOne] at ht

def firstStep : Step data .basic stateZero :=
  ⟨pt 0,iv 0,pt (1/4),initial_master_min,by funext j; norm_num [pt,intCast,iv],projection_zero⟩
def secondStep : Step data .basic stateOne :=
  ⟨pt 1,iv 1,pt (3/4),second_master_min,by funext j; norm_num [pt,intCast,iv],projection_one⟩

/-- A total legal selector, with an actual optimizer choice at each named state
and the proved raw-choice existence theorem as fallback elsewhere. -/
def selected : Selector data .basic := by
  classical
  exact fun s hs =>
    if h0 : s=stateZero then h0.symm ▸ Decision.project firstStep
    else if h1 : s=stateOne then h1.symm ▸ Decision.project secondStep
    else if h2 : s=stateTwo then h2.symm ▸ Decision.empty final_master_empty
    else Classical.choice (decision_nonempty data analytic .basic s hs)

theorem states_distinct : stateOne≠stateZero ∧ stateTwo≠stateZero ∧ stateTwo≠stateOne := by
  refine ⟨?_,?_,?_⟩ <;> intro h <;>
    have hh := congrArg (fun s : State 0 1 => s.history.length) h <;>
    norm_num [stateZero,stateOne,stateTwo,append,initialState] at hh

theorem selected_zero (hs : stateZero.seed ∈ data.relaxation) :
    selected stateZero hs = .project firstStep := by simp [selected]

theorem selected_one (hs : stateOne.seed ∈ data.relaxation) :
    selected stateOne hs = .project secondStep := by
  simp [selected,states_distinct.1]

theorem selected_two (hs : stateTwo.seed ∈ data.relaxation) :
    selected stateTwo hs = .empty final_master_empty := by
  simp [selected,states_distinct.2.1,states_distinct.2.2]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Concrete first-search execution: two positive-distance fractional failures,
then infeasibility after exactly three masters and two projections. -/
theorem actual_two_failure_run :
    procedureWithFuel data .basic (.minimum (pt (1/2)) initializer) selected 3 =
      some (.loop ⟨stateTwo,.emptyMaster,3,2,2⟩) := by
  classical
  have hseed := fractional_of_relaxation initializer.1
  have hzero := fractional_of_relaxation projection_zero.1
  have hone := fractional_of_relaxation projection_one.1
  have h2 (hs : stateTwo.seed ∈ data.relaxation) :
      run data .basic selected 1 stateTwo hs = some (terminalOutput stateTwo .emptyMaster) := by
    simp only [run,selected_two]
  have h1 (hs : stateOne.seed ∈ data.relaxation) :
      run data .basic selected 2 stateOne hs =
        some ((terminalOutput stateTwo .emptyMaster).bump) := by
    rw [run,selected_one]
    change (if Integral (pt (3/4)) then _ else
      (run data .basic selected 1 stateTwo hs).map LoopOutput.bump) = _
    rw [if_neg hone,h2]
    rfl
  have h0 (hs : stateZero.seed ∈ data.relaxation) :
      run data .basic selected 3 stateZero hs =
        some ((terminalOutput stateTwo .emptyMaster).bump.bump) := by
    rw [run,selected_zero]
    change (if Integral (pt (1/4)) then _ else
      (run data .basic selected 2 stateOne hs).map LoopOutput.bump) = _
    rw [if_neg hzero,h1]
    rfl
  rw [procedureWithFuel,if_neg hseed]
  change (run data .basic selected 3 stateZero initializer.1).map Outcome.loop = _
  rw [h0]
  rfl

end Chapter03.FPSearchCQControl
