module

public import Chapter03FPSearchModel
public import Chapter03FPSearchCQ
public import Chapter03FPUnboundedControlAnalytic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

/-! AUTHOR CANDIDATE. Literal additive-cutoff background witness for
thesis TeX291–323 / final2020 p178. This is not the proposed method on p179:
there is no true nonlinear projection cutoff, polishing, or successful-target
exclusion. All four box bounds occur exactly once among the original rows.

This draft targets concrete source subproblem minima and explicit updates at every
index. The background passage does not specify a complete outer-loop stopping
procedure; this file does not invent or certify a general recursive driver.
The source's repeated exact choices are exhibited without optimizer/progress
callbacks. The selected MIP point itself is not delta-optimal. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FPUnboundedControls
open Chapter03.FP (distance l1 intCast Allows)
open Chapter03.FPSearch
namespace Chapter03.FPBackgroundAdditive

abbrev P := Point 1 1

def row : Fin 4 → P → ℝ := ![
  fun p => -p.1 0,
  fun p => p.1 0-1,
  fun p => -p.2 0,
  fun p => p.2 0-1]

def rowD (j : Fin 4) (_ : P) : P →L[ℝ] ℝ :=
  ![-xc,xc,-(yc 1),yc 1] j

def data : Data 1 1 4 where
  base := Set.univ
  f p := p.1 0+(p.2 0-1/2)^2
  g := row
  Df p := xc+(2*(p.2 0-1/2)) • yc 1
  Dg := rowD

def delta : ℝ := 1/10
def seed : P := xy 0 (1/2)
def bad : P := xy 1 0
def chosen : P := xy (1/2) 0
def optimum : P := xy 0 0

theorem delta_positive : 0<delta := by norm_num [delta]

def Box (p : P) : Prop :=
  0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1

theorem row_derivative (j : Fin 4) (p : P) :
    HasFDerivAt (row j) (rowD j p) p := by
  fin_cases j
  · exact xc.hasFDerivAt.neg
  · exact xc.hasFDerivAt.sub_const 1
  · exact (yc 1).hasFDerivAt.neg
  · exact (yc 1).hasFDerivAt.sub_const 1

theorem objective_derivative (p : P) : HasFDerivAt data.f (data.Df p) p :=
  xc.hasFDerivAt.add (square_derivative (yc 1) (1/2) p)

/-- The source C1 requirement is explicit, in addition to actual derivatives. -/
theorem derivative_continuity : Continuous data.Df ∧ ∀ j, Continuous (data.Dg j) := by
  constructor
  · exact continuous_const.add
      ((continuous_const.mul ((yc 1).continuous.sub continuous_const)).smul continuous_const)
  · intro j; exact continuous_const

theorem row_convex (j : Fin 4) : ConvexOn ℝ Set.univ (row j) := by
  fin_cases j
  · exact FPTrace.linear_convex convex_univ (-xc)
  · simpa [row,Pi.add_def,sub_eq_add_neg] using
      (FPTrace.linear_convex convex_univ xc).add_const (-1)
  · exact FPTrace.linear_convex convex_univ (-(yc 1))
  · simpa [row,Pi.add_def,sub_eq_add_neg] using
      (FPTrace.linear_convex convex_univ (yc 1)).add_const (-1)

theorem objective_convex : ConvexOn ℝ Set.univ data.f :=
  (FPTrace.linear_convex convex_univ xc).add
    (square_convex convex_univ (yc 1) (1/2))

theorem relaxation_iff (p : P) : p ∈ data.relaxation ↔ Box p := by
  constructor
  · rintro ⟨_,h⟩
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    change -p.1 0≤0 at h0
    change p.1 0-1≤0 at h1
    change -p.2 0≤0 at h2
    change p.2 0-1≤0 at h3
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · rintro ⟨hx0,hx1,hy0,hy1⟩
    refine ⟨Set.mem_univ _,?_⟩
    intro j; fin_cases j
    · change -p.1 0≤0; linarith
    · change p.1 0-1≤0; linarith
    · change -p.2 0≤0; linarith
    · change p.2 0-1≤0; linarith

theorem relaxation_eq : data.relaxation=Set.Icc (xy 0 0) (xy 1 1) := by
  ext p
  rw [relaxation_iff]
  change _ ↔ ((fun _ : Fin 1 => (0:ℝ))≤p.1 ∧
    (fun _ : Fin 1 => (0:ℝ))≤p.2) ∧
    (p.1≤(fun _ : Fin 1 => (1:ℝ)) ∧ p.2≤(fun _ : Fin 1 => (1:ℝ)))
  simp only [Box,Pi.le_def,Fin.forall_fin_one]
  tauto

theorem relaxation_compact : IsCompact data.relaxation := by
  rw [relaxation_eq]; exact isCompact_Icc

theorem analytic : Analytic data := by
  refine ⟨isClosed_univ,convex_univ,objective_convex,row_convex,?_,?_,?_,?_⟩
  · intro p _; exact objective_derivative p
  · intro j p _; exact row_derivative j p
  · exact relaxation_compact.isBounded
  · norm_num [Data.toUnbounded]

theorem initializer : IsMinimizer data.relaxation data.f seed := by
  refine ⟨(relaxation_iff _).mpr (by norm_num [Box,seed]),?_⟩
  intro p hp
  have hx := ((relaxation_iff p).mp hp).1
  change (0:ℝ)+((1/2:ℝ)-1/2)^2 ≤ p.1 0+(p.2 0-1/2)^2
  nlinarith [sq_nonneg (p.2 0-1/2)]

theorem seed_fractional : ¬Integral seed := by
  rintro ⟨q,hq⟩
  have h : (1/2:ℝ)=(q 0:ℝ) := congrFun hq 0
  have hl : (0:ℝ)<(q 0:ℝ) := by linarith
  have hu : (q 0:ℝ)<1 := by linarith
  have hl' : 0<q 0 := by exact_mod_cast hl
  have hu' : q 0<1 := by exact_mod_cast hu
  omega

theorem integer_box_cases (p : P) (hb : Box p) (hi : Integral p) :
    p.2 0=0 ∨ p.2 0=1 := by
  obtain ⟨k,hk⟩ := (scalar_integer p).mp hi
  have h := binary_value (show 0≤(k:ℝ) by linarith [hb.2.2.1])
    (show (k:ℝ)≤1 by linarith [hb.2.2.2])
  rcases h with rfl | rfl <;> simp [hk]

theorem integer_of_zero (p : P) (hp : p.2 0=0) : Integral p := by
  apply (scalar_integer p).mpr
  exact ⟨0,by simpa using hp⟩

theorem original_optimum : IsMinimizer data.original data.f optimum := by
  refine ⟨⟨(relaxation_iff _).mpr (by norm_num [Box,optimum]),
    integer_of_zero _ rfl⟩,?_⟩
  intro p hp
  have hb := (relaxation_iff p).mp hp.1
  rcases integer_box_cases p hb hp.2 with hy | hy <;>
    simp only [data,optimum,xy_fst,xy_snd,hy] <;> nlinarith [hb.1]

theorem chosen_original : chosen ∈ data.original :=
  ⟨(relaxation_iff _).mpr (by norm_num [Box,chosen]),integer_of_zero chosen rfl⟩

theorem bad_original : bad ∈ data.original :=
  ⟨(relaxation_iff _).mpr (by norm_num [Box,bad]),integer_of_zero bad rfl⟩

theorem source_values : data.f seed=0 ∧ data.f chosen=3/4 ∧
    data.f bad=5/4 ∧ data.f optimum=1/4 ∧ delta=1/10 := by
  norm_num [data,seed,chosen,bad,optimum,delta]

/-- Both true target coordinates equal zero; this is a successful (integral)
projection, not a failed fractional event in the accepted first-search driver. -/
def repeatedEvent : FPSearch.Event 1 1 := ⟨iv 0,bad⟩

def state (k : ℕ) : FPSearch.State 1 1 :=
  ⟨seed,List.replicate k repeatedEvent⟩

def incumbent : ℕ → Option P
  | 0 => none
  | _+1 => some bad

/-- Literal additive level. No normalized max(|UB|,1) factor is inserted. -/
def level (k : ℕ) : Option ℝ := (incumbent k).map (fun p => data.f p-delta)

def objectiveTangent (a p : P) : ℝ := data.f a+data.Df a (p-a)

def objectiveRows (k : ℕ) (z : P × ℝ) : Prop :=
  objectiveTangent seed z.1≤z.2 ∧
    ∀ e ∈ (state k).history, objectiveTangent e.projection z.1≤z.2

/-- The exact displayed background master: original constraint tangents,
integrality, all objective tangents, and the additive upper cutoff. Its projection
below still uses data.relaxation, not an objective-filtered feasible region. -/
def literalMaster (k : ℕ) : Set (P × ℝ) :=
  {z | z.1 ∈ FPSearch.master data .basic (state k) ∧
    objectiveRows k z ∧ Allows (level k) z.2}

def literalCost (k : ℕ) (z : P × ℝ) : ℝ :=
  FPSearch.masterCost (state k) z.1

def chosenMaster : ℕ → P × ℝ
  | 0 => (chosen,1/2)
  | _+1 => (chosen,3/4)

/-- The represented continuation collects integral projections. On this sequence,
strict-update and unconditional projected-assignment rules agree. The chosen MIP
point itself is feasible and improves the projected incumbent; collecting it as
an incumbent would change the cutoff and invalidate this repeated sequence. -/
def recordProjected (old : Option P) (p : P) : Option P :=
  match old with
  | none => some p
  | some q => if data.f p<data.f q then some p else some q

theorem initial_state : state 0=FPSearch.initialState seed := rfl

theorem state_recurrence (k : ℕ) :
    state (k+1)=FPSearch.append (state k) repeatedEvent := by
  simp [state,FPSearch.append,List.replicate_succ']

theorem incumbent_recurrence (k : ℕ) :
    incumbent (k+1)=recordProjected (incumbent k) bad := by
  cases k <;> simp [incumbent,recordProjected]

theorem reference_initial : (state 0).reference=seed := rfl

theorem reference_later (k : ℕ) : (state (k+1)).reference=bad := by
  simp [FPSearch.State.reference,state,List.replicate_succ',repeatedEvent]

theorem tangent_exact (a p : P) (j : Fin 4) :
    FPSearch.tangent data a j p=data.g j p := by
  fin_cases j <;> simp [FPSearch.tangent,data,row,rowD] <;> ring

theorem rows_iff (k : ℕ) (p : P) : FPSearch.Rows data (state k) p ↔ Box p := by
  constructor
  · intro h
    apply (relaxation_iff p).mp
    refine ⟨Set.mem_univ _,?_⟩
    intro j
    rw [←tangent_exact seed p j]
    exact h.1 j
  · intro hb
    have hg := ((relaxation_iff p).mpr hb).2
    constructor
    · intro j; rw [tangent_exact]; exact hg j
    · intro e he j hj; rw [tangent_exact]; exact hg j

theorem basic_master_iff (k : ℕ) (p : P) :
    p ∈ FPSearch.master data .basic (state k) ↔
      0≤p.1 0 ∧ p.1 0≤1 ∧ (p.2 0=0 ∨ p.2 0=1) := by
  constructor
  · intro hp
    have hb := (rows_iff k p).mp hp.2.2.1
    exact ⟨hb.1,hb.2.1,integer_box_cases p hb hp.2.1⟩
  · rintro ⟨hx0,hx1,hy⟩
    have hb : Box p := by
      rcases hy with h | h <;> exact ⟨hx0,hx1,by linarith,by linarith⟩
    have hi : Integral p := by
      rcases hy with h | h
      · exact integer_of_zero p h
      · apply (scalar_integer p).mpr
        exact ⟨1,by simpa using h⟩
    exact ⟨Set.mem_univ _,hi,(rows_iff k p).mpr hb,by simp⟩

theorem seed_tangent (p : P) : objectiveTangent seed p=p.1 0 := by
  simp [objectiveTangent,data,seed]

theorem bad_tangent (p : P) : objectiveTangent bad p=p.1 0-p.2 0+1/4 := by
  simp [objectiveTangent,data,bad]; ring

theorem objective_rows_initial (z : P × ℝ) :
    objectiveRows 0 z ↔ z.1.1 0≤z.2 := by
  simp [objectiveRows,state,seed_tangent]

theorem objective_rows_later (k : ℕ) (z : P × ℝ) :
    objectiveRows (k+1) z ↔
      z.1.1 0≤z.2 ∧ z.1.1 0-z.1.2 0+1/4≤z.2 := by
  constructor
  · rintro ⟨h0,h1⟩
    refine ⟨by simpa [seed_tangent] using h0,?_⟩
    have h := h1 repeatedEvent (by simp [state])
    simpa [repeatedEvent,bad_tangent] using h
  · rintro ⟨h0,h1⟩
    refine ⟨by simpa [seed_tangent] using h0,?_⟩
    intro e he
    have heq : e=repeatedEvent := (List.mem_replicate.mp he).2
    subst e
    simpa [repeatedEvent,bad_tangent] using h1

theorem master_initial_iff (z : P × ℝ) : z ∈ literalMaster 0 ↔
    (0≤z.1.1 0 ∧ z.1.1 0≤1 ∧ (z.1.2 0=0 ∨ z.1.2 0=1)) ∧
      z.1.1 0≤z.2 := by
  change (z.1 ∈ FPSearch.master data .basic (state 0) ∧
    objectiveRows 0 z ∧ Allows (level 0) z.2) ↔ _
  rw [basic_master_iff,objective_rows_initial]
  simp [level,incumbent,Allows]

theorem master_later_iff (k : ℕ) (z : P × ℝ) : z ∈ literalMaster (k+1) ↔
    (0≤z.1.1 0 ∧ z.1.1 0≤1 ∧ (z.1.2 0=0 ∨ z.1.2 0=1)) ∧
      (z.1.1 0≤z.2 ∧ z.1.1 0-z.1.2 0+1/4≤z.2) ∧ z.2≤23/20 := by
  change (z.1 ∈ FPSearch.master data .basic (state (k+1)) ∧
    objectiveRows (k+1) z ∧ Allows (level (k+1)) z.2) ↔ _
  rw [basic_master_iff,objective_rows_later]
  norm_num [level,incumbent,Allows,data,bad,delta]

theorem chosen_master_mem (k : ℕ) : chosenMaster k ∈ literalMaster k := by
  cases k with
  | zero => apply (master_initial_iff _).mpr; norm_num [chosenMaster,chosen]
  | succ k => apply (master_later_iff k _).mpr; norm_num [chosenMaster,chosen]

theorem chosen_master_minimum (k : ℕ) :
    IsMinimizer (literalMaster k) (literalCost k) (chosenMaster k) := by
  refine ⟨chosen_master_mem k,?_⟩
  intro z hz
  cases k with
  | zero =>
    have hy := ((master_initial_iff z).mp hz).1.2.2
    simp only [literalCost,FPSearch.masterCost,reference_initial,scalar_l1]
    rcases hy with h | h <;> norm_num [chosenMaster,chosen,seed,h]
  | succ k =>
    simp only [literalCost,FPSearch.masterCost,reference_later,scalar_l1]
    simp [chosenMaster,chosen,bad]

theorem target_eq (k : ℕ) : (chosenMaster k).1.2=intCast (iv 0) := by
  cases k <;> funext j <;> norm_num [chosenMaster,chosen,intCast,iv]

theorem projection_minimum :
    IsMinimizer data.relaxation (distance (iv 0)) bad := by
  refine ⟨(relaxation_iff _).mpr (by norm_num [Box,bad]),?_⟩
  intro p hp
  simpa [scalar_distance,bad] using sq_nonneg (p.2 0)

theorem projection_integral : Integral bad := integer_of_zero bad rfl

theorem active_seed : {j : Fin 4 | row j seed=0}={0} := by
  ext j; fin_cases j <;> norm_num [row,seed]

theorem active_bad : {j : Fin 4 | row j bad=0}={1,2} := by
  ext j; fin_cases j <;> norm_num [row,bad] <;> decide

theorem seed_full_licq : JointLICQ row (fun j => rowD j seed) seed := by
  change LinearIndepOn ℝ (fun j => rowD j seed) {j | row j seed=0}
  rw [active_seed,linearIndepOn_singleton_iff]
  intro h
  have he := congrArg (fun L : P →L[ℝ] ℝ => L (xy 1 0)) h
  norm_num [rowD] at he

theorem projection_full_licq : JointLICQ row (fun j => rowD j bad) bad := by
  change LinearIndepOn ℝ (fun j => rowD j bad) {j | row j bad=0}
  rw [active_bad,LinearIndepOn.pair_iff _ (by decide : (1:Fin 4)≠2)]
  intro c d h
  change c • xc + d • (-(yc 1)) = 0 at h
  have hx := congrArg (fun L : P →L[ℝ] ℝ => L (xy 1 0)) h
  have hy := congrArg (fun L : P →L[ℝ] ℝ => L (xy 0 1)) h
  norm_num at hx hy
  exact ⟨by linarith,by linarith⟩

/-- Source accuracy definition relative to every original feasible competitor. -/
def DeltaOptimal (p : P) : Prop :=
  p ∈ data.original ∧ ∀ q ∈ data.original, data.f p≤data.f q+delta

theorem chosen_not_delta_optimal : ¬DeltaOptimal chosen := by
  intro h
  have hh := h.2 optimum original_optimum.1
  norm_num [data,chosen,optimum,delta] at hh

theorem projection_not_delta_optimal : ¬DeltaOptimal bad := by
  intro h
  have hh := h.2 optimum original_optimum.1
  norm_num [data,bad,optimum,delta] at hh

/-- Positive delta really excludes the full incumbent from the master. -/
theorem incumbent_point_excluded (k : ℕ) (a : ℝ) : (bad,a) ∉ literalMaster (k+1) := by
  intro h
  have hh := (master_later_iff k (bad,a)).mp h
  have ht := hh.2.1.2
  have hc := hh.2.2
  norm_num [bad] at ht
  linarith

/-- The same integer block nevertheless remains available at a different full
point. No assertion that every point in that integer fiber has been excluded. -/
theorem incumbent_integer_block_retained (k : ℕ) :
    (chosenMaster (k+1)).1.2=bad.2 ∧ chosenMaster (k+1) ∈ literalMaster (k+1) :=
  ⟨rfl,chosen_master_mem (k+1)⟩

/-- Only exact concrete subproblem/update obligations, not an assumed progress
law or a general outer-loop stopping specification. -/
def ExactSourceStep (k : ℕ) : Prop :=
  IsMinimizer (literalMaster k) (literalCost k) (chosenMaster k) ∧
  (chosenMaster k).1.2=intCast (iv 0) ∧
  IsMinimizer data.relaxation (distance (iv 0)) bad ∧ Integral bad ∧
  state (k+1)=FPSearch.append (state k) repeatedEvent ∧
  incumbent (k+1)=recordProjected (incumbent k) bad

theorem all_exact_source_steps (k : ℕ) : ExactSourceStep k :=
  ⟨chosen_master_minimum k,target_eq k,projection_minimum,projection_integral,
    state_recurrence k,incumbent_recurrence k⟩

theorem every_finite_prefix (N : ℕ) :
    state 0=FPSearch.initialState seed ∧ incumbent 0=none ∧
      ∀ k<N, ExactSourceStep k :=
  ⟨initial_state,rfl,fun k _ => all_exact_source_steps k⟩

theorem no_selected_master_delta_optimal (k : ℕ) :
    ¬DeltaOptimal (chosenMaster k).1 := by
  cases k <;> exact chosen_not_delta_optimal

theorem no_recorded_incumbent_delta_optimal (k : ℕ) (p : P)
    (hp : incumbent k=some p) : ¬DeltaOptimal p := by
  cases k with
  | zero => simp [incumbent] at hp
  | succ k =>
    have he : bad=p := Option.some.inj hp
    rw [←he]
    exact projection_not_delta_optimal

/-- Complete concrete witness premises. This describes every exact repeated
source subproblem and collected incumbent; it does not assert a source-wide
return theorem for unstated background stopping rules. The continuation collects
projections only. Collecting feasible selected MIP points would change UB and is
outside this countercontrol, as are true-cutoff projections and polishing. -/
theorem concrete_stagnation_obligations :
    0<delta ∧ Analytic data ∧
    (Continuous data.Df ∧ ∀ j, Continuous (data.Dg j)) ∧ IsCompact data.relaxation ∧
    chosen ∈ data.original ∧ bad ∈ data.original ∧
    IsMinimizer data.relaxation data.f seed ∧ ¬Integral seed ∧
    IsMinimizer data.original data.f optimum ∧
    JointLICQ data.g (fun j => data.Dg j seed) seed ∧
    JointLICQ data.g (fun j => data.Dg j bad) bad ∧
    (∀ k, ExactSourceStep k) ∧
    (∀ k, ¬DeltaOptimal (chosenMaster k).1) ∧
    (∀ k p, incumbent k=some p → ¬DeltaOptimal p) :=
  ⟨delta_positive,analytic,derivative_continuity,relaxation_compact,chosen_original,bad_original,
    initializer,seed_fractional,original_optimum,
    seed_full_licq,projection_full_licq,all_exact_source_steps,
    no_selected_master_delta_optimal,no_recorded_incumbent_delta_optimal⟩

end Chapter03.FPBackgroundAdditive
