module

public import Chapter03FPSearchBonamiMaster
public import Chapter03FPSearchFinite

@[expose] public section

/-! Held Bonami2006 Example3. The printed equality t-u=0 is represented by
the two actual affine rows t-u<=0 and u-t<=0. Rows 0,1,2 of Examples1/2
remain in their original order and the reverse residual is added as row3.
This equality encoding is disclosed; no projection LICQ claim is made. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch.BonamiInfeasible

abbrev P := Bonami.P
def row : Fin 4 → P → ℝ := ![
  Bonami.row 0, Bonami.row 1, Bonami.row 2, fun p => p.1 0-p.2 0]
def rowD (j : Fin 4) (p : P) : P →L[ℝ] ℝ := ![
  Bonami.rowD 0 p, Bonami.rowD 1 p, Bonami.rowD 2 p, Bonami.xc 0-Bonami.yc] j
def data : Data 2 1 4 := ⟨Bonami.base,fun _ => 0,row,fun _ => 0,rowD⟩

theorem equality_encoding (p : P) :
    row 1 p ≤ 0 ∧ row 3 p ≤ 0 ↔ p.2 0=p.1 0 := by
  change p.2 0-p.1 0 ≤ 0 ∧ p.1 0-p.2 0 ≤ 0 ↔ p.2 0=p.1 0
  constructor <;> intro h
  · exact le_antisymm (sub_nonpos.mp h.1) (sub_nonpos.mp h.2)
  · simp [h]

theorem row_derivative (j : Fin 4) (p : P) :
    HasFDerivAt (row j) (rowD j p) p := by
  fin_cases j
  · exact Bonami.row_derivative 0 p
  · exact Bonami.row_derivative 1 p
  · exact Bonami.row_derivative 2 p
  · exact (Bonami.xc 0).hasFDerivAt.sub Bonami.yc.hasFDerivAt

theorem row_convex (j : Fin 4) : ConvexOn ℝ Bonami.base (row j) := by
  fin_cases j
  · exact Bonami.row_convex 0
  · exact Bonami.row_convex 1
  · exact Bonami.row_convex 2
  · exact FPTrace.linear_convex Bonami.base_convex (Bonami.xc 0-Bonami.yc)

theorem relaxation_iff (p : P) : p ∈ data.relaxation ↔ p=Bonami.seed := by
  constructor
  · rintro ⟨hb,hg⟩
    have hold : p ∈ Bonami.base ∧ ∀ j, Bonami.row j p ≤ 0 := by
      refine ⟨hb,?_⟩
      intro j
      fin_cases j
      · exact hg 0
      · exact hg 1
      · exact hg 2
    obtain ⟨hu,hv,_,ht⟩ := (Bonami.feasible_iff p).mp hold
    have heq := (equality_encoding p).mp ⟨hg 1,hg 3⟩
    apply Prod.ext
    · funext i
      fin_cases i
      · simpa [Bonami.seed,Bonami.point] using hu
      · simpa [Bonami.seed,Bonami.point] using hv
    · funext i
      fin_cases i
      simpa [Bonami.seed,Bonami.point,hu] using heq
  · rintro rfl
    refine ⟨Bonami.seed_feasible.1,?_⟩
    intro j
    fin_cases j
    · exact Bonami.seed_feasible.2 0
    · exact Bonami.seed_feasible.2 1
    · exact Bonami.seed_feasible.2 2
    · norm_num [data,row,Bonami.seed,Bonami.point]

theorem relaxation_singleton : data.relaxation={Bonami.seed} := by
  ext p
  exact relaxation_iff p

theorem analytic : Analytic data := by
  refine ⟨Bonami.base_closed,Bonami.base_convex,
    convexOn_const 0 Bonami.base_convex,row_convex,?_,?_,?_,le_rfl⟩
  · intro p hp
    exact hasFDerivAt_const 0 p
  · intro j p hp
    exact row_derivative j p
  · change Bornology.IsBounded data.relaxation
    rw [relaxation_singleton]
    exact isCompact_singleton.isBounded

theorem seed_feasible : Bonami.seed ∈ data.relaxation := (relaxation_iff _).mpr rfl
theorem seed_fractional : ¬Integral Bonami.seed := Bonami.seed_fractional
theorem seed_minimum : IsMinimizer data.relaxation data.f Bonami.seed :=
  ⟨seed_feasible,fun _ _ => le_rfl⟩
theorem projection_minimum (q : IntVector 1) :
    IsMinimizer data.relaxation (distance q) Bonami.seed := by
  refine ⟨seed_feasible,?_⟩
  intro p hp
  rw [(relaxation_iff p).mp hp]

theorem original_empty : ¬data.original.Nonempty := by
  rintro ⟨p,hp,hi⟩
  rw [(relaxation_iff p).mp hp] at hi
  exact Bonami.seed_fractional hi

def start : State 2 1 := initialState Bonami.seed
def first : State 2 1 := append start Bonami.failed
def failedZero : Event 2 1 := ⟨Bonami.integer 0,Bonami.seed⟩
def second : State 2 1 := append first failedZero
def masterZero : P := Bonami.point 0 0 0

theorem initial_rows_iff (p : P) :
    (∀ j, tangent data Bonami.seed j p ≤ 0) ↔ p.1 1=0 ∧ p.2 0=p.1 0 := by
  have hrev : tangent data Bonami.seed 3 p = p.1 0-p.2 0 := by
    change (Bonami.seed.1 0-Bonami.seed.2 0) +
      (Bonami.xc 0-Bonami.yc) (p-Bonami.seed) = p.1 0-p.2 0
    simp [Bonami.seed,Bonami.point,ContinuousLinearMap.sub_apply,map_sub]
  constructor
  · intro h
    have hold : ∀ j, tangent Bonami.data Bonami.seed j p ≤ 0 := by
      intro j
      fin_cases j
      · exact h 0
      · exact h 1
      · exact h 2
    obtain ⟨hv,ht⟩ := (Bonami.initial_rows_iff p).mp hold
    have hr := h 3
    rw [hrev] at hr
    exact ⟨hv,by linarith⟩
  · rintro ⟨hv,ht⟩
    have hold := (Bonami.initial_rows_iff p).mpr ⟨hv,ht.le⟩
    intro j
    fin_cases j
    · exact hold 0
    · exact hold 1
    · exact hold 2
    · change tangent data Bonami.seed 3 p ≤ 0
      rw [hrev]
      linarith

theorem rows_at_seed_history (s : State 2 1) (hs : s.seed=Bonami.seed)
    (hh : ∀ e ∈ s.history, e.projection=Bonami.seed) (p : P) :
    Rows data s p ↔ p.1 1=0 ∧ p.2 0=p.1 0 := by
  constructor
  · intro h
    apply (initial_rows_iff p).mp
    simpa [hs] using h.1
  · intro h
    have hi := (initial_rows_iff p).mpr h
    refine ⟨by simpa [hs] using hi,?_⟩
    intro e he j _
    simpa [hh e he] using hi j

theorem rows_start (p : P) : Rows data start p ↔ p.1 1=0 ∧ p.2 0=p.1 0 :=
  rows_at_seed_history start rfl (by simp [start,initialState]) p
theorem rows_first (p : P) : Rows data first p ↔ p.1 1=0 ∧ p.2 0=p.1 0 := by
  apply rows_at_seed_history first rfl
  intro e he
  have heq : e=Bonami.failed := by simpa [first,start,append,initialState] using he
  subst e
  rfl

theorem master_binary {mode : Mode} {s : State 2 1} {p : P}
    (hp : p ∈ master data mode s) : p.2 0=0 ∨ p.2 0=1 := by
  obtain ⟨q,hq⟩ := hp.2.1
  have he : p.2 0=(q 0:ℝ) := congrFun hq 0
  have hb : 0 ≤ (q 0:ℝ) ∧ (q 0:ℝ) ≤ 1 := by
    simpa only [data,Bonami.base,Set.mem_setOf_eq,he] using hp.1
  rcases FPUnboundedControls.binary_value hb.1 hb.2 with h|h <;> simp [he,h]

theorem start_master_one :
    Bonami.masterOne ∈ master data .enhanced start := by
  refine ⟨by norm_num [data,Bonami.base,Bonami.masterOne,Bonami.point],
    ⟨Bonami.integer 1,by funext i; norm_num [Bonami.masterOne,Bonami.point,intCast,Bonami.integer]⟩,
    (rows_start _).mpr ?_,?_⟩
  · norm_num [Bonami.masterOne,Bonami.point]
  · simp [start,initialState]

theorem reference_start : start.reference=Bonami.seed := rfl
theorem reference_first : first.reference=Bonami.seed := by
  simp [State.reference,first,start,append,initialState,Bonami.failed]

theorem start_master_minimum :
    IsMinimizer (master data .enhanced start) (masterCost start) Bonami.masterOne := by
  refine ⟨start_master_one,?_⟩
  intro p hp
  have hi := master_binary hp
  simp only [masterCost,reference_start,FPUnboundedControls.scalar_l1]
  rcases hi with h|h <;> norm_num [Bonami.masterOne,Bonami.seed,Bonami.point,h]

theorem first_master_iff (p : P) : p ∈ master data .enhanced first ↔
    p.2 0=0 ∧ p.1 1=0 ∧ p.1 0=0 := by
  constructor
  · intro hp
    obtain ⟨hv,ht⟩ := (rows_first p).mp hp.2.2.1
    have hn := hp.2.2.2 rfl Bonami.failed (by simp [first,start,append,initialState])
    rw [Bonami.failed_normal] at hn
    have h0 : p.2 0=0 := by
      rcases master_binary hp with h|h
      · exact h
      · rw [h] at hn
        norm_num at hn
    exact ⟨h0,hv,by linarith⟩
  · rintro ⟨ht,hv,hu⟩
    refine ⟨by simp [data,Bonami.base,ht],?_,(rows_first p).mpr ⟨hv,by linarith⟩,?_⟩
    · refine ⟨Bonami.integer 0,?_⟩
      funext i
      fin_cases i
      simpa [intCast,Bonami.integer] using ht
    · intro _ e he
      have heq : e=Bonami.failed := by simpa [first,start,append,initialState] using he
      subst e
      rw [Bonami.failed_normal,ht]
      norm_num

theorem first_master_minimum :
    IsMinimizer (master data .enhanced first) (masterCost first) masterZero := by
  refine ⟨(first_master_iff masterZero).mpr (by norm_num [masterZero,Bonami.point]),?_⟩
  intro p hp
  have ht := ((first_master_iff p).mp hp).1
  simp only [masterCost,reference_first,FPUnboundedControls.scalar_l1]
  simp [masterZero,Bonami.point,ht]

theorem zero_normal (p : P) : failedZero.normal p=(1/2:ℝ)*(p.2 0-1/2) := by
  simp [Event.normal,failedZero,Bonami.seed,Bonami.point,Bonami.integer,
    Chapter03.yMap,intY,intCast,PiLp.inner_apply,Fin.sum_univ_one,real_inner_eq_re_inner]
  ring

theorem second_master_empty : ¬(master data .enhanced second).Nonempty := by
  rintro ⟨p,hp⟩
  have hfirst := master_append_subset data .enhanced first failedZero hp
  have ht := ((first_master_iff p).mp hfirst).1
  have hn := hp.2.2.2 rfl failedZero (by simp [second,append])
  rw [zero_normal,ht] at hn
  norm_num at hn

def stepOne : Step data .enhanced start :=
  ⟨Bonami.masterOne,Bonami.integer 1,Bonami.seed,start_master_minimum,
    by funext i; norm_num [Bonami.masterOne,Bonami.point,intCast,Bonami.integer],
    projection_minimum _⟩
def stepZero : Step data .enhanced first :=
  ⟨masterZero,Bonami.integer 0,Bonami.seed,first_master_minimum,
    by funext i; norm_num [masterZero,Bonami.point,intCast,Bonami.integer],
    projection_minimum _⟩

theorem first_ne_start : first ≠ start := by
  intro h
  have he := congrArg (fun s : State 2 1 => s.history.length) h
  norm_num [first,start,append,initialState] at he
theorem second_ne_start : second ≠ start := by
  intro h
  have he := congrArg (fun s : State 2 1 => s.history.length) h
  norm_num [second,first,start,append,initialState] at he
theorem second_ne_first : second ≠ first := by
  intro h
  have he := congrArg (fun s : State 2 1 => s.history.length) h
  norm_num [second,first,start,append,initialState] at he

def selector : Selector data .enhanced := by
  classical
  intro s hs
  by_cases h0 : s=start
  · subst s
    exact .project stepOne
  · by_cases h1 : s=first
    · subst s
      exact .project stepZero
    · by_cases h2 : s=second
      · subst s
        exact .empty second_master_empty
      · exact Classical.choice (decision_nonempty data analytic .enhanced s hs)

theorem selector_start (hs : start.seed ∈ data.relaxation) :
    selector start hs = .project stepOne := by simp [selector]
theorem selector_first (hs : first.seed ∈ data.relaxation) :
    selector first hs = .project stepZero := by simp [selector,first_ne_start]
theorem selector_second (hs : second.seed ∈ data.relaxation) :
    selector second hs = .empty second_master_empty := by
  simp [selector,second_ne_start,second_ne_first]

def output : LoopOutput 2 1 := (terminalOutput second .emptyMaster).bump.bump

theorem run_exact : run data .enhanced selector 3 start seed_feasible = some output := by
  rw [run_fractional data .enhanced selector 2 start seed_feasible stepOne
    (selector_start _) seed_fractional]
  change (run data .enhanced selector 2 first seed_feasible).map LoopOutput.bump = some output
  rw [run_fractional data .enhanced selector 1 first seed_feasible stepZero
    (selector_first _) seed_fractional]
  change ((run data .enhanced selector 1 second seed_feasible).map LoopOutput.bump).map
    LoopOutput.bump = some output
  rw [run_empty data .enhanced selector 0 second seed_feasible second_master_empty
    (selector_second _)]
  rfl

theorem procedure_exact : procedureWithFuel data .enhanced (.minimum Bonami.seed seed_minimum)
    selector 3 = some (.loop output) := by
  simpa only [start,procedureWithFuel,seed_fractional,if_false,Option.map_some] using
    congrArg (Option.map Outcome.loop) run_exact

theorem actual_repeated_projection_and_counts :
    stepOne.projection=stepZero.projection ∧ ¬Integral stepOne.projection ∧
    stepOne.target=Bonami.integer 1 ∧ stepZero.target=Bonami.integer 0 ∧
    output.reason=.emptyMaster ∧ output.masters=3 ∧ output.projections=2 ∧
    output.failures=2 ∧ ¬data.original.Nonempty :=
  ⟨rfl,seed_fractional,rfl,rfl,rfl,rfl,rfl,rfl,original_empty⟩

end Chapter03.FPSearch.BonamiInfeasible
