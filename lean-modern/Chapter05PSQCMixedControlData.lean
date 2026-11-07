module

public import Chapter05PSQCControlData
public import Chapter05PSQCSource
public import Chapter05PSQCMixedModel

@[expose] public section

/-! The single rational mixed-return control. The structured model and selected
source entry are literal; no supplied multiplier vector replaces selection. -/
noncomputable section
open Set Chapter02 Chapter02PSCExamples Chapter03.OAKKT
open Chapter05.Quadratic
open scoped BigOperators
namespace Chapter05.PSQC.Mixed.Control

abbrev P := Point 1 1

def iv (y : ℤ) : IntVector 1 := fun _ => y
def pt (v y : ℝ) : P := (scalar v, scalar y)
def integers : Finset (IntVector 1) := {iv 0, iv 1}
def relaxedY : Set (RealVector 1) := Icc 0 1

def model : PSCData 0 1 1 1 0 0 2 :=
  { skeleton (-1) 1 (singleY false) with
    c := lin 1
    r := quadratic 1 (-1) (1/4)
    C := fun _ => lin (-1)
    t := fun _ => quadratic 1 0 (1/2) }

@[simp] theorem iv_apply (y : ℤ) (i : Fin 1) : iv y i = y := rfl
@[simp] theorem pt_v (v y : ℝ) (i : Fin 1) : (pt v y).1 i = v := rfl
@[simp] theorem pt_y (v y : ℝ) (i : Fin 1) : (pt v y).2 i = y := rfl
@[simp] theorem intCast_iv (y : ℤ) : intCast (iv y) = scalar y := rfl
@[simp] theorem projection_v (x : RealVector (0+1)) : weightedV (n:=0) x = x := by
  ext i
  simp [weightedV]
@[simp] theorem insertion_v (v : RealVector 1) : weightedInsert (0 : RealVector 0) v = v := by
  ext i
  fin_cases i
  rfl

theorem pt_eta (z : P) : pt (z.1 0) (z.2 0) = z := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

theorem mem_integers (k : IntVector 1) : k ∈ integers ↔ k = iv 0 ∨ k = iv 1 := by
  simp [integers]

theorem integers_card : integers.card = 2 := by
  have h : iv 0 ≠ iv 1 := by intro h; have := congrFun h 0; norm_num at this
  simp [integers, h]

theorem literal_Y : model.Y = {y | ∃ k ∈ integers, y = intCast k} := by
  ext y
  constructor
  · intro hy
    change y 0 = 0 ∨ y 0 = 1 at hy
    rcases hy with hy | hy
    · refine ⟨iv 0, by simp [integers], ?_⟩
      ext i; fin_cases i; simpa [scalar] using hy
    · refine ⟨iv 1, by simp [integers], ?_⟩
      ext i; fin_cases i; simpa [scalar] using hy
  · rintro ⟨k, hk, rfl⟩
    rcases (mem_integers k).mp hk with rfl | rfl <;>
      norm_num [model, skeleton, singleY, intCast, iv, scalar]

@[simp] theorem mem_W (w : RealVector 0) : w ∈ model.W := by
  intro i; exact Fin.elim0 i

theorem mem_V (v : RealVector 1) : v ∈ model.V ↔ -1 ≤ v 0 ∧ v 0 ≤ 1 := by
  constructor
  · intro h
    have h0 := h (0 : Fin 2)
    have h1 := h (1 : Fin 2)
    norm_num [model, skeleton, intervalRow, intervalBound, lin, scalarCoord] at h0 h1
    exact ⟨by linarith, h1⟩
  · intro h i
    fin_cases i <;> norm_num [model, skeleton, intervalRow, intervalBound, lin, scalarCoord] <;>
      linarith [h.1, h.2]

theorem V_interval : model.V = Icc (scalar (-1)) (scalar 1) := by
  ext v
  rw [mem_V]
  simp only [mem_Icc, Pi.le_def, Fin.forall_fin_one, scalar]

theorem W_compact : IsCompact model.W := by
  have he : model.W = {0} := by
    ext w
    simp only [Set.mem_singleton_iff]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => mem_W _⟩
  rw [he]
  exact isCompact_singleton

theorem V_compact : IsCompact model.V := by rw [V_interval]; exact isCompact_Icc

theorem objective_formula (w : RealVector 0) (v y : RealVector 1) :
    model.objective w v y = (v 0-1/2)^2+y 0 := by
  simp [PSCData.objective, model, skeleton, quadratic, lin, scalarCoord]
  ring

theorem nonlinear_formula (j : Fin 1) (w : RealVector 0) (v y : RealVector 1) :
    model.nonlinear j w v y = (v 0)^2+1/2-y 0 := by
  simp [PSCData.nonlinear, model, skeleton, quadratic, lin, scalarCoord]
  ring

theorem affineFiber_mem (y : RealVector 1) (x : RealVector 1) :
    x ∈ model.affineFiber y ↔ -1 ≤ x 0 ∧ x 0 ≤ 1 := by
  rw [PSCData.affineFiber_mem_iff]
  simp only [mem_W, projection_v, mem_V, true_and, Fin.isEmpty, IsEmpty.forall_iff, and_true]

theorem fiberFeasible_mem (y : RealVector 1) (x : RealVector 1) :
    x ∈ model.fiberFeasible y ↔
      (-1 ≤ x 0 ∧ x 0 ≤ 1) ∧ (x 0)^2+1/2-y 0 ≤ 0 := by
  simp [PSCData.fiberFeasible, affineFiber_mem, PSCData.fiberNonlinear,
    nonlinear_formula, projection_v]

theorem fiberObjective_formula (y : RealVector 1) (x : RealVector 1) :
    model.fiberObjective y x = (x 0-1/2)^2+y 0 := by
  simp [PSCData.fiberObjective, objective_formula, projection_v]

theorem zero_fiber_empty : ¬ (model.fiberFeasible (scalar 0)).Nonempty := by
  rintro ⟨x, hx⟩
  have h := ((fiberFeasible_mem _ _).mp hx).2
  simp only [scalar, sub_zero] at h
  nlinarith [sq_nonneg (x 0)]

theorem one_fiber_minimum : IsMinimizer (model.fiberFeasible (scalar 1))
    (model.fiberObjective (scalar 1)) (scalar (1/2)) := by
  refine ⟨by rw [fiberFeasible_mem]; norm_num [scalar], ?_⟩
  intro x hx
  simp only [fiberObjective_formula, scalar]
  nlinarith [sq_nonneg (x 0-1/2)]

theorem one_fiber_slater : ∃ x ∈ model.affineFiber (scalar 1),
    ∀ j, model.fiberNonlinear (scalar 1) j x < 0 := by
  refine ⟨scalar 0, by rw [affineFiber_mem]; norm_num [scalar], ?_⟩
  intro j
  norm_num [PSCData.fiberNonlinear, nonlinear_formula, projection_v, scalar]

theorem r_convex : ConvexOn ℝ univ model.r := quadratic_convex 1 (-1) (1/4) (by norm_num)
theorem t_convex (j : Fin 1) : ConvexOn ℝ univ (model.t j) :=
  quadratic_convex 1 0 (1/2) (by norm_num)
theorem r_C2 : ContDiff ℝ 2 model.r := PSQC.Control.quadratic_contDiff 1 (-1) (1/4)
theorem t_C2 (j : Fin 1) : ContDiff ℝ 2 (model.t j) :=
  PSQC.Control.quadratic_contDiff 1 0 (1/2)

def source : PSCSourceAnchor model where
  w := 0
  v := scalar (1/2)
  y := scalar 1
  Dr := (2*1*(1/2)+(-1) : ℝ) • scalarCoord
  Dt _ := (2*1*(1/2)+(0) : ℝ) • scalarCoord
  y_mem := singleY_one false
  derivative_r := quadratic_derivative 1 (-1) (1/4) (scalar (1/2))
  derivative_t _ := quadratic_derivative 1 0 (1/2) (scalar (1/2))
  minimum := by
    rw [insertion_v]
    exact one_fiber_minimum
  slater := one_fiber_slater

def selected : PSCEntry model := sourceEntry model r_convex t_convex source

theorem selected_matches : pscSourceMatches source selected :=
  source_entry_matches model r_convex t_convex source

@[simp] theorem selected_w : selected.data.w = 0 := selected_matches.1
@[simp] theorem selected_v : selected.data.v = scalar (1/2) := selected_matches.2.1
@[simp] theorem selected_y : selected.data.y = scalar 1 := selected_matches.2.2.1

theorem selected_lambda (j : Fin 1) : selected.data.lambda j = 0 := by
  have h := selected.kkt.nonlinear_complementarity j
  rw [nonlinear_formula, selected_v, selected_y] at h
  norm_num [scalar] at h
  linarith

theorem selected_nuV (i : Fin 2) : selected.data.nuV i = 0 := by
  have h := selected.kkt.v_complementarity i
  rw [selected_v] at h
  fin_cases i <;>
    norm_num [model, skeleton, intervalRow, intervalBound, lin, scalarCoord, scalar] at h ⊢ <;>
    linarith

theorem selected_normalV : selected.data.normalV = 0 := by
  simp [PSCAnchor.normalV, selected_nuV]

theorem selected_lagrangian : lagrangian model selected.data = quadratic 1 (-1) (5/4) := by
  funext v
  simp [lagrangian, selected_lambda, selected_y, objective_formula, scalar, quadratic]
  ring

theorem selected_positive_domain :
    (positiveCurvatureDomain (lagrangian model selected.data) selected.data.v model.V).Nonempty := by
  refine ⟨scalar 0, by rw [mem_V]; norm_num [scalar], ?_⟩
  rw [selected_lagrangian, PSQC.Control.quadratic_curvature, selected_v]
  norm_num [scalar]

theorem selected_safeScale :
    safeScale (lagrangian model selected.data) selected.data.v model.V = 1 := by
  rw [selected_lagrangian]
  exact PSQC.Control.quadratic_safeScale 1 (-1) (5/4) _ _
    (by simpa only [selected_lagrangian] using selected_positive_domain)

theorem selected_pscRow (w : RealVector 0) (v y : RealVector 1) :
    pscRow model selected.data w v y = 0 := by
  norm_num [pscRow, selected_lambda, selected_v, model, quadratic, scalar]

theorem selected_fullCut (w : RealVector 0) (v y : RealVector 1) :
    fullCut model selected.data 1 w v y = y 0+(v 0-1/2)^2 := by
  rw [fullCut, psqcRow, selected_pscRow, selected_lagrangian,
    PSQC.Control.quadratic_curvature, selected_v]
  simp [model, skeleton, lin, scalarCoord, scalar]

def context : Context 0 1 1 1 0 0 2 where
  data := model
  integers := integers
  relaxedY := relaxedY
  Y_eq := literal_Y
  W_nonempty := ⟨0, mem_W 0⟩
  V_nonempty := ⟨scalar 0, by rw [mem_V]; norm_num [scalar]⟩
  W_compact := W_compact
  V_compact := V_compact
  r_convex := r_convex
  t_convex := t_convex
  r_C2 := r_C2
  t_C2 := t_C2
  fiber_slater := by
    intro k hk hne
    rcases (mem_integers k).mp hk with rfl | rfl
    · exact (zero_fiber_empty (by simpa using hne)).elim
    · simpa using one_fiber_slater
  relaxed_compact := isCompact_Icc
  relaxed_convex := convex_Icc _ _
  relaxed_contains := by
    intro k hk
    rcases (mem_integers k).mp hk with rfl | rfl <;>
      norm_num [intCast, iv, scalar, relaxedY, mem_Icc, Pi.le_def]

abbrev data := context.qd

def objective (z : P) : ℝ := (z.1 0-1/2)^2+z.2 0
def constraint (z : P) : ℝ := (z.1 0)^2+1/2-z.2 0

theorem data_f : data.f = objective := by
  funext z
  exact (objective_formula _ _ _).trans (by simp [objective, projection_v])

theorem data_g (j : Fin 1) : data.g j = constraint := by
  funext z
  exact (nonlinear_formula j _ _ _).trans (by simp [constraint, projection_v])

theorem data_X_mem (x : RealVector 1) :
    x ∈ data.X ↔ -1 ≤ x 0 ∧ x 0 ≤ 1 := by
  change (weightedX (n:=0) (s:=1) x ∈ model.W ∧ weightedV (n:=0) (s:=1) x ∈ model.V) ↔ _
  simp only [projection_v, mem_W, true_and, mem_V]

theorem data_base_mem (z : P) :
    z ∈ data.base ↔ (-1 ≤ z.1 0 ∧ z.1 0 ≤ 1) ∧ (z.2 0=0 ∨ z.2 0=1) := by
  rw [base_iff]
  change model.base (weightedX (n:=0) (s:=1) z.1) (weightedV (n:=0) (s:=1) z.1) z.2 ↔ _
  rw [projection_v]
  simp only [PSCData.base, mem_W, mem_V, true_and, IsEmpty.forall_iff, and_true]
  rfl

theorem data_hard_mem (k : IntVector 1) (x : RealVector 1) :
    x ∈ data.hardFiber k ↔ -1 ≤ x 0 ∧ x 0 ≤ 1 := by
  rw [hardFiber_eq]
  exact affineFiber_mem _ _

theorem data_zero_empty : ¬ (data.feasibleFiber (iv 0)).Nonempty := by
  rw [feasibleFiber_eq, intCast_iv, Int.cast_zero]
  change ¬ (model.fiberFeasible (scalar 0)).Nonempty
  exact zero_fiber_empty

theorem data_one_minimum : IsMinimizer (data.feasibleFiber (iv 1))
    (data.fiberObjective (iv 1)) (scalar (1/2)) := by
  rw [feasibleFiber_eq, fiberObjective_eq, intCast_iv, Int.cast_one]
  change IsMinimizer (model.fiberFeasible (scalar 1))
    (model.fiberObjective (scalar 1)) (scalar (1/2))
  exact one_fiber_minimum

theorem activeY_eq : data.activeY = integers := by
  classical
  ext k
  simp only [QOA.Data.activeY, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hk
    exact ⟨hk, ⟨scalar 0, by rw [data_hard_mem]; norm_num [scalar]⟩⟩

theorem activeY_card : data.activeY.card = 2 := by rw [activeY_eq, integers_card]

def vc : P →L[ℝ] ℝ := scalarCoord.comp (ContinuousLinearMap.fst ℝ _ _)
def yc : P →L[ℝ] ℝ := scalarCoord.comp (ContinuousLinearMap.snd ℝ _ _)
def Dobjective (z : P) : P →L[ℝ] ℝ := (2*(z.1 0-1/2)) • vc + yc
def Dconstraint (z : P) : P →L[ℝ] ℝ := (2*z.1 0) • vc - yc

@[simp] theorem vc_apply (z : P) : vc z = z.1 0 := rfl
@[simp] theorem yc_apply (z : P) : yc z = z.2 0 := rfl

theorem square_derivative (L : P →L[ℝ] ℝ) (a : ℝ) (z : P) :
    HasFDerivAt (fun p => (L p-a)^2) ((2*(L z-a)) • L) z := by
  have hd := ((L.hasFDerivAt (x := z)).sub_const a).fun_mul
    ((L.hasFDerivAt (x := z)).sub_const a)
  simpa only [pow_two] using hd.congr_fderiv (show
    (L z-a) • L + (L z-a) • L = (2*(L z-a)) • L by
      apply ContinuousLinearMap.ext; intro p; simp; ring)

theorem objective_hasFDerivAt (z : P) : HasFDerivAt objective (Dobjective z) z := by
  change HasFDerivAt (fun z : P => (vc z-1/2)^2+yc z) (Dobjective z) z
  exact (square_derivative vc (1/2) z).fun_add
    (yc.hasFDerivAt (x := z))

theorem constraint_hasFDerivAt (z : P) : HasFDerivAt constraint (Dconstraint z) z := by
  unfold constraint Dconstraint
  simpa only [sub_zero, vc_apply, yc_apply] using ((square_derivative vc 0 z).add_const (1/2)).fun_sub
    (yc.hasFDerivAt (x := z))

@[simp] theorem objective_fderiv (z : P) : fderiv ℝ objective z = Dobjective z :=
  (objective_hasFDerivAt z).fderiv
@[simp] theorem constraint_fderiv (z : P) : fderiv ℝ constraint z = Dconstraint z :=
  (constraint_hasFDerivAt z).fderiv

def seed : P := pt (1/4) (9/16)
def firstTrial : P := pt (-7/8) 0
def secondTrial : P := pt 1 1
def optimum : P := pt (1/2) 1
def restorationAnchor : P := pt 0 0

theorem objective_seed : data.f seed = 5/8 := by rw [data_f]; norm_num [objective, seed]
theorem objective_optimum : data.f optimum = 1 := by rw [data_f]; norm_num [objective, optimum]
theorem constraint_secondTrial (j : Fin 1) : data.g j secondTrial = 1/2 := by
  rw [data_g]; norm_num [constraint, secondTrial]

theorem seed_objective_cut (z : P) : cut data.f seed 0 z = 3/16-z.1 0/2+z.2 0 := by
  rw [cut_zero, data_f]
  simp [tangent, seed, objective, Dobjective, vc, yc, scalarCoord, scalar, pt]
  ring

theorem seed_constraint_cut (j : Fin 1) (z : P) :
    cut (data.g j) seed 0 z = 7/16+z.1 0/2-z.2 0 := by
  rw [cut_zero, data_g]
  simp [tangent, seed, constraint, Dconstraint, vc, yc, scalarCoord, scalar, pt]
  ring

theorem restoration_constraint_cut (j : Fin 1) (z : P) :
    cut (data.g j) restorationAnchor 0 z = 1/2-z.2 0 := by
  rw [cut_zero, data_g]
  simp [tangent, restorationAnchor, constraint, Dconstraint, vc, yc, scalarCoord, scalar, pt]
  ring

theorem seed_relaxation_minimum : IsMinimizer data.relaxation data.f seed := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [data_X_mem]; norm_num [seed]
    · norm_num [context, Context.qd, relaxedY, seed, pt, scalar, mem_Icc, Pi.le_def]
    · intro i; exact Fin.elim0 i
    · intro j; rw [data_g]; norm_num [constraint, seed]
  · intro z hz
    have hg := hz.2.2.2 (0 : Fin 1)
    rw [data_g] at hg
    rw [objective_seed, data_f]
    unfold constraint at hg
    unfold objective
    nlinarith [sq_nonneg (z.1 0-1/4)]

theorem seed_fractional : ¬ ∃ k ∈ data.Y, seed.2 = intCast k := by
  rintro ⟨k, hk, h⟩
  rcases (mem_integers k).mp hk with rfl | rfl <;>
    have hh := congrFun h 0 <;> norm_num [seed, intCast, iv] at hh

def zeroToken (a : P) : QOA.Token 1 1 1 := ⟨a, 0, fun _ => 0⟩
def executionSeed : QOA.Token 1 1 1 := zeroToken seed

theorem zeroToken_safe (a : P) : (zeroToken a).Safe data :=
  QOA.zero_token_safe (qoa_regularity context) a

theorem restoration_minimum : IsMinimizer (data.restSet (iv 0)) data.restCost
    (weightedInsert (scalar 0) (scalar (1/2))) := by
  refine ⟨?_, ?_⟩
  · rw [QOA.restSet_insert_iff]
    refine ⟨by rw [data_hard_mem]; norm_num [scalar], ?_, ?_⟩ <;> intro j
    · change data.g j (scalar 0, intCast (iv 0)) ≤ scalar (1/2) j
      rw [data_g]; norm_num [constraint, scalar]
    · norm_num [scalar]
  · intro z hz
    have hrows := (weighted_lift_rows_iff
      (Fin.elim0 : Fin 0 → RealVector 1 → ℝ) (data.soft (iv 0)) z).mp hz.2
    have hs := hrows.2.1 (0 : Fin 1)
    change data.g 0 (weightedX z, intCast (iv 0)) ≤ weightedV z 0 at hs
    rw [data_g] at hs
    simp only [constraint, intCast_iv, scalar, sub_zero] at hs
    rw [QOA.restCost_insert]
    simp only [Fin.sum_univ_one, scalar, QOA.Data.restCost, weightedLiftObjective_apply,
      one_mul, Fin.sum_univ_one]
    nlinarith [sq_nonneg ((weightedX z) 0)]

def restorationQOA : QOA.Event data where
  target := iv 0
  target_mem := by simp [context, Context.qd, integers]
  x := scalar 0
  restoration := some (scalar (1/2))
  objectiveScale := 0
  constraintScale _ := 0

def restorationData : RestorationEvent context := ⟨restorationQOA, scalar (1/2), rfl⟩
def restorationEvent : Event context := .restoration restorationData

def feasibleData : FeasibleEvent context where
  target := iv 1
  target_mem := by simp [context, integers]
  source := source
  source_y := by simp [source]
  scale := 1

def feasibleEvent : Event context := .feasible feasibleData

theorem feasibleData_entry : feasibleData.entry = selected := rfl

theorem feasibleEvent_valid : EventValid context feasibleEvent := by
  change 0 ≤ (1 : ℝ) ∧ 1 ≤ safeScale (lagrangian model selected.data) selected.data.v model.V
  rw [selected_safeScale]
  norm_num

theorem restorationEvent_valid : EventValid context restorationEvent := by
  refine ⟨?_, data_zero_empty, restoration_minimum⟩
  simpa only [QOA.Event.token, restorationData, restorationQOA, QOA.Event.anchor,
    intCast_iv, Int.cast_zero, zeroToken, restorationAnchor, pt]
    using zeroToken_safe restorationAnchor

@[simp] theorem feasibleEvent_anchor : feasibleEvent.anchor = optimum := by
  apply Prod.ext
  · change weightedInsert (0 : RealVector 0) (scalar (1/2)) = scalar (1/2)
    exact insertion_v _
  · change intCast (iv 1) = scalar 1
    simp

@[simp] theorem restorationEvent_anchor : restorationEvent.anchor = restorationAnchor := by
  simp [Event.anchor, Event.toQOA, restorationEvent, restorationData, restorationQOA,
    QOA.Event.anchor, restorationAnchor, pt]
@[simp] theorem feasibleEvent_target : feasibleEvent.target = iv 1 := rfl
@[simp] theorem restorationEvent_target : restorationEvent.target = iv 0 := rfl

theorem feasible_fullCut (z : P) : fullCut context.data feasibleData.entry.data feasibleData.scale
    (weightedX (n:=0) (s:=1) z.1) (weightedV (n:=0) (s:=1) z.1) z.2 = z.2 0+(z.1 0-1/2)^2 := by
  exact (selected_fullCut _ _ _).trans (by simp only [projection_v])

theorem optimum_original : optimum ∈ data.original := by
  rw [← feasibleEvent_anchor]
  exact QOA.event_feasible (event_toQOA_valid feasibleEvent_valid) rfl

theorem secondTrial_not_original : secondTrial ∉ data.original := by
  intro h
  have hh := h.2 (0 : Fin 1)
  rw [constraint_secondTrial] at hh
  norm_num at hh

theorem secondTrial_ne_optimum : secondTrial ≠ optimum := by
  intro h
  have hh := congrArg (fun z : P => z.1 0) h
  norm_num [secondTrial, optimum] at hh

theorem restorationData_cut (j : Fin 1) (z : P) :
    cut (data.g j) restorationData.event.anchor (restorationData.event.constraintScale j) z =
      1/2-z.2 0 := by
  change cut (data.g j) (scalar 0, intCast (iv 0)) 0 z = _
  simpa only [restorationAnchor, pt, intCast_iv, Int.cast_zero]
    using restoration_constraint_cut j z

theorem master0_mem (z : P × ℝ) : z ∈ master context executionSeed [] ↔
    ((-1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1) ∧ (z.1.2 0=0 ∨ z.1.2 0=1)) ∧
      3/16-z.1.1 0/2+z.1.2 0 ≤ z.2 ∧ 7/16+z.1.1 0/2-z.1.2 0 ≤ 0 := by
  rw [master_mem_iff, data_base_mem]
  simp only [executionSeed, zeroToken, seed_objective_cut, seed_constraint_cut,
    data_base_mem, List.not_mem_nil, IsEmpty.forall_iff, forall_const, false_implies,
    forall_true_iff, and_true]

theorem master1_mem (z : P × ℝ) :
    z ∈ master context executionSeed [restorationEvent] ↔
    ((-1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1) ∧ (z.1.2 0=0 ∨ z.1.2 0=1)) ∧
      3/16-z.1.1 0/2+z.1.2 0 ≤ z.2 ∧
      7/16+z.1.1 0/2-z.1.2 0 ≤ 0 ∧ 1/2-z.1.2 0 ≤ 0 := by
  rw [master_mem_iff, data_base_mem]
  simp only [restorationEvent, List.mem_singleton, Event.restoration.injEq,
    reduceCtorEq, forall_eq, false_implies, forall_true_iff, and_true,
    executionSeed, zeroToken, seed_objective_cut, seed_constraint_cut,
    data_base_mem, restorationData_cut, forall_const]

theorem master2_mem (z : P × ℝ) :
    z ∈ master context executionSeed [restorationEvent, feasibleEvent] ↔
    ((-1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1) ∧ (z.1.2 0=0 ∨ z.1.2 0=1)) ∧
      3/16-z.1.1 0/2+z.1.2 0 ≤ z.2 ∧
      7/16+z.1.1 0/2-z.1.2 0 ≤ 0 ∧ 1/2-z.1.2 0 ≤ 0 ∧
      z.1.2 0+(z.1.1 0-1/2)^2 ≤ z.2 := by
  rw [master_mem_iff, data_base_mem]
  simp only [restorationEvent, feasibleEvent, List.mem_cons, List.mem_singleton,
    Event.restoration.injEq, Event.feasible.injEq, List.not_mem_nil, reduceCtorEq, or_false, false_or,
    forall_eq, executionSeed, zeroToken, seed_objective_cut, seed_constraint_cut,
    data_base_mem, restorationData_cut, feasible_fullCut, forall_const]

theorem first_master_minimum :
    IsMinimizer (master context executionSeed []) Prod.snd (firstTrial, 5/8) := by
  refine ⟨by rw [master0_mem]; norm_num [firstTrial], ?_⟩
  intro z hz
  obtain ⟨⟨⟨hvlo, hvhi⟩, hy⟩, ho, hg⟩ := (master0_mem z).mp hz
  rcases hy with hy | hy <;> simp only [hy] at ho hg <;> dsimp <;> linarith

theorem second_master_minimum :
    IsMinimizer (master context executionSeed [restorationEvent]) Prod.snd (secondTrial, 11/16) := by
  refine ⟨by rw [master1_mem]; norm_num [secondTrial], ?_⟩
  intro z hz
  obtain ⟨⟨⟨hvlo, hvhi⟩, hy⟩, ho, hg, hr⟩ := (master1_mem z).mp hz
  rcases hy with hy | hy <;> simp only [hy] at ho hg hr <;> dsimp <;> linarith

theorem third_master_minimum :
    IsMinimizer (master context executionSeed [restorationEvent, feasibleEvent]) Prod.snd
      (optimum, 1) := by
  refine ⟨by rw [master2_mem]; norm_num [optimum], ?_⟩
  intro z hz
  obtain ⟨⟨⟨hvlo, hvhi⟩, hy⟩, ho, hg, hr, hp⟩ := (master2_mem z).mp hz
  rcases hy with hy | hy
  · simp only [hy] at hr
    norm_num at hr
  · simp only [hy] at hp
    dsimp
    nlinarith [sq_nonneg (z.1.1 0-1/2)]

end Chapter05.PSQC.Mixed.Control
