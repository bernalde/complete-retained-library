module

public import Chapter05PSQCSource
public import Chapter05QOAAvailability

@[expose] public section

/-! Literal structured-to-QOA adapter and the qualified mixed row history.
Only an OA seed and restoration constraints accompany the source-selected PSC
objective rows. Query attainment is derived from the retained compact model. -/
noncomputable section
open Set Chapter02 Chapter03.OAKKT
open scoped BigOperators
namespace Chapter05.PSQC.Mixed
variable {p q m l s nw nv : ℕ}
attribute [local instance] Classical.propDecidable

structure Context (p q m l s nw nv : ℕ) where
  data : PSCData p q m l s nw nv
  integers : Finset (IntVector m)
  relaxedY : Set (RealVector m)
  Y_eq : data.Y = {y | ∃ k ∈ integers, y = intCast k}
  W_nonempty : data.W.Nonempty
  V_nonempty : data.V.Nonempty
  W_compact : IsCompact data.W
  V_compact : IsCompact data.V
  r_convex : ConvexOn ℝ univ data.r
  t_convex : ∀ j, ConvexOn ℝ univ (data.t j)
  r_C2 : ContDiff ℝ 2 data.r
  t_C2 : ∀ j, ContDiff ℝ 2 (data.t j)
  fiber_slater : ∀ k ∈ integers, (data.fiberFeasible (intCast k)).Nonempty →
    ∃ x ∈ data.affineFiber (intCast k), ∀ j, data.fiberNonlinear (intCast k) j x < 0
  relaxed_compact : IsCompact relaxedY
  relaxed_convex : Convex ℝ relaxedY
  relaxed_contains : ∀ k ∈ integers, intCast k ∈ relaxedY

def pointW : Point (p+q) m →L[ℝ] RealVector p :=
  weightedX.comp (ContinuousLinearMap.fst ℝ _ _)
def pointV : Point (p+q) m →L[ℝ] RealVector q :=
  weightedV.comp (ContinuousLinearMap.fst ℝ _ _)
def pointY : Point (p+q) m →L[ℝ] RealVector m :=
  ContinuousLinearMap.snd ℝ _ _

def couplingLinear (c : Context p q m l s nw nv) (i : Fin s) :
    RealVector (p+q) →L[ℝ] ℝ :=
  (c.data.F i).comp weightedX + (c.data.G i).comp weightedV

def Context.qd (c : Context p q m l s nw nv) : QOA.Data (p+q) m l s where
  f z := c.data.objective (weightedX z.1) (weightedV z.1) z.2
  g j z := c.data.nonlinear j (weightedX z.1) (weightedV z.1) z.2
  X := {x | weightedX x ∈ c.data.W ∧ weightedV x ∈ c.data.V}
  Y := c.integers
  A i k := couplingLinear c i (Pi.single k 1)
  E i k := c.data.E i (Pi.single k 1)
  b := c.data.b
  relaxedY := c.relaxedY

@[simp] theorem objective_eq (c : Context p q m l s nw nv) (z : Point (p+q) m) :
    c.qd.f z = c.data.objective (weightedX z.1) (weightedV z.1) z.2 := rfl
@[simp] theorem nonlinear_eq (c : Context p q m l s nw nv) (j : Fin l)
    (z : Point (p+q) m) :
    c.qd.g j z = c.data.nonlinear j (weightedX z.1) (weightedV z.1) z.2 := rfl

theorem coupling_coordinates (c : Context p q m l s nw nv) (i : Fin s)
    (z : Point (p+q) m) :
    LinearForm (c.qd.A i) (c.qd.E i) z =
      c.data.F i (weightedX z.1) + c.data.G i (weightedV z.1) + c.data.E i z.2 := by
  change (∑ k, couplingLinear c i
    (Pi.single k 1) * z.1 k) + (∑ k, c.data.E i (Pi.single k 1) * z.2 k) = _
  rw [← pscRow_coordinates, ← pscRow_coordinates]
  rfl

theorem hardFiber_eq (c : Context p q m l s nw nv) (k : IntVector m) :
    c.qd.hardFiber k = c.data.affineFiber (intCast k) := by
  ext x
  rw [c.data.affineFiber_mem_iff]
  change ((weightedX x ∈ c.data.W ∧ weightedV x ∈ c.data.V) ∧
    ∀ i, LinearForm (c.qd.A i) (c.qd.E i) (x,intCast k) ≤ c.data.b i) ↔ _
  simp only [coupling_coordinates, PSCData.coupling]
  constructor
  · rintro ⟨⟨hw,hv⟩,hc⟩
    exact ⟨hw,hv,fun i => by have h := hc i; linarith⟩
  · rintro ⟨hw,hv,hc⟩
    exact ⟨⟨hw,hv⟩,fun i => by have h := hc i; linarith⟩

theorem feasibleFiber_eq (c : Context p q m l s nw nv) (k : IntVector m) :
    c.qd.feasibleFiber k = c.data.fiberFeasible (intCast k) := by
  simp only [QOA.Data.feasibleFiber, hardFiber_eq, PSCData.fiberFeasible]
  rfl

theorem fiberObjective_eq (c : Context p q m l s nw nv) (k : IntVector m) :
    c.qd.fiberObjective k = c.data.fiberObjective (intCast k) := rfl

theorem base_iff (c : Context p q m l s nw nv) (z : Point (p+q) m) :
    z ∈ c.qd.base ↔ c.data.base (weightedX z.1) (weightedV z.1) z.2 := by
  constructor
  · rintro ⟨k,hk,hy,hx⟩
    rw [hardFiber_eq,c.data.affineFiber_mem_iff] at hx
    exact ⟨hx.1,hx.2.1,by rw [c.Y_eq]; exact ⟨k,hk,hy⟩,by simpa only [hy] using hx.2.2⟩
  · rintro ⟨hw,hv,hy,hc⟩
    rw [c.Y_eq] at hy
    obtain ⟨k,hk,hy⟩ := hy
    refine ⟨k,hk,hy,?_⟩
    rw [hardFiber_eq,c.data.affineFiber_mem_iff]
    exact ⟨hw,hv,by simpa only [hy] using hc⟩

theorem original_iff (c : Context p q m l s nw nv) (z : Point (p+q) m) :
    z ∈ c.qd.original ↔ c.data.feasible (weightedX z.1) (weightedV z.1) z.2 := by
  simp only [QOA.Data.original,Set.mem_setOf_eq,base_iff,nonlinear_eq,PSCData.feasible]

theorem qoa_regularity (c : Context p q m l s nw nv) : QOA.Regularity c.qd := by
  have hw : Convex ℝ c.data.W := by
    intro x hx y hy a b ha hb hab i
    change c.data.Wrow i (a • x + b • y) ≤ _
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      a * c.data.Wrow i x + b * c.data.Wrow i y ≤
          a * c.data.Wbound i + b * c.data.Wbound i := add_le_add
        (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
      _ = c.data.Wbound i := by rw [← add_mul,hab,one_mul]
  have hv := v_convex c.data
  have hin : Continuous (fun z : RealVector p × RealVector q => weightedInsert z.1 z.2) := by
    apply continuous_pi
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [weightedInsert, Function.comp_def] using (continuous_apply j).comp continuous_fst
    · simpa [weightedInsert, Function.comp_def] using (continuous_apply j).comp continuous_snd
  have hx : c.qd.X = (fun z : RealVector p × RealVector q => weightedInsert z.1 z.2) ''
      (c.data.W ×ˢ c.data.V) := by
    ext x
    constructor
    · intro h
      exact ⟨(weightedX x,weightedV x),h,weightedInsert_project x⟩
    · rintro ⟨⟨w,v⟩,⟨hw,hv⟩,rfl⟩
      simpa only [Context.qd,Set.mem_setOf_eq,weightedX_insert,weightedV_insert] using And.intro hw hv
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    have hr := c.r_convex.2 (mem_univ (weightedV x.1)) (mem_univ (weightedV y.1)) ha hb hab
    change c.data.objective (weightedX (a • x + b • y).1) (weightedV (a • x + b • y).1)
      (a • x + b • y).2 ≤ a • c.data.objective _ _ _ + b • c.data.objective _ _ _
    simp only [PSCData.objective,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
      map_add,map_smul,smul_eq_mul] at hr ⊢
    linarith
  · exact (((c.data.a.comp (pointW (m:=m))).contDiff).add
      (c.r_C2.comp (pointV (p:=p) (m:=m)).contDiff)).add
      (c.data.c.comp (pointY (p:=p) (q:=q))).contDiff
  · intro j
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    have ht := (c.t_convex j).2 (mem_univ (weightedV x.1)) (mem_univ (weightedV y.1)) ha hb hab
    change c.data.nonlinear j (weightedX (a • x + b • y).1) (weightedV (a • x + b • y).1)
      (a • x + b • y).2 ≤ a • c.data.nonlinear j _ _ _ + b • c.data.nonlinear j _ _ _
    simp only [PSCData.nonlinear,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
      map_add,map_smul,smul_eq_mul] at ht ⊢
    linarith
  · intro j
    exact (((c.data.C j).comp (pointY (p:=p) (q:=q))).contDiff.add
      ((c.data.D j).comp (pointW (m:=m))).contDiff).add
      ((c.t_C2 j).comp (pointV (p:=p) (m:=m)).contDiff)
  · obtain ⟨w,hw⟩ := c.W_nonempty
    obtain ⟨v,hv⟩ := c.V_nonempty
    exact ⟨weightedInsert w v,by simpa only [Context.qd,Set.mem_setOf_eq,
      weightedX_insert,weightedV_insert] using And.intro hw hv⟩
  · rw [hx]
    exact (c.W_compact.prod c.V_compact).image hin
  · intro x hx y hy a b ha hb hab
    change weightedX (a • x + b • y) ∈ c.data.W ∧ weightedV (a • x + b • y) ∈ c.data.V
    simp only [map_add,map_smul]
    exact ⟨hw hx.1 hy.1 ha hb hab,hv hx.2 hy.2 ha hb hab⟩
  · intro k hk hne
    rw [feasibleFiber_eq] at hne
    obtain ⟨x,hx,hg⟩ := c.fiber_slater k hk hne
    exact ⟨x,by rwa [hardFiber_eq],hg⟩

theorem relaxation_regularity (c : Context p q m l s nw nv) :
    QOA.RelaxationRegularity c.qd :=
  ⟨c.relaxed_compact,c.relaxed_convex,c.relaxed_contains⟩

def sourceOfMinimum (c : Context p q m l s nw nv) (k : IntVector m)
    (hk : k ∈ c.integers) (x : RealVector (p+q))
    (hm : IsMinimizer (c.qd.feasibleFiber k) (c.qd.fiberObjective k) x) :
    PSCSourceAnchor c.data where
  w := weightedX x
  v := weightedV x
  y := intCast k
  Dr := fderiv ℝ c.data.r (weightedV x)
  Dt j := fderiv ℝ (c.data.t j) (weightedV x)
  y_mem := by rw [c.Y_eq]; exact ⟨k,hk,rfl⟩
  derivative_r := (c.r_C2.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  derivative_t j := ((c.t_C2 j).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  minimum := by simpa only [weightedInsert_project,← feasibleFiber_eq c k,
    ← fiberObjective_eq c k] using hm
  slater := c.fiber_slater k hk ⟨x,by simpa only [← feasibleFiber_eq c k] using hm.1⟩

structure FeasibleEvent (c : Context p q m l s nw nv) where
  target : IntVector m
  target_mem : target ∈ c.integers
  source : PSCSourceAnchor c.data
  source_y : source.y = intCast target
  scale : ℝ

def FeasibleEvent.entry {c : Context p q m l s nw nv} (e : FeasibleEvent c) :
    PSCEntry c.data := sourceEntry c.data c.r_convex c.t_convex e.source

def FeasibleEvent.Valid {c : Context p q m l s nw nv} (e : FeasibleEvent c) : Prop :=
  0 ≤ e.scale ∧ e.scale ≤ Quadratic.safeScale (lagrangian c.data e.entry.data)
    e.entry.data.v c.data.V

def FeasibleEvent.toQOA {c : Context p q m l s nw nv} (e : FeasibleEvent c) : QOA.Event c.qd :=
  ⟨e.target,e.target_mem,weightedInsert e.source.w e.source.v,none,0,fun _ => 0⟩

theorem FeasibleEvent.entry_matches {c : Context p q m l s nw nv} (e : FeasibleEvent c) :
    pscSourceMatches e.source e.entry :=
  source_entry_matches c.data c.r_convex c.t_convex e.source

@[simp] theorem FeasibleEvent.entry_w {c : Context p q m l s nw nv} (e : FeasibleEvent c) :
    e.entry.data.w = e.source.w := e.entry_matches.1
@[simp] theorem FeasibleEvent.entry_v {c : Context p q m l s nw nv} (e : FeasibleEvent c) :
    e.entry.data.v = e.source.v := e.entry_matches.2.1
@[simp] theorem FeasibleEvent.entry_y {c : Context p q m l s nw nv} (e : FeasibleEvent c) :
    e.entry.data.y = intCast e.target := e.entry_matches.2.2.1.trans e.source_y

@[simp] theorem FeasibleEvent.anchor_objective {c : Context p q m l s nw nv}
    (e : FeasibleEvent c) :
    c.qd.f e.toQOA.anchor = c.data.objective e.source.w e.source.v e.source.y := by
  simp only [objective_eq,QOA.Event.anchor,FeasibleEvent.toQOA,
    weightedX_insert,weightedV_insert,e.source_y]

structure RestorationEvent (c : Context p q m l s nw nv) where
  event : QOA.Event c.qd
  slack : RealVector l
  restoration_eq : event.restoration = some slack

inductive Event (c : Context p q m l s nw nv) where
  | feasible : FeasibleEvent c → Event c
  | restoration : RestorationEvent c → Event c

def Event.toQOA {c : Context p q m l s nw nv} : Event c → QOA.Event c.qd
  | .feasible e => e.toQOA
  | .restoration e => e.event

def Event.target {c : Context p q m l s nw nv} (e : Event c) : IntVector m := e.toQOA.target
def Event.anchor {c : Context p q m l s nw nv} (e : Event c) : Point (p+q) m := e.toQOA.anchor

def EventValid (c : Context p q m l s nw nv) : Event c → Prop
  | .feasible e => e.Valid
  | .restoration e => QOA.EventValid c.qd e.event

def HistoryValid (c : Context p q m l s nw nv) (H : List (Event c)) : Prop :=
  ∀ e ∈ H, EventValid c e

theorem feasible_toQOA_valid (c : Context p q m l s nw nv) (e : FeasibleEvent c) :
    QOA.EventValid c.qd e.toQOA := by
  refine ⟨QOA.zero_token_safe (qoa_regularity c) _,?_⟩
  change IsMinimizer (c.qd.feasibleFiber e.target) (c.qd.fiberObjective e.target)
    (weightedInsert e.source.w e.source.v)
  rw [feasibleFiber_eq,fiberObjective_eq,← e.source_y]
  exact e.source.minimum

theorem event_toQOA_valid {c : Context p q m l s nw nv} {e : Event c}
    (h : EventValid c e) : QOA.EventValid c.qd e.toQOA := by
  cases e with
  | feasible a => exact feasible_toQOA_valid c a
  | restoration a => exact h

theorem event_none_iff (c : Context p q m l s nw nv) (e : Event c) :
    e.toQOA.restoration = none ↔ ∃ a, e = .feasible a := by
  cases e with
  | feasible a => simp [Event.toQOA,FeasibleEvent.toQOA]
  | restoration a => simp [Event.toQOA,a.restoration_eq]

theorem event_exists (c : Context p q m l s nw nv) (k : IntVector m)
    (hk : k ∈ c.integers) (hh : (c.qd.hardFiber k).Nonempty) :
    ∃ e : Event c, e.target = k ∧ EventValid c e := by
  by_cases hf : (c.qd.feasibleFiber k).Nonempty
  · obtain ⟨x,hx⟩ := QOA.fixed_minimum_exists (qoa_regularity c) k hf
    let a : FeasibleEvent c := ⟨k,hk,sourceOfMinimum c k hk x hx,rfl,0⟩
    refine ⟨.feasible a,rfl,le_rfl,?_⟩
    exact (Quadratic.safeScale_bounds
      (lagrangian_convex c.data a.entry.data a.entry.kkt c.r_convex c.t_convex)
      (lagrangian_contDiff c.data a.entry.data c.r_C2 c.t_C2) _ _).1
  · obtain ⟨x,t,ht⟩ := QOA.restoration_minimum_exists (qoa_regularity c) k hh
    let e : QOA.Event c.qd := ⟨k,hk,x,some t,0,fun _ => 0⟩
    exact ⟨.restoration ⟨e,t,rfl⟩,rfl,QOA.zero_token_safe (qoa_regularity c) _,hf,ht⟩

def Event.constraintTokens {c : Context p q m l s nw nv} : Event c → List (QOA.Token (p+q) m l)
  | .feasible _ => []
  | .restoration e => [e.event.token]

def Event.objectiveRows {c : Context p q m l s nw nv} : Event c → List (Point (p+q) m → ℝ)
  | .feasible e => [fun z => fullCut c.data e.entry.data e.scale (weightedX z.1) (weightedV z.1) z.2]
  | .restoration _ => []

def constraintTokens {c : Context p q m l s nw nv} (seed : QOA.Token (p+q) m l)
    (H : List (Event c)) : List (QOA.Token (p+q) m l) :=
  seed :: H.flatMap Event.constraintTokens

def objectiveRows (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (H : List (Event c)) : List (Point (p+q) m → ℝ) :=
  Quadratic.cut c.qd.f seed.anchor seed.objectiveScale :: H.flatMap Event.objectiveRows

def master (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (H : List (Event c)) : Set (Point (p+q) m × ℝ) :=
  pscEnvelopeEpigraph (QOA.constraintBase (QOA.masterData c.qd) (constraintTokens seed H))
    (fun row => row) (objectiveRows c seed H)

theorem master_mem_iff (c : Context p q m l s nw nv) (seed : QOA.Token (p+q) m l)
    (H : List (Event c)) (z : Point (p+q) m × ℝ) :
    z ∈ master c seed H ↔ z.1 ∈ c.qd.base ∧
      Quadratic.cut c.qd.f seed.anchor seed.objectiveScale z.1 ≤ z.2 ∧
      (∀ j, Quadratic.cut (c.qd.g j) seed.anchor (seed.constraintScale j) z.1 ≤ 0) ∧
      (∀ e, Event.restoration e ∈ H → ∀ j, Quadratic.cut (c.qd.g j)
        e.event.anchor (e.event.constraintScale j) z.1 ≤ 0) ∧
      ∀ e, Event.feasible e ∈ H →
        fullCut c.data e.entry.data e.scale (weightedX z.1.1) (weightedV z.1.1) z.1.2 ≤ z.2 := by
  simp only [master,pscEnvelopeEpigraph,pscEnvelopeRows,QOA.constraintBase,
    QOA.masterData,Set.mem_setOf_eq,constraintTokens,objectiveRows,List.mem_cons,
    List.mem_flatMap,forall_eq_or_imp,forall_exists_index,and_imp]
  constructor
  · rintro ⟨⟨hb,hs,hrest⟩,ho,hfeas⟩
    refine ⟨hb,ho,hs,?_,?_⟩
    · intro e he j
      exact hrest e.event.token (.restoration e) he (by simp [Event.constraintTokens]) j
    · intro e he
      exact hfeas (fun z => fullCut c.data e.entry.data e.scale (weightedX z.1) (weightedV z.1) z.2)
        (.feasible e) he (by simp [Event.objectiveRows])
  · rintro ⟨hb,ho,hs,hr,hf⟩
    refine ⟨⟨hb,hs,?_⟩,ho,?_⟩
    · intro t e he ht j
      cases e with
      | feasible e => simp [Event.constraintTokens] at ht
      | restoration e =>
        simp only [Event.constraintTokens,List.mem_singleton] at ht
        subst t
        exact hr e he j
    · intro f e he hfmem
      cases e with
      | feasible e =>
        simp only [Event.objectiveRows,List.mem_singleton] at hfmem
        subst f
        exact hf e he
      | restoration e => simp [Event.objectiveRows] at hfmem

def pscPointOf (c : Context p q m l s nw nv) (z : Point (p+q) m × ℝ) : PSCPoint p q m :=
  ⟨weightedX z.1.1,weightedV z.1.1,z.1.2,z.2-c.data.a (weightedX z.1.1)-c.data.c z.1.2,z.2⟩

theorem pscPointOf_base (c : Context p q m l s nw nv) {z : Point (p+q) m × ℝ}
    (hz : z.1 ∈ c.qd.base) : pscPointBase c.data (pscPointOf c z) := by
  refine ⟨(base_iff c z.1).mp hz,?_⟩
  dsimp [pscPointOf]
  ring

end Chapter05.PSQC.Mixed
