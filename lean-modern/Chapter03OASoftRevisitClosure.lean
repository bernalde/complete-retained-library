module

public import Chapter03OASoftMasterBounds
public import Chapter03OAExecHistory
public import Chapter03OAKKTControlConvexity

@[expose] public section

/-! Qualified local successful-revisit closure for the actual constraint-slack
master. Coverage and multiplier domination concern this retained event and this
history; their persistence through later histories is not asserted. Hard coverage
is actual entailment from the hard domain on the event fiber. No hard-master
membership, optimizer existence, solver behavior or finite return is inferred. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OASoftMaster

variable {n m l r k : ℕ}

/-- Selected soft-supported rows use distinct actual occurrences. Matching is
an equality of the full affine tangent functions, allowing an earlier identical
affine row as well as the current nonlinear row. Other supported rows must be
entailed by the actual hard domain on this fiber. -/
def SupportedCoverage {d : ModelData n m l r} {f : Point n m → ℝ}
    {x : RealVector n} {y : RealVector m} (K : FixedKKT d f x y)
    (c : TangentFamily n m l k) (w : Occurrence c → ℝ)
    (S : Finset (Fin l)) (occ : S → Occurrence c) : Prop :=
  Function.Injective occ ∧
  (∀ j : S, ∀ q : Point n m,
    d.g j (x,y) + K.Dg j (q-(x,y)) =
      d.g (occ j).1.2 (c.origin (occ j).1.1) +
        c.derivative (occ j).1.1 (occ j).1.2 (q-c.origin (occ j).1.1)) ∧
  (∀ j : S, 1000 * K.lambda j ≤ w (occ j)) ∧
  ∀ j, j ∉ S → K.lambda j ≠ 0 → ∀ q ∈ d.linearRegion, q.2 = y →
    d.g j (x,y) + K.Dg j (q-(x,y)) ≤ 0

/-- Exactly the nonzero-multiplier nonlinear rows of the retained event. -/
def nonlinearSupport {d : ModelData n m l r} {f : Point n m → ℝ}
    {x : RealVector n} {y : RealVector m} (K : FixedKKT d f x y)
    (N : Set (Fin l)) : Finset (Fin l) := by
  classical
  exact Finset.univ.filter (fun j => j ∈ N ∧ K.lambda j ≠ 0)

/-- Complementarity makes a supported nonlinear row active, hence selected by
literal weak residual selection at the retained current occurrence. -/
def currentOccurrence {d : ModelData n m l r} {f : Point n m → ℝ}
    {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {y : RealVector m}
    (H : History d f N c df x y) (K : FixedKKT d f x y)
    (j : nonlinearSupport K N) : Occurrence c := by
  classical
  refine ⟨(H.current,j),?_⟩
  have hj : (j : Fin l) ∈ N ∧ K.lambda j ≠ 0 := by
    exact (Finset.mem_filter.mp j.2).2
  rw [H.current_selected]
  exact ⟨hj.1,le_of_eq (K.supported_residual j hj.2).symm⟩

/-- Source specialization: current selected nonlinear rows are automatically
matched injectively. The separate affine hard-coverage requirement remains an
explicit sufficient assumption; A1–A3 do not establish it. -/
theorem current_occurrence_coverage {d : ModelData n m l r}
    {f : Point n m → ℝ} {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {y : RealVector m}
    (H : History d f N c df x y) (K : FixedKKT d f x y)
    (w : Occurrence c → ℝ)
    (hw : ∀ j : nonlinearSupport K N, 1000 * K.lambda j ≤ w (currentOccurrence H K j))
    (hh : ∀ j, j ∉ N → K.lambda j ≠ 0 → ∀ q ∈ d.linearRegion, q.2 = y →
      d.g j (x,y) + K.Dg j (q-(x,y)) ≤ 0) :
    SupportedCoverage K c w (nonlinearSupport K N) (currentOccurrence H K) := by
  classical
  refine ⟨?_,?_,hw,?_⟩
  · intro u v huv
    apply Subtype.ext
    exact congrArg (fun a : Occurrence c => a.1.2) huv
  · intro j q
    change _ = d.g j (c.origin H.current) + c.derivative H.current j (q-c.origin H.current)
    rw [H.current_origin,H.current_g_derivative_eq K.Dg K.derivative_g]
  · intro j hj hn q hq hy
    apply hh j ?_ hn q hq hy
    intro hN
    exact hj (by simp [nonlinearSupport,hN,hn])

/-- Injectivity prevents counting one occurrence's penalty more than once. -/
theorem occurrence_sum_le_penalty {c : TangentFamily n m l k}
    {w : Occurrence c → ℝ} {z : Candidate c} {S : Finset (Fin l)}
    (occ : S → Occurrence c) (hinj : Function.Injective occ)
    (hw : ∀ a, 0 ≤ w a) (hs : ∀ a, 0 ≤ z.2.2 a) :
    (∑ j : S, w (occ j) * z.2.2 (occ j)) ≤ penalty w z := by
  classical
  rw [← Finset.sum_image (f := fun a => w a * z.2.2 a) (s := Finset.univ)
    (g := occ) (fun a _ b _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => mul_nonneg (hw a) (hs a))

/-- KKT stationarity/complementarity and actual master rows derive the weighted
comparison; the desired lower inequality is not an assumption. -/
theorem supported_weighted_kkt_comparison {d : ModelData n m l r}
    {f : Point n m → ℝ} {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {y : RealVector m}
    (H : History d f N c df x y) (K : FixedKKT d f x y)
    {w : Occurrence c → ℝ} {S : Finset (Fin l)} {occ : S → Occurrence c}
    (hc : SupportedCoverage K c w S occ) (hw : ∀ a, 0 ≤ w a)
    {keep : Point n m → Prop} {z : Candidate c}
    (hz : z ∈ master d f c df keep) (hy : z.1.2 = y) :
    f (x,y) ≤ z.2.1 + penalty w z / 1000 := by
  classical
  have hpoint : z.1 = (z.1.1,y) := Prod.ext rfl hy
  have hs (j : S) : 1000 * (K.lambda j * K.Dg j (z.1-(x,y))) ≤
      w (occ j) * z.2.2 (occ j) := by
    have ht := hz.2.2.2.2.2 (occ j)
    rw [← hc.2.1 j z.1] at ht
    have hm := mul_le_mul_of_nonneg_left ht (K.lambda_nonneg j)
    have hdom := mul_le_mul_of_nonneg_right (hc.2.2.1 j) (hz.2.2.2.1 (occ j))
    have hcompl := K.soft_compl j
    change K.lambda j * d.g j (x,y) = 0 at hcompl
    nlinarith
  have ho : (∑ j : {j : Fin l // j ∉ S},
      K.lambda j * K.Dg j (z.1-(x,y))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : K.lambda j = 0
    · simp [hj]
    · have ht := hc.2.2.2 j j.2 hj z.1 hz.1 hy
      have hm := mul_le_mul_of_nonneg_left ht (K.lambda_nonneg j)
      have hcompl := K.soft_compl j
      change K.lambda j * d.g j (x,y) = 0 at hcompl
      nlinarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hs j)
  rw [← Finset.mul_sum] at hsum
  have himage := occurrence_sum_le_penalty occ hc.1 hw hz.2.2.2.1
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j : Fin l => j ∈ S)
    (fun j => K.lambda j * K.Dg j (z.1-(x,y)))
  have hfint : Subtype.fintype (fun j : Fin l => j ∈ S) = Finset.Subtype.fintype S :=
    Subsingleton.elim _ _
  rw [hfint] at hsplit
  have hsoft : 1000 * (∑ j, K.lambda j * K.Dg j (z.1-(x,y))) ≤ penalty w z := by
    rw [← hsplit]
    calc
      _ ≤ 1000 * (∑ j : S, K.lambda j * K.Dg j (z.1-(x,y))) :=
        mul_le_mul_of_nonneg_left (add_le_of_nonpos_right ho) (by norm_num)
      _ ≤ penalty w z := hsum.trans himage
  have hhard : (∑ i, K.mu i * fiberLinearRow d i (z.1.1-x)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have ht : hard d y i x + fiberLinearRow d i (z.1.1-x) ≤ 0 := by
      rw [hard_tangent]
      have h := hz.1 i
      rw [hpoint] at h
      exact sub_nonpos.mpr h
    have hm := mul_le_mul_of_nonneg_left ht (K.mu_nonneg i)
    nlinarith [K.hard_compl i]
  have hstat := congrArg (fun D : RealVector n →L[ℝ] ℝ => D (z.1.1-x))
    K.stationarity
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply] at hstat
  have hf := hz.2.2.2.2.1 H.current
  rw [H.current_origin, H.current_f_derivative_eq K.Df K.derivative_f] at hf
  rw [hpoint, derivative_fiber_action] at hf
  rw [hpoint] at hsoft
  simp only [derivative_fiber_action] at hsoft
  linarith

/-- One headline: an actual minimizing return to a successful retained event
closes the intended stripped-alpha gap when this history covers that event's
KKT-supported rows with factor1000 weights. Convexity, derivative/domain guards,
actual valid history and preservation of the anchor justify zero-slack embedding.
Zero total weighted penalty does not assert that every slack vanishes. -/
theorem supported_soft_revisit_closure (d : OAExec.Data n m l r)
    (a : OAExec.Analytic d) (seed : Point n m) (H : List (OAExec.Event d))
    (hH : OAExec.ValidHistory d seed H) (i : Fin H.length)
    (hn : (H.get i).restoration = none)
    (K : FixedKKT d.model d.f (H.get i).x (intCast (H.get i).target))
    (keep : Point n m → Prop) (hk : keep (H.get i).anchor)
    (w : Occurrence (OAExec.family d seed H) → ℝ) (hw : ∀ j, 0 ≤ w j)
    (S : Finset (Fin l)) (occ : S → Occurrence (OAExec.family d seed H))
    (hc : SupportedCoverage K (OAExec.family d seed H) w S occ)
    (z : Candidate (OAExec.family d seed H))
    (hm : IsMinimizer (master d.model d.f (OAExec.family d seed H)
      (OAExec.familyDf d seed H) (fun p => OAExec.noGoods H p ∧ keep p)) (cost w) z)
    (hy : z.1.2 = intCast (H.get i).target) :
    (∀ q ∈ master d.model d.f (OAExec.family d seed H) (OAExec.familyDf d seed H)
        (fun p => OAExec.noGoods H p ∧ keep p),
      q.1.2 = intCast (H.get i).target →
      d.f (H.get i).anchor ≤ q.2.1 + penalty w q / 1000) ∧
    penalty w z = 0 ∧ z.2.1 = d.f (H.get i).anchor ∧
    cost w z = d.f (H.get i).anchor ∧
    ∀ incumbent : ℝ, incumbent ≤ d.f (H.get i).anchor → ¬ z.2.1 < incumbent := by
  have he := hH.2 (H.get i) (List.get_mem H i)
  have hp := OAExec.event_feasible he hn
  have hepi := OAExec.original_epigraph_mem a hH hp
  have hem := embed_of_hard_epigraph (keep := fun p => OAExec.noGoods H p ∧ keep p)
    hepi.1 ⟨hepi.2,hk⟩
  have hub := hm.2 _ hem
  rw [cost_embed] at hub
  have hlo : ∀ q ∈ master d.model d.f (OAExec.family d seed H)
      (OAExec.familyDf d seed H) (fun p => OAExec.noGoods H p ∧ keep p),
      q.1.2 = intCast (H.get i).target →
      d.f (H.get i).anchor ≤ q.2.1 + penalty w q / 1000 := by
    intro q hq hqy
    exact supported_weighted_kkt_comparison (OAExec.eventHistory d a seed H hH i)
      K hc hw hq hqy
  have hlow := hlo z hm.1 hy
  have hnonneg := penalty_nonneg hw hm.1
  have hzero : penalty w z = 0 := by
    change z.2.1 + penalty w z ≤ d.f (H.get i).anchor at hub
    linarith! only [hub,hlow,hnonneg]
  have halpha : z.2.1 = d.f (H.get i).anchor := by
    simp only [cost,hzero,add_zero] at hub
    rw [hzero,zero_div,add_zero] at hlow
    exact le_antisymm hub hlow
  refine ⟨hlo,hzero,halpha,?_,?_⟩
  · simp [cost,hzero,halpha]
  · intro incumbent hi
    rw [halpha]
    exact not_lt.mpr hi

/-- Uncounted implication: when extra keep preserves every original feasible
point, the cost equality obtained on a revisit identifies an original global
minimum. This uses objective-preserving embedding, not a master-equivalence claim. -/
theorem original_minimum_of_revisit_equality (d : OAExec.Data n m l r)
    (a : OAExec.Analytic d) (seed : Point n m) (H : List (OAExec.Event d))
    (hH : OAExec.ValidHistory d seed H) (e : OAExec.Event d) (he : e ∈ H)
    (hn : e.restoration = none) (keep : Point n m → Prop)
    (hkeep : ∀ p ∈ d.original, keep p)
    (w : Occurrence (OAExec.family d seed H) → ℝ)
    (z : Candidate (OAExec.family d seed H))
    (hm : IsMinimizer (master d.model d.f (OAExec.family d seed H)
      (OAExec.familyDf d seed H) (fun p => OAExec.noGoods H p ∧ keep p)) (cost w) z)
    (heq : cost w z = d.f e.anchor) : IsMinimizer d.original d.f e.anchor := by
  refine ⟨OAExec.event_feasible (hH.2 e he) hn,?_⟩
  intro p hp
  have h := OAExec.original_epigraph_mem a hH hp
  have hem := embed_of_hard_epigraph
    (keep := fun q => OAExec.noGoods H q ∧ keep q) h.1 ⟨h.2,hkeep p hp⟩
  calc
    d.f e.anchor = cost w z := heq.symm
    _ ≤ cost w (embed d.f (OAExec.family d seed H) p) := hm.2 _ hem
    _ = d.f p := cost_embed w p

namespace RevisitControl
open Chapter02DICOPTExamples Chapter03.OAKKT.Controls

/-- A nonempty local control; its seed is already integral. It does not exhibit
a driver initialization that would continue past the integral-seed test. -/
def objective (p : P) : ℝ := -p.1 0

def spec : OAExec.Data 1 1 3 0 where
  model := activeModel
  f := objective
  Df _ := -cx
  Dg := activeDg
  domain := Set.univ

theorem objective_derivative (p : P) : HasFDerivAt objective (-cx) p :=
  cx.hasFDerivAt.neg

def analytic : OAExec.Analytic spec where
  convex_f := by
    change ConvexOn ℝ Set.univ (fun p : P => -p.1 0)
    simpa using affine_convex (-1) 0 0
  convex_g := active_convex
  original_domain := Set.subset_univ _
  derivative_f p _ := objective_derivative p
  derivative_g p _ j := active_derivative p j

def event : OAExec.Event spec where
  target _ := 1
  target_mem := by intro i; norm_num [spec,activeModel,scalar]
  x := scalar 1
  restoration := none

theorem cast_target : intCast event.target = scalar 1 := by
  ext i; norm_num [intCast,event,scalar]

theorem anchor_eq : event.anchor = pt 1 1 := by
  change (scalar 1,intCast event.target) = _
  rw [cast_target]; rfl

def certificate : FixedKKT activeModel objective event.x (intCast event.target) where
  Df := -cx
  Dg := activeDg event.anchor
  lambda := ![1/2,0,0]
  mu := Fin.elim0
  primal := by
    refine ⟨active_hard _,?_⟩
    intro j
    rw [cast_target]
    fin_cases j <;> norm_num [event,activeModel,positiveG,scalar]
  derivative_f := objective_derivative _
  derivative_g := active_derivative _
  lambda_nonneg := by intro j; fin_cases j <;> norm_num
  mu_nonneg i := Fin.elim0 i
  soft_compl := by
    intro j
    rw [cast_target]
    fin_cases j <;> norm_num [soft,event,activeModel,positiveG,scalar]
  hard_compl i := Fin.elim0 i
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    norm_num [restrict_apply,activeDg,anchor_eq,positiveDg,pt,scalar,Fin.sum_univ_succ]
    ring

theorem fixed_minimum : IsMinimizer (fiber activeModel (intCast event.target))
    (fiberObjective objective (intCast event.target)) event.x := by
  refine ⟨certificate.primal,?_⟩
  intro x hx
  have hg := hx.2 0
  rw [cast_target] at hg ⊢
  have hsq : (x 0)^2 ≤ 1 := by simpa [activeModel,positiveG,scalar] using hg
  change -(event.x 0) ≤ -(x 0)
  norm_num [event,scalar]
  nlinarith [sq_nonneg (x 0-1)]

theorem event_valid : OAExec.EventValid spec event :=
  ⟨Set.mem_univ _,fixed_minimum,⟨certificate⟩⟩

def history : List (OAExec.Event spec) := [event]
def seed : P := event.anchor

theorem seed_minimum : IsMinimizer spec.relaxation objective seed := by
  refine ⟨?_,?_⟩
  · change event.anchor ∈ activeModel.relaxationOn Set.univ
    rw [anchor_eq,active_relaxation]
    norm_num [pt,scalar]
  · intro p hp
    obtain ⟨hg,h0,h1⟩ := (active_relaxation p).mp hp
    change objective event.anchor ≤ objective p
    rw [anchor_eq]
    norm_num [objective,pt,scalar]
    nlinarith [sq_nonneg (p.1 0-1)]

theorem history_valid : OAExec.ValidHistory spec seed history := by
  refine ⟨Set.mem_univ _,?_⟩
  intro e he
  have heq : e = event := by simpa [history] using he
  simpa [heq] using event_valid

theorem row_nonlinear : ¬ AffineRow (activeModel.g 0) := by
  rintro ⟨ax,ay,b,he⟩
  have h0 := he (pt 0 0)
  have h1 := he (pt 1 0)
  have hn := he (pt (-1) 0)
  norm_num [activeModel,positiveG,LinearForm,pt,scalar,Fin.sum_univ_one] at h0 h1 hn
  linarith

theorem other_rows_affine (j : Fin 3) (hj : j ≠ 0) : AffineRow (activeModel.g j) := by
  fin_cases j
  · exact (hj rfl).elim
  · refine ⟨scalar 0,scalar (-1),0,?_⟩
    intro p; simp [activeModel,LinearForm,scalar,Fin.sum_univ_one]
  · refine ⟨scalar 0,scalar 1,1,?_⟩
    intro p; simp [activeModel,LinearForm,scalar,Fin.sum_univ_one]

theorem selected_exact : spec.selected event.anchor = {0} := by
  ext j
  constructor
  · intro hj
    by_contra hn
    exact hj.1 (other_rows_affine j (by simpa using hn))
  · intro hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    exact ⟨row_nonlinear,by norm_num [spec,anchor_eq,activeModel,positiveG,pt,scalar]⟩

def tangents := OAExec.family spec seed history
def objectiveTangents := OAExec.familyDf spec seed history

def current : Occurrence tangents := ⟨(1,0),by
  change 0 ∈ spec.selected event.anchor
  rw [selected_exact]; simp⟩

/-- Both copies of row0 receive500; zero-weight bound-row slacks are allowed. -/
def weight (a : Occurrence tangents) : ℝ := if a.1.2 = 0 then 500 else 0

theorem weight_nonneg (a : Occurrence tangents) : 0 ≤ weight a := by
  unfold weight; split <;> norm_num

def retainedHistory := OAExec.eventHistory spec analytic seed history history_valid (0 : Fin 1)

theorem current_coverage : SupportedCoverage certificate tangents weight
    (nonlinearSupport certificate spec.nonlinear) (currentOccurrence retainedHistory certificate) := by
  classical
  apply current_occurrence_coverage retainedHistory certificate weight
  · intro j
    have hj : certificate.lambda j ≠ 0 := by
      have h : (j : Fin 3) ∈ spec.nonlinear ∧ certificate.lambda j ≠ 0 := by
        exact (Finset.mem_filter.mp j.2).2
      exact h.2
    have hj0 : (j : Fin 3) = 0 := by
      have hn : ∀ a : Fin 3, certificate.lambda a ≠ 0 → a = 0 := by
        intro a; fin_cases a <;> norm_num [certificate]
      exact hn j hj
    norm_num [currentOccurrence,weight,hj0,certificate]
  · intro j hj hn q hq hy
    have hj0 : j = 0 := by
      fin_cases j <;> simp_all [certificate]
    subst j
    exact (hj row_nonlinear).elim

def softMaster := master activeModel objective tangents objectiveTangents
  (fun p => OAExec.noGoods history p ∧ True)
def chosen : Candidate tangents := embed objective tangents event.anchor

theorem chosen_feasible : chosen ∈ softMaster := by
  have hp := OAExec.event_feasible event_valid (by rfl)
  have he := OAExec.original_epigraph_mem analytic history_valid hp
  exact embed_of_hard_epigraph he.1 ⟨he.2,trivial⟩

theorem objective_tangent (p q : P) : objective p + (-cx) (q-p) = objective q := by
  simp [objective]
  ring

theorem chosen_minimum : IsMinimizer softMaster (cost weight) chosen := by
  classical
  refine ⟨chosen_feasible,?_⟩
  intro q hq
  have hf := hq.2.2.2.2.1 0
  change objective seed + (-cx) (q.1-seed) ≤ q.2.1 at hf
  rw [objective_tangent] at hf
  have hg := hq.2.2.2.2.2 current
  change positiveG event.anchor + positiveDg event.anchor (q.1-event.anchor) ≤ q.2.2 current at hg
  rw [anchor_eq,active_current_row_tangent] at hg
  obtain ⟨y,hy,hqy⟩ := hq.2.1
  have hy1 : q.1.2 0 ≤ 1 := by
    rw [hqy]
    exact (hy 0).2
  have hs := hq.2.2.2.1 current
  have hp : 500 * q.2.2 current ≤ penalty weight q := by
    have h := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) =>
      mul_nonneg (weight_nonneg a) (hq.2.2.2.1 a)) (Finset.mem_univ current)
    simpa [penalty,weight,current] using h
  rw [show chosen = embed objective tangents event.anchor from rfl,cost_embed,anchor_eq]
  change -(1:ℝ) ≤ q.2.1 + penalty weight q
  change -q.1.1 0 ≤ q.2.1 at hf
  nlinarith

/-- Actual application of the headline and current-source-row specialization,
with positive nonlinear multiplier and global penalized optimizer. -/
theorem nonvacuity : OAExec.Analytic spec ∧
    IsMinimizer spec.relaxation objective seed ∧
    OAExec.ValidHistory spec seed history ∧ OAExec.EventValid spec event ∧
    spec.selected event.anchor = {0} ∧ certificate.lambda 0 = (1/2:ℝ) ∧
    weight current = 1000 * |certificate.lambda 0| ∧
    IsMinimizer softMaster (cost weight) chosen ∧
    penalty weight chosen = 0 ∧ chosen.2.1 = objective event.anchor ∧
    cost weight chosen = objective event.anchor ∧
    IsMinimizer spec.original objective event.anchor ∧
    ∀ incumbent : ℝ, incumbent ≤ objective event.anchor → ¬ chosen.2.1 < incumbent := by
  have h := supported_soft_revisit_closure spec analytic seed history history_valid
    (0 : Fin 1) (by rfl) certificate (fun _ => True) trivial weight weight_nonneg
    (nonlinearSupport certificate spec.nonlinear) (currentOccurrence retainedHistory certificate)
    current_coverage chosen chosen_minimum (by rfl)
  refine ⟨analytic,seed_minimum,history_valid,event_valid,selected_exact,?_,?_,
    chosen_minimum,h.2.1,h.2.2.1,h.2.2.2.1,?_,h.2.2.2.2⟩
  · norm_num [certificate]
  · change 500 = 1000 * |(1/2:ℝ)|
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  · exact original_minimum_of_revisit_equality spec analytic seed history history_valid
      event (by simp [history]) (by rfl) (fun _ => True) (fun _ _ => trivial)
      weight chosen chosen_minimum h.2.2.2.1

end RevisitControl
end Chapter03.OASoftMaster
