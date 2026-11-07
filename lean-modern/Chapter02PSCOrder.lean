module

public import Chapter02PSCModel
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Qualified QG-(5)/Grossmann-PL feasible-anchor comparison.
The literal retained domains and matched anchors govern every master.
No numerical solver, source-journal identity, or PSC termination is asserted. -/

noncomputable section
open scoped BigOperators
namespace Chapter02

variable {p q m l s nw nv : ℕ}

structure PSCPoint (p q m : ℕ) where
  w : RealVector p
  v : RealVector q
  y : RealVector m
  beta : ℝ
  alpha : ℝ

def pscRow (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) : ℝ :=
  d.r e.v + ∑ j, e.lambda j * d.nonlinear j w e.v y -
    ∑ i, e.mu i * d.G i (v-e.v)

def pscGBDRow (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (y : RealVector m) : ℝ :=
  d.objective e.w e.v e.y + d.c (y-e.y) +
    ∑ j, e.lambda j * d.C j (y-e.y) +
    ∑ i, e.mu i * d.E i (y-e.y)

def pscObjectiveTangent (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (v : RealVector q) : ℝ := d.r e.v + e.Dr (v-e.v)

def pscConstraintTangent (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (j : Fin l) (w : RealVector p) (v : RealVector q)
    (y : RealVector m) : ℝ :=
  d.nonlinear j w e.v y + e.Dt j (v-e.v)

def pscOARows (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) (beta : ℝ) : Prop :=
  pscObjectiveTangent d e v ≤ beta ∧
    ∀ j, pscConstraintTangent d e j w v y ≤ 0

def pscPointBase (d : PSCData p q m l s nw nv) (z : PSCPoint p q m) : Prop :=
  d.base z.w z.v z.y ∧ z.alpha = d.a z.w + d.c z.y + z.beta

def pscOAMaster (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    Set (PSCPoint p q m) :=
  {z | pscPointBase d z ∧ ∀ e ∈ H, pscOARows d e.data z.w z.v z.y z.beta}

def pscMaster (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    Set (PSCPoint p q m) :=
  {z | pscPointBase d z ∧ ∀ e ∈ H, pscRow d e.data z.w z.v z.y ≤ z.beta}

def pscGBDMaster (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    Set (RealVector m × ℝ) :=
  {ya | ya.1 ∈ d.Y ∧ ∀ e ∈ H, pscGBDRow d e.data ya.1 ≤ ya.2}

def pscProject (S : Set (PSCPoint p q m)) : Set (RealVector m × ℝ) :=
  {ya | ∃ z ∈ S, z.y = ya.1 ∧ z.alpha = ya.2}

def pscOriginalPoint (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) : PSCPoint p q m :=
  ⟨w,v,y,d.r v,d.objective w v y⟩

def pscBetaZeroMaster (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    Set (PSCPoint p q m) := {z ∈ pscMaster d H | z.beta = 0}

theorem psc_oa_surrogate_identity (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    pscObjectiveTangent d e v - pscRow d e w v y =
      -(∑ j, e.lambda j * pscConstraintTangent d e j w v y) -
        e.normalV (v-e.v) := by
  have hs := hk.stationarity_v (v-e.v)
  simp only [pscObjectiveTangent,pscRow,pscConstraintTangent,mul_add,
    Finset.sum_add_distrib]
  linarith

theorem psc_oa_implies_row (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) (beta : ℝ)
    (hv : v ∈ d.V) (hoa : pscOARows d e w v y beta) :
    pscRow d e w v y ≤ beta := by
  have hi := psc_oa_surrogate_identity d e hk w v y
  have hn := hk.normalV_nonpos hv
  have hs : (∑ j, e.lambda j * pscConstraintTangent d e j w v y) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos
      (hk.lambda_nonneg j) (hoa.2 j)
  have ho := hoa.1
  linarith

theorem psc_nonlinear_sum_difference (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e) (w : RealVector p) (y : RealVector m) :
    (∑ j, e.lambda j * d.nonlinear j w e.v y) =
      (∑ j, e.lambda j * d.C j (y-e.y)) +
      ∑ j, e.lambda j * d.D j (w-e.w) := by
  calc
    _ = ∑ j, (e.lambda j * d.nonlinear j e.w e.v e.y +
        e.lambda j * d.C j (y-e.y) + e.lambda j * d.D j (w-e.w)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [PSCData.nonlinear,map_sub]
      ring
    _ = _ := by simp only [hk.nonlinear_complementarity,zero_add,
      Finset.sum_add_distrib]

theorem psc_coupling_sum_difference (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    (∑ i, e.mu i * d.coupling i w v y) =
      (∑ i, e.mu i * d.E i (y-e.y)) +
      (∑ i, e.mu i * d.F i (w-e.w)) +
      ∑ i, e.mu i * d.G i (v-e.v) := by
  calc
    _ = ∑ i, (e.mu i * d.coupling i e.w e.v e.y +
        e.mu i * d.E i (y-e.y) + e.mu i * d.F i (w-e.w) +
        e.mu i * d.G i (v-e.v)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [PSCData.coupling,map_sub]
      ring
    _ = _ := by simp only [hk.coupling_complementarity,zero_add,
      Finset.sum_add_distrib]

theorem psc_gbd_surrogate_identity (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    d.a w + d.c y + pscRow d e w v y - pscGBDRow d e y =
      -(∑ i, e.mu i * d.coupling i w v y) - e.normalW (w-e.w) := by
  have hn := psc_nonlinear_sum_difference d e hk w y
  have hc := psc_coupling_sum_difference d e hk w v y
  have hs := hk.stationarity_w (w-e.w)
  simp only [map_sub] at hn hc hs
  simp only [pscRow,pscGBDRow,PSCData.objective,map_sub]
  linarith

theorem psc_row_implies_gbd (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e) (z : PSCPoint p q m)
    (hb : pscPointBase d z) (hr : pscRow d e z.w z.v z.y ≤ z.beta) :
    pscGBDRow d e z.y ≤ z.alpha := by
  have hi := psc_gbd_surrogate_identity d e hk z.w z.v z.y
  have hn := hk.normalW_nonpos hb.1.1
  have hs : (∑ i, e.mu i * d.coupling i z.w z.v z.y) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos
      (hk.mu_nonneg i) (hb.1.2.2.2 i)
  have heq := hb.2
  linarith

theorem psc_oa_subset (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    pscOAMaster d H ⊆ pscMaster d H := by
  intro z hz
  refine ⟨hz.1,fun e he => ?_⟩
  exact psc_oa_implies_row d e.data e.kkt z.w z.v z.y z.beta
    hz.1.1.2.1 (hz.2 e he)

theorem psc_project_mono {A B : Set (PSCPoint p q m)} (h : A ⊆ B) :
    pscProject A ⊆ pscProject B := by
  rintro ya ⟨z,hz,hy,ha⟩
  exact ⟨z,h hz,hy,ha⟩

theorem psc_projected_oa_subset (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) : pscProject (pscOAMaster d H) ⊆ pscProject (pscMaster d H) :=
  psc_project_mono (psc_oa_subset d H)

theorem psc_projected_subset_gbd (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) : pscProject (pscMaster d H) ⊆ pscGBDMaster d H := by
  rintro ya ⟨z,hz,hy,ha⟩
  refine ⟨hy ▸ hz.1.1.2.2.1,fun e he => ?_⟩
  have h := psc_row_implies_gbd d e.data e.kkt z hz.1 (hz.2 e he)
  simpa only [hy,ha] using h

theorem psc_original_mem_oa (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) :
    pscOriginalPoint d w v y ∈ pscOAMaster d H := by
  refine ⟨⟨hf.1, ?_⟩, ?_⟩
  · dsimp [pscOriginalPoint,PSCData.objective]
    ring
  · intro e _
    refine ⟨tangent_underestimator_on hr e.kkt.v_mem hf.1.2.1
      e.kkt.derivative_r, fun j => ?_⟩
    have h := tangent_underestimator_on (ht j) e.kkt.v_mem hf.1.2.1
      (e.kkt.derivative_t j)
    have hb := hf.2 j
    dsimp [pscConstraintTangent,pscOriginalPoint,PSCData.nonlinear] at *
    linarith

theorem psc_original_mem_psc (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) :
    pscOriginalPoint d w v y ∈ pscMaster d H :=
  psc_oa_subset d H (psc_original_mem_oa d H hr ht w v y hf)

theorem psc_original_mem_gbd (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) :
    (y,d.objective w v y) ∈ pscGBDMaster d H :=
  psc_projected_subset_gbd d H
    ⟨pscOriginalPoint d w v y,psc_original_mem_psc d H hr ht w v y hf,rfl,rfl⟩

theorem psc_gbd_at_anchor (d : PSCData p q m l s nw nv) (e : PSCAnchor d) :
    pscGBDRow d e e.y = d.objective e.w e.v e.y := by
  simp [pscGBDRow]

/-- Sufficiency of explicitly constructed full KKT data on the declared domain.
The source-to-KKT existence theorem is a separate necessity direction. -/
theorem psc_kkt_sufficient_fixed_minimum (d : PSCData p q m l s nw nv)
    (e : PSCEntry d) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j)) :
    IsMinimizer (d.fiberFeasible e.data.y) (d.fiberObjective e.data.y)
      (weightedInsert e.data.w e.data.v) := by
  refine ⟨(d.feasible_iff_fiber _ _ _).mp e.kkt.feasible |>.2, ?_⟩
  intro z hz
  have hf : d.feasible (weightedX z) (weightedV z) e.data.y := by
    have h := (d.fiberFeasible_mem_iff e.data.y z).mp hz
    exact ⟨⟨h.1,h.2.1,e.kkt.y_mem,h.2.2.1⟩,h.2.2.2⟩
  have hg := (psc_original_mem_gbd d [e] hr ht (weightedX z) (weightedV z)
    e.data.y hf).2 e (by simp)
  simpa only [psc_gbd_at_anchor,PSCData.fiberObjective_insert,
    PSCData.fiberObjective,weightedX_insert,weightedV_insert] using hg

theorem psc_attained_value_order (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (oa ps : PSCPoint p q m) (gb : RealVector m × ℝ)
    (ho : IsMinimizer (pscOAMaster d H) PSCPoint.alpha oa)
    (hp : IsMinimizer (pscMaster d H) PSCPoint.alpha ps)
    (hg : IsMinimizer (pscGBDMaster d H) Prod.snd gb) :
    gb.2 ≤ ps.alpha ∧ ps.alpha ≤ oa.alpha := by
  exact ⟨hg.2 (ps.y,ps.alpha)
    (psc_projected_subset_gbd d H ⟨ps,hp.1,rfl,rfl⟩),
    hp.2 oa (psc_oa_subset d H ho.1)⟩

theorem psc_attained_value_original_bound (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (oa : PSCPoint p q m) (ho : IsMinimizer (pscOAMaster d H) PSCPoint.alpha oa)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) : oa.alpha ≤ d.objective w v y :=
  ho.2 (pscOriginalPoint d w v y) (psc_original_mem_oa d H hr ht w v y hf)

#print axioms psc_original_mem_oa
#print axioms psc_original_mem_psc
#print axioms psc_original_mem_gbd
#print axioms psc_gbd_at_anchor
#print axioms psc_kkt_sufficient_fixed_minimum
#print axioms psc_attained_value_order
#print axioms psc_attained_value_original_bound

#print axioms psc_oa_surrogate_identity
#print axioms psc_oa_implies_row
#print axioms psc_nonlinear_sum_difference
#print axioms psc_coupling_sum_difference
#print axioms psc_gbd_surrogate_identity
#print axioms psc_row_implies_gbd
#print axioms psc_oa_subset
#print axioms psc_project_mono
#print axioms psc_projected_oa_subset
#print axioms psc_projected_subset_gbd

end Chapter02
