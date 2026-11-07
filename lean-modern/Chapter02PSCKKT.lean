module

public import Chapter02PSCModel

@[expose] public section

/-! Candidate qualified PSC source wrapper. The actual fixed-y minimum,
relative convexity on the literal V polyhedron, full derivatives at that
minimum and a strict nonlinear point in that same affine fiber derive all
nonlinear, coupling and facet multipliers. No global convexity, affine strict
point, domain interior, cut validity or support oracle is assumed. -/
noncomputable section
open scoped BigOperators
open Set
namespace Chapter02

variable {p q m l s nw nv : ℕ}

namespace PSCData

theorem affineFiber_convex (d : PSCData p q m l s nw nv) (y : RealVector m) :
    Convex ℝ (d.affineFiber y) := by
  intro x hx z hz a b ha hb hab i
  change d.fiberRows i (a • x + b • z) ≤ d.fiberBounds y i
  simp only [map_add,map_smul,smul_eq_mul]
  calc
    a * d.fiberRows i x + b * d.fiberRows i z ≤
        a * d.fiberBounds y i + b * d.fiberBounds y i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hz i) hb)
    _ = d.fiberBounds y i := by rw [← add_mul,hab,one_mul]

theorem fiberObjective_convex (d : PSCData p q m l s nw nv) (y : RealVector m)
    (hr : ConvexOn ℝ d.V d.r) : ConvexOn ℝ (d.affineFiber y) (d.fiberObjective y) := by
  have hc : ConvexOn ℝ (d.affineFiber y) (fun z => d.r (weightedV z)) :=
    (hr.comp_linearMap weightedV.toLinearMap).subset
      (fun z hz => (d.affineFiber_mem_iff y z).mp hz |>.2.1) (d.affineFiber_convex y)
  exact (((d.a.comp weightedX).toLinearMap.convexOn (d.affineFiber_convex y)).add hc).add_const (d.c y)

theorem fiberNonlinear_convex (d : PSCData p q m l s nw nv) (y : RealVector m)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j)) (j : Fin l) :
    ConvexOn ℝ (d.affineFiber y) (d.fiberNonlinear y j) := by
  have hc : ConvexOn ℝ (d.affineFiber y) (fun z => d.t j (weightedV z)) :=
    ((ht j).comp_linearMap weightedV.toLinearMap).subset
      (fun z hz => (d.affineFiber_mem_iff y z).mp hz |>.2.1) (d.affineFiber_convex y)
  exact ((convexOn_const (d.C j y) (d.affineFiber_convex y)).add
    (((d.D j).comp weightedX).toLinearMap.convexOn (d.affineFiber_convex y))).add hc

/-- Actual full derivative of the fixed-y source objective, including the
nonlinear r term rather than silently replacing it by zero. -/
def fiberObjectiveDerivative (d : PSCData p q m l s nw nv)
    (Dr : RealVector q →L[ℝ] ℝ) : RealVector (p+q) →L[ℝ] ℝ :=
  d.a.comp weightedX + Dr.comp weightedV

def fiberNonlinearDerivative (d : PSCData p q m l s nw nv)
    (Dt : Fin l → RealVector q →L[ℝ] ℝ) (j : Fin l) :
    RealVector (p+q) →L[ℝ] ℝ :=
  (d.D j).comp weightedX + (Dt j).comp weightedV

def fiberPartialDerivative (d : PSCData p q m l s nw nv)
    (Dr : RealVector q →L[ℝ] ℝ) (Dt : Fin l → RealVector q →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) : RealVector (p+q) →L[ℝ] ℝ :=
  d.fiberObjectiveDerivative Dr + ∑ j, lambda j • d.fiberNonlinearDerivative Dt j

theorem fiberObjective_hasFDerivAt (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dr : RealVector q →L[ℝ] ℝ) (hr : HasFDerivAt d.r Dr v) :
    HasFDerivAt (d.fiberObjective y) (d.fiberObjectiveDerivative Dr) (weightedInsert w v) := by
  have hr' : HasFDerivAt d.r Dr (weightedV (weightedInsert w v)) := by simpa using hr
  have hc := hr'.comp (f := weightedV (n := p) (s := q)) (weightedInsert w v)
    (weightedV (n := p) (s := q)).hasFDerivAt
  unfold PSCData.fiberObjective PSCData.fiberObjectiveDerivative
  simpa only [weightedV_insert, PSCData.objective, Function.comp_def, ContinuousLinearMap.comp_apply] using
    (((d.a.comp weightedX).hasFDerivAt).fun_add hc).add_const (d.c y)

theorem fiberNonlinear_hasFDerivAt (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dt : Fin l → RealVector q →L[ℝ] ℝ)
    (ht : ∀ j, HasFDerivAt (d.t j) (Dt j) v) (j : Fin l) :
    HasFDerivAt (d.fiberNonlinear y j) (d.fiberNonlinearDerivative Dt j)
      (weightedInsert w v) := by
  have ht' : HasFDerivAt (d.t j) (Dt j) (weightedV (weightedInsert w v)) := by simpa using ht j
  have hc := ht'.comp (f := weightedV (n := p) (s := q)) (weightedInsert w v)
    (weightedV (n := p) (s := q)).hasFDerivAt
  exact (((d.D j).comp weightedX).hasFDerivAt.const_add (d.C j y)).add hc

theorem fiberPartial_hasFDerivAt (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dr : RealVector q →L[ℝ] ℝ) (Dt : Fin l → RealVector q →L[ℝ] ℝ)
    (lambda : Fin l → ℝ)
    (hr : HasFDerivAt d.r Dr v) (ht : ∀ j, HasFDerivAt (d.t j) (Dt j) v) :
    HasFDerivAt (fun z => d.fiberObjective y z + ∑ j, lambda j * d.fiberNonlinear y j z)
      (d.fiberPartialDerivative Dr Dt lambda) (weightedInsert w v) := by
  exact (d.fiberObjective_hasFDerivAt w v y Dr hr).add
    (HasFDerivAt.fun_sum fun j _ => (d.fiberNonlinear_hasFDerivAt w v y Dt ht j).const_mul (lambda j))

/-- Flattening preserves the actual minimizer problem and requires no extra
regularity or full-dimensional domain. Y membership stays explicit outside
this fixed-y problem. -/
theorem fiber_minimum_iff (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    IsMinimizer (d.fiberFeasible y) (d.fiberObjective y) (weightedInsert w v) ↔
      (w ∈ d.W ∧ v ∈ d.V ∧ (∀ i, d.coupling i w v y ≤ 0) ∧
        (∀ j, d.nonlinear j w v y ≤ 0)) ∧
      ∀ w' v', w' ∈ d.W → v' ∈ d.V →
        (∀ i, d.coupling i w' v' y ≤ 0) → (∀ j, d.nonlinear j w' v' y ≤ 0) →
        d.objective w v y ≤ d.objective w' v' y := by
  constructor
  · rintro ⟨hmem,hmin⟩
    refine ⟨(d.fiberFeasible_insert_iff w v y).mp hmem,?_⟩
    intro w' v' hw hv hC hN
    simpa only [fiberObjective_insert] using
      hmin (weightedInsert w' v') ((d.fiberFeasible_insert_iff w' v' y).mpr ⟨hw,hv,hC,hN⟩)
  · rintro ⟨hmem,hmin⟩
    refine ⟨(d.fiberFeasible_insert_iff w v y).mpr hmem,?_⟩
    intro z hz
    obtain ⟨hw,hv,hC,hN⟩ := (d.fiberFeasible_mem_iff y z).mp hz
    simpa only [fiberObjective,weightedX_insert,weightedV_insert] using
      hmin (weightedX z) (weightedV z) hw hv hC hN

/-- The strict point is in the literal affine fiber; affine rows may be tight. -/
theorem fiber_slater_iff (d : PSCData p q m l s nw nv) (y : RealVector m) :
    (∃ z ∈ d.affineFiber y, ∀ j, d.fiberNonlinear y j z < 0) ↔
      ∃ w v, w ∈ d.W ∧ v ∈ d.V ∧ (∀ i, d.coupling i w v y ≤ 0) ∧
        ∀ j, d.nonlinear j w v y < 0 := by
  constructor
  · rintro ⟨z,hz,hn⟩
    obtain ⟨hw,hv,hC⟩ := (d.affineFiber_mem_iff y z).mp hz
    exact ⟨weightedX z,weightedV z,hw,hv,hC,hn⟩
  · rintro ⟨w,v,hw,hv,hC,hN⟩
    exact ⟨weightedInsert w v,(d.affineFiber_insert_iff w v y).mpr ⟨hw,hv,hC⟩,
      by simpa only [fiberNonlinear_insert] using hN⟩

end PSCData

#print axioms PSCData.affineFiber_convex
#print axioms PSCData.fiberObjective_convex
#print axioms PSCData.fiberNonlinear_convex
#print axioms PSCData.fiberObjective_hasFDerivAt
#print axioms PSCData.fiberNonlinear_hasFDerivAt
#print axioms PSCData.fiberPartial_hasFDerivAt
#print axioms PSCData.fiber_minimum_iff
#print axioms PSCData.fiber_slater_iff

/-- The coupling and the two domain-facet blocks retain their original row
encoding. These restrictions merely select coefficients supplied by the
polyhedral multiplier theorem. -/
def pscCouplingMultiplier (M : Fin (s+(nw+nv)) → ℝ) (i : Fin s) : ℝ :=
  M (i.castAdd (nw+nv))

def pscWMultiplier (M : Fin (s+(nw+nv)) → ℝ) (i : Fin nw) : ℝ :=
  M ((i.castAdd nv).natAdd s)

def pscVMultiplier (M : Fin (s+(nw+nv)) → ℝ) (i : Fin nv) : ℝ :=
  M ((i.natAdd nw).natAdd s)

def pscAnchorOfMultipliers (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dr : RealVector q →L[ℝ] ℝ) (Dt : Fin l → RealVector q →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (M : Fin (s+(nw+nv)) → ℝ) : PSCAnchor d where
  w := w
  v := v
  y := y
  Dr := Dr
  Dt := Dt
  lambda := lambda
  mu := pscCouplingMultiplier M
  nuW := pscWMultiplier M
  nuV := pscVMultiplier M

theorem psc_fiber_coupling_residual (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) (i : Fin s) :
    d.fiberRows (i.castAdd (nw+nv)) (weightedInsert w v) -
        d.fiberBounds y (i.castAdd (nw+nv)) = d.coupling i w v y := by
  simp [PSCData.fiberRows,PSCData.fiberBounds,PSCData.coupling]
  ring

theorem psc_fiber_w_residual (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) (i : Fin nw) :
    d.fiberRows ((i.castAdd nv).natAdd s) (weightedInsert w v) -
        d.fiberBounds y ((i.castAdd nv).natAdd s) = d.Wrow i w-d.Wbound i := by
  simp [PSCData.fiberRows,PSCData.fiberBounds]

theorem psc_fiber_v_residual (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) (i : Fin nv) :
    d.fiberRows ((i.natAdd nw).natAdd s) (weightedInsert w v) -
        d.fiberBounds y ((i.natAdd nw).natAdd s) = d.Vrow i v-d.Vbound i := by
  simp [PSCData.fiberRows,PSCData.fiberBounds]

/-- Exact stationarity identity before setting either direction to zero.
All nonlinear, coupling and domain terms appear once, with literal signs. -/
theorem psc_flat_stationarity_apply (d : PSCData p q m l s nw nv)
    (Dr : RealVector q →L[ℝ] ℝ) (Dt : Fin l → RealVector q →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (M : Fin (s+(nw+nv)) → ℝ)
    (dw : RealVector p) (dv : RealVector q) :
    (d.fiberPartialDerivative Dr Dt lambda + ∑ i, M i • d.fiberRows i)
        (weightedInsert dw dv) =
      (d.a dw + (∑ j, lambda j * d.D j dw) +
        (∑ i, pscCouplingMultiplier M i * d.F i dw) +
        (∑ i, pscWMultiplier M i * d.Wrow i dw)) +
      (Dr dv + (∑ j, lambda j * Dt j dv) +
        (∑ i, pscCouplingMultiplier M i * d.G i dv) +
        (∑ i, pscVMultiplier M i * d.Vrow i dv)) := by
  simp only [PSCData.fiberPartialDerivative,PSCData.fiberObjectiveDerivative,
    PSCData.fiberNonlinearDerivative,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    Fin.sum_univ_add,PSCData.fiberRows,Fin.addCases_left,Fin.addCases_right,
    ContinuousLinearMap.comp_apply,weightedX_insert,weightedV_insert,
    pscCouplingMultiplier,pscWMultiplier,pscVMultiplier,mul_add,Finset.sum_add_distrib]
  ring

/-- Algebraic extraction from exact flat multipliers is separate from their
existence. It adds no validity oracle or hidden minimizer assumption. -/
theorem psc_kkt_of_flat_multipliers (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dr : RealVector q →L[ℝ] ℝ) (Dt : Fin l → RealVector q →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (M : Fin (s+(nw+nv)) → ℝ)
    (hfeas : d.feasible w v y)
    (hr : HasFDerivAt d.r Dr v) (ht : ∀ j, HasFDerivAt (d.t j) (Dt j) v)
    (hl : ∀ j, 0 ≤ lambda j)
    (hlc : ∀ j, lambda j * d.nonlinear j w v y = 0)
    (hM : ∀ i, 0 ≤ M i)
    (hMc : ∀ i, M i * (d.fiberRows i (weightedInsert w v)-d.fiberBounds y i) = 0)
    (hstat : d.fiberPartialDerivative Dr Dt lambda + ∑ i, M i • d.fiberRows i = 0) :
    PSCKKT d (pscAnchorOfMultipliers d w v y Dr Dt lambda M) := by
  refine ⟨hfeas.1.1,hfeas.1.2.1,hfeas.1.2.2.1,hfeas.2,hfeas.1.2.2.2,
    hr,ht,hl,?_,?_,?_,hlc,?_,?_,?_,?_,?_⟩
  · intro i
    exact hM (i.castAdd (nw+nv))
  · intro i
    exact hM ((i.castAdd nv).natAdd s)
  · intro i
    exact hM ((i.natAdd nw).natAdd s)
  · intro i
    have hi := hMc (i.castAdd (nw+nv))
    rw [psc_fiber_coupling_residual] at hi
    exact hi
  · intro i
    have hi := hMc ((i.castAdd nv).natAdd s)
    rw [psc_fiber_w_residual] at hi
    exact hi
  · intro i
    have hi := hMc ((i.natAdd nw).natAdd s)
    rw [psc_fiber_v_residual] at hi
    exact hi
  · intro dw
    have he := congrArg (fun L : RealVector (p+q) →L[ℝ] ℝ =>
      L (weightedInsert dw 0)) hstat
    simp only [psc_flat_stationarity_apply,ContinuousLinearMap.zero_apply] at he
    simpa [pscAnchorOfMultipliers,PSCAnchor.normalW] using he
  · intro dv
    have he := congrArg (fun L : RealVector (p+q) →L[ℝ] ℝ =>
      L (weightedInsert 0 dv)) hstat
    simp only [psc_flat_stationarity_apply,ContinuousLinearMap.zero_apply] at he
    simpa [pscAnchorOfMultipliers,PSCAnchor.normalV] using he

/-- Source-qualified existence: relative convexity and a strict nonlinear point
in this actual affine fiber, together with its actual minimum and actual full
anchor derivatives, derive the complete separated KKT data. -/
theorem psc_kkt_exists_of_minimum (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dr : RealVector q →L[ℝ] ℝ) (Dt : Fin l → RealVector q →L[ℝ] ℝ)
    (hy : y ∈ d.Y) (hrc : ConvexOn ℝ d.V d.r)
    (htc : ∀ j, ConvexOn ℝ d.V (d.t j))
    (hr : HasFDerivAt d.r Dr v) (ht : ∀ j, HasFDerivAt (d.t j) (Dt j) v)
    (hmin : IsMinimizer (d.fiberFeasible y) (d.fiberObjective y) (weightedInsert w v))
    (hslater : ∃ z ∈ d.affineFiber y, ∀ j, d.fiberNonlinear y j z < 0) :
    ∃ lambda : Fin l → ℝ, ∃ M : Fin (s+(nw+nv)) → ℝ,
      PSCKKT d (pscAnchorOfMultipliers d w v y Dr Dt lambda M) := by
  obtain ⟨lambda,hl,hlc,hpartial⟩ := convex_slater_partialLagrangian_minimum
    (d.affineFiber y) (d.fiberObjective y) (d.fiberNonlinear y) (weightedInsert w v)
    (d.affineFiber_convex y) (d.fiberObjective_convex y hrc)
    (d.fiberNonlinear_convex y htc) hmin hslater
  obtain ⟨M,hM,hMc,hstat⟩ := polyhedral_minimum_multipliers
    d.fiberRows (d.fiberBounds y) hpartial (d.fiberPartial_hasFDerivAt w v y Dr Dt lambda hr ht)
  refine ⟨lambda,M,psc_kkt_of_flat_multipliers d w v y Dr Dt lambda M
    ((d.feasible_iff_fiber w v y).mpr ⟨hy,hmin.1⟩) hr ht hl ?_ hM hMc hstat⟩
  simpa only [PSCData.fiberNonlinear_insert] using hlc

/-- A consumer can obtain a well-formed matched-history entry without assuming
any KKT multiplier oracle. Every original anchor coordinate and derivative is
preserved, while multipliers are derived. -/
theorem psc_entry_exists_of_minimum (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dr : RealVector q →L[ℝ] ℝ) (Dt : Fin l → RealVector q →L[ℝ] ℝ)
    (hy : y ∈ d.Y) (hrc : ConvexOn ℝ d.V d.r)
    (htc : ∀ j, ConvexOn ℝ d.V (d.t j))
    (hr : HasFDerivAt d.r Dr v) (ht : ∀ j, HasFDerivAt (d.t j) (Dt j) v)
    (hmin : IsMinimizer (d.fiberFeasible y) (d.fiberObjective y) (weightedInsert w v))
    (hslater : ∃ z ∈ d.affineFiber y, ∀ j, d.fiberNonlinear y j z < 0) :
    ∃ e : PSCEntry d, e.data.w = w ∧ e.data.v = v ∧ e.data.y = y ∧
      e.data.Dr = Dr ∧ e.data.Dt = Dt := by
  obtain ⟨lambda,M,hk⟩ := psc_kkt_exists_of_minimum d w v y Dr Dt hy hrc htc hr ht hmin hslater
  exact ⟨⟨pscAnchorOfMultipliers d w v y Dr Dt lambda M,hk⟩,rfl,rfl,rfl,rfl,rfl⟩

#print axioms psc_fiber_coupling_residual
#print axioms psc_fiber_w_residual
#print axioms psc_fiber_v_residual
#print axioms psc_flat_stationarity_apply
#print axioms psc_kkt_of_flat_multipliers
#print axioms psc_kkt_exists_of_minimum
#print axioms psc_entry_exists_of_minimum

end Chapter02
