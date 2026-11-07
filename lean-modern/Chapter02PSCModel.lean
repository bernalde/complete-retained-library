module

public import Chapter02WeightedRestoration

@[expose] public section

/-! Qualified PSC source geometry for the QG-(5)/Grossmann-PL separable
subclass and matched feasible-anchor histories. Domain facet normals and
fiber-Slater multiplier existence are explicit qualifications, not claims
about the unmodified source display. Every result here has this bounded scope.
The raw KKT predicate assumes no minimum, cut validity, support or ordering.
All finite dimensions and row counts, including zero, are permitted. -/
noncomputable section
open scoped BigOperators
open Set
namespace Chapter02

structure PSCData (p q m l s nw nv : ℕ) where
  a : RealVector p →L[ℝ] ℝ
  c : RealVector m →L[ℝ] ℝ
  r : RealVector q → ℝ
  C : Fin l → RealVector m →L[ℝ] ℝ
  D : Fin l → RealVector p →L[ℝ] ℝ
  t : Fin l → RealVector q → ℝ
  E : Fin s → RealVector m →L[ℝ] ℝ
  F : Fin s → RealVector p →L[ℝ] ℝ
  G : Fin s → RealVector q →L[ℝ] ℝ
  b : Fin s → ℝ
  Wrow : Fin nw → RealVector p →L[ℝ] ℝ
  Wbound : Fin nw → ℝ
  Vrow : Fin nv → RealVector q →L[ℝ] ℝ
  Vbound : Fin nv → ℝ
  Y : Set (RealVector m)

variable {p q m l s nw nv : ℕ}

namespace PSCData

def W (d : PSCData p q m l s nw nv) : Set (RealVector p) :=
  affinePolyhedron d.Wrow d.Wbound

def V (d : PSCData p q m l s nw nv) : Set (RealVector q) :=
  affinePolyhedron d.Vrow d.Vbound

def objective (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) : ℝ :=
  d.a w + d.r v + d.c y

def nonlinear (d : PSCData p q m l s nw nv) (j : Fin l)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) : ℝ :=
  d.C j y + d.D j w + d.t j v

def coupling (d : PSCData p q m l s nw nv) (i : Fin s)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) : ℝ :=
  d.E i y + d.F i w + d.G i v - d.b i

def base (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) : Prop :=
  w ∈ d.W ∧ v ∈ d.V ∧ y ∈ d.Y ∧ ∀ i, d.coupling i w v y ≤ 0

def feasible (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) : Prop :=
  d.base w v y ∧ ∀ j, d.nonlinear j w v y ≤ 0

def fiberRows (d : PSCData p q m l s nw nv) :
    Fin (s+(nw+nv)) → RealVector (p+q) →L[ℝ] ℝ :=
  Fin.addCases (fun i => (d.F i).comp weightedX + (d.G i).comp weightedV)
    (Fin.addCases (fun i => (d.Wrow i).comp weightedX)
      (fun i => (d.Vrow i).comp weightedV))

def fiberBounds (d : PSCData p q m l s nw nv) (y : RealVector m) :
    Fin (s+(nw+nv)) → ℝ :=
  Fin.addCases (fun i => d.b i-d.E i y) (Fin.addCases d.Wbound d.Vbound)

def affineFiber (d : PSCData p q m l s nw nv) (y : RealVector m) :
    Set (RealVector (p+q)) := affinePolyhedron d.fiberRows (d.fiberBounds y)

def fiberObjective (d : PSCData p q m l s nw nv) (y : RealVector m)
    (z : RealVector (p+q)) : ℝ := d.objective (weightedX z) (weightedV z) y

def fiberNonlinear (d : PSCData p q m l s nw nv) (y : RealVector m)
    (j : Fin l) (z : RealVector (p+q)) : ℝ :=
  d.nonlinear j (weightedX z) (weightedV z) y

def fiberFeasible (d : PSCData p q m l s nw nv) (y : RealVector m) :
    Set (RealVector (p+q)) := {z ∈ d.affineFiber y | ∀ j, d.fiberNonlinear y j z ≤ 0}

@[simp] theorem W_mem (d : PSCData p q m l s nw nv) (w : RealVector p) :
    w ∈ d.W ↔ ∀ i, d.Wrow i w ≤ d.Wbound i := Iff.rfl

@[simp] theorem V_mem (d : PSCData p q m l s nw nv) (v : RealVector q) :
    v ∈ d.V ↔ ∀ i, d.Vrow i v ≤ d.Vbound i := Iff.rfl

theorem affineFiber_mem_iff (d : PSCData p q m l s nw nv) (y : RealVector m)
    (z : RealVector (p+q)) :
    z ∈ d.affineFiber y ↔ weightedX z ∈ d.W ∧ weightedV z ∈ d.V ∧
      ∀ i, d.coupling i (weightedX z) (weightedV z) y ≤ 0 := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i
      have hi := h ((i.castAdd nv).natAdd s)
      simpa [fiberRows,fiberBounds] using hi
    · intro i
      have hi := h ((i.natAdd nw).natAdd s)
      simpa [fiberRows,fiberBounds] using hi
    · intro i
      have hi := h (i.castAdd (nw+nv))
      simp only [fiberRows,fiberBounds,Fin.addCases_left,
        ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply] at hi
      dsimp [coupling]
      linarith
  · rintro ⟨hW,hV,hC⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro j
      have hj := hC j
      simp only [fiberRows,fiberBounds,Fin.addCases_left,
        ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply]
      dsimp [coupling] at hj
      linarith
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro k
        simpa [fiberRows,fiberBounds] using hW k
      · intro k
        simpa [fiberRows,fiberBounds] using hV k

@[simp] theorem affineFiber_insert_iff (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    weightedInsert w v ∈ d.affineFiber y ↔ w ∈ d.W ∧ v ∈ d.V ∧
      ∀ i, d.coupling i w v y ≤ 0 := by
  simpa only [weightedX_insert,weightedV_insert] using
    d.affineFiber_mem_iff y (weightedInsert w v)

@[simp] theorem fiberObjective_insert (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    d.fiberObjective y (weightedInsert w v) = d.objective w v y := by
  simp [fiberObjective]

@[simp] theorem fiberNonlinear_insert (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) (j : Fin l) :
    d.fiberNonlinear y j (weightedInsert w v) = d.nonlinear j w v y := by
  simp [fiberNonlinear]

theorem fiberFeasible_mem_iff (d : PSCData p q m l s nw nv) (y : RealVector m)
    (z : RealVector (p+q)) :
    z ∈ d.fiberFeasible y ↔ weightedX z ∈ d.W ∧ weightedV z ∈ d.V ∧
      (∀ i, d.coupling i (weightedX z) (weightedV z) y ≤ 0) ∧
      ∀ j, d.nonlinear j (weightedX z) (weightedV z) y ≤ 0 := by
  simp only [fiberFeasible,Set.mem_setOf_eq,affineFiber_mem_iff,fiberNonlinear]
  tauto

theorem feasible_iff_fiber (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    d.feasible w v y ↔ y ∈ d.Y ∧ weightedInsert w v ∈ d.fiberFeasible y := by
  simp only [feasible,base,fiberFeasible_mem_iff,weightedX_insert,weightedV_insert]
  tauto

end PSCData

structure PSCAnchor (d : PSCData p q m l s nw nv) where
  w : RealVector p
  v : RealVector q
  y : RealVector m
  Dr : RealVector q →L[ℝ] ℝ
  Dt : Fin l → RealVector q →L[ℝ] ℝ
  lambda : Fin l → ℝ
  mu : Fin s → ℝ
  nuW : Fin nw → ℝ
  nuV : Fin nv → ℝ

def PSCAnchor.normalW {d : PSCData p q m l s nw nv} (e : PSCAnchor d) :
    RealVector p →L[ℝ] ℝ := ∑ i, e.nuW i • d.Wrow i

def PSCAnchor.normalV {d : PSCData p q m l s nw nv} (e : PSCAnchor d) :
    RealVector q →L[ℝ] ℝ := ∑ i, e.nuV i • d.Vrow i

structure PSCKKT (d : PSCData p q m l s nw nv) (e : PSCAnchor d) : Prop where
  w_mem : e.w ∈ d.W
  v_mem : e.v ∈ d.V
  y_mem : e.y ∈ d.Y
  nonlinear_feasible : ∀ j, d.nonlinear j e.w e.v e.y ≤ 0
  coupling_feasible : ∀ i, d.coupling i e.w e.v e.y ≤ 0
  derivative_r : HasFDerivAt d.r e.Dr e.v
  derivative_t : ∀ j, HasFDerivAt (d.t j) (e.Dt j) e.v
  lambda_nonneg : ∀ j, 0 ≤ e.lambda j
  mu_nonneg : ∀ i, 0 ≤ e.mu i
  nuW_nonneg : ∀ i, 0 ≤ e.nuW i
  nuV_nonneg : ∀ i, 0 ≤ e.nuV i
  nonlinear_complementarity : ∀ j, e.lambda j * d.nonlinear j e.w e.v e.y = 0
  coupling_complementarity : ∀ i, e.mu i * d.coupling i e.w e.v e.y = 0
  w_complementarity : ∀ i, e.nuW i * (d.Wrow i e.w-d.Wbound i) = 0
  v_complementarity : ∀ i, e.nuV i * (d.Vrow i e.v-d.Vbound i) = 0
  stationarity_w : ∀ dw, d.a dw + (∑ j, e.lambda j * d.D j dw) +
    (∑ i, e.mu i * d.F i dw) + e.normalW dw = 0
  stationarity_v : ∀ dv, e.Dr dv + (∑ j, e.lambda j * e.Dt j dv) +
    (∑ i, e.mu i * d.G i dv) + e.normalV dv = 0

theorem PSCKKT.normalW_nonpos {d : PSCData p q m l s nw nv} {e : PSCAnchor d}
    (h : PSCKKT d e) {w : RealVector p} (hw : w ∈ d.W) :
    e.normalW (w-e.w) ≤ 0 := by
  simp only [PSCAnchor.normalW,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonpos
  intro i _
  have hn := h.nuW_nonneg i
  have hc := h.w_complementarity i
  have hb : d.Wrow i w ≤ d.Wbound i := hw i
  nlinarith

theorem PSCKKT.normalV_nonpos {d : PSCData p q m l s nw nv} {e : PSCAnchor d}
    (h : PSCKKT d e) {v : RealVector q} (hv : v ∈ d.V) :
    e.normalV (v-e.v) ≤ 0 := by
  simp only [PSCAnchor.normalV,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonpos
  intro i _
  have hn := h.nuV_nonneg i
  have hc := h.v_complementarity i
  have hb : d.Vrow i v ≤ d.Vbound i := hv i
  nlinarith

theorem PSCKKT.feasible {d : PSCData p q m l s nw nv} {e : PSCAnchor d}
    (h : PSCKKT d e) : d.feasible e.w e.v e.y :=
  ⟨⟨h.w_mem,h.v_mem,h.y_mem,h.coupling_feasible⟩,h.nonlinear_feasible⟩

structure PSCEntry (d : PSCData p q m l s nw nv) where
  data : PSCAnchor d
  kkt : PSCKKT d data

/-- Every finite-dimensional row in the source data has its literal coordinate
matrix representation, including all coupling and facet rows. -/
theorem pscRow_coordinates {n : ℕ} (row : RealVector n →L[ℝ] ℝ)
    (z : RealVector n) : row z = ∑ i, row (Pi.single i 1) * z i :=
  slaterFunctional_coordinates row z

@[simp] theorem PSCData.fiberFeasible_insert_iff (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    weightedInsert w v ∈ d.fiberFeasible y ↔
      w ∈ d.W ∧ v ∈ d.V ∧ (∀ i, d.coupling i w v y ≤ 0) ∧
      (∀ j, d.nonlinear j w v y ≤ 0) := by
  simp only [PSCData.fiberFeasible,Set.mem_setOf_eq,
    PSCData.affineFiber_insert_iff,PSCData.fiberNonlinear_insert]
  tauto

#print axioms PSCData.W_mem
#print axioms PSCData.V_mem
#print axioms PSCData.affineFiber_mem_iff
#print axioms PSCData.affineFiber_insert_iff
#print axioms PSCData.fiberObjective_insert
#print axioms PSCData.fiberNonlinear_insert
#print axioms PSCData.fiberFeasible_mem_iff
#print axioms PSCData.feasible_iff_fiber
#print axioms PSCKKT.normalW_nonpos
#print axioms PSCKKT.normalV_nonpos
#print axioms PSCKKT.feasible

#print axioms pscRow_coordinates
#print axioms PSCData.fiberFeasible_insert_iff

end Chapter02
