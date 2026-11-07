module

public import Chapter02PSCOrder
public import Chapter02PSCKKT

@[expose] public section

/-! The t=0 reclassification in the qualified QG-(5)/Grossmann-PL subclass.
All original affine nonlinear rows are retained as coupling rows. Original
feasibility and objective are preserved; equality of the old and rebuilt PSC
masters is not claimed. Full derivatives justify eliminating Dt. The source
wrapper derives new KKT entries from actual fixed-fiber minima with relative
convexity of r; no nonlinear Slater premise is needed for an empty row family.
LP/MILP naming still requires the corresponding structure of the common Y. -/

noncomputable section
open scoped BigOperators
namespace Chapter02
variable {p q m l s nw nv : ℕ}

def pscAffineReclassification (d : PSCData p q m l s nw nv) :
    PSCData p q m 0 (s+l) nw nv where
  a := d.a
  c := d.c
  r := d.r
  C := fun j => Fin.elim0 j
  D := fun j => Fin.elim0 j
  t := fun j => Fin.elim0 j
  E := Fin.addCases d.E d.C
  F := Fin.addCases d.F d.D
  G := Fin.addCases d.G (fun _ => 0)
  b := Fin.addCases d.b (fun _ => 0)
  Wrow := d.Wrow
  Wbound := d.Wbound
  Vrow := d.Vrow
  Vbound := d.Vbound
  Y := d.Y

@[simp] theorem psc_reclassification_objective (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    (pscAffineReclassification d).objective w v y = d.objective w v y := rfl

@[simp] theorem psc_reclassification_W (d : PSCData p q m l s nw nv) :
    (pscAffineReclassification d).W = d.W := rfl

@[simp] theorem psc_reclassification_V (d : PSCData p q m l s nw nv) :
    (pscAffineReclassification d).V = d.V := rfl

@[simp] theorem psc_reclassification_old_coupling (d : PSCData p q m l s nw nv)
    (i : Fin s) (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    (pscAffineReclassification d).coupling (i.castAdd l) w v y = d.coupling i w v y := by
  simp [pscAffineReclassification, PSCData.coupling]

@[simp] theorem psc_reclassification_new_coupling (d : PSCData p q m l s nw nv)
    (j : Fin l) (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    (pscAffineReclassification d).coupling (j.natAdd s) w v y = d.C j y + d.D j w := by
  simp [pscAffineReclassification, PSCData.coupling]

theorem psc_reclassification_coupling_iff (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    (∀ i, (pscAffineReclassification d).coupling i w v y ≤ 0) ↔
      (∀ i, d.coupling i w v y ≤ 0) ∧ (∀ j, d.C j y + d.D j w ≤ 0) := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [psc_reclassification_old_coupling] using h (i.castAdd l),
      fun j => by simpa only [psc_reclassification_new_coupling] using h (j.natAdd s)⟩
  · rintro ⟨h,h'⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simpa only [psc_reclassification_old_coupling] using h k
    · intro j
      simpa only [psc_reclassification_new_coupling] using h' j

theorem psc_reclassification_base_iff (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    (pscAffineReclassification d).base w v y ↔
      d.base w v y ∧ ∀ j, d.C j y + d.D j w ≤ 0 := by
  change (w ∈ d.W ∧ v ∈ d.V ∧ y ∈ d.Y ∧
    ∀ i, (pscAffineReclassification d).coupling i w v y ≤ 0) ↔ _
  rw [psc_reclassification_coupling_iff]
  simp only [PSCData.base]
  tauto

theorem psc_reclassification_feasible_iff (d : PSCData p q m l s nw nv)
    (ht : ∀ j, d.t j = fun _ => 0)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    (pscAffineReclassification d).feasible w v y ↔ d.feasible w v y := by
  simp only [PSCData.feasible, psc_reclassification_base_iff]
  simp [PSCData.nonlinear, ht]

theorem psc_reclassification_fiber_feasible (d : PSCData p q m l s nw nv)
    (ht : ∀ j, d.t j = fun _ => 0) (y : RealVector m) :
    (pscAffineReclassification d).fiberFeasible y = d.fiberFeasible y := by
  ext z
  simp only [PSCData.fiberFeasible_mem_iff, psc_reclassification_W,
    psc_reclassification_V, psc_reclassification_coupling_iff]
  simp [PSCData.nonlinear, ht, and_assoc]

@[simp] theorem psc_reclassification_fiber_objective (d : PSCData p q m l s nw nv)
    (y : RealVector m) :
    (pscAffineReclassification d).fiberObjective y = d.fiberObjective y := rfl

theorem psc_reclassification_fixed_minimum_iff (d : PSCData p q m l s nw nv)
    (ht : ∀ j, d.t j = fun _ => 0) (y : RealVector m) (z : RealVector (p+q)) :
    IsMinimizer ((pscAffineReclassification d).fiberFeasible y)
      ((pscAffineReclassification d).fiberObjective y) z ↔
      IsMinimizer (d.fiberFeasible y) (d.fiberObjective y) z := by
  rw [psc_reclassification_fiber_feasible d ht, psc_reclassification_fiber_objective]

theorem psc_zero_t_derivative (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e) (ht : ∀ j, d.t j = fun _ => 0) (j : Fin l) :
    e.Dt j = 0 := by
  have hz : HasFDerivAt (d.t j) (0 : RealVector q →L[ℝ] ℝ) e.v := by
    rw [ht j]
    exact hasFDerivAt_const _ _
  exact (hk.derivative_t j).unique hz

def pscReclassifiedAnchor (d : PSCData p q m l s nw nv) (e : PSCAnchor d) :
    PSCAnchor (pscAffineReclassification d) where
  w := e.w
  v := e.v
  y := e.y
  Dr := e.Dr
  Dt := fun j => Fin.elim0 j
  lambda := fun j => Fin.elim0 j
  mu := Fin.addCases e.mu e.lambda
  nuW := e.nuW
  nuV := e.nuV

@[simp] theorem psc_reclassified_normalW (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) : (pscReclassifiedAnchor d e).normalW = e.normalW := rfl

@[simp] theorem psc_reclassified_normalV (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) : (pscReclassifiedAnchor d e).normalV = e.normalV := rfl

theorem psc_reclassified_kkt (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (hk : PSCKKT d e) (ht : ∀ j, d.t j = fun _ => 0) :
    PSCKKT (pscAffineReclassification d) (pscReclassifiedAnchor d e) := by
  refine ⟨hk.w_mem, hk.v_mem, hk.y_mem, ?_, ?_, hk.derivative_r, ?_, ?_, ?_,
    hk.nuW_nonneg, hk.nuV_nonneg, ?_, ?_, hk.w_complementarity, hk.v_complementarity,
    ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simpa [pscReclassifiedAnchor] using hk.coupling_feasible k
    · intro j
      have h := hk.nonlinear_feasible j
      simpa [pscReclassifiedAnchor, PSCData.nonlinear, ht] using h
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simpa [pscReclassifiedAnchor] using hk.mu_nonneg k
    · intro j
      simpa [pscReclassifiedAnchor] using hk.lambda_nonneg j
  · intro j
    exact Fin.elim0 j
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simpa [pscReclassifiedAnchor] using hk.coupling_complementarity k
    · intro j
      have h := hk.nonlinear_complementarity j
      simpa [pscReclassifiedAnchor, PSCData.nonlinear, ht] using h
  · intro dw
    have h := hk.stationarity_w dw
    simp [pscReclassifiedAnchor, pscAffineReclassification, Fin.sum_univ_add,
      PSCAnchor.normalW] at *
    linarith
  · intro dv
    have h := hk.stationarity_v dv
    have hDt := psc_zero_t_derivative d e hk ht
    simp [pscReclassifiedAnchor, pscAffineReclassification, Fin.sum_univ_add,
      PSCAnchor.normalV, hDt] at *
    exact h

def pscReclassifiedEntry (d : PSCData p q m l s nw nv) (e : PSCEntry d)
    (ht : ∀ j, d.t j = fun _ => 0) : PSCEntry (pscAffineReclassification d) :=
  ⟨pscReclassifiedAnchor d e.data, psc_reclassified_kkt d e.data e.kkt ht⟩

def pscReclassifiedHistory (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    (ht : ∀ j, d.t j = fun _ => 0) : List (PSCEntry (pscAffineReclassification d)) :=
  H.map (fun e => pscReclassifiedEntry d e ht)

theorem psc_reclassified_history_length (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (ht : ∀ j, d.t j = fun _ => 0) :
    (pscReclassifiedHistory d H ht).length = H.length := by
  simp [pscReclassifiedHistory]

/-- The rebuilt row has no aggregate nonlinear-row contribution: those affine
rows are now enforced individually in the retained coupling base. -/
theorem psc_reclassified_row_formula (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    pscRow (pscAffineReclassification d) (pscReclassifiedAnchor d e) w v y =
      d.r e.v - ∑ i, e.mu i * d.G i (v-e.v) := by
  simp [pscRow, pscAffineReclassification, pscReclassifiedAnchor, Fin.sum_univ_add]

theorem psc_old_row_vs_reclassified (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (ht : ∀ j, d.t j = fun _ => 0)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    pscRow d e w v y =
      pscRow (pscAffineReclassification d) (pscReclassifiedAnchor d e) w v y +
      ∑ j, e.lambda j * (d.C j y + d.D j w) := by
  rw [psc_reclassified_row_formula]
  simp only [pscRow, PSCData.nonlinear, ht, add_zero]
  ring

/-- Actual feasibility is preserved when the original nonlinear expressions
vanish. Rebuilt rows need not equal the old aggregate PSC rows. -/
theorem psc_reclassified_outer_valid (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (ht : ∀ j, d.t j = fun _ => 0)
    (hr : ConvexOn ℝ d.V d.r) (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) :
    pscOriginalPoint (pscAffineReclassification d) w v y ∈
      pscMaster (pscAffineReclassification d) (pscReclassifiedHistory d H ht) := by
  apply psc_original_mem_psc
  · exact hr
  · intro j
    exact Fin.elim0 j
  · exact (psc_reclassification_feasible_iff d ht w v y).mpr hf

theorem psc_reclassified_projected_order (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (ht : ∀ j, d.t j = fun _ => 0) :
    pscProject (pscOAMaster (pscAffineReclassification d) (pscReclassifiedHistory d H ht)) ⊆
      pscProject (pscMaster (pscAffineReclassification d) (pscReclassifiedHistory d H ht)) ∧
    pscProject (pscMaster (pscAffineReclassification d) (pscReclassifiedHistory d H ht)) ⊆
      pscGBDMaster (pscAffineReclassification d) (pscReclassifiedHistory d H ht) :=
  ⟨psc_projected_oa_subset _ _, psc_projected_subset_gbd _ _⟩

/-- With no nonlinear rows left, the required nonlinear strict point is the
actual feasible anchor itself; affine rows may be tight. -/
theorem psc_reclassified_entry_exists (d : PSCData p q m l s nw nv)
    (ht : ∀ j, d.t j = fun _ => 0)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dr : RealVector q →L[ℝ] ℝ) (hy : y ∈ d.Y) (hrc : ConvexOn ℝ d.V d.r)
    (hr : HasFDerivAt d.r Dr v)
    (hmin : IsMinimizer (d.fiberFeasible y) (d.fiberObjective y) (weightedInsert w v)) :
    ∃ e : PSCEntry (pscAffineReclassification d),
      e.data.w = w ∧ e.data.v = v ∧ e.data.y = y ∧ e.data.Dr = Dr := by
  have hm := (psc_reclassification_fixed_minimum_iff d ht y (weightedInsert w v)).mpr hmin
  obtain ⟨e, hw, hv, hy', hDr, _⟩ := psc_entry_exists_of_minimum
    (pscAffineReclassification d) w v y Dr (fun j => Fin.elim0 j) hy hrc
    (fun j => Fin.elim0 j) hr (fun j => Fin.elim0 j) hm
    ⟨weightedInsert w v, hm.1.1, fun j => Fin.elim0 j⟩
  exact ⟨e, hw, hv, hy', hDr⟩

/-- The r=t=0 case is exactly the original all-affine model, with every
former h row retained. Y is unchanged and not silently declared polyhedral. -/
theorem psc_zero_r_t_all_affine (d : PSCData p q m l s nw nv)
    (hr : d.r = fun _ => 0) (ht : ∀ j, d.t j = fun _ => 0)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    (d.feasible w v y ↔ w ∈ d.W ∧ v ∈ d.V ∧ y ∈ d.Y ∧
      (∀ i, d.E i y + d.F i w + d.G i v ≤ d.b i) ∧
      (∀ j, d.C j y + d.D j w ≤ 0)) ∧
    d.objective w v y = d.a w + d.c y := by
  constructor
  · simp [PSCData.feasible, PSCData.base, PSCData.nonlinear, PSCData.coupling,
      ht, sub_nonpos, and_assoc]
  · simp [PSCData.objective, hr]

end Chapter02

#print axioms Chapter02.psc_reclassification_objective
#print axioms Chapter02.psc_reclassification_W
#print axioms Chapter02.psc_reclassification_V
#print axioms Chapter02.psc_reclassification_old_coupling
#print axioms Chapter02.psc_reclassification_new_coupling
#print axioms Chapter02.psc_reclassification_coupling_iff
#print axioms Chapter02.psc_reclassification_base_iff
#print axioms Chapter02.psc_reclassification_feasible_iff
#print axioms Chapter02.psc_reclassification_fiber_feasible
#print axioms Chapter02.psc_reclassification_fiber_objective
#print axioms Chapter02.psc_reclassification_fixed_minimum_iff
#print axioms Chapter02.psc_zero_t_derivative
#print axioms Chapter02.psc_reclassified_normalW
#print axioms Chapter02.psc_reclassified_normalV
#print axioms Chapter02.psc_reclassified_kkt
#print axioms Chapter02.psc_reclassified_history_length
#print axioms Chapter02.psc_reclassified_row_formula
#print axioms Chapter02.psc_old_row_vs_reclassified
#print axioms Chapter02.psc_reclassified_outer_valid
#print axioms Chapter02.psc_reclassified_projected_order
#print axioms Chapter02.psc_reclassified_entry_exists
#print axioms Chapter02.psc_zero_r_t_all_affine
