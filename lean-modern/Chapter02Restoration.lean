module

public import Chapter02ESH
public import Chapter02Epigraph

@[expose] public section

/-! Source free-slack restoration and signed margins. The original nonlinear
rows are all replaced by g_j - slack, without a slack sign bound. Fixed y is
an explicit fiber set, not an implicit modification of the model's bounds.
Attainment is derived on compact nonempty original fibers; the free-height
lift itself is not asserted compact. No multiplier existence or algorithm
termination is assumed or concluded. -/

noncomputable section
namespace Chapter02

def ModelData.fixedLinearFiber {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) : Set (Point n m) := {p | p ∈ d.linearRegion ∧ p.2 = y}

def ModelData.fixedNonlinearFiber {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) : Set (Point n m) :=
  {p | p ∈ d.fixedLinearFiber y ∧ p ∈ d.nonlinearRegion}

@[simp] theorem mem_fixedLinearFiber {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (p : Point n m) :
    p ∈ d.fixedLinearFiber y ↔ p ∈ d.linearRegion ∧ p.2 = y := Iff.rfl

@[simp] theorem mem_fixedNonlinearFiber {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (p : Point n m) :
    p ∈ d.fixedNonlinearFiber y ↔ p ∈ d.linearRegion ∧ p.2 = y ∧
      p ∈ d.nonlinearRegion := by
  simp only [ModelData.fixedNonlinearFiber, Set.mem_setOf_eq, mem_fixedLinearFiber, and_assoc]

def RestorationPairs {E J : Type*} (S : Set E) (g : J → E → ℝ) : Set (E × ℝ) :=
  {q | q.1 ∈ S ∧ ∀ j, g j q.1 ≤ q.2}

theorem eshMaximum_lt_iff {E J : Type*} [Fintype J] [Nonempty J]
    (g : J → E → ℝ) (x : E) (a : ℝ) : eshMaximum g x < a ↔ ∀ j, g j x < a := by
  simp [eshMaximum, Finset.sup'_lt_iff]

theorem restorationPairs_eq_epigraph {E J : Type*} [Fintype J] [Nonempty J]
    (S : Set E) (g : J → E → ℝ) :
    RestorationPairs S g = EpigraphLift S (eshMaximum g) := by
  ext q
  simp [RestorationPairs, EpigraphLift, eshMaximum_le_iff]

theorem restorationPairs_minimizer_iff {E J : Type*} [Fintype J] [Nonempty J]
    (S : Set E) (g : J → E → ℝ) (q : E × ℝ) :
    IsMinimizer (RestorationPairs S g) Prod.snd q ↔
      IsMinimizer S (eshMaximum g) q.1 ∧ q.2 = eshMaximum g q.1 := by
  rw [restorationPairs_eq_epigraph]
  constructor
  · intro h
    exact ⟨epigraph_project_minimizer h, epigraph_tight_at_minimizer h⟩
  · rcases q with ⟨p, v⟩
    rintro ⟨hmin, hv⟩
    dsimp only at hv hmin
    subst v
    exact epigraph_lift_minimizer hmin

theorem signedMinimum_neg_iff {E J : Type*} [Fintype J] [Nonempty J]
    {S : Set E} {g : J → E → ℝ} {p : E} (hp : IsMinimizer S (eshMaximum g) p) :
    eshMaximum g p < 0 ↔ ∃ x ∈ S, ∀ j, g j x < 0 := by
  constructor
  · exact fun h => ⟨p, hp.1, (eshMaximum_lt_iff _ _ _).mp h⟩
  · rintro ⟨x, hx, hg⟩
    exact (hp.2 x hx).trans_lt ((eshMaximum_lt_iff _ _ _).mpr hg)

theorem signedMinimum_nonpos_iff {E J : Type*} [Fintype J] [Nonempty J]
    {S : Set E} {g : J → E → ℝ} {p : E} (hp : IsMinimizer S (eshMaximum g) p) :
    eshMaximum g p ≤ 0 ↔ ∃ x ∈ S, ∀ j, g j x ≤ 0 := by
  constructor
  · exact fun h => ⟨p, hp.1, (eshMaximum_le_iff _ _ _).mp h⟩
  · rintro ⟨x, hx, hg⟩
    exact (hp.2 x hx).trans ((eshMaximum_le_iff _ _ _).mpr hg)

theorem signedMinimum_pos_iff {E J : Type*} [Fintype J] [Nonempty J]
    {S : Set E} {g : J → E → ℝ} {p : E} (hp : IsMinimizer S (eshMaximum g) p) :
    0 < eshMaximum g p ↔ ¬ ∃ x ∈ S, ∀ j, g j x ≤ 0 := by
  rw [← signedMinimum_nonpos_iff hp, not_le]

theorem signedMinimum_zero_iff {E J : Type*} [Fintype J] [Nonempty J]
    {S : Set E} {g : J → E → ℝ} {p : E} (hp : IsMinimizer S (eshMaximum g) p) :
    eshMaximum g p = 0 ↔ (∃ x ∈ S, ∀ j, g j x ≤ 0) ∧
      ¬ ∃ x ∈ S, ∀ j, g j x < 0 := by
  rw [← signedMinimum_nonpos_iff hp, ← signedMinimum_neg_iff hp]
  exact ⟨fun h => ⟨h.le, not_lt.mpr h.ge⟩, fun h => le_antisymm h.1 (not_lt.mp h.2)⟩

theorem signedMinimum_exists {E J : Type*} [TopologicalSpace E] [Fintype J] [Nonempty J]
    {S : Set E} {g : J → E → ℝ} (hS : IsCompact S) (hne : S.Nonempty)
    (hg : ∀ j, Continuous (g j)) : ∃ p, IsMinimizer S (eshMaximum g) p :=
  compact_feasible_attainment hS hne (eshMaximum_continuous hg).continuousOn

theorem restorationPairs_minimum_attained {E J : Type*} [TopologicalSpace E]
    [Fintype J] [Nonempty J] {S : Set E} {g : J → E → ℝ}
    (hS : IsCompact S) (hne : S.Nonempty) (hg : ∀ j, Continuous (g j)) :
    ∃ q, IsMinimizer (RestorationPairs S g) Prod.snd q := by
  obtain ⟨p, hp⟩ := signedMinimum_exists hS hne hg
  exact ⟨(p, eshMaximum g p), (restorationPairs_minimizer_iff S g _).mpr ⟨hp, rfl⟩⟩

/-- Positive-part infinity violation is this finite nonnegative maximum,
whereas the source slack objective is the signed maximum. -/
def positivePartMaximum {E J : Type*} [Fintype J] [Nonempty J]
    (g : J → E → ℝ) (p : E) : ℝ := eshMaximum (fun j x => max (g j x) 0) p

theorem positivePartMaximum_eq_max {E J : Type*} [Fintype J] [Nonempty J]
    (g : J → E → ℝ) (p : E) : positivePartMaximum g p = max (eshMaximum g p) 0 := by
  apply le_antisymm
  · apply (eshMaximum_le_iff _ _ _).mpr
    intro j
    exact max_le_max ((eshMaximum_le_iff g p _).mp le_rfl j) le_rfl
  · obtain ⟨j, hj⟩ := eshMaximum_attained g p
    rw [hj]
    exact (eshMaximum_le_iff (fun j x => max (g j x) 0) p _).mp le_rfl j

theorem positivePartMaximum_eq_signed_of_infeasible {E J : Type*} [Fintype J] [Nonempty J]
    (g : J → E → ℝ) (p : E) (hp : ¬ ∀ j, g j p ≤ 0) :
    positivePartMaximum g p = eshMaximum g p := by
  have hpos : 0 < eshMaximum g p := by
    exact lt_of_not_ge (fun h => hp ((eshMaximum_le_iff g p 0).mp h))
  rw [positivePartMaximum_eq_max, max_eq_left hpos.le]

/-- The standard norm on a finite real function space is the infinity norm.
Its positive-part vector has norm exactly the finite nonnegative maximum. -/
theorem positivePartMaximum_eq_pi_norm {E J : Type*} [Fintype J] [Nonempty J]
    (g : J → E → ℝ) (p : E) :
    positivePartMaximum g p = ‖fun j => max (g j p) 0‖ := by
  apply le_antisymm
  · apply (eshMaximum_le_iff _ _ _).mpr
    intro j
    simpa only [Real.norm_eq_abs, abs_of_nonneg (le_max_right (g j p) 0)] using
      norm_le_pi_norm (fun k => max (g k p) 0) j
  · apply (pi_norm_le_iff_of_nonempty _).mpr
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (g j p) 0)]
    exact (eshMaximum_le_iff (fun j x => max (g j x) 0) p _).mp le_rfl j

theorem restorationPairs_empty_domain {E J : Type*} (g : J → E → ℝ) :
    RestorationPairs (∅ : Set E) g = ∅ := by ext q; simp [RestorationPairs]

theorem restorationPairs_unbounded_empty_rows {E J : Type*} [IsEmpty J]
    {S : Set E} (g : J → E → ℝ) (hne : S.Nonempty) :
    ∀ v : ℝ, ∃ q ∈ RestorationPairs S g, q.2 < v := by
  obtain ⟨p, hp⟩ := hne
  intro v
  exact ⟨(p, v - 1), ⟨hp, fun j => isEmptyElim j⟩, by dsimp only; linarith⟩

theorem restorationPairs_no_minimizer_empty_rows {E J : Type*} [IsEmpty J]
    (S : Set E) (g : J → E → ℝ) :
    ¬ ∃ q, IsMinimizer (RestorationPairs S g) Prod.snd q := by
  rintro ⟨q, hq⟩
  have hlow := hq.2 (q.1, q.2 - 1) ⟨hq.1.1, fun j => isEmptyElim j⟩
  dsimp only at hlow
  linarith

def ModelData.restorationModel {n m l r : ℕ} (d : ModelData n m l r) :
    ModelData (n+1) m l r where
  g := fun j p => d.g j (epiProject p) - epiHeight p
  A := fun row => Fin.cons 0 (d.A row)
  B := d.B
  rhs := d.rhs
  c1 := Fin.cons 1 (fun _ => 0)
  c2 := fun _ => 0
  lo := d.lo
  hi := d.hi

@[simp] theorem restorationModel_objective {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point (n+1) m) : d.restorationModel.objective p = epiHeight p := by
  simp [ModelData.objective, ModelData.restorationModel, LinearForm,
    Fin.sum_univ_succ, epiHeight]

@[simp] theorem restorationModel_linearRegion_iff {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point (n+1) m) :
    p ∈ d.restorationModel.linearRegion ↔ epiProject p ∈ d.linearRegion := by
  simp only [ModelData.linearRegion, Set.mem_setOf_eq, ModelData.restorationModel,
    linearForm_prepend_zero]

theorem restorationModel_fixedFiber_iff {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (p : Point (n+1) m) :
    p ∈ d.restorationModel.fixedNonlinearFiber y ↔
      (epiProject p, epiHeight p) ∈ RestorationPairs (d.fixedLinearFiber y) d.g := by
  rw [mem_fixedNonlinearFiber, restorationModel_linearRegion_iff]
  change (epiProject p ∈ d.linearRegion ∧ p.2 = y ∧
    ∀ j, d.g j (epiProject p) - epiHeight p ≤ 0) ↔
    ((epiProject p ∈ d.linearRegion ∧ p.2 = y) ∧
      ∀ j, d.g j (epiProject p) ≤ epiHeight p)
  simp only [sub_nonpos]
  tauto

theorem restorationModel_continuousRegion_iff {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point (n+1) m) :
    p ∈ d.restorationModel.nonlinearRegion ∩ d.restorationModel.linearRegion ↔
      (epiProject p, epiHeight p) ∈ RestorationPairs d.linearRegion d.g := by
  rw [Set.mem_inter_iff, restorationModel_linearRegion_iff]
  change ((∀ j, d.g j (epiProject p) - epiHeight p ≤ 0) ∧
    epiProject p ∈ d.linearRegion) ↔
    (epiProject p ∈ d.linearRegion ∧ ∀ j, d.g j (epiProject p) ≤ epiHeight p)
  simp only [sub_nonpos, and_comm]

theorem restorationModel_row_hasFDerivAt {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point (n+1) m) (j : Fin l) (D : Point n m →L[ℝ] ℝ)
    (hg : HasFDerivAt (d.g j) D (epiProject p)) :
    HasFDerivAt (d.restorationModel.g j) (epigraphDerivative D) p :=
  (hg.comp p epiProjectCLM.hasFDerivAt).sub epiHeightCLM.hasFDerivAt

theorem restorationModel_pairMinimizer_iff {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (p : Point (n+1) m) :
    IsMinimizer (d.restorationModel.fixedNonlinearFiber y) d.restorationModel.objective p ↔
      IsMinimizer (RestorationPairs (d.fixedLinearFiber y) d.g) Prod.snd
        (epiProject p, epiHeight p) := by
  constructor
  · rintro ⟨hp, hmin⟩
    refine ⟨(restorationModel_fixedFiber_iff d y p).mp hp, ?_⟩
    intro q hq
    have hq' : epiInsert q.1 q.2 ∈ d.restorationModel.fixedNonlinearFiber y := by
      apply (restorationModel_fixedFiber_iff d y _).mpr
      simpa only [epiProject_insert, epiHeight_insert] using hq
    simpa only [restorationModel_objective, epiHeight_insert] using hmin _ hq'
  · rintro ⟨hp, hmin⟩
    refine ⟨(restorationModel_fixedFiber_iff d y p).mpr hp, ?_⟩
    intro q hq
    simpa only [restorationModel_objective] using
      hmin (epiProject q, epiHeight q) ((restorationModel_fixedFiber_iff d y q).mp hq)

theorem restorationModel_minimizer_iff {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : RealVector m) (p : Point (n+1) m) :
    IsMinimizer (d.restorationModel.fixedNonlinearFiber y) d.restorationModel.objective p ↔
      IsMinimizer (d.fixedLinearFiber y) (eshMaximum d.g) (epiProject p) ∧
        epiHeight p = eshMaximum d.g (epiProject p) := by
  rw [restorationModel_pairMinimizer_iff, restorationPairs_minimizer_iff]

/-- This is the source mixed-base compactness bridge, only for an embedded
integer vector satisfying its actual bounds. It does not apply to arbitrary
real y or to the unrestricted continuous linear region. -/
theorem fixedLinearFiber_eq_base_slice {n m l r : ℕ} (d : ModelData n m l r)
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi) :
    d.fixedLinearFiber (fun i => (y i : ℝ)) =
      (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) ∩
        {p | p.2 = fun i => (y i : ℝ)} := by
  ext p
  constructor
  · rintro ⟨hpL, hpy⟩
    exact ⟨⟨hpL, y, hy, hpy⟩, hpy⟩
  · rintro ⟨⟨hpL, _⟩, hpy⟩
    exact ⟨hpL, hpy⟩

theorem source_fixedLinearFiber_compact {n m l r : ℕ} (d : ModelData n m l r)
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi)) :
    IsCompact (d.fixedLinearFiber (fun i => (y i : ℝ))) := by
  rw [fixedLinearFiber_eq_base_slice d y hy]
  exact hbase.inter_right (isClosed_eq continuous_snd continuous_const)

theorem source_signedMinimum_attained {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hne : (d.fixedLinearFiber (fun i => (y i : ℝ))).Nonempty)
    (hg : ∀ j, Continuous (d.g j)) :
    ∃ p, IsMinimizer (d.fixedLinearFiber (fun i => (y i : ℝ))) (eshMaximum d.g) p :=
  signedMinimum_exists (source_fixedLinearFiber_compact d y hy hbase) hne hg

theorem source_restoration_minimum_attained {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hne : (d.fixedLinearFiber (fun i => (y i : ℝ))).Nonempty)
    (hg : ∀ j, Continuous (d.g j)) :
    ∃ q, IsMinimizer (d.restorationModel.fixedNonlinearFiber (fun i => (y i : ℝ)))
      d.restorationModel.objective q := by
  obtain ⟨p, hp⟩ := source_signedMinimum_attained d y hy hbase hne hg
  refine ⟨epiInsert p (eshMaximum d.g p), (restorationModel_minimizer_iff d _ _).mpr ?_⟩
  simpa only [epiProject_insert, epiHeight_insert] using
    And.intro hp (rfl : eshMaximum d.g p = eshMaximum d.g p)

theorem source_restoration_positive_iff {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : RealVector m) {q : Point (n+1) m}
    (hq : IsMinimizer (d.restorationModel.fixedNonlinearFiber y) d.restorationModel.objective q) :
    0 < epiHeight q ↔ ¬ (d.fixedNonlinearFiber y).Nonempty := by
  obtain ⟨hmin, htight⟩ := (restorationModel_minimizer_iff d y q).mp hq
  rw [htight, signedMinimum_pos_iff hmin]
  rfl

theorem source_restoration_negative_iff {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : RealVector m) {q : Point (n+1) m}
    (hq : IsMinimizer (d.restorationModel.fixedNonlinearFiber y) d.restorationModel.objective q) :
    epiHeight q < 0 ↔ ∃ p ∈ d.fixedLinearFiber y, ∀ j, d.g j p < 0 := by
  obtain ⟨hmin, htight⟩ := (restorationModel_minimizer_iff d y q).mp hq
  rw [htight, signedMinimum_neg_iff hmin]

theorem source_restoration_zero_iff {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : RealVector m) {q : Point (n+1) m}
    (hq : IsMinimizer (d.restorationModel.fixedNonlinearFiber y) d.restorationModel.objective q) :
    epiHeight q = 0 ↔ (d.fixedNonlinearFiber y).Nonempty ∧
      ¬ ∃ p ∈ d.fixedLinearFiber y, ∀ j, d.g j p < 0 := by
  obtain ⟨hmin, htight⟩ := (restorationModel_minimizer_iff d y q).mp hq
  rw [htight, signedMinimum_zero_iff hmin]
  rfl

theorem restorationModel_base_eq_epigraph_base {n m l r : ℕ}
    (d : ModelData n m l r) (f : Point n m → ℝ) :
    d.restorationModel.linearRegion ∩
        IntegerCylinder (n := n+1) d.restorationModel.lo d.restorationModel.hi =
      (d.epigraphModel f).linearRegion ∩
        IntegerCylinder (n := n+1) (d.epigraphModel f).lo (d.epigraphModel f).hi := rfl

theorem restorationModel_base_not_compact {n m l r : ℕ} (d : ModelData n m l r)
    (hne : (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi).Nonempty) :
    ¬ IsCompact (d.restorationModel.linearRegion ∩
      IntegerCylinder (n := n+1) d.restorationModel.lo d.restorationModel.hi) := by
  rw [restorationModel_base_eq_epigraph_base d (fun _ => 0)]
  exact epigraphModel_base_not_compact d (fun _ => 0) hne

theorem source_restoration_empty_linear_fiber {n m l r : ℕ}
    (d : ModelData n m l r) (y : RealVector m) (hy : d.fixedLinearFiber y = ∅) :
    d.restorationModel.fixedNonlinearFiber y = ∅ := by
  ext p
  rw [restorationModel_fixedFiber_iff, hy, restorationPairs_empty_domain]
  simp only [Set.mem_empty_iff_false]

theorem source_restoration_unbounded_empty_rows {n m r : ℕ}
    (d : ModelData n m 0 r) (y : RealVector m) (hne : (d.fixedLinearFiber y).Nonempty) :
    ∀ v : ℝ, ∃ p ∈ d.restorationModel.fixedNonlinearFiber y,
      d.restorationModel.objective p < v := by
  intro v
  obtain ⟨q, hq, hlt⟩ := restorationPairs_unbounded_empty_rows d.g hne v
  refine ⟨epiInsert q.1 q.2, (restorationModel_fixedFiber_iff d y _).mpr ?_, ?_⟩
  · simpa only [epiProject_insert, epiHeight_insert] using hq
  · simpa only [restorationModel_objective, epiHeight_insert] using hlt

/-- ESH preprocessing is over continuous L, not over the integer cylinder.
Compactness of L is an additional explicit sufficient condition here. -/
theorem esh_preprocessing_minimum_attained {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (hL : IsCompact d.linearRegion)
    (hne : d.linearRegion.Nonempty) (hg : ∀ j, Continuous (d.g j)) :
    ∃ q, IsMinimizer (RestorationPairs d.linearRegion d.g) Prod.snd q :=
  restorationPairs_minimum_attained hL hne hg

theorem esh_preprocessing_strict_iff {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) {q : Point n m × ℝ}
    (hq : IsMinimizer (RestorationPairs d.linearRegion d.g) Prod.snd q) :
    q.2 < 0 ↔ ∃ p ∈ d.linearRegion, ∀ j, d.g j p < 0 := by
  obtain ⟨hmin, htight⟩ := (restorationPairs_minimizer_iff _ _ _).mp hq
  rw [htight, signedMinimum_neg_iff hmin]

@[simp] theorem restorationModel_fixedLinearFiber_iff {n m l r : ℕ}
    (d : ModelData n m l r) (y : RealVector m) (p : Point (n+1) m) :
    p ∈ d.restorationModel.fixedLinearFiber y ↔ epiProject p ∈ d.fixedLinearFiber y := by
  rw [mem_fixedLinearFiber, restorationModel_linearRegion_iff, mem_fixedLinearFiber]
  rfl

/-- The nonlinear part of the restoration Slater condition is constructible
on every nonempty fixed linear fiber by raising the free slack. This neither
makes the affine rows strict nor supplies KKT multipliers. -/
theorem source_restoration_strict_slack_exists {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : RealVector m) (hne : (d.fixedLinearFiber y).Nonempty) :
    ∃ q ∈ d.restorationModel.fixedLinearFiber y, ∀ j, d.restorationModel.g j q < 0 := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨epiInsert p (eshMaximum d.g p + 1), ?_, ?_⟩
  · apply (restorationModel_fixedLinearFiber_iff d y _).mpr
    simpa only [epiProject_insert] using hp
  · intro j
    change d.g j (epiProject (epiInsert p (eshMaximum d.g p + 1))) -
      epiHeight (epiInsert p (eshMaximum d.g p + 1)) < 0
    simp only [epiProject_insert, epiHeight_insert]
    have hle := (eshMaximum_le_iff d.g p _).mp le_rfl j
    linarith

theorem restorationModel_rows_convex {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (hg : ∀ j, ConvexOn ℝ S (d.g j)) :
    ∀ j, ConvexOn ℝ (epiProject ⁻¹' S) (d.restorationModel.g j) := by
  intro j
  exact epigraphModel_rows_convex d (d.g j) S (hg j) hg 0

/-- Pointwise agreement on an everywhere-infeasible domain gives the same
argmin predicate for signed slack and maximum positive-part violation. -/
theorem signed_positivePart_minimizer_iff {E J : Type*} [Fintype J] [Nonempty J]
    (S : Set E) (g : J → E → ℝ) (hS : ∀ p ∈ S, ¬ ∀ j, g j p ≤ 0) (p : E) :
    IsMinimizer S (eshMaximum g) p ↔ IsMinimizer S (positivePartMaximum g) p := by
  constructor
  · rintro ⟨hp, hmin⟩
    refine ⟨hp, fun x hx => ?_⟩
    rw [positivePartMaximum_eq_signed_of_infeasible g p (hS p hp),
      positivePartMaximum_eq_signed_of_infeasible g x (hS x hx)]
    exact hmin x hx
  · rintro ⟨hp, hmin⟩
    refine ⟨hp, fun x hx => ?_⟩
    have h := hmin x hx
    rwa [positivePartMaximum_eq_signed_of_infeasible g p (hS p hp),
      positivePartMaximum_eq_signed_of_infeasible g x (hS x hx)] at h

end Chapter02

#print axioms Chapter02.mem_fixedLinearFiber
#print axioms Chapter02.mem_fixedNonlinearFiber
#print axioms Chapter02.eshMaximum_lt_iff
#print axioms Chapter02.restorationPairs_eq_epigraph
#print axioms Chapter02.restorationPairs_minimizer_iff
#print axioms Chapter02.signedMinimum_neg_iff
#print axioms Chapter02.signedMinimum_nonpos_iff
#print axioms Chapter02.signedMinimum_pos_iff
#print axioms Chapter02.signedMinimum_zero_iff
#print axioms Chapter02.signedMinimum_exists
#print axioms Chapter02.restorationPairs_minimum_attained
#print axioms Chapter02.positivePartMaximum_eq_max
#print axioms Chapter02.positivePartMaximum_eq_signed_of_infeasible
#print axioms Chapter02.positivePartMaximum_eq_pi_norm
#print axioms Chapter02.restorationPairs_empty_domain
#print axioms Chapter02.restorationPairs_unbounded_empty_rows
#print axioms Chapter02.restorationPairs_no_minimizer_empty_rows
#print axioms Chapter02.restorationModel_objective
#print axioms Chapter02.restorationModel_linearRegion_iff
#print axioms Chapter02.restorationModel_fixedFiber_iff
#print axioms Chapter02.restorationModel_continuousRegion_iff
#print axioms Chapter02.restorationModel_row_hasFDerivAt
#print axioms Chapter02.restorationModel_pairMinimizer_iff
#print axioms Chapter02.restorationModel_minimizer_iff
#print axioms Chapter02.fixedLinearFiber_eq_base_slice
#print axioms Chapter02.source_fixedLinearFiber_compact
#print axioms Chapter02.source_signedMinimum_attained
#print axioms Chapter02.source_restoration_minimum_attained
#print axioms Chapter02.source_restoration_positive_iff
#print axioms Chapter02.source_restoration_negative_iff
#print axioms Chapter02.source_restoration_zero_iff
#print axioms Chapter02.restorationModel_base_eq_epigraph_base
#print axioms Chapter02.restorationModel_base_not_compact
#print axioms Chapter02.source_restoration_empty_linear_fiber
#print axioms Chapter02.source_restoration_unbounded_empty_rows
#print axioms Chapter02.esh_preprocessing_minimum_attained
#print axioms Chapter02.esh_preprocessing_strict_iff
#print axioms Chapter02.restorationModel_fixedLinearFiber_iff
#print axioms Chapter02.source_restoration_strict_slack_exists
#print axioms Chapter02.restorationModel_rows_convex
#print axioms Chapter02.signed_positivePart_minimizer_iff
