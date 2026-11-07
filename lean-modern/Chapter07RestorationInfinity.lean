module

public import Chapter06LevelMaster

@[expose] public section

/-!
The source nonnegative vector-infinity restoration and the accepted nonnegative
common-slack restoration have the same lower bounds and attained values. The
finite-Pi norm is the coordinate maximum norm, including value zero for no rows.
Only the canonical constant lift identifies relaxed activity with g_j(a)=rho;
arbitrary optimal slack vectors need not have the same full active set.
-/
noncomputable section
open Set Chapter02 Chapter06.Level
namespace Chapter07.RestorationInfinity

variable {n m l r : ℕ} {d : Data n m l r}

def vectorRestoration (d : Data n m l r) (y : IntVector m) :
    Set (Point n m × RealVector l) :=
  {z | z.1 ∈ d.hardFiber y ∧ (∀ j, d.g j z.1 ≤ z.2 j) ∧ ∀ j, 0 ≤ z.2 j}

def vectorCost (z : Point n m × RealVector l) : ℝ := ‖z.2‖

def toCommon (z : Point n m × RealVector l) : Point n m × ℝ :=
  (z.1, vectorCost z)

def constantLift (z : Point n m × ℝ) : Point n m × RealVector l :=
  (z.1, fun _ => z.2)

/-- On nonnegative slacks the finite-Pi norm is precisely max({0} union {s_j}),
as expressed by its complete upper-bound characterization, also for zero rows. -/
theorem vectorCost_le_iff {z : Point n m × RealVector l}
    (hn : ∀ j, 0 ≤ z.2 j) (rho : ℝ) :
    vectorCost z ≤ rho ↔ 0 ≤ rho ∧ ∀ j, z.2 j ≤ rho := by
  constructor
  · intro h
    refine ⟨(norm_nonneg _).trans h, fun j => ?_⟩
    have hj := (norm_le_pi_norm z.2 j).trans h
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn j)] using hj
  · rintro ⟨hr, hj⟩
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro j
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn j)] using hj j

theorem vector_to_common_feasible (y : IntVector m)
    {z : Point n m × RealVector l} (hz : z ∈ vectorRestoration d y) :
    toCommon z ∈ d.restoration y := by
  refine ⟨hz.1, fun j => (hz.2.1 j).trans ?_, norm_nonneg _⟩
  have hj := norm_le_pi_norm z.2 j
  change z.2 j ≤ ‖z.2‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hz.2.2 j)] using hj

theorem constant_lift_feasible (y : IntVector m) {z : Point n m × ℝ}
    (hz : z ∈ d.restoration y) : constantLift (l := l) z ∈ vectorRestoration d y :=
  ⟨hz.1, hz.2.1, fun _ => hz.2.2⟩

theorem constant_cost_le {z : Point n m × ℝ} (hn : 0 ≤ z.2) :
    vectorCost (constantLift (l := l) z) ≤ z.2 := by
  exact (vectorCost_le_iff (fun _ => hn) z.2).mpr ⟨hn, fun _ => le_rfl⟩

theorem constant_cost [Nonempty (Fin l)] {z : Point n m × ℝ} (hn : 0 ≤ z.2) :
    vectorCost (constantLift (l := l) z) = z.2 := by
  simp [vectorCost, constantLift, pi_norm_const, Real.norm_eq_abs, abs_of_nonneg hn]

/-- Equality of all real lower bounds avoids totalizing an empty or unbounded
infimum. This holds for empty hard fibers and for an empty soft-row family. -/
theorem lower_bound_iff (y : IntVector m) (v : ℝ) :
    (∀ z ∈ vectorRestoration d y, v ≤ vectorCost z) ↔
      (∀ z ∈ d.restoration y, v ≤ z.2) := by
  constructor
  · intro h z hz
    exact (h (constantLift z) (constant_lift_feasible y hz)).trans
      (constant_cost_le hz.2.2)
  · intro h z hz
    exact h (toCommon z) (vector_to_common_feasible y hz)

/-- Any vector optimum projects to an actual common-slack optimum. -/
theorem vector_minimizer_to_common (y : IntVector m)
    {z : Point n m × RealVector l}
    (hz : IsMinimizer (vectorRestoration d y) vectorCost z) :
    IsMinimizer (d.restoration y) Prod.snd (toCommon z) := by
  refine ⟨vector_to_common_feasible y hz.1, ?_⟩
  intro q hq
  exact (hz.2 (constantLift q) (constant_lift_feasible y hq)).trans
    (constant_cost_le hq.2.2)

/-- Every common optimum has a vector optimum at its canonical constant lift. -/
theorem common_minimizer_constant (y : IntVector m) {z : Point n m × ℝ}
    (hz : IsMinimizer (d.restoration y) Prod.snd z) :
    IsMinimizer (vectorRestoration d y) vectorCost (constantLift z) := by
  refine ⟨constant_lift_feasible y hz.1, ?_⟩
  intro q hq
  exact (constant_cost_le hz.1.2.2).trans
    (hz.2 (toCommon q) (vector_to_common_feasible y hq))

/-- Even with no rows, actual common optimality forces exact cost preservation.
Without optimality, a positive scalar slack would lift to zero cost in that case. -/
theorem common_minimizer_constant_cost (y : IntVector m) {z : Point n m × ℝ}
    (hz : IsMinimizer (d.restoration y) Prod.snd z) :
    vectorCost (constantLift (l := l) z) = z.2 := by
  apply le_antisymm (constant_cost_le hz.1.2.2)
  exact hz.2 (toCommon (constantLift z))
    (vector_to_common_feasible y (constant_lift_feasible y hz.1))

theorem attained_value_iff (y : IntVector m) (v : ℝ) :
    (∃ z, IsMinimizer (vectorRestoration d y) vectorCost z ∧ vectorCost z = v) ↔
      (∃ z, IsMinimizer (d.restoration y) Prod.snd z ∧ z.2 = v) := by
  constructor
  · rintro ⟨z, hz, hv⟩
    exact ⟨toCommon z, vector_minimizer_to_common y hz, hv⟩
  · rintro ⟨z, hz, hv⟩
    exact ⟨constantLift z, common_minimizer_constant y hz,
      (common_minimizer_constant_cost y hz).trans hv⟩

theorem vector_minimum_attained (hr : Regularity d) (y : IntVector m)
    (hne : (d.hardFiber y).Nonempty) :
    ∃ z, IsMinimizer (vectorRestoration d y) vectorCost z := by
  obtain ⟨a, rho, ha⟩ := restoration_attained d hr y hne
  exact ⟨constantLift (a, rho), common_minimizer_constant y ha⟩

/-- Canonical vector activity is exactly the common-maximal residual condition. -/
theorem constant_active_iff (a : Point n m) (rho : ℝ) (j : Fin l) :
    d.g j a = (constantLift (l := l) (a, rho)).2 j ↔ d.g j a = rho := Iff.rfl

theorem selectedRows_constant_iff (a q : Point n m) (rho : ℝ) :
    (∀ j, d.g j a = (constantLift (l := l) (a, rho)).2 j →
      tangent (d.g j) a q ≤ 0) ↔ selectedRows d a rho q := Iff.rfl

/-- A common-maximal row is active for any feasible vector slack. The converse
can fail because lower residuals can be vector-active as well. -/
theorem common_maximal_vector_active (y : IntVector m)
    {z : Point n m × RealVector l} (hz : z ∈ vectorRestoration d y) (j : Fin l)
    (hj : d.g j z.1 = vectorCost z) :
    z.2 j = vectorCost z ∧ d.g j z.1 = z.2 j := by
  have hle : z.2 j ≤ vectorCost z :=
    ((vectorCost_le_iff hz.2.2 (vectorCost z)).mp le_rfl).2 j
  have hge : vectorCost z ≤ z.2 j := hj ▸ hz.2.1 j
  have he := le_antisymm hle hge
  exact ⟨he, hj.trans he.symm⟩

/-- The scalar exclusion theorem applies to a vector optimum with the explicit
common-maximal selection convention. It retains all affine normals. -/
theorem vector_minimizer_common_excludes (hr : Regularity d) (y : IntVector m)
    {z : Point n m × RealVector l} {q : Point n m}
    (hi : ¬ (d.feasibleFiber y).Nonempty)
    (hz : IsMinimizer (vectorRestoration d y) vectorCost z)
    (hq : q ∈ d.hardFiber y)
    (hrows : selectedRows d z.1 (vectorCost z) q) : False :=
  restoration_selected_excludes d hr y hi (vector_minimizer_to_common y hz) hq hrows

theorem zero_rows_cost (z : Point n m × RealVector 0) : vectorCost z = 0 := by
  have he : z.2 = 0 := Subsingleton.elim _ _
  simp [vectorCost, he]

theorem zero_rows_vector_minimum (d : Data n m 0 r) (y : IntVector m)
    {a : Point n m} (ha : a ∈ d.hardFiber y) :
    IsMinimizer (vectorRestoration d y) vectorCost (a, 0) := by
  refine ⟨⟨ha, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩, ?_⟩
  intro q _
  rw [zero_rows_cost, zero_rows_cost]

theorem zero_rows_common_minimum_iff (d : Data n m 0 r) (y : IntVector m)
    (a : Point n m) (rho : ℝ) :
    IsMinimizer (d.restoration y) Prod.snd (a, rho) ↔
      a ∈ d.hardFiber y ∧ rho = 0 := by
  constructor
  · intro h
    refine ⟨h.1.1, ?_⟩
    have hc := h.2 (a, 0) (zero_rows_restoration_minimum d y h.1.1).1
    exact le_antisymm hc h.1.2.2
  · rintro ⟨ha, rfl⟩
    exact zero_rows_restoration_minimum d y ha

end Chapter07.RestorationInfinity

#print axioms Chapter07.RestorationInfinity.vectorCost_le_iff
#print axioms Chapter07.RestorationInfinity.vector_to_common_feasible
#print axioms Chapter07.RestorationInfinity.constant_lift_feasible
#print axioms Chapter07.RestorationInfinity.constant_cost_le
#print axioms Chapter07.RestorationInfinity.constant_cost
#print axioms Chapter07.RestorationInfinity.lower_bound_iff
#print axioms Chapter07.RestorationInfinity.vector_minimizer_to_common
#print axioms Chapter07.RestorationInfinity.common_minimizer_constant
#print axioms Chapter07.RestorationInfinity.common_minimizer_constant_cost
#print axioms Chapter07.RestorationInfinity.attained_value_iff
#print axioms Chapter07.RestorationInfinity.vector_minimum_attained
#print axioms Chapter07.RestorationInfinity.constant_active_iff
#print axioms Chapter07.RestorationInfinity.selectedRows_constant_iff
#print axioms Chapter07.RestorationInfinity.common_maximal_vector_active
#print axioms Chapter07.RestorationInfinity.vector_minimizer_common_excludes
#print axioms Chapter07.RestorationInfinity.zero_rows_cost
#print axioms Chapter07.RestorationInfinity.zero_rows_vector_minimum
#print axioms Chapter07.RestorationInfinity.zero_rows_common_minimum_iff
