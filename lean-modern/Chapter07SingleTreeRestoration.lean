module

public import Chapter02STSourceGeometry

@[expose] public section

/-! The explicitly repaired single-tree route uses positive weighted individual
slacks. Unit weights give the source L1 norm, not common-slack infinity. -/
noncomputable section
open Set Chapter02
open scoped BigOperators
namespace Chapter07.SingleTreeRestoration
variable {N l r : ℕ}

def vectorSet (D : BBPolyData N l r) (I : Finset (Fin N)) (a : RealVector N) :
    Set (RealVector N × RealVector l) :=
  {p | p.1 ∈ stSourceFiber D I a ∧ (∀ j, D.c p.1 j ≤ p.2 j) ∧ ∀ j, 0 ≤ p.2 j}

def cost (w : Fin l → ℝ) (p : RealVector N × RealVector l) : ℝ :=
  ∑ j, w j * p.2 j

def lift (D : BBPolyData N l r) (z : RealVector N) : RealVector N × RealVector l :=
  (z, fun j => max (D.c z j) 0)

theorem lift_feasible (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) {z : RealVector N} (hz : z ∈ stSourceFiber D I a) :
    lift D z ∈ vectorSet D I a :=
  ⟨hz, fun _ => le_max_left _ _, fun _ => le_max_right _ _⟩

theorem lift_cost (D : BBPolyData N l r) (w : Fin l → ℝ) (z : RealVector N) :
    cost w (lift D z) = weightedPositive w (fun j x => D.c x j) z := rfl

theorem lower_cost (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) (w : Fin l → ℝ) (hw : ∀ j, 0 ≤ w j)
    {p : RealVector N × RealVector l} (hp : p ∈ vectorSet D I a) :
    weightedPositive w (fun j x => D.c x j) p.1 ≤ cost w p := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (max_le (hp.2.1 j) (hp.2.2 j)) (hw j)

/-- Every real lower bound agrees, even for an empty hard fiber or zero rows. -/
theorem lower_bounds_iff (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) (w : Fin l → ℝ) (hw : ∀ j, 0 ≤ w j) (v : ℝ) :
    (∀ p ∈ vectorSet D I a, v ≤ cost w p) ↔
      ∀ z ∈ stSourceFiber D I a, v ≤ weightedPositive w (fun j x => D.c x j) z := by
  constructor
  · intro h z hz
    exact h (lift D z) (lift_feasible D I a hz)
  · intro h p hp
    exact (h p.1 hp.1).trans (lower_cost D I a w hw hp)

theorem minimum_lifts (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) (w : Fin l → ℝ) (hw : ∀ j, 0 ≤ w j)
    {z : RealVector N}
    (hz : IsMinimizer (stSourceFiber D I a) (weightedPositive w (fun j x => D.c x j)) z) :
    IsMinimizer (vectorSet D I a) (cost w) (lift D z) := by
  refine ⟨lift_feasible D I a hz.1, ?_⟩
  intro p hp
  exact (hz.2 p.1 hp.1).trans (lower_cost D I a w hw hp)

theorem minimum_projects (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) (w : Fin l → ℝ) (hw : ∀ j, 0 ≤ w j)
    {p : RealVector N × RealVector l}
    (hp : IsMinimizer (vectorSet D I a) (cost w) p) :
    IsMinimizer (stSourceFiber D I a) (weightedPositive w (fun j x => D.c x j)) p.1 ∧
      cost w p = weightedPositive w (fun j x => D.c x j) p.1 := by
  have hlo := lower_cost D I a w hw hp.1
  have hhi := hp.2 (lift D p.1) (lift_feasible D I a hp.1.1)
  refine ⟨⟨hp.1.1, ?_⟩, le_antisymm hhi hlo⟩
  intro z hz
  exact hlo.trans (hp.2 (lift D z) (lift_feasible D I a hz))

theorem vector_attained (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) (w : Fin l → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hne : (stSourceFiber D I a).Nonempty) :
    ∃ p, IsMinimizer (vectorSet D I a) (cost w) p := by
  obtain ⟨z, hz⟩ := compact_feasible_attainment (st_source_fiber_compact D I a hX) hne
    (weightedPositive_continuous w (fun j x => D.c x j)
      (fun j => (continuous_apply j).comp hc)).continuousOn
  exact ⟨lift D z, minimum_lifts D I a w hw hz⟩

/-- The source norm is explicitly the sum of coordinate absolute values,
not Lean's default finite-Pi infinity norm. -/
theorem unit_cost_is_l1 (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) {p : RealVector N × RealVector l} (hp : p ∈ vectorSet D I a) :
    cost (fun _ => 1) p = ∑ j, |p.2 j| := by
  simp only [cost, one_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact (abs_of_nonneg (hp.2.2 j)).symm

/-- A raw restoration batch is also an actual source vector-slack optimum. -/
theorem batch_vector_minimum (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (hw : ∀ j, 0 ≤ w j) (b : STSourceBatch N)
    (hb : stSourceBatchValid D I w b) (he : b.restoration = true) :
    IsMinimizer (vectorSet D I b.anchor) (cost w) (lift D b.anchor) := by
  have h := hb.2
  simp only [he, Bool.true_eq, ↓reduceIte] at h
  exact minimum_lifts D I b.anchor w hw h.2

end Chapter07.SingleTreeRestoration
#print axioms Chapter07.SingleTreeRestoration.lower_bounds_iff
#print axioms Chapter07.SingleTreeRestoration.minimum_lifts
#print axioms Chapter07.SingleTreeRestoration.minimum_projects
#print axioms Chapter07.SingleTreeRestoration.vector_attained
#print axioms Chapter07.SingleTreeRestoration.unit_cost_is_l1
#print axioms Chapter07.SingleTreeRestoration.batch_vector_minimum
