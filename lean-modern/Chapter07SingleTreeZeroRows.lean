module

public import Chapter07SingleTreeRestoration

@[expose] public section

/-! The individual-slack L1 bridge at zero nonlinear rows, and the necessary
violated-row condition at a valid restoration anchor. These statements do not
turn an arbitrary violated trial point into an infeasible-fiber certificate. -/
noncomputable section
open Set Chapter02
open Chapter07.SingleTreeRestoration

namespace Chapter07.SingleTreeZeroRows
variable {N l r : ℕ}

/-- An empty weighted slack sum is zero, without a weight-sign premise. -/
theorem cost_zero_rows (w : Fin 0 → ℝ) (p : RealVector N × RealVector 0) :
    cost w p = 0 := by
  simp [cost]

/-- With no nonlinear rows, the nonlinear fiber is exactly its hard fiber. -/
theorem nonlinearFiber_zero_rows (D : BBPolyData N 0 r) (I : Finset (Fin N))
    (a : RealVector N) : stSourceNonlinearFiber D I a = stSourceFiber D I a := by
  ext z
  constructor
  · exact fun hz => hz.1
  · exact fun hz => ⟨hz, fun j => Fin.elim0 j⟩

/-- A supplied hard-feasible point gives an attained zero vector value.
No attained value is assigned when the hard fiber is empty. -/
theorem zero_rows_vector_minimum (D : BBPolyData N 0 r) (I : Finset (Fin N))
    (a : RealVector N) (w : Fin 0 → ℝ) (z : RealVector N)
    (hz : z ∈ stSourceFiber D I a) :
    IsMinimizer (vectorSet D I a) (cost w) (z, fun j => Fin.elim0 j) ∧
      cost w (z, fun j => Fin.elim0 j) = 0 := by
  refine ⟨⟨⟨hz, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩, ?_⟩,
    cost_zero_rows w _⟩
  intro p _
  rw [cost_zero_rows, cost_zero_rows]

/-- Valid restoration supplies an empty nonlinear fiber and a hard-feasible
anchor. Therefore at least one nonlinear row is strictly violated there. -/
theorem restoration_has_violated_row (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (b : STSourceBatch N) (hb : stSourceBatchValid D I w b)
    (he : b.restoration = true) : ∃ j, 0 < D.c b.anchor j := by
  classical
  have hr : stSourceNonlinearFiber D I b.anchor = ∅ ∧
      IsMinimizer (stSourceFiber D I b.anchor)
        (weightedPositive w (fun j z => D.c z j)) b.anchor := by
    simpa [he] using hb.2
  by_contra h
  push_neg at h
  have hm : b.anchor ∈ stSourceNonlinearFiber D I b.anchor := ⟨hr.2.1, h⟩
  rw [hr.1] at hm
  exact hm

/-- Reuse the accepted Chapter2 boundary: a valid zero-row batch cannot restore. -/
theorem zero_rows_no_restoration (D : BBPolyData N 0 r) (I : Finset (Fin N))
    (w : Fin 0 → ℝ) (b : STSourceBatch N) (hb : stSourceBatchValid D I w b) :
    b.restoration = false :=
  st_source_zero_rows_no_restoration D I w b hb

end Chapter07.SingleTreeZeroRows

#print axioms Chapter07.SingleTreeZeroRows.cost_zero_rows
#print axioms Chapter07.SingleTreeZeroRows.nonlinearFiber_zero_rows
#print axioms Chapter07.SingleTreeZeroRows.zero_rows_vector_minimum
#print axioms Chapter07.SingleTreeZeroRows.restoration_has_violated_row
#print axioms Chapter07.SingleTreeZeroRows.zero_rows_no_restoration
