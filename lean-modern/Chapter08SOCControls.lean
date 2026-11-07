module

public import Chapter08QuadraticRows

@[expose] public section

/-! Exact nonvacuity and convention controls for the Euclidean source bridges.
They exercise the primary interfaces; they are not numerical experiments. -/
noncomputable section
open scoped BigOperators
namespace Chapter08.SecondOrder.Controls

def raw34 : Fin 2 → ℝ := ![3,4]
def tail34 : Tail 2 := ofCoords raw34

theorem tail34_squares : squares tail34 = 25 := by
  norm_num [squares,tail34,raw34,Fin.sum_univ_two]

theorem euclidean_norm34 : ‖tail34‖ = 5 := by
  rw [norm_eq_sqrt_squares,tail34_squares]
  norm_num

theorem function_sup_norm34 : ‖raw34‖ = 4 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤4)).mpr
    intro i
    fin_cases i <;> norm_num [raw34]
  · simpa [raw34] using norm_le_pi_norm raw34 (1 : Fin 2)

theorem euclidean_not_sup_control :
    ‖tail34‖=5 ∧ ‖raw34‖=4 ∧ soc 5 tail34 ∧ ¬soc 4 tail34 := by
  exact ⟨euclidean_norm34,function_sup_norm34,
    by norm_num [soc,euclidean_norm34],by norm_num [soc,euclidean_norm34]⟩

theorem nonzero_rotated_and_embedding :
    rsoc (5/2) 5 tail34 ∧ soc (15/2) (cons (5/2) (cons 5 tail34)) := by
  have h : rsoc (5/2) 5 tail34 := by norm_num [rsoc,tail34_squares]
  refine ⟨h,?_⟩
  convert (rsoc_iff_alternate_embedding (5/2) 5 tail34).mp h using 1 <;> norm_num

theorem nonzero_source_rotation :
    rsoc (5/Real.sqrt 2) (5/Real.sqrt 2) tail34 := by
  have h : soc 5 (cons 0 tail34) := by
    rw [soc_iff_squares,squares_cons,tail34_squares]
    norm_num
  simpa using (source_rotation 5 0 tail34).mp h

theorem zero_scale_control :
    rsoc 0 7 (0 : Tail 2) ∧ ¬rsoc 0 7 tail34 ∧
      squares (0 : Tail 2) ≤ (-1)*0 ∧ ¬rsoc 0 (-1) (0 : Tail 2) := by
  refine ⟨(square_perspective_zero _ _).mpr ⟨rfl,by norm_num⟩,?_,?_,?_⟩
  · intro h
    have := (square_perspective_zero tail34 7).mp h
    have hz := congrArg squares this.1
    rw [tail34_squares] at hz
    norm_num [squares] at hz
  · simp [squares]
  · simp [square_perspective_zero]

def weights : Fin 2 → ℝ := ![1,4]
def affineCoefficients : Fin 2 → ℝ := ![2,-3]
def point12 : Tail 2 := ofCoords ![1,2]

theorem nonzero_weighted_source_row :
    ∃ t : ℝ, rsoc (1/2) t (weightedTail weights point12) ∧
      t+(∑ i, affineCoefficients i*point12 i)+(-12) ≤ 1 := by
  have ha : ∀ i, 0≤weights i := by
    intro i
    fin_cases i <;> norm_num [weights]
  apply (weighted_quadratic_row weights affineCoefficients (-12) point12 ha).mp
  norm_num [weights,affineCoefficients,point12,Fin.sum_univ_two]

/-- The final-paper sign-loss matrix repeats the positive row. It accepts this
point although the source Lorentz condition rejects it. This is a diagnostic
for that matrix, not a modification of the standard rotation theorem. -/
theorem positive_row_duplication_witness :
    rsoc (1/Real.sqrt 2) (1/Real.sqrt 2) (0 : Tail 1) ∧
      ¬soc 0 (cons 1 (0 : Tail 1)) := by
  have h : 0 ≤ 1/Real.sqrt 2 := div_nonneg (by norm_num) sqrt_two_pos.le
  constructor
  · refine ⟨h,h,?_⟩
    simpa [squares] using mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) h) h
  · rw [soc_iff_squares,squares_cons]
    norm_num [squares]

end Chapter08.SecondOrder.Controls

#print axioms Chapter08.SecondOrder.Controls.euclidean_not_sup_control
#print axioms Chapter08.SecondOrder.Controls.nonzero_rotated_and_embedding
#print axioms Chapter08.SecondOrder.Controls.nonzero_source_rotation
#print axioms Chapter08.SecondOrder.Controls.zero_scale_control
#print axioms Chapter08.SecondOrder.Controls.nonzero_weighted_source_row
#print axioms Chapter08.SecondOrder.Controls.positive_row_duplication_witness
