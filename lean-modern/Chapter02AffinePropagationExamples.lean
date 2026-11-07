module

public import Chapter02AffinePropagationSource

@[expose] public section

/-! Full operator controls, not independent scalar arithmetic witnesses.
The infeasible unchanged-box example does not assert a fixed-point theorem. -/
noncomputable section
open scoped BigOperators
namespace Chapter02.AffinePropagationExamples

def unitBox (n : ℕ) : AffineBox n :=
  .interval (fun _ => 0) (fun _ => 1) (by intro; norm_num)

def symmetricBox (n : ℕ) : AffineBox n :=
  .interval (fun _ => -1) (fun _ => 1) (by intro; norm_num)

def singletonBox {n : ℕ} (x : RealVector n) : AffineBox n :=
  .interval x x (fun _ => le_rfl)

def differenceRow : AffineIntervalRow 2 := ⟨![1,-1],0,1,1⟩

def zeroRow (n : ℕ) (b : ℝ) : AffineIntervalRow n := ⟨0,0,b,b⟩

macro "affine_numeric" : tactic => `(tactic|
  norm_num [affineRowStep, AffineBox.ofBounds, AffineIntervalRow.imageLo,
    AffineIntervalRow.imageHi, AffineIntervalRow.impliedLo,
    AffineIntervalRow.impliedHi, AffineIntervalRow.restLo, AffineIntervalRow.restHi,
    affineProductLo, affineProductHi, Finset.sum_erase_eq_sub,
    Fin.sum_univ_succ, Fin.forall_fin_succ])

private theorem difference_step_computed :
    affineRowStep differenceRow (unitBox 2) = singletonBox ![1,0] := by
  unfold differenceRow unitBox singletonBox
  affine_numeric
  constructor <;> funext j <;> fin_cases j <;> norm_num

theorem strict_negative_tightening_control :
    affineRowStep differenceRow (unitBox 2) = singletonBox ![1,0] ∧
    differenceRow.coefficient 1 = -1 ∧ differenceRow.Holds ![1,0] ∧
    ![1,0] ∈ (affineRowStep differenceRow (unitBox 2)).members ∧
    (0 : RealVector 2) ∈ (unitBox 2).members ∧
    (0 : RealVector 2) ∉ (affineRowStep differenceRow (unitBox 2)).members := by
  rw [difference_step_computed]
  norm_num [differenceRow, AffineIntervalRow.Holds, AffineIntervalRow.value,
    unitBox, singletonBox, AffineBox.members, Fin.forall_fin_succ, Fin.sum_univ_succ]

theorem zero_row_control {n : ℕ} (X : AffineBox n) :
    affineRowStep (zeroRow n 0) X = X ∧
    affineRowStep (zeroRow n 1) X = .empty := by
  cases X with
  | empty => exact ⟨rfl,rfl⟩
  | interval l u ho =>
    constructor
    · simp [affineRowStep, zeroRow, AffineIntervalRow.imageLo,
        AffineIntervalRow.imageHi, affineProductLo, affineProductHi,
        AffineIntervalRow.impliedLo, AffineIntervalRow.impliedHi,
        AffineBox.ofBounds, ho]
    · norm_num [affineRowStep, zeroRow, AffineIntervalRow.imageLo,
        AffineIntervalRow.imageHi, affineProductLo, affineProductHi]

theorem empty_input_control {n : ℕ} (rows : List (AffineIntervalRow n)) :
    affinePropagate rows .empty = .empty ∧
    ∀ X : AffineBox n, affinePropagate [] X = X := by
  refine ⟨?_,fun _ => rfl⟩
  induction rows with
  | nil => rfl
  | cons r rs ih => simpa [affinePropagate, affineRowStep] using ih

theorem zero_dimension_and_rows_control :
    (unitBox 0).members = {(0 : RealVector 0)} ∧
    unitBox 0 ≠ .empty ∧ affinePropagate [] (unitBox 0) = unitBox 0 ∧
    affineRowStep (zeroRow 0 1) (unitBox 0) = .empty := by
  refine ⟨?_,by simp [unitBox],rfl,(zero_row_control _).2⟩
  ext x
  simp [unitBox, AffineBox.members, Subsingleton.elim x 0]

theorem already_tight_control :
    affineRowStep differenceRow (singletonBox ![1,0]) = singletonBox ![1,0] := by
  unfold differenceRow singletonBox
  affine_numeric
  constructor <;> funext j <;> fin_cases j <;> norm_num

/-- The inactive coordinate stays free: zero is not divided through or
replaced by a free product variable, even while another coordinate tightens. -/
theorem zero_coefficient_control :
    let row : AffineIntervalRow 2 := ⟨![1,0],0,1,1⟩
    let X := AffineBox.interval (![1,0] : RealVector 2) ![1,1]
      (by intro i; fin_cases i <;> norm_num)
    affineRowStep row (unitBox 2) = X ∧
    row.Holds ![1,1/2] ∧ ![1,1/2] ∈ (affineRowStep row (unitBox 2)).members := by
  dsimp only
  have heq : affineRowStep (⟨![1,0],0,1,1⟩ : AffineIntervalRow 2) (unitBox 2) =
      AffineBox.interval ![1,0] ![1,1] (by intro i; fin_cases i <;> norm_num) := by
    unfold unitBox
    affine_numeric
    constructor <;> funext j <;> fin_cases j <;> norm_num
  rw [heq]
  norm_num [AffineIntervalRow.Holds, AffineIntervalRow.value,
    AffineBox.members, Fin.sum_univ_succ, Fin.forall_fin_succ]

def inconsistentRow (i : Fin 4) : AffineIntervalRow 3 where
  coefficient := ![![1,1,1],![1,1,-1],![1,-1,1],![-1,1,1]] i
  offset := 0
  lower := ![0,0,0,1] i
  upper := ![0,0,0,1] i

def inconsistentRows : List (AffineIntervalRow 3) :=
  [inconsistentRow 0,inconsistentRow 1,inconsistentRow 2,inconsistentRow 3]

private theorem inconsistent_row_step (i : Fin 4) :
    affineRowStep (inconsistentRow i) (symmetricBox 3) = symmetricBox 3 := by
  fin_cases i <;> unfold inconsistentRow symmetricBox <;> affine_numeric
  all_goals constructor <;> funext j <;> fin_cases j <;> norm_num

theorem unchanged_infeasible_box_control :
    affinePropagate inconsistentRows (symmetricBox 3) = symmetricBox 3 ∧
    (symmetricBox 3).members.Nonempty ∧
    ¬ ∃ x ∈ (symmetricBox 3).members, ∀ r ∈ inconsistentRows, r.Holds x := by
  refine ⟨?_,⟨0,by intro i; norm_num [symmetricBox, AffineBox.members]⟩,?_⟩
  · simp only [inconsistentRows, affinePropagate, inconsistent_row_step]
  · rintro ⟨x,_,h⟩
    have h0 := h (inconsistentRow 0) (by simp [inconsistentRows])
    have h1 := h (inconsistentRow 1) (by simp [inconsistentRows])
    have h2 := h (inconsistentRow 2) (by simp [inconsistentRows])
    have h3 := h (inconsistentRow 3) (by simp [inconsistentRows])
    norm_num [inconsistentRow, AffineIntervalRow.Holds, AffineIntervalRow.value,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] at h0 h1 h2 h3
    linarith

/-- Equality is represented by two retained affine inequalities; the model
also retains a nonlinear row and one designated integer coordinate. -/
def mixedSource : BBPolyData 2 1 2 where
  coefficient := ![![1,-1],![-1,1]]
  rhs := ![1,-1]
  c := fun x => ![x 0 ^ 2-1]
  f := fun x => x 0+x 1

private theorem mixed_source_computed :
    affineSourcePropagate mixedSource (unitBox 2) [0,1] = singletonBox ![1,0] := by
  have h0 : affineRowStep (affineSourceRow mixedSource (unitBox 2) 0) (unitBox 2) =
      unitBox 2 := by
    unfold affineSourceRow mixedSource unitBox
    affine_numeric
    constructor <;> funext j <;> fin_cases j <;> norm_num
  change affineRowStep (affineSourceRow mixedSource (unitBox 2) 1)
    (affineRowStep (affineSourceRow mixedSource (unitBox 2) 0) (unitBox 2)) = _
  rw [h0]
  unfold affineSourceRow mixedSource unitBox singletonBox
  affine_numeric
  constructor <;> funext j <;> fin_cases j <;> norm_num

theorem mixed_source_control :
    affineSourcePropagate mixedSource (unitBox 2) [0,1] = singletonBox ![1,0] ∧
    ![1,0] ∈ mixedSource.feasible {0} ∧
    ![1,0] ∈ (affineSourcePropagate mixedSource (unitBox 2) [0,1]).members ∧
    mixedSource.feasible {0} ∩
        (affineSourcePropagate mixedSource (unitBox 2) [0,1]).members =
      mixedSource.feasible {0} ∩ (unitBox 2).members := by
  have hf : ![1,0] ∈ mixedSource.feasible {0} := by
    refine ⟨?_,?_,?_⟩
    · intro i
      fin_cases i <;> norm_num [mixedSource, Fin.sum_univ_succ]
    · intro j
      fin_cases j
      norm_num [mixedSource]
    · intro i
      refine ⟨1,?_⟩
      have hi : (i : Fin 2) = 0 := Finset.mem_singleton.mp i.property
      simp [hi]
  have hx : ![1,0] ∈ (unitBox 2).members := by
    norm_num [unitBox, AffineBox.members, Fin.forall_fin_succ]
  have heq := affine_source_preservation mixedSource {0} (unitBox 2) [0,1]
  exact ⟨mixed_source_computed,hf,((Set.ext_iff.mp heq ![1,0]).2 ⟨hf,hx⟩).2,heq⟩

#print axioms strict_negative_tightening_control
#print axioms zero_row_control
#print axioms empty_input_control
#print axioms zero_dimension_and_rows_control
#print axioms already_tight_control
#print axioms zero_coefficient_control
#print axioms unchanged_infeasible_box_control
#print axioms mixed_source_control

end Chapter02.AffinePropagationExamples
