module

public import Chapter02Model

@[expose] public section

/-! Candidate affine finite-box arithmetic. Explicit emptiness is distinct from
ordered endpoints, including in dimension zero. No fixed-point result is claimed. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

inductive AffineBox (n : ℕ) where
  | empty
  | interval (lower upper : RealVector n) (ordered : ∀ i, lower i ≤ upper i)

def AffineBox.members {n : ℕ} : AffineBox n → Set (RealVector n)
  | .empty => ∅
  | .interval l u _ => {x | ∀ i, l i ≤ x i ∧ x i ≤ u i}

def AffineBox.ofBounds {n : ℕ} (l u : RealVector n) : AffineBox n :=
  if h : ∀ i, l i ≤ u i then .interval l u h else .empty

theorem affine_mem_ofBounds_iff {n : ℕ} (l u x : RealVector n) :
    x ∈ (AffineBox.ofBounds l u).members ↔ ∀ i, l i ≤ x i ∧ x i ≤ u i := by
  unfold AffineBox.ofBounds
  split_ifs with h
  · rfl
  · simp only [AffineBox.members, Set.mem_empty_iff_false, false_iff]
    intro hx
    exact h (fun i => (hx i).1.trans (hx i).2)

theorem affine_interval_nonempty {n : ℕ} (l u : RealVector n)
    (h : ∀ i, l i ≤ u i) : (AffineBox.interval l u h).members.Nonempty :=
  ⟨l, fun i => ⟨le_rfl, h i⟩⟩

def affineProductLo (a l u : ℝ) : ℝ := if 0 ≤ a then a*l else a*u
def affineProductHi (a l u : ℝ) : ℝ := if 0 ≤ a then a*u else a*l

theorem affine_product_bounds {a l u x : ℝ} (hx : l ≤ x ∧ x ≤ u) :
    affineProductLo a l u ≤ a*x ∧ a*x ≤ affineProductHi a l u := by
  by_cases ha : 0 ≤ a
  · simp only [affineProductLo, affineProductHi, if_pos ha]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 ha, mul_le_mul_of_nonneg_left hx.2 ha⟩
  · simp only [affineProductLo, affineProductHi, if_neg ha]
    exact ⟨mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge ha),
      mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge ha)⟩

structure AffineIntervalRow (n : ℕ) where
  coefficient : RealVector n
  offset : ℝ
  lower : ℝ
  upper : ℝ

def AffineIntervalRow.value {n : ℕ} (r : AffineIntervalRow n) (x : RealVector n) : ℝ :=
  r.offset + ∑ i, r.coefficient i * x i

def AffineIntervalRow.Holds {n : ℕ} (r : AffineIntervalRow n) (x : RealVector n) : Prop :=
  r.lower ≤ r.value x ∧ r.value x ≤ r.upper

def AffineIntervalRow.imageLo {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) : ℝ :=
  r.offset + ∑ i, affineProductLo (r.coefficient i) (l i) (u i)

def AffineIntervalRow.imageHi {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) : ℝ :=
  r.offset + ∑ i, affineProductHi (r.coefficient i) (l i) (u i)

def AffineIntervalRow.restLo {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, affineProductLo (r.coefficient i) (l i) (u i)

def AffineIntervalRow.restHi {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, affineProductHi (r.coefficient i) (l i) (u i)

theorem affine_image_bounds {n : ℕ} (r : AffineIntervalRow n)
    (l u x : RealVector n) (hx : ∀ i, l i ≤ x i ∧ x i ≤ u i) :
    r.imageLo l u ≤ r.value x ∧ r.value x ≤ r.imageHi l u := by
  unfold AffineIntervalRow.imageLo AffineIntervalRow.value AffineIntervalRow.imageHi
  constructor
  · exact add_le_add_right (Finset.sum_le_sum fun i _ => (affine_product_bounds (hx i)).1) _
  · exact add_le_add_right (Finset.sum_le_sum fun i _ => (affine_product_bounds (hx i)).2) _

theorem affine_rest_bounds {n : ℕ} (r : AffineIntervalRow n)
    (l u x : RealVector n) (hx : ∀ i, l i ≤ x i ∧ x i ≤ u i) (j : Fin n) :
    r.restLo l u j ≤ ∑ i ∈ Finset.univ.erase j, r.coefficient i * x i ∧
    (∑ i ∈ Finset.univ.erase j, r.coefficient i * x i) ≤ r.restHi l u j := by
  constructor
  · exact Finset.sum_le_sum fun i _ => (affine_product_bounds (hx i)).1
  · exact Finset.sum_le_sum fun i _ => (affine_product_bounds (hx i)).2

theorem affine_value_split {n : ℕ} (r : AffineIntervalRow n)
    (x : RealVector n) (j : Fin n) :
    r.value x = r.offset + (∑ i ∈ Finset.univ.erase j, r.coefficient i * x i) +
      r.coefficient j * x j := by
  rw [AffineIntervalRow.value, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  ring

/-- The image endpoints are attained by sign-selected corners of the box,
not asserted attainable in the full nonlinear/integer feasible set. -/
theorem affine_image_extrema {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (h : ∀ i, l i ≤ u i) :
    (∃ x ∈ (AffineBox.interval l u h).members, r.value x = r.imageLo l u) ∧
    (∃ x ∈ (AffineBox.interval l u h).members, r.value x = r.imageHi l u) := by
  constructor
  · refine ⟨(fun i => if 0 ≤ r.coefficient i then l i else u i), ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs <;> exact ⟨by first | exact le_rfl | exact h i,
        by first | exact le_rfl | exact h i⟩
    · unfold AffineIntervalRow.value AffineIntervalRow.imageLo
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      unfold affineProductLo
      split_ifs <;> rfl
  · refine ⟨(fun i => if 0 ≤ r.coefficient i then u i else l i), ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs <;> exact ⟨by first | exact le_rfl | exact h i,
        by first | exact le_rfl | exact h i⟩
    · unfold AffineIntervalRow.value AffineIntervalRow.imageHi
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      unfold affineProductHi
      split_ifs <;> rfl

#print axioms affine_mem_ofBounds_iff
#print axioms affine_interval_nonempty
#print axioms affine_product_bounds
#print axioms affine_image_bounds
#print axioms affine_rest_bounds
#print axioms affine_value_split
#print axioms affine_image_extrema

end Chapter02
