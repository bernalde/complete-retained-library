module

public import Chapter02AffineBox

@[expose] public section

/-! Concrete schedule: forward-intersect one row, simultaneously compute all
its inverse coordinate bounds from the incoming box, then visit the next row.
This is not an identification with a global simultaneous Belotti operator. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

def AffineIntervalRow.impliedLo {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (L U : ℝ) (j : Fin n) : ℝ :=
  if r.coefficient j = 0 then l j else
  if 0 < r.coefficient j then (L-r.offset-r.restHi l u j)/r.coefficient j
  else (U-r.offset-r.restLo l u j)/r.coefficient j

def AffineIntervalRow.impliedHi {n : ℕ} (r : AffineIntervalRow n)
    (l u : RealVector n) (L U : ℝ) (j : Fin n) : ℝ :=
  if r.coefficient j = 0 then u j else
  if 0 < r.coefficient j then (U-r.offset-r.restLo l u j)/r.coefficient j
  else (L-r.offset-r.restHi l u j)/r.coefficient j

theorem affine_inverse_bounds {n : ℕ} (r : AffineIntervalRow n)
    (l u x : RealVector n) (L U : ℝ)
    (hx : ∀ i, l i ≤ x i ∧ x i ≤ u i)
    (hv : L ≤ r.value x ∧ r.value x ≤ U) (j : Fin n) :
    r.impliedLo l u L U j ≤ x j ∧ x j ≤ r.impliedHi l u L U j := by
  by_cases hz : r.coefficient j = 0
  · simpa [AffineIntervalRow.impliedLo, AffineIntervalRow.impliedHi, hz] using hx j
  have hs := affine_value_split r x j
  have hb := affine_rest_bounds r l u x hx j
  have hlo : L-r.offset-r.restHi l u j ≤ x j * r.coefficient j := by
    nlinarith [hv.1, hb.2]
  have hhi : x j * r.coefficient j ≤ U-r.offset-r.restLo l u j := by
    nlinarith [hv.2, hb.1]
  by_cases hp : 0 < r.coefficient j
  · simp only [AffineIntervalRow.impliedLo, AffineIntervalRow.impliedHi,
      if_neg hz, if_pos hp]
    exact ⟨(div_le_iff₀ hp).2 hlo, (le_div_iff₀ hp).2 hhi⟩
  · have hn : r.coefficient j < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
    simp only [AffineIntervalRow.impliedLo, AffineIntervalRow.impliedHi,
      if_neg hz, if_neg hp]
    exact ⟨(div_le_iff_of_neg hn).2 hhi, (le_div_iff_of_neg hn).2 hlo⟩

def affineRowStep {n : ℕ} (r : AffineIntervalRow n) : AffineBox n → AffineBox n
  | .empty => .empty
  | .interval l u _ =>
      let L := max r.lower (r.imageLo l u)
      let U := min r.upper (r.imageHi l u)
      if L ≤ U then
        AffineBox.ofBounds (fun j => max (l j) (r.impliedLo l u L U j))
          (fun j => min (u j) (r.impliedHi l u L U j))
      else .empty

theorem affine_row_step_contracts {n : ℕ} (r : AffineIntervalRow n)
    (X : AffineBox n) : (affineRowStep r X).members ⊆ X.members := by
  cases X with
  | empty => exact Set.Subset.refl _
  | interval l u h =>
    unfold affineRowStep
    dsimp only
    split_ifs with hf
    · intro x hx
      have hx' := (affine_mem_ofBounds_iff _ _ _).1 hx
      intro i
      exact ⟨(le_max_left _ _).trans (hx' i).1,
        (hx' i).2.trans (min_le_left _ _)⟩
    · exact Set.empty_subset _

theorem affine_row_step_preserves {n : ℕ} (r : AffineIntervalRow n)
    (X : AffineBox n) (x : RealVector n) (hx : x ∈ X.members) (hr : r.Holds x) :
    x ∈ (affineRowStep r X).members := by
  cases X with
  | empty => exact hx
  | interval l u h =>
    have hb := affine_image_bounds r l u x hx
    have hv : max r.lower (r.imageLo l u) ≤ r.value x ∧
        r.value x ≤ min r.upper (r.imageHi l u) :=
      ⟨max_le hr.1 hb.1, le_min hr.2 hb.2⟩
    have hf := hv.1.trans hv.2
    simp only [affineRowStep, if_pos hf]
    apply (affine_mem_ofBounds_iff _ _ _).2
    intro j
    have hi := affine_inverse_bounds r l u x _ _ hx hv j
    exact ⟨max_le (hx j).1 hi.1, le_min (hx j).2 hi.2⟩

def affinePropagate {n : ℕ} : List (AffineIntervalRow n) → AffineBox n → AffineBox n
  | [], X => X
  | r :: rs, X => affinePropagate rs (affineRowStep r X)

theorem affine_propagate_contracts {n : ℕ} (rows : List (AffineIntervalRow n))
    (X : AffineBox n) : (affinePropagate rows X).members ⊆ X.members := by
  induction rows generalizing X with
  | nil => exact Set.Subset.refl _
  | cons r rs ih => exact (ih _).trans (affine_row_step_contracts r X)

theorem affine_propagate_preserves {n : ℕ} (rows : List (AffineIntervalRow n))
    (X : AffineBox n) (x : RealVector n) (hx : x ∈ X.members)
    (hr : ∀ r ∈ rows, r.Holds x) : x ∈ (affinePropagate rows X).members := by
  induction rows generalizing X with
  | nil => exact hx
  | cons r rs ih =>
    exact ih _ (affine_row_step_preserves r X x hx (hr r (by simp)))
      (fun a ha => hr a (by simp [ha]))

/-- The base still contains all propagated constraints, nonlinear rows and
integer restrictions. The operator is the literal finite row fold above. -/
theorem affine_propagate_base_eq {n : ℕ} (rows : List (AffineIntervalRow n))
    (base : Set (RealVector n)) (X : AffineBox n)
    (hb : ∀ x ∈ base, ∀ r ∈ rows, r.Holds x) :
    base ∩ (affinePropagate rows X).members = base ∩ X.members := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, affine_propagate_contracts rows X hx.2⟩
  · intro hx
    exact ⟨hx.1, affine_propagate_preserves rows X x hx.2 (hb x hx.1)⟩

theorem affine_propagate_empty_certificate {n : ℕ}
    (rows : List (AffineIntervalRow n)) (base : Set (RealVector n)) (X : AffineBox n)
    (hb : ∀ x ∈ base, ∀ r ∈ rows, r.Holds x)
    (he : affinePropagate rows X = .empty) : base ∩ X.members = ∅ := by
  rw [← affine_propagate_base_eq rows base X hb, he]
  exact Set.inter_empty _

#print axioms affine_inverse_bounds
#print axioms affine_row_step_contracts
#print axioms affine_row_step_preserves
#print axioms affine_propagate_contracts
#print axioms affine_propagate_preserves
#print axioms affine_propagate_base_eq
#print axioms affine_propagate_empty_certificate

end Chapter02
