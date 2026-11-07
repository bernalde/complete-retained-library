module

public import Chapter08ContinuousHull
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Compactness of the actual finite boxed lift, including the displayed x
coordinate. No unrestricted epigraph heights are added or assumed bounded. -/
noncomputable section
open scoped BigOperators
open Set

namespace Chapter08.ContinuousHull

variable {ι : Type*} [Fintype ι] {n : ℕ}

theorem weight_le_one (D : Data ι n) {p : LiftPoint ι n}
    (hp : p ∈ lift D) (i : ι) : p.1 i ≤ 1 := by
  classical
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hp.1 j)
    (Finset.mem_univ i)
  simpa [hp.2.1] using h

theorem scaled_interval_bound {l u w z : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hl : l * w ≤ z) (hu : z ≤ u * w) : min l 0 ≤ z ∧ z ≤ max u 0 := by
  constructor
  · by_cases h : 0 ≤ l
    · rw [min_eq_right h]
      exact (mul_nonneg h hw).trans hl
    · rw [min_eq_left (le_of_not_ge h)]
      have hm := mul_le_mul_of_nonpos_left hw1 (le_of_not_ge h)
      nlinarith
  · by_cases h : 0 ≤ u
    · rw [max_eq_left h]
      have hm := mul_le_mul_of_nonneg_left hw1 h
      nlinarith
    · rw [max_eq_right (le_of_not_ge h)]
      exact hu.trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hw)

theorem block_coordinate_bound (D : Data ι n) {p : LiftPoint ι n}
    (hp : p ∈ lift D) (i : ι) (j : Fin n) :
    min (D.lower j) 0 ≤ p.2 i j ∧ p.2 i j ≤ max (D.upper j) 0 :=
  scaled_interval_bound (hp.1 i) (weight_le_one D hp i)
    (hp.2.2.2 i j).1 (hp.2.2.2 i j).2

theorem projected_inBox (D : Data ι n) {x : Vec n} (hx : x ∈ projection D) :
    InBox D.lower D.upper x := by
  rcases hx with ⟨p, hp, rfl⟩
  intro j
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    (hp.2.2.2 i j).1)
  have hu := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    (hp.2.2.2 i j).2)
  constructor
  · simpa [← Finset.mul_sum, hp.2.1, Finset.sum_apply] using hl
  · simpa [← Finset.mul_sum, hp.2.1, Finset.sum_apply] using hu

theorem fullLift_all_coordinate_bounds (D : Data ι n)
    {p : Vec n × LiftPoint ι n} (hp : p ∈ fullLift D) :
    InBox D.lower D.upper p.1 ∧
    (∀ i, 0 ≤ p.2.1 i ∧ p.2.1 i ≤ 1) ∧
    (∀ i j, min (D.lower j) 0 ≤ p.2.2 i j ∧
      p.2.2 i j ≤ max (D.upper j) 0) :=
  ⟨projected_inBox D ⟨p.2, hp.1, hp.2⟩,
    fun i => ⟨hp.1.1 i, weight_le_one D hp.1 i⟩,
    fun i j => block_coordinate_bound D hp.1 i j⟩

theorem isClosed_lift (D : Data ι n) (hK : ∀ i, IsClosed (D.cone i)) :
    IsClosed (lift D) := by
  have hn : IsClosed {p : LiftPoint ι n | ∀ i, 0 ≤ p.1 i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_apply i).comp continuous_fst)
  have hs : IsClosed {p : LiftPoint ι n | (∑ i, p.1 i) = 1} := by
    exact isClosed_eq (by fun_prop) continuous_const
  have hc : IsClosed {p : LiftPoint ι n |
      ∀ i, D.map i (p.2 i) - p.1 i • D.offset i ∈ D.cone i} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    apply (hK i).preimage
    exact ((D.map i).continuous_of_finiteDimensional.comp
      ((continuous_apply i).comp continuous_snd)).sub
      (((continuous_apply i).comp continuous_fst).smul continuous_const)
  have hb : IsClosed {p : LiftPoint ι n |
      ∀ i j, D.lower j * p.1 i ≤ p.2 i j ∧ p.2 i j ≤ D.upper j * p.1 i} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    exact (isClosed_le
      (f := fun p : LiftPoint ι n => D.lower j * p.1 i)
      (g := fun p : LiftPoint ι n => p.2 i j) (by fun_prop) (by fun_prop)).inter
      (isClosed_le (f := fun p : LiftPoint ι n => p.2 i j)
        (g := fun p : LiftPoint ι n => D.upper j * p.1 i) (by fun_prop) (by fun_prop))
  exact hn.inter (hs.inter (hc.inter hb))

/-- A concrete compact containing box bounds both weights and every copied
coordinate. The finite-dimensional cone constraints are a closed subset. -/
theorem isCompact_lift (D : Data ι n) (hK : ∀ i, IsClosed (D.cone i)) :
    IsCompact (lift D) := by
  let B : Set (LiftPoint ι n) :=
    (Icc (fun _ : ι => (0 : ℝ)) (fun _ => (1 : ℝ))) ×ˢ
      (Icc (fun (_ : ι) (j : Fin n) => min (D.lower j) 0)
        (fun (_ : ι) (j : Fin n) => max (D.upper j) 0))
  have hB : IsCompact B := isCompact_Icc.prod isCompact_Icc
  apply hB.of_isClosed_subset (isClosed_lift D hK)
  intro p hp
  exact ⟨⟨hp.1, fun i => weight_le_one D hp i⟩,
    ⟨fun i j => (block_coordinate_bound D hp i j).1,
      fun i j => (block_coordinate_bound D hp i j).2⟩⟩

theorem projection_eq_image (D : Data ι n) :
    projection D = (fun p : LiftPoint ι n => ∑ i, p.2 i) '' lift D := by
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    exact ⟨p, hp, hx.symm⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨p, hp, hx.symm⟩

theorem fullLift_eq_image (D : Data ι n) :
    fullLift D = (fun p : LiftPoint ι n => (∑ i, p.2 i, p)) '' lift D := by
  ext p
  constructor
  · intro hp
    refine ⟨p.2, hp.1, ?_⟩
    exact Prod.ext hp.2.symm rfl
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq, rfl⟩

theorem isCompact_fullLift (D : Data ι n) (hK : ∀ i, IsClosed (D.cone i)) :
    IsCompact (fullLift D) := by
  rw [fullLift_eq_image]
  exact (isCompact_lift D hK).image (by fun_prop)

theorem isCompact_projection (D : Data ι n) (hK : ∀ i, IsClosed (D.cone i)) :
    IsCompact (projection D) := by
  rw [projection_eq_image]
  exact (isCompact_lift D hK).image (by fun_prop)

theorem isClosed_projection (D : Data ι n) (hK : ∀ i, IsClosed (D.cone i)) :
    IsClosed (projection D) := (isCompact_projection D hK).isClosed

theorem closed_hull_exact (D : Data ι n) (hD : Conic D)
    (hK : ∀ i, IsClosed (D.cone i)) :
    closure (convexHull ℝ (boundedUnion D)) = projection D := by
  rw [← continuous_hull_exact D hD]
  exact (isClosed_projection D hK).closure_eq

end Chapter08.ContinuousHull

#print axioms Chapter08.ContinuousHull.weight_le_one
#print axioms Chapter08.ContinuousHull.scaled_interval_bound
#print axioms Chapter08.ContinuousHull.block_coordinate_bound
#print axioms Chapter08.ContinuousHull.projected_inBox
#print axioms Chapter08.ContinuousHull.fullLift_all_coordinate_bounds
#print axioms Chapter08.ContinuousHull.isClosed_lift
#print axioms Chapter08.ContinuousHull.isCompact_lift
#print axioms Chapter08.ContinuousHull.projection_eq_image
#print axioms Chapter08.ContinuousHull.fullLift_eq_image
#print axioms Chapter08.ContinuousHull.isCompact_fullLift
#print axioms Chapter08.ContinuousHull.isCompact_projection
#print axioms Chapter08.ContinuousHull.isClosed_projection
#print axioms Chapter08.ContinuousHull.closed_hull_exact
