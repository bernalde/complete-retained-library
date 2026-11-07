module

public import Chapter08
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-! Bounded continuous HR-Cone: literal dependent residual dimensions.
Source: ChCones/cones.tex 560–610, with the finite scaled coordinate bounds
actually present in HR-Cone. This is not the unrestricted adopted hull theorem.
Empty branches and an empty index type are permitted. -/
noncomputable section
open scoped BigOperators
open Set

namespace Chapter08.ContinuousHull

structure Data (ι : Type*) (n : ℕ) where
  dim : ι → ℕ
  map : (i : ι) → Vec n →ₗ[ℝ] Vec (dim i)
  offset : (i : ι) → Vec (dim i)
  cone : (i : ι) → Set (Vec (dim i))
  lower : Vec n
  upper : Vec n

structure Conic {ι : Type*} {n : ℕ} (D : Data ι n) : Prop where
  zero_mem : ∀ i, 0 ∈ D.cone i
  convex : ∀ i, Convex ℝ (D.cone i)
  smul_mem : ∀ i (a : ℝ), 0 ≤ a → ∀ z ∈ D.cone i, a • z ∈ D.cone i

variable {ι : Type*} [Fintype ι] {n : ℕ}

abbrev LiftPoint (ι : Type*) (n : ℕ) := (ι → ℝ) × (ι → Vec n)

def branch (D : Data ι n) (i : ι) : Set (Vec n) :=
  {x | InBox D.lower D.upper x ∧ D.map i x - D.offset i ∈ D.cone i}

def boundedUnion (D : Data ι n) : Set (Vec n) := ⋃ i, branch D i

def lift (D : Data ι n) : Set (LiftPoint ι n) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ (∑ i, p.1 i) = 1 ∧
    (∀ i, D.map i (p.2 i) - p.1 i • D.offset i ∈ D.cone i) ∧
    (∀ i j, D.lower j * p.1 i ≤ p.2 i j ∧ p.2 i j ≤ D.upper j * p.1 i)}

def projection (D : Data ι n) : Set (Vec n) :=
  {x | ∃ p ∈ lift D, x = ∑ i, p.2 i}

/-- The literal full system retains the displayed x coordinate and its equality. -/
def fullLift (D : Data ι n) : Set (Vec n × LiftPoint ι n) :=
  {p | p.2 ∈ lift D ∧ p.1 = ∑ i, p.2.2 i}

theorem zero_block (D : Data ι n) {p : LiftPoint ι n} (hp : p ∈ lift D)
    (i : ι) (hi : p.1 i = 0) : p.2 i = 0 :=
  Chapter08.zero_weight_box_forces_zero D.lower D.upper (p.2 i) (p.1 i) hi
    (hp.2.2.2 i)

theorem normalized_block (D : Data ι n) (hD : Conic D)
    {p : LiftPoint ι n} (hp : p ∈ lift D) (i : ι) (hi : 0 < p.1 i) :
    (p.1 i)⁻¹ • p.2 i ∈ branch D i := by
  constructor
  · intro j
    change D.lower j ≤ (p.1 i)⁻¹ * p.2 i j ∧
      (p.1 i)⁻¹ * p.2 i j ≤ D.upper j
    have hl := mul_le_mul_of_nonneg_left (hp.2.2.2 i j).1 (inv_nonneg.mpr hi.le)
    have hu := mul_le_mul_of_nonneg_left (hp.2.2.2 i j).2 (inv_nonneg.mpr hi.le)
    constructor
    · simpa [← mul_assoc, inv_mul_cancel₀ hi.ne', mul_comm] using hl
    · simpa [← mul_assoc, inv_mul_cancel₀ hi.ne', mul_comm] using hu
  · have h := hD.smul_mem i (p.1 i)⁻¹ (inv_nonneg.mpr hi.le) _ (hp.2.2.1 i)
    simpa [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hi.ne'] using h

theorem convex_lift (D : Data ι n) (hK : ∀ i, Convex ℝ (D.cone i)) :
    Convex ℝ (lift D) := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    change 0 ≤ a * p.1 i + b * q.1 i
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · change (∑ i, (a * p.1 i + b * q.1 i)) = 1
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2.1, hq.2.1, hab]
  · intro i
    have h := hK i (hp.2.2.1 i) (hq.2.2.1 i) ha hb hab
    convert h using 1 <;> ext j <;>
      simp [map_add, map_smul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul] <;> ring
  · intro i j
    change D.lower j * (a * p.1 i + b * q.1 i) ≤
        a * p.2 i j + b * q.2 i j ∧
      a * p.2 i j + b * q.2 i j ≤ D.upper j * (a * p.1 i + b * q.1 i)
    have hlp := mul_le_mul_of_nonneg_left (hp.2.2.2 i j).1 ha
    have hlq := mul_le_mul_of_nonneg_left (hq.2.2.2 i j).1 hb
    have hup := mul_le_mul_of_nonneg_left (hp.2.2.2 i j).2 ha
    have huq := mul_le_mul_of_nonneg_left (hq.2.2.2 i j).2 hb
    constructor <;> nlinarith

theorem convex_projection (D : Data ι n) (hK : ∀ i, Convex ℝ (D.cone i)) :
    Convex ℝ (projection D) := by
  rintro x ⟨p, hp, hx⟩ y ⟨q, hq, hy⟩ a b ha hb hab
  refine ⟨a • p + b • q, convex_lift D hK hp hq ha hb hab, ?_⟩
  rw [hx, hy]
  change a • (∑ i, p.2 i) + b • (∑ i, q.2 i) =
    ∑ i, (a • p.2 i + b • q.2 i)
  simp [Finset.sum_add_distrib, ← Finset.smul_sum]

theorem union_subset_projection (D : Data ι n) (hK0 : ∀ i, 0 ∈ D.cone i) :
    boundedUnion D ⊆ projection D := by
  classical
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  refine ⟨⟨(fun j => if j = i then 1 else 0), (fun j => if j = i then x else 0)⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    change 0 ≤ (if j = i then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  · simp
  · intro j; by_cases h : j = i
    · subst j; simpa using hi.2
    · simpa [h] using hK0 j
  · intro j k; by_cases h : j = i
    · subst j; simpa using hi.1 k
    · simp [h]
  · simp

/-- Only positive blocks enter the convex combination; no branch witness is
chosen for a zero weight or an empty branch. -/
theorem projection_subset_convexHull (D : Data ι n) (hD : Conic D) :
    projection D ⊆ convexHull ℝ (boundedUnion D) := by
  classical
  rintro x ⟨p, hp, hx⟩
  let s : Finset ι := Finset.univ.filter (fun i => 0 < p.1 i)
  have hs : ∀ i, i ∈ s ↔ 0 < p.1 i := by intro i; simp [s]
  have hz : ∀ i, i ∉ s → p.1 i = 0 := by
    intro i hi
    exact le_antisymm (le_of_not_gt (fun h => hi ((hs i).2 h))) (hp.1 i)
  have hsum : (∑ i ∈ s, p.1 i) = 1 := by
    calc
      (∑ i ∈ s, p.1 i) = ∑ i, p.1 i := by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _ hi
        exact hz i hi
      _ = 1 := hp.2.1
  have hmem : ∀ i ∈ s, (p.1 i)⁻¹ • p.2 i ∈ convexHull ℝ (boundedUnion D) := by
    intro i hi
    exact subset_convexHull ℝ _ (mem_iUnion.mpr
      ⟨i, normalized_block D hD hp i ((hs i).1 hi)⟩)
  have hc := (convex_convexHull ℝ (boundedUnion D)).sum_mem
    (fun i (_ : i ∈ s) => hp.1 i) hsum hmem
  have heq : (∑ i ∈ s, p.1 i • ((p.1 i)⁻¹ • p.2 i)) = x := by
    calc
      (∑ i ∈ s, p.1 i • ((p.1 i)⁻¹ • p.2 i)) = ∑ i ∈ s, p.2 i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [smul_smul, mul_inv_cancel₀ ((hs i).1 hi).ne']
      _ = ∑ i, p.2 i := by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _ hi
        exact zero_block D hp i (hz i hi)
      _ = x := hx.symm
  exact heq ▸ hc

theorem continuous_hull_exact (D : Data ι n) (hD : Conic D) :
    projection D = convexHull ℝ (boundedUnion D) :=
  Set.Subset.antisymm (projection_subset_convexHull D hD)
    (convexHull_min (union_subset_projection D hD.zero_mem)
      (convex_projection D hD.convex))

theorem empty_branch_weight_zero (D : Data ι n) (hD : Conic D)
    {p : LiftPoint ι n} (hp : p ∈ lift D) (i : ι) (hi : branch D i = ∅) :
    p.1 i = 0 := by
  by_contra hn
  have hp' : 0 < p.1 i := lt_of_le_of_ne (hp.1 i) (Ne.symm hn)
  have hm := normalized_block D hD hp i hp'
  rw [hi] at hm
  exact hm

theorem empty_branch_block_zero (D : Data ι n) (hD : Conic D)
    {p : LiftPoint ι n} (hp : p ∈ lift D) (i : ι) (hi : branch D i = ∅) :
    p.2 i = 0 := zero_block D hp i (empty_branch_weight_zero D hD hp i hi)

theorem projection_empty_index [IsEmpty ι] (D : Data ι n) : projection D = ∅ := by
  ext x
  simp [projection, lift]

theorem all_empty_projection (D : Data ι n) (hD : Conic D)
    (he : ∀ i, branch D i = ∅) : projection D = ∅ := by
  rw [continuous_hull_exact D hD]
  simp [boundedUnion, he]

end Chapter08.ContinuousHull

#print axioms Chapter08.ContinuousHull.zero_block
#print axioms Chapter08.ContinuousHull.normalized_block
#print axioms Chapter08.ContinuousHull.convex_lift
#print axioms Chapter08.ContinuousHull.convex_projection
#print axioms Chapter08.ContinuousHull.union_subset_projection
#print axioms Chapter08.ContinuousHull.projection_subset_convexHull
#print axioms Chapter08.ContinuousHull.continuous_hull_exact
#print axioms Chapter08.ContinuousHull.empty_branch_weight_zero
#print axioms Chapter08.ContinuousHull.empty_branch_block_zero
#print axioms Chapter08.ContinuousHull.projection_empty_index
#print axioms Chapter08.ContinuousHull.all_empty_projection
