module

public import Chapter03OAKKTMaps
public import Chapter03OAKKTBoundaryConsumers

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAKKTBoundary

/-- Distinct initial/current slots imply this exact finite cardinality bound. -/
theorem history_requires_two_slots {n m l r k : ℕ} {d : ModelData n m l r}
    {f : Point n m → ℝ} {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {y : RealVector m}
    (H : History d f N c df x y) : 2 ≤ k := by
  have hs := H.seed.isLt
  have hc := H.current.isLt
  have hn : H.seed.val ≠ H.current.val := fun h => H.distinct (Fin.ext h)
  omega

def unboundedBounds : Bounds 1 where
  lower := fun _ => .negInfinity
  upper := fun _ => .posInfinity

def unboundedEncoding : HardBoundEncoding unboundedBounds (emptyData 1) where
  valid := by intro i; simp [unboundedBounds]
  side := fun i => Fin.elim0 i
  injective := by intro i; exact Fin.elim0 i
  lower_cover := by intro i a h; simp [unboundedBounds] at h
  upper_cover := by intro i a h; simp [unboundedBounds] at h
  row_spec := fun i => Fin.elim0 i

theorem unbounded_bounds_region : unboundedBounds.region = Set.univ := by
  ext x
  simp [Bounds.region,unboundedBounds,ExtendedBound.lowerHolds,ExtendedBound.upperHolds]

/-- In this exact single-coordinate encoding there can be no hard side at all;
a fictitious finite side cannot satisfy row_spec. -/
theorem unbounded_encoding_no_artificial_rows {m l r : ℕ}
    (d : ModelData 1 m l r) (E : HardBoundEncoding unboundedBounds d) : r=0 := by
  by_contra h
  have hr : 0 < r := Nat.pos_of_ne_zero h
  let j : Fin r := ⟨0,hr⟩
  have hs := E.row_spec j
  cases he : E.side j with
  | inl i =>
    rw [he] at hs
    obtain ⟨a,ha,_⟩ := hs
    simp [unboundedBounds] at ha
  | inr i =>
    rw [he] at hs
    obtain ⟨a,ha,_⟩ := hs
    simp [unboundedBounds] at ha

def intervalBounds (lo hi : ℝ) : Bounds 1 where
  lower := fun _ => .finite lo
  upper := fun _ => .finite hi

def intervalEncoding (lo hi : ℝ) : HardBoundEncoding (intervalBounds lo hi) (intervalData lo hi) where
  valid := by intro i; simp [intervalBounds]
  side := ![Sum.inl 0,Sum.inr 0]
  injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  lower_cover := by
    intro i a h
    fin_cases i
    exact ⟨0,rfl⟩
  upper_cover := by
    intro i a h
    fin_cases i
    exact ⟨1,rfl⟩
  row_spec := by
    intro j
    fin_cases j
    · refine ⟨lo,rfl,?_⟩
      intro p
      simp [linearResidual,intervalData,LinearForm,vec]
      ring
    · refine ⟨hi,rfl,?_⟩
      intro p
      simp [linearResidual,intervalData,LinearForm,vec]

theorem interval_bounds_correspondence (lo hi : ℝ) (x : RealVector 1) :
    x ∈ (intervalBounds lo hi).region ↔ (x,0) ∈ (intervalData lo hi).linearRegion :=
  (intervalEncoding lo hi).region_iff x 0

theorem reversed_bounds_empty : (intervalBounds 1 0).region = ∅ :=
  Bounds.reversed_finite_empty (intervalBounds 1 0) 0 1 0 rfl rfl (by norm_num)

theorem fixed_encoding_retains_distinct_sides :
    (intervalEncoding 2 2).side 0 = Sum.inl 0 ∧
    (intervalEncoding 2 2).side 1 = Sum.inr 0 ∧
    (intervalEncoding 2 2).side 0 ≠ (intervalEncoding 2 2).side 1 := by
  simp [intervalEncoding]

theorem fixed_encoding_actual_normals (v : RealVector 1) :
    fiberLinearRow (intervalData 2 2) 0 v = -v 0 ∧
    fiberLinearRow (intervalData 2 2) 1 v = v 0 :=
  ⟨(intervalEncoding 2 2).lower_normal 0 0 rfl v,
   (intervalEncoding 2 2).upper_normal 1 0 rfl v⟩

def splitSoftEncoding : HardBoundEncoding unboundedBounds splitSoftData where
  valid := by intro i; simp [unboundedBounds]
  side := fun i => Fin.elim0 i
  injective := by intro i; exact Fin.elim0 i
  lower_cover := by intro i a h; simp [unboundedBounds] at h
  upper_cover := by intro i a h; simp [unboundedBounds] at h
  row_spec := fun i => Fin.elim0 i

def splitHardEncoding : HardBoundEncoding (intervalBounds 0 1) splitHardData where
  valid := by intro i; simp [intervalBounds]
  side := ![Sum.inl 0,Sum.inr 0]
  injective := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  lower_cover := by intro i a h; fin_cases i; exact ⟨0,rfl⟩
  upper_cover := by intro i a h; fin_cases i; exact ⟨1,rfl⟩
  row_spec := by
    intro j
    fin_cases j
    · refine ⟨0,rfl,?_⟩
      intro p
      simp [linearResidual,splitHardData,LinearForm,vec]
    · refine ⟨1,rfl,?_⟩
      intro p
      simp [linearResidual,splitHardData,LinearForm,vec]

theorem split_hard_bounds_correspondence (x : RealVector 1) (y : RealVector 1) :
    x ∈ (intervalBounds 0 1).region ↔ (x,y) ∈ splitHardData.linearRegion :=
  splitHardEncoding.region_iff x y

theorem split_soft_bounds_correspondence (x : RealVector 1) (y : RealVector 1) :
    x ∈ unboundedBounds.region ↔ (x,y) ∈ splitSoftData.linearRegion :=
  splitSoftEncoding.region_iff x y

/-- Both domain-split models retain the exact soft integer-bound rows as well
as their duplicate metadata. -/
def splitSoftIntegerRows : IntegerBoundRows splitSoftData where
  lower := fun _ => 3
  upper := fun _ => 4
  lower_eq := by intro i p; fin_cases i; simp [splitSoftData]
  upper_eq := by intro i p; fin_cases i; simp [splitSoftData]

def splitHardIntegerRows : IntegerBoundRows splitHardData where
  lower := fun _ => 1
  upper := fun _ => 2
  lower_eq := by intro i p; fin_cases i; simp [splitHardData]
  upper_eq := by intro i p; fin_cases i; simp [splitHardData]

theorem split_soft_original_metadata (p : Point 1 1) :
    p ∈ sourceOriginal splitSoftData ↔ p ∈ splitSoftData.feasibleOn Set.univ :=
  splitSoftIntegerRows.original_iff p

theorem split_hard_original_metadata (p : Point 1 1) :
    p ∈ sourceOriginal splitHardData ↔ p ∈ splitHardData.feasibleOn Set.univ :=
  splitHardIntegerRows.original_iff p

theorem split_soft_master_metadata (z : Point 1 1 × ℝ) :
    z ∈ sourceMaster splitSoftData (fun _ => 0) splitOutsideTangents (fun _ => 0) ↔
    z ∈ Chapter06.EpigraphMaster splitSoftData (fun _ => 0)
      splitOutsideTangents (fun _ => 0) Set.univ :=
  splitSoftIntegerRows.master_iff (fun _ => 0) splitOutsideTangents (fun _ => 0)
    0 rfl (fun j => split_soft_derivative _ j) z

end Chapter03.OAKKTBoundary
