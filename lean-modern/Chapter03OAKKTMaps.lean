module

public import Chapter03OAKKT

@[expose] public section

/-! Exact source metadata and finite-sided bound adapters. Physical bounds in
thesis g are an explicit interpretation; article X bounds are externally hard.
No wrong-signed infinite side is erased and no finite endpoints are reordered. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter03.OAKKT

variable {n m l r k : ℕ}

theorem RowReindexing.slack_rows_iff {s : ℕ} {g : Fin s → Point n m → ℝ}
    {d : ModelData n m l r} (R : RowReindexing g d)
    (p : Point n m) (v : RealVector s) :
    (∀ j, g j p ≤ v j) ↔ ∀ j, d.g j p ≤ v (R.index.symm j) := by
  constructor
  · intro h j
    have hh := h (R.index.symm j)
    simpa only [← R.row_eq,Equiv.apply_symm_apply] using hh
  · intro h j
    have hh := h (R.index j)
    simpa only [R.row_eq,Equiv.symm_apply_apply] using hh

theorem RowReindexing.slack_sum {s : ℕ} {g : Fin s → Point n m → ℝ}
    {d : ModelData n m l r} (R : RowReindexing g d) (v : RealVector s) :
    (∑ j : Fin l, v (R.index.symm j)) = ∑ j : Fin s, v j :=
  Equiv.sum_comp R.index.symm v

/-- Source integer bounds remain actual g rows. Index maps do not delete any
other row, and every source slack remains in the sum. -/
structure IntegerBoundRows (d : ModelData n m l r) where
  lower : Fin m → Fin l
  upper : Fin m → Fin l
  lower_eq : ∀ i p, d.g (lower i) p = d.lo i-p.2 i
  upper_eq : ∀ i p, d.g (upper i) p = p.2 i-d.hi i

theorem IntegerBoundRows.bounds_of_rows {d : ModelData n m l r}
    (B : IntegerBoundRows d) {p : Point n m} (hp : ∀ j, d.g j p ≤ 0) :
    ∀ i, d.lo i ≤ p.2 i ∧ p.2 i ≤ d.hi i := by
  intro i
  have hl := hp (B.lower i)
  have hu := hp (B.upper i)
  rw [B.lower_eq] at hl
  rw [B.upper_eq] at hu
  exact ⟨sub_nonpos.mp hl,sub_nonpos.mp hu⟩

theorem IntegerBoundRows.lower_affine {d : ModelData n m l r}
    (B : IntegerBoundRows d) (i : Fin m) : AffineRow (d.g (B.lower i)) := by
  refine ⟨0,-Pi.single i 1,-d.lo i,?_⟩
  intro p
  rw [B.lower_eq]
  simp [LinearForm,Pi.single_apply,Finset.sum_ite_eq',neg_mul]
  ring

theorem IntegerBoundRows.upper_affine {d : ModelData n m l r}
    (B : IntegerBoundRows d) (i : Fin m) : AffineRow (d.g (B.upper i)) := by
  refine ⟨0,Pi.single i 1,d.hi i,?_⟩
  intro p
  rw [B.upper_eq]
  simp [LinearForm,Pi.single_apply,Finset.sum_ite_eq']

/-- Integrality without the duplicate bound metadata. -/
def integral (p : Point n m) : Prop := ∃ y : IntVector m, p.2 = intCast y

def sourceOriginal (d : ModelData n m l r) : Set (Point n m) :=
  {p | (∀ j, d.g j p ≤ 0) ∧ p ∈ d.linearRegion ∧ integral p}

theorem IntegerBoundRows.original_iff {d : ModelData n m l r}
    (B : IntegerBoundRows d) (p : Point n m) :
    p ∈ sourceOriginal d ↔ p ∈ d.feasibleOn Set.univ := by
  rw [source_feasible_iff]
  constructor
  · rintro ⟨hg,hh,z,hz⟩
    refine ⟨Set.mem_univ _,hg,hh,z,?_,hz⟩
    have hb := B.bounds_of_rows hg
    rw [hz] at hb
    exact hb
  · rintro ⟨_,hg,hh,z,hz,he⟩
    exact ⟨hg,hh,z,he⟩

theorem IntegerBoundRows.initial_tangents_bounds {d : ModelData n m l r}
    (B : IntegerBoundRows d) (c : TangentFamily n m l k) (seed : Fin k)
    (hall : c.selected seed = Set.univ)
    (hd : ∀ j, HasFDerivAt (d.g j) (c.derivative seed j) (c.origin seed))
    {p : Point n m} (hp : p ∈ c.cutRegion d) :
    ∀ i, d.lo i ≤ p.2 i ∧ p.2 i ≤ d.hi i := by
  intro i
  have hl := hp seed (B.lower i) (by rw [hall]; trivial)
  have hu := hp seed (B.upper i) (by rw [hall]; trivial)
  rw [affine_tangent (B.lower_affine i) (hd _) p,B.lower_eq] at hl
  rw [affine_tangent (B.upper_affine i) (hd _) p,B.upper_eq] at hu
  exact ⟨sub_nonpos.mp hl,sub_nonpos.mp hu⟩

/-- The literal retained-row epigraph without separately duplicated y bounds. -/
def sourceMaster (d : ModelData n m l r) (f : Point n m → ℝ)
    (c : TangentFamily n m l k) (df : Fin k → Point n m →L[ℝ] ℝ) :
    Set (Point n m × ℝ) :=
  {z | z.1 ∈ c.cutRegion d ∧ z.1 ∈ d.linearRegion ∧ integral z.1 ∧
    ∀ i, f (c.origin i) + df i (z.1-c.origin i) ≤ z.2}

theorem IntegerBoundRows.master_iff {d : ModelData n m l r}
    (B : IntegerBoundRows d) (f : Point n m → ℝ) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (seed : Fin k)
    (hall : c.selected seed = Set.univ)
    (hd : ∀ j, HasFDerivAt (d.g j) (c.derivative seed j) (c.origin seed))
    (z : Point n m × ℝ) :
    z ∈ sourceMaster d f c df ↔ z ∈ Chapter06.EpigraphMaster d f c df Set.univ := by
  constructor
  · rintro ⟨hc,hl,hi,hobj⟩
    obtain ⟨yi,hyi⟩ := hi
    refine ⟨⟨⟨⟨Set.mem_univ _,hc⟩,hl⟩,yi,?_,hyi⟩,hobj⟩
    have hb := B.initial_tangents_bounds c seed hall hd hc
    rw [hyi] at hb
    exact hb
  · rintro ⟨⟨⟨⟨_,hc⟩,hl⟩,yi,hyi,he⟩,hobj⟩
    exact ⟨hc,hl,⟨yi,he⟩,hobj⟩

inductive ExtendedBound where
  | negInfinity
  | finite (value : ℝ)
  | posInfinity

def ExtendedBound.lowerHolds : ExtendedBound → ℝ → Prop
  | .negInfinity, _ => True
  | .finite a, x => a ≤ x
  | .posInfinity, _ => False

def ExtendedBound.upperHolds : ExtendedBound → ℝ → Prop
  | .negInfinity, _ => False
  | .finite a, x => x ≤ a
  | .posInfinity, _ => True

structure Bounds (n : ℕ) where
  lower : Fin n → ExtendedBound
  upper : Fin n → ExtendedBound

def Bounds.Valid (b : Bounds n) : Prop :=
  ∀ i, b.lower i ≠ .posInfinity ∧ b.upper i ≠ .negInfinity

def Bounds.region (b : Bounds n) : Set (RealVector n) :=
  {x | ∀ i, (b.lower i).lowerHolds (x i) ∧ (b.upper i).upperHolds (x i)}

theorem Bounds.invalid_lower_empty (b : Bounds n) (i : Fin n)
    (hi : b.lower i = .posInfinity) : b.region = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := (hx i).1
  simp [hi,ExtendedBound.lowerHolds] at hh

theorem Bounds.invalid_upper_empty (b : Bounds n) (i : Fin n)
    (hi : b.upper i = .negInfinity) : b.region = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := (hx i).2
  simp [hi,ExtendedBound.upperHolds] at hh

theorem Bounds.reversed_finite_empty (b : Bounds n) (i : Fin n) (a u : ℝ)
    (hl : b.lower i = .finite a) (hu : b.upper i = .finite u) (h : u < a) :
    b.region = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := hx i
  simp only [hl,hu,ExtendedBound.lowerHolds,ExtendedBound.upperHolds] at hh
  exact (not_le_of_gt h) (hh.1.trans hh.2)

/-- A bijective enumeration of exactly the present finite sides. Valid excludes
wrong-signed infinite endpoints; identical finite endpoints retain both sides. -/
structure HardBoundEncoding (b : Bounds n) (d : ModelData n m l r) where
  valid : b.Valid
  side : Fin r → Sum (Fin n) (Fin n)
  injective : Function.Injective side
  lower_cover : ∀ i a, b.lower i = .finite a → ∃ j, side j = .inl i
  upper_cover : ∀ i a, b.upper i = .finite a → ∃ j, side j = .inr i
  row_spec : ∀ j, match side j with
    | .inl i => ∃ a, b.lower i = .finite a ∧ ∀ p, linearResidual d j p = a-p.1 i
    | .inr i => ∃ a, b.upper i = .finite a ∧ ∀ p, linearResidual d j p = p.1 i-a

theorem HardBoundEncoding.region_iff {b : Bounds n} {d : ModelData n m l r}
    (E : HardBoundEncoding b d) (x : RealVector n) (y : RealVector m) :
    x ∈ b.region ↔ (x,y) ∈ d.linearRegion := by
  constructor
  · intro hx j
    have hs := E.row_spec j
    cases hh : E.side j with
    | inl i =>
      rw [hh] at hs
      obtain ⟨a,ha,hr⟩ := hs
      have h := (hx i).1
      simp only [ha,ExtendedBound.lowerHolds] at h
      apply sub_nonpos.mp
      change linearResidual d j (x,y) ≤ 0
      rw [hr]
      exact sub_nonpos.mpr h
    | inr i =>
      rw [hh] at hs
      obtain ⟨a,ha,hr⟩ := hs
      have h := (hx i).2
      simp only [ha,ExtendedBound.upperHolds] at h
      apply sub_nonpos.mp
      change linearResidual d j (x,y) ≤ 0
      rw [hr]
      exact sub_nonpos.mpr h
  · intro hx i
    constructor
    · cases hh : b.lower i with
      | negInfinity => trivial
      | posInfinity => exact False.elim ((E.valid i).1 hh)
      | finite a =>
        obtain ⟨j,hj⟩ := E.lower_cover i a hh
        have hs := E.row_spec j
        rw [hj] at hs
        obtain ⟨a',ha,hr⟩ := hs
        have he : a' = a := by simpa [hh] using ha.symm
        subst a'
        have h : linearResidual d j (x,y) ≤ 0 := sub_nonpos.mpr (hx j)
        rw [hr] at h
        exact sub_nonpos.mp h
    · cases hh : b.upper i with
      | posInfinity => trivial
      | negInfinity => exact False.elim ((E.valid i).2 hh)
      | finite a =>
        obtain ⟨j,hj⟩ := E.upper_cover i a hh
        have hs := E.row_spec j
        rw [hj] at hs
        obtain ⟨a',ha,hr⟩ := hs
        have he : a' = a := by simpa [hh] using ha.symm
        subst a'
        have h : linearResidual d j (x,y) ≤ 0 := sub_nonpos.mpr (hx j)
        rw [hr] at h
        exact sub_nonpos.mp h

theorem HardBoundEncoding.lower_normal {b : Bounds n} {d : ModelData n m l r}
    (E : HardBoundEncoding b d) (j : Fin r) (i : Fin n) (hj : E.side j = .inl i)
    (v : RealVector n) : fiberLinearRow d j v = -v i := by
  have hs := E.row_spec j
  rw [hj] at hs
  obtain ⟨a,_,hr⟩ := hs
  have hh := hard_tangent d (0 : RealVector m) j 0 v
  simp only [hard,hr,Pi.zero_apply,sub_zero] at hh
  linarith

theorem HardBoundEncoding.upper_normal {b : Bounds n} {d : ModelData n m l r}
    (E : HardBoundEncoding b d) (j : Fin r) (i : Fin n) (hj : E.side j = .inr i)
    (v : RealVector n) : fiberLinearRow d j v = v i := by
  have hs := E.row_spec j
  rw [hj] at hs
  obtain ⟨a,_,hr⟩ := hs
  have hh := hard_tangent d (0 : RealVector m) j 0 v
  simp only [hard,hr,Pi.zero_apply,sub_zero] at hh
  linarith

/-- Source wrapper fixes an admissible integer y and retains the actual
original-fiber optimizer, with the same separate nonlinear objective. -/
theorem integer_fixed_solution_lower {d : ModelData n m l r}
    {f : Point n m → ℝ} {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n}
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (H : History d f N c df x (intCast y))
    (hm : IsMinimizer {p ∈ d.feasibleOn Set.univ | p.2 = intCast y} f (x,intCast y))
    (K : FixedKKT d f x (intCast y)) {z : Point n m × ℝ}
    (hz : z ∈ Chapter06.EpigraphMaster d f c df Set.univ)
    (hzy : z.1.2 = intCast y) : f (x,intCast y) ≤ z.2 :=
  fixed_solution_master_lower H ((fiber_minimizer_original_iff d f y hy x).mpr hm)
    K hz hzy

/-- The actual original infeasible branch, at an admissible integer vector.
The restoration minimum is an explicit attained global minimum. -/
theorem integer_infeasible_restoration_exclusion {d : ModelData n m l r}
    {f : Point n m → ℝ} {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {s : RealVector l}
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (H : History d f N c df x (intCast y))
    (hempty : ¬ ∃ p ∈ d.feasibleOn Set.univ, p.2 = intCast y)
    (hm : IsMinimizer (restSet d (intCast y)) restCost (weightedInsert x s))
    (K : SumKKT d x (intCast y) s) :
    ¬ ∃ z ∈ Chapter06.EpigraphMaster d f c df Set.univ, z.1.2 = intCast y := by
  apply infeasible_restoration_master_exclusion H ?_ hm K
  rintro ⟨a,ha⟩
  exact hempty ⟨(a,intCast y),(fiber_original_iff d y hy a).mp ha,rfl⟩

/-- Conditional global validity keeps the convexity domain separate from the
literal master domain. Exterior restored anchors need the explicit membership
premise (or a justified larger convexity domain), including objective tangents. -/
theorem source_epigraph_contains_on_domain (d : ModelData n m l r)
    (f : Point n m → ℝ) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (D : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ D (d.g j)) (hf : ConvexOn ℝ D f)
    (ha : ∀ i, c.origin i ∈ D)
    (hdg : ∀ i j, j ∈ c.selected i → HasFDerivAt (d.g j) (c.derivative i j) (c.origin i))
    (hdf : ∀ i, HasFDerivAt f (df i) (c.origin i))
    (hcover : d.feasibleOn Set.univ ⊆ D)
    {q : Point n m} (hq : q ∈ d.feasibleOn Set.univ) :
    (q,f q) ∈ Chapter06.EpigraphMaster d f c df Set.univ := by
  have hqD : q ∈ d.feasibleOn D :=
    ⟨⟨⟨hcover hq,hq.1.1.2⟩,hq.1.2⟩,hq.2⟩
  have hh := Chapter06.source_feasible_epigraph_in_master d f c df D hg hf ha hdg hdf hqD
  exact ⟨⟨⟨⟨Set.mem_univ _,hh.1.1.1.2⟩,hh.1.1.2⟩,hh.1.2⟩,hh.2⟩

end Chapter03.OAKKT
