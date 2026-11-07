module

public import Chapter03FPUnboundedBasic
public import Chapter03OAKKTMaps

@[expose] public section

/-! Exact hard-product and all-soft bound-row adapters. Missing sides remain
missing; contradictory finite endpoints are not reordered. Every original row
is retained. These identities concern the normalized disabled-exclusion pump. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP Chapter03.OAKKT
namespace Chapter03.FPUnbounded
variable {n m l : ℕ}

theorem bounds_closed {k : ℕ} (b : Bounds k) : IsClosed b.region := by
  have he : b.region = ⋂ i, {x | (b.lower i).lowerHolds (x i)} ∩
      {x | (b.upper i).upperHolds (x i)} := by
    ext x; simp [Bounds.region]
  rw [he]
  apply isClosed_iInter
  intro i
  apply IsClosed.inter
  · cases h : b.lower i with
    | negInfinity => simp [h,ExtendedBound.lowerHolds]
    | posInfinity => simp [h,ExtendedBound.lowerHolds]
    | finite a => exact isClosed_le continuous_const (continuous_apply i)
  · cases h : b.upper i with
    | negInfinity => simp [h,ExtendedBound.upperHolds]
    | posInfinity => simp [h,ExtendedBound.upperHolds]
    | finite a => exact isClosed_le (continuous_apply i) continuous_const

theorem bounds_convex {k : ℕ} (b : Bounds k) : Convex ℝ b.region := by
  intro x hx y hy a c ha hc hac i
  constructor
  · have hx' := (hx i).1
    have hy' := (hy i).1
    cases h : b.lower i with
    | negInfinity => trivial
    | posInfinity => simp [h,ExtendedBound.lowerHolds] at hx'
    | finite v =>
      simp only [h,ExtendedBound.lowerHolds] at hx' hy'
      change v ≤ a * x i + c * y i
      have hh := add_le_add (mul_le_mul_of_nonneg_left hx' ha)
        (mul_le_mul_of_nonneg_left hy' hc)
      simpa only [← add_mul,hac,one_mul] using hh
  · have hx' := (hx i).2
    have hy' := (hy i).2
    cases h : b.upper i with
    | posInfinity => trivial
    | negInfinity => simp [h,ExtendedBound.upperHolds] at hx'
    | finite v =>
      simp only [h,ExtendedBound.upperHolds] at hx' hy'
      change a * x i + c * y i ≤ v
      have hh := add_le_add (mul_le_mul_of_nonneg_left hx' ha)
        (mul_le_mul_of_nonneg_left hy' hc)
      simpa only [← add_mul,hac,one_mul] using hh

def boundProduct (x : Bounds n) (y : Bounds m) : Set (Point n m) :=
  {p | p.1 ∈ x.region ∧ p.2 ∈ y.region}

theorem boundProduct_closed (x : Bounds n) (y : Bounds m) : IsClosed (boundProduct x y) :=
  ((bounds_closed x).preimage continuous_fst).inter
    ((bounds_closed y).preimage continuous_snd)

theorem boundProduct_convex (x : Bounds n) (y : Bounds m) : Convex ℝ (boundProduct x y) := by
  intro p hp q hq a b ha hb hab
  exact ⟨bounds_convex x hp.1 hq.1 ha hb hab, bounds_convex y hp.2 hq.2 ha hb hab⟩

/-- Source metadata for the article's original X/Y. Infinite sides are retained;
every finite integer endpoint is integral. No two-sided finiteness is required. -/
structure ArticleData (n m l : ℕ) where
  xBounds : Bounds n
  yBounds : Bounds m
  yLower_integral : ∀ i a, yBounds.lower i = .finite a → ∃ z : ℤ, a = z
  yUpper_integral : ∀ i a, yBounds.upper i = .finite a → ∃ z : ℤ, a = z
  f : Point n m → ℝ
  g : Fin l → Point n m → ℝ
  Df : Point n m → Point n m →L[ℝ] ℝ
  Dg : Fin l → Point n m → Point n m →L[ℝ] ℝ
  delta : ℝ

def ArticleData.toData (a : ArticleData n m l) : Data n m l :=
  ⟨boundProduct a.xBounds a.yBounds, a.f, a.g, a.Df, a.Dg, a.delta⟩

theorem ArticleData.base_closed (a : ArticleData n m l) : IsClosed a.toData.base :=
  boundProduct_closed a.xBounds a.yBounds

theorem ArticleData.base_convex (a : ArticleData n m l) : Convex ℝ a.toData.base :=
  boundProduct_convex a.xBounds a.yBounds

theorem ArticleData.relaxation_iff (a : ArticleData n m l) (p : Point n m) :
    p ∈ a.toData.relaxation ↔
      (p.1 ∈ a.xBounds.region ∧ p.2 ∈ a.yBounds.region) ∧ ∀ j, a.g j p ≤ 0 := Iff.rfl

theorem ArticleData.original_iff (a : ArticleData n m l) (p : Point n m) :
    p ∈ a.toData.original ↔
      ((p.1 ∈ a.xBounds.region ∧ p.2 ∈ a.yBounds.region) ∧ ∀ j, a.g j p ≤ 0) ∧
      ∃ y : IntVector m, p.2 = FP.intCast y := Iff.rfl

theorem ArticleData.fiber_iff (a : ArticleData n m l) (y : IntVector m) (p : Point n m) :
    p ∈ a.toData.fiber y ↔
      ((p.1 ∈ a.xBounds.region ∧ p.2 ∈ a.yBounds.region) ∧ ∀ j, a.g j p ≤ 0) ∧
      p.2 = FP.intCast y := Iff.rfl

/-- The literal retained rows, without an extra hard-domain predicate. -/
def softEpigraph (d : Data n m l) (s : State n m) : Set (Point n m × ℝ) :=
  {z | (∃ y : IntVector m, z.1.2 = FP.intCast y) ∧
    (∀ i j, j ∈ (family d s).selected i →
      d.g j ((family d s).origin i) +
        (family d s).derivative i j (z.1 - (family d s).origin i) ≤ 0) ∧
    ∀ i, d.f ((family d s).origin i) +
      d.Df ((family d s).origin i) (z.1 - (family d s).origin i) ≤ z.2}

def softMaster (d : Data n m l) (s : State n m) : Set (Point n m × ℝ) :=
  {z | z ∈ softEpigraph d s ∧ retainedNormals s z.1 ∧ Allows (d.level s.incumbent) z.2}

def softHandoff (d : Data n m l) (s : State n m) : Set (Point n m × ℝ) :=
  {z | z ∈ softEpigraph d s ∧ handoffNormals s z.1}

theorem ArticleData.epigraph_iff (a : ArticleData n m l) (s : State n m)
    (z : Point n m × ℝ) :
    z ∈ epigraph a.toData s ↔
      (z.1.1 ∈ a.xBounds.region ∧ z.1.2 ∈ a.yBounds.region) ∧
      z ∈ softEpigraph a.toData s := Iff.rfl

theorem ArticleData.master_iff (a : ArticleData n m l) (s : State n m)
    (z : Point n m × ℝ) :
    z ∈ master a.toData s ↔ (z.1.1 ∈ a.xBounds.region ∧ z.1.2 ∈ a.yBounds.region) ∧
      z ∈ softMaster a.toData s := by
  constructor
  · intro hz
    exact ⟨hz.1.1,hz.1.2,hz.2⟩
  · rintro ⟨hb,he,hr⟩
    exact ⟨⟨hb,he⟩,hr⟩

theorem ArticleData.handoff_iff (a : ArticleData n m l) (s : State n m)
    (z : Point n m × ℝ) :
    z ∈ handoff a.toData s ↔ (z.1.1 ∈ a.xBounds.region ∧ z.1.2 ∈ a.yBounds.region) ∧
      z ∈ softHandoff a.toData s := by
  constructor
  · intro hz
    exact ⟨hz.1.1,hz.1.2,hz.2⟩
  · rintro ⟨hb,he,hr⟩
    exact ⟨⟨hb,he⟩,hr⟩

/-- All-soft source: every present finite side has its actual global affine
residual among g. Equal/duplicate sides and all other original rows survive.
Valid excludes wrong-signed infinities but permits reversed finite endpoints. -/
structure SoftBoundRows (d : Data n m l) (x : Bounds n) (y : Bounds m) where
  base_eq : d.base = boundProduct x y
  xValid : x.Valid
  yValid : y.Valid
  xLower : ∀ i a, x.lower i = .finite a → ∃ j, ∀ p, d.g j p = a - p.1 i
  xUpper : ∀ i a, x.upper i = .finite a → ∃ j, ∀ p, d.g j p = p.1 i - a
  yLower : ∀ i a, y.lower i = .finite a → ∃ j, ∀ p, d.g j p = a - p.2 i
  yUpper : ∀ i a, y.upper i = .finite a → ∃ j, ∀ p, d.g j p = p.2 i - a

theorem bounds_of_present_sides {k : ℕ} (b : Bounds k) (hb : b.Valid)
    (v : RealVector k)
    (hl : ∀ i a, b.lower i = .finite a → a ≤ v i)
    (hu : ∀ i a, b.upper i = .finite a → v i ≤ a) : v ∈ b.region := by
  intro i
  constructor
  · cases he : b.lower i with
    | negInfinity => trivial
    | posInfinity => exact False.elim ((hb i).1 he)
    | finite a => exact hl i a he
  · cases he : b.upper i with
    | posInfinity => trivial
    | negInfinity => exact False.elim ((hb i).2 he)
    | finite a => exact hu i a he

theorem x_lower_affine (i : Fin n) (a : ℝ) :
    AffineRow (fun p : Point n m => a - p.1 i) := by
  refine ⟨-Pi.single i 1,0,-a,?_⟩
  intro p
  simp [LinearForm,Pi.single_apply,Finset.sum_ite_eq',neg_mul]
  ring

theorem x_upper_affine (i : Fin n) (a : ℝ) :
    AffineRow (fun p : Point n m => p.1 i - a) := by
  refine ⟨Pi.single i 1,0,a,?_⟩
  intro p
  simp [LinearForm,Pi.single_apply,Finset.sum_ite_eq']

theorem y_lower_affine (i : Fin m) (a : ℝ) :
    AffineRow (fun p : Point n m => a - p.2 i) := by
  refine ⟨0,-Pi.single i 1,-a,?_⟩
  intro p
  simp [LinearForm,Pi.single_apply,Finset.sum_ite_eq',neg_mul]
  ring

theorem y_upper_affine (i : Fin m) (a : ℝ) :
    AffineRow (fun p : Point n m => p.2 i - a) := by
  refine ⟨0,Pi.single i 1,a,?_⟩
  intro p
  simp [LinearForm,Pi.single_apply,Finset.sum_ite_eq']

theorem SoftBoundRows.base_of_rows {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) {p : Point n m} (hp : ∀ j, d.g j p ≤ 0) : p ∈ d.base := by
  rw [B.base_eq]
  constructor
  · apply bounds_of_present_sides x B.xValid p.1
    · intro i a ha
      obtain ⟨j,hj⟩ := B.xLower i a ha
      exact sub_nonpos.mp (by simpa [hj] using hp j)
    · intro i a ha
      obtain ⟨j,hj⟩ := B.xUpper i a ha
      exact sub_nonpos.mp (by simpa [hj] using hp j)
  · apply bounds_of_present_sides y B.yValid p.2
    · intro i a ha
      obtain ⟨j,hj⟩ := B.yLower i a ha
      exact sub_nonpos.mp (by simpa [hj] using hp j)
    · intro i a ha
      obtain ⟨j,hj⟩ := B.yUpper i a ha
      exact sub_nonpos.mp (by simpa [hj] using hp j)

theorem initial_row_of_softEpigraph (d : Data n m l) (s : State n m)
    {z : Point n m × ℝ} (hz : z ∈ softEpigraph d s) (j : Fin l) :
    d.g j s.seed + d.Dg j s.seed (z.1 - s.seed) ≤ 0 := by
  let i : Fin (anchors d s).length := ⟨0, by simp [anchors]⟩
  have hh := hz.2.1 i j (by simp [i,family,anchors])
  simpa [i,family,anchors] using hh

theorem affine_row_of_softEpigraph (d : Data n m l) (s : State n m)
    {z : Point n m × ℝ} (hz : z ∈ softEpigraph d s) (j : Fin l)
    (ha : AffineRow (d.g j)) (hd : HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) :
    d.g j z.1 ≤ 0 := by
  rw [← affine_tangent ha hd z.1]
  exact initial_row_of_softEpigraph d s hz j

theorem SoftBoundRows.base_of_initial_rows {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    {z : Point n m × ℝ} (hz : z ∈ softEpigraph d s) : z.1 ∈ d.base := by
  rw [B.base_eq]
  constructor
  · apply bounds_of_present_sides x B.xValid z.1.1
    · intro i a ha
      obtain ⟨j,hj⟩ := B.xLower i a ha
      have haf : AffineRow (d.g j) := by rw [funext hj]; exact x_lower_affine i a
      have h := affine_row_of_softEpigraph d s hz j haf (hd j)
      exact sub_nonpos.mp (by simpa [hj] using h)
    · intro i a ha
      obtain ⟨j,hj⟩ := B.xUpper i a ha
      have haf : AffineRow (d.g j) := by rw [funext hj]; exact x_upper_affine i a
      have h := affine_row_of_softEpigraph d s hz j haf (hd j)
      exact sub_nonpos.mp (by simpa [hj] using h)
  · apply bounds_of_present_sides y B.yValid z.1.2
    · intro i a ha
      obtain ⟨j,hj⟩ := B.yLower i a ha
      have haf : AffineRow (d.g j) := by rw [funext hj]; exact y_lower_affine i a
      have h := affine_row_of_softEpigraph d s hz j haf (hd j)
      exact sub_nonpos.mp (by simpa [hj] using h)
    · intro i a ha
      obtain ⟨j,hj⟩ := B.yUpper i a ha
      have haf : AffineRow (d.g j) := by rw [funext hj]; exact y_upper_affine i a
      have h := affine_row_of_softEpigraph d s hz j haf (hd j)
      exact sub_nonpos.mp (by simpa [hj] using h)

theorem SoftBoundRows.relaxation_iff {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (p : Point n m) :
    p ∈ d.relaxation ↔ ∀ j, d.g j p ≤ 0 :=
  ⟨fun h => h.2, fun h => ⟨B.base_of_rows h,h⟩⟩

theorem SoftBoundRows.original_iff {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (p : Point n m) :
    p ∈ d.original ↔ (∀ j, d.g j p ≤ 0) ∧ ∃ y : IntVector m, p.2 = FP.intCast y := by
  change (p ∈ d.relaxation ∧ _) ↔ _
  rw [B.relaxation_iff]

theorem SoftBoundRows.fiber_iff {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (v : IntVector m) (p : Point n m) :
    p ∈ d.fiber v ↔ (∀ j, d.g j p ≤ 0) ∧ p.2 = FP.intCast v := by
  change (p ∈ d.relaxation ∧ _) ↔ _
  rw [B.relaxation_iff]

theorem SoftBoundRows.epigraph_iff {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) (z : Point n m × ℝ) :
    z ∈ softEpigraph d s ↔ z ∈ epigraph d s :=
  ⟨fun hz => ⟨B.base_of_initial_rows s hd hz,hz⟩, fun hz => hz.2⟩

theorem SoftBoundRows.master_iff {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) (z : Point n m × ℝ) :
    z ∈ softMaster d s ↔ z ∈ master d s := by
  change (z ∈ softEpigraph d s ∧ _) ↔ (z ∈ epigraph d s ∧ _)
  rw [B.epigraph_iff s hd]

theorem SoftBoundRows.handoff_iff {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) (z : Point n m × ℝ) :
    z ∈ softHandoff d s ↔ z ∈ handoff d s := by
  change (z ∈ softEpigraph d s ∧ _) ↔ (z ∈ epigraph d s ∧ _)
  rw [B.epigraph_iff s hd]

/-- Generic exact source-domain encoding by a selected collection of actual
original globally affine g rows. This may include bound, constant-infeasible,
and other affine rows. No original row is deleted or merged. -/
structure AffineBaseRows (d : Data n m l) where
  selected : Set (Fin l)
  affine : ∀ j ∈ selected, AffineRow (d.g j)
  base_eq : d.base = {p | ∀ j ∈ selected, d.g j p ≤ 0}

theorem AffineBaseRows.base_of_rows {d : Data n m l} (A : AffineBaseRows d)
    {p : Point n m} (hp : ∀ j, d.g j p ≤ 0) : p ∈ d.base := by
  rw [A.base_eq]
  exact fun j _ => hp j

theorem AffineBaseRows.base_of_initial_rows {d : Data n m l} (A : AffineBaseRows d)
    (s : State n m) (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    {z : Point n m × ℝ} (hz : z ∈ softEpigraph d s) : z.1 ∈ d.base := by
  rw [A.base_eq]
  intro j hj
  exact affine_row_of_softEpigraph d s hz j (A.affine j hj) (hd j)

theorem AffineBaseRows.relaxation_iff {d : Data n m l} (A : AffineBaseRows d)
    (p : Point n m) : p ∈ d.relaxation ↔ ∀ j, d.g j p ≤ 0 :=
  ⟨fun h => h.2, fun h => ⟨A.base_of_rows h,h⟩⟩

theorem AffineBaseRows.original_iff {d : Data n m l} (A : AffineBaseRows d)
    (p : Point n m) : p ∈ d.original ↔
      (∀ j, d.g j p ≤ 0) ∧ ∃ y : IntVector m, p.2 = FP.intCast y := by
  change (p ∈ d.relaxation ∧ _) ↔ _
  rw [A.relaxation_iff]

theorem AffineBaseRows.fiber_iff {d : Data n m l} (A : AffineBaseRows d)
    (v : IntVector m) (p : Point n m) : p ∈ d.fiber v ↔
      (∀ j, d.g j p ≤ 0) ∧ p.2 = FP.intCast v := by
  change (p ∈ d.relaxation ∧ _) ↔ _
  rw [A.relaxation_iff]

theorem AffineBaseRows.epigraph_iff {d : Data n m l} (A : AffineBaseRows d)
    (s : State n m) (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    (z : Point n m × ℝ) : z ∈ softEpigraph d s ↔ z ∈ epigraph d s :=
  ⟨fun hz => ⟨A.base_of_initial_rows s hd hz,hz⟩, fun hz => hz.2⟩

theorem AffineBaseRows.master_iff {d : Data n m l} (A : AffineBaseRows d)
    (s : State n m) (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    (z : Point n m × ℝ) : z ∈ softMaster d s ↔ z ∈ master d s := by
  change (z ∈ softEpigraph d s ∧ _) ↔ (z ∈ epigraph d s ∧ _)
  rw [A.epigraph_iff s hd]

theorem AffineBaseRows.handoff_iff {d : Data n m l} (A : AffineBaseRows d)
    (s : State n m) (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    (z : Point n m × ℝ) : z ∈ softHandoff d s ↔ z ∈ handoff d s := by
  change (z ∈ softEpigraph d s ∧ _) ↔ (z ∈ epigraph d s ∧ _)
  rw [A.epigraph_iff s hd]

end Chapter03.FPUnbounded
