module

public import Chapter03FPSearchModel
public import Chapter03FPUnboundedSourceAdapters

@[expose] public section

/-! Article box and thesis all-soft row adapters for first-feasibility search.
Missing/infinite bounds and duplicated/contradictory rows are retained. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP Chapter03.OAKKT
namespace Chapter03.FPSearch
variable {n m l : ℕ}

structure ArticleData (n m l : ℕ) where
  xBounds : Bounds n
  yBounds : Bounds m
  yLower_integral : ∀ i a, yBounds.lower i = .finite a → ∃ z : ℤ, a = z
  yUpper_integral : ∀ i a, yBounds.upper i = .finite a → ∃ z : ℤ, a = z
  f : Point n m → ℝ
  g : Fin l → Point n m → ℝ
  Df : Point n m → Point n m →L[ℝ] ℝ
  Dg : Fin l → Point n m → Point n m →L[ℝ] ℝ

def ArticleData.toData (a : ArticleData n m l) : Data n m l :=
  ⟨FPUnbounded.boundProduct a.xBounds a.yBounds,a.f,a.g,a.Df,a.Dg⟩

theorem ArticleData.relaxation_iff (a : ArticleData n m l) (p : Point n m) :
    p ∈ a.toData.relaxation ↔
      (p.1 ∈ a.xBounds.region ∧ p.2 ∈ a.yBounds.region) ∧ ∀ j, a.g j p ≤ 0 := Iff.rfl

theorem ArticleData.original_iff (a : ArticleData n m l) (p : Point n m) :
    p ∈ a.toData.original ↔
      ((p.1 ∈ a.xBounds.region ∧ p.2 ∈ a.yBounds.region) ∧ ∀ j, a.g j p ≤ 0) ∧
        ∃ q : IntVector m, p.2=FP.intCast q := Iff.rfl

/-- Literal all-soft selected-row master; no hard domain predicate. -/
def softMaster (d : Data n m l) (mode : Mode) (s : State n m) : Set (Point n m) :=
  {p | Integral p ∧ Rows d s p ∧
    (mode=.enhanced → ∀ e ∈ s.history, 0 ≤ e.normal p)}

theorem ArticleData.master_iff (a : ArticleData n m l) (mode : Mode)
    (s : State n m) (p : Point n m) :
    p ∈ master a.toData mode s ↔
      (p.1 ∈ a.xBounds.region ∧ p.2 ∈ a.yBounds.region) ∧
        p ∈ softMaster a.toData mode s := Iff.rfl

theorem affine_row_of_rows (d : Data n m l) (s : State n m)
    {p : Point n m} (hp : Rows d s p) (j : Fin l)
    (ha : AffineRow (d.g j)) (hd : HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) :
    d.g j p ≤ 0 := by
  rw [← affine_tangent ha hd p]
  exact hp.1 j

/-- Exact reuse of the original indexed affine-row base representation. -/
abbrev AffineBaseRows (d : Data n m l) := FPUnbounded.AffineBaseRows d.toUnbounded

theorem base_of_rows (d : Data n m l) (B : AffineBaseRows d) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    {p : Point n m} (hp : Rows d s p) : p ∈ d.base := by
  rw [show d.base = _ from B.base_eq]
  intro j hj
  exact affine_row_of_rows d s hp j (B.affine j hj) (hd j)

theorem master_soft_iff (d : Data n m l) (B : AffineBaseRows d)
    (mode : Mode) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    (p : Point n m) : p ∈ master d mode s ↔ p ∈ softMaster d mode s := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨base_of_rows d B s hd h.2.1,h⟩

theorem hard_box_target_bound (d : Data n m l) (mode : Mode)
    (lo hi : RealVector m)
    (hb : ∀ p ∈ d.base, ∀ j, lo j ≤ p.2 j ∧ p.2 j ≤ hi j) :
    TargetBound d mode (integerBox_finite lo hi).toFinset := by
  intro s hs p hp q hq
  rw [Set.Finite.mem_toFinset]
  intro j
  have h := hb p hp.1 j
  simpa only [hq,FP.intCast] using h

theorem ArticleData.target_bound (a : ArticleData n m l) (mode : Mode)
    (lo hi : RealVector m)
    (hl : ∀ i, a.yBounds.lower i=.finite (lo i))
    (hu : ∀ i, a.yBounds.upper i=.finite (hi i)) :
    TargetBound a.toData mode (integerBox_finite lo hi).toFinset := by
  apply hard_box_target_bound a.toData mode lo hi
  intro p hp j
  have hj := hp.2 j
  simpa only [hl j,hu j,ExtendedBound.lowerHolds,ExtendedBound.upperHolds] using hj

end Chapter03.FPSearch
