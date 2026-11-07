module

public import Chapter03FPSearchSource
public import Chapter03FPSearchAffineCQ
public import Chapter03FPSearchBasic

@[expose] public section

/-! Exact finite-side presentation of the article's X/Y boxes. A finite side
has its own index even when its value agrees with another side. Missing sides
have no index; wrong-signed infinities are excluded explicitly by Bounds.Valid.
No ordering or consistency assumption is imposed on finite endpoint values. -/
noncomputable section
open Chapter02 Chapter03.FP Chapter03.OAKKT
namespace Chapter03.FPSearch
variable {n m l k : ℕ}

def boundAtSide (b : Bounds k) : Fin k ⊕ Fin k → ExtendedBound :=
  Sum.elim b.lower b.upper

/-- Lower and upper are distinct tags; only actually finite sides are indexed. -/
def FiniteBoundSide (b : Bounds k) :=
  {s : Fin k ⊕ Fin k // ∃ a : ℝ, boundAtSide b s = .finite a}

instance finiteBoundSideFintype (b : Bounds k) : Fintype (FiniteBoundSide b) := by
  classical
  unfold FiniteBoundSide
  infer_instance

def finiteSideValue {b : Bounds k} (s : FiniteBoundSide b) : ℝ :=
  Classical.choose s.property

theorem finiteSideValue_spec {b : Bounds k} (s : FiniteBoundSide b) :
    boundAtSide b s.val = .finite (finiteSideValue s) :=
  Classical.choose_spec s.property

def finiteLower (b : Bounds k) (i : Fin k) (a : ℝ)
    (h : b.lower i = .finite a) : FiniteBoundSide b := ⟨.inl i,a,h⟩

def finiteUpper (b : Bounds k) (i : Fin k) (a : ℝ)
    (h : b.upper i = .finite a) : FiniteBoundSide b := ⟨.inr i,a,h⟩

theorem finiteLower_value (b : Bounds k) (i : Fin k) (a : ℝ)
    (h : b.lower i = .finite a) : finiteSideValue (finiteLower b i a h) = a := by
  have hs := finiteSideValue_spec (finiteLower b i a h)
  change b.lower i = .finite _ at hs
  rw [h] at hs
  exact (ExtendedBound.finite.inj hs).symm

theorem finiteUpper_value (b : Bounds k) (i : Fin k) (a : ℝ)
    (h : b.upper i = .finite a) : finiteSideValue (finiteUpper b i a h) = a := by
  have hs := finiteSideValue_spec (finiteUpper b i a h)
  change b.upper i = .finite _ at hs
  rw [h] at hs
  exact (ExtendedBound.finite.inj hs).symm

theorem finiteLower_ne_upper (b : Bounds k) (i j : Fin k) (a u : ℝ)
    (hl : b.lower i = .finite a) (hu : b.upper j = .finite u) :
    finiteLower b i a hl ≠ finiteUpper b j u hu := by
  intro he
  have hv := congrArg Subtype.val he
  change (Sum.inl i : Fin k ⊕ Fin k) = Sum.inr j at hv
  exact Sum.inl_ne_inr hv

theorem missing_lower_no_side (b : Bounds k) (i : Fin k)
    (h : b.lower i = .negInfinity) :
    ¬∃ s : FiniteBoundSide b, s.val = .inl i := by
  rintro ⟨s,hs⟩
  have hv := finiteSideValue_spec s
  rw [hs] at hv
  change b.lower i = .finite _ at hv
  rw [h] at hv
  cases hv

theorem missing_upper_no_side (b : Bounds k) (i : Fin k)
    (h : b.upper i = .posInfinity) :
    ¬∃ s : FiniteBoundSide b, s.val = .inr i := by
  rintro ⟨s,hs⟩
  have hv := finiteSideValue_spec s
  rw [hs] at hv
  change b.upper i = .finite _ at hv
  rw [h] at hv
  cases hv

def finiteSideLinear {b : Bounds k} (s : FiniteBoundSide b) : RealVector k →L[ℝ] ℝ :=
  match s.val with
  | .inl i => -ContinuousLinearMap.proj i
  | .inr i => ContinuousLinearMap.proj i

def finiteSideOffset {b : Bounds k} (s : FiniteBoundSide b) : ℝ :=
  match s.val with
  | .inl _ => finiteSideValue s
  | .inr _ => -finiteSideValue s

theorem finiteLower_residual (b : Bounds k) (i : Fin k) (a : ℝ)
    (h : b.lower i = .finite a) (x : RealVector k) :
    finiteSideLinear (finiteLower b i a h) x +
      finiteSideOffset (finiteLower b i a h) = a - x i := by
  simp only [finiteSideLinear,finiteSideOffset,finiteLower,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.proj_apply]
  rw [show finiteSideValue (⟨.inl i,a,h⟩ : FiniteBoundSide b) = a from
    finiteLower_value b i a h]
  ring

theorem finiteUpper_residual (b : Bounds k) (i : Fin k) (a : ℝ)
    (h : b.upper i = .finite a) (x : RealVector k) :
    finiteSideLinear (finiteUpper b i a h) x +
      finiteSideOffset (finiteUpper b i a h) = x i - a := by
  simp only [finiteSideLinear,finiteSideOffset,finiteUpper,
    ContinuousLinearMap.proj_apply]
  rw [show finiteSideValue (⟨.inr i,a,h⟩ : FiniteBoundSide b) = a from
    finiteUpper_value b i a h]
  rfl

/-- Exact row intersection, including reversed and collapsed finite intervals. -/
theorem finiteSides_region_iff (b : Bounds k) (hb : b.Valid) (x : RealVector k) :
    x ∈ b.region ↔ ∀ s : FiniteBoundSide b,
      finiteSideLinear s x + finiteSideOffset s ≤ 0 := by
  constructor
  · intro hx s
    have hv := finiteSideValue_spec s
    cases hs : s.val with
    | inl i =>
      have hbound : b.lower i = .finite (finiteSideValue s) := by
        simpa only [hs,boundAtSide,Sum.elim_inl] using hv
      have hi := (hx i).1
      rw [hbound] at hi
      change finiteSideValue s ≤ x i at hi
      simpa only [finiteSideLinear,finiteSideOffset,hs,
        ContinuousLinearMap.neg_apply,ContinuousLinearMap.proj_apply] using
        (by linarith : -x i + finiteSideValue s ≤ 0)
    | inr i =>
      have hbound : b.upper i = .finite (finiteSideValue s) := by
        simpa only [hs,boundAtSide,Sum.elim_inr] using hv
      have hi := (hx i).2
      rw [hbound] at hi
      change x i ≤ finiteSideValue s at hi
      simpa only [finiteSideLinear,finiteSideOffset,hs,
        ContinuousLinearMap.proj_apply] using
        (by linarith : x i + -finiteSideValue s ≤ 0)
  · intro hx i
    constructor
    · cases hl : b.lower i with
      | negInfinity => trivial
      | posInfinity => exact False.elim ((hb i).1 hl)
      | finite a =>
        have hi := hx (finiteLower b i a hl)
        rw [finiteLower_residual] at hi
        exact sub_nonpos.mp hi
    · cases hu : b.upper i with
      | posInfinity => trivial
      | negInfinity => exact False.elim ((hb i).2 hu)
      | finite a =>
        have hi := hx (finiteUpper b i a hu)
        rw [finiteUpper_residual] at hi
        exact sub_nonpos.mp hi

abbrev ArticleData.BoxSide (a : ArticleData n m l) :=
  FiniteBoundSide a.xBounds ⊕ FiniteBoundSide a.yBounds

def ArticleData.boxLinear (a : ArticleData n m l) : a.BoxSide → Point n m →L[ℝ] ℝ
  | .inl s => (finiteSideLinear s).comp (ContinuousLinearMap.fst ℝ _ _)
  | .inr s => (finiteSideLinear s).comp (ContinuousLinearMap.snd ℝ _ _)

def ArticleData.boxOffset (a : ArticleData n m l) : a.BoxSide → ℝ :=
  Sum.elim finiteSideOffset finiteSideOffset

theorem ArticleData.boxSides_iff (a : ArticleData n m l)
    (hx : a.xBounds.Valid) (hy : a.yBounds.Valid) (p : Point n m) :
    p ∈ a.toData.base ↔ ∀ s : a.BoxSide, a.boxLinear s p + a.boxOffset s ≤ 0 := by
  change (p.1 ∈ a.xBounds.region ∧ p.2 ∈ a.yBounds.region) ↔ _
  rw [finiteSides_region_iff a.xBounds hx,finiteSides_region_iff a.yBounds hy]
  constructor
  · rintro ⟨h₁,h₂⟩ s
    cases s with
    | inl s => exact h₁ s
    | inr s => exact h₂ s
  · intro h
    exact ⟨fun s => h (.inl s),fun s => h (.inr s)⟩

/-- Explicit bijection; no finite-side identity is merged or discarded. -/
def ArticleData.boxIndex (a : ArticleData n m l) :
    Fin (Fintype.card a.BoxSide) ≃ a.BoxSide := (Fintype.equivFin a.BoxSide).symm

def ArticleData.boxBaseRows (a : ArticleData n m l)
    (hx : a.xBounds.Valid) (hy : a.yBounds.Valid) :
    BaseRows a.toData (Fintype.card a.BoxSide) where
  linear i := a.boxLinear (a.boxIndex i)
  offset i := a.boxOffset (a.boxIndex i)
  exact_base p := by
    rw [a.boxSides_iff hx hy p]
    constructor
    · exact fun h i => h (a.boxIndex i)
    · intro h s
      simpa only [Equiv.apply_symm_apply] using h (a.boxIndex.symm s)

theorem ArticleData.boxBaseRows_residual (a : ArticleData n m l)
    (hx : a.xBounds.Valid) (hy : a.yBounds.Valid) (s : a.BoxSide) (p : Point n m) :
    (a.boxBaseRows hx hy).residual (a.boxIndex.symm s) p =
      a.boxLinear s p + a.boxOffset s := by
  simp only [BaseRows.residual,ArticleData.boxBaseRows,Equiv.apply_symm_apply]

theorem ArticleData.boxIndex_injective (a : ArticleData n m l) :
    Function.Injective a.boxIndex := a.boxIndex.injective

theorem ArticleData.boxIndex_surjective (a : ArticleData n m l) :
    Function.Surjective a.boxIndex := a.boxIndex.surjective

/-- Thesis all-soft interpretation: full space contributes no extra hard rows.
Actual bound constraints must remain in g; this does not establish their LICQ. -/
def fullSpaceBaseRows (d : Data n m l) (hb : d.base = Set.univ) : BaseRows d 0 where
  linear := Fin.elim0
  offset := Fin.elim0
  exact_base p := by simp [hb]

/-- Actual article hard boxes discharge finite target containment. Full joint
LICQ of every original g row and every finite X/Y side remains an explicit
uniform premise; validity of the endpoints alone does not establish it. -/
theorem ArticleData.basic_first_feasibility (a : ArticleData n m l)
    (hx : a.xBounds.Valid) (hy : a.yBounds.Valid) (h : Analytic a.toData)
    (lo hi : RealVector m)
    (hl : ∀ i, a.yBounds.lower i = .finite (lo i))
    (hu : ∀ i, a.yBounds.upper i = .finite (hi i))
    (hcq : ProjectionLICQ a.toData (a.boxBaseRows hx hy)
      (integerBox_finite lo hi).toFinset) :
    Nonempty (Initialization a.toData) ∧ Nonempty (Selector a.toData .basic) ∧
      ∀ (initial : Initialization a.toData) (choose : Selector a.toData .basic),
        ∃ out, procedureWithFuel a.toData .basic initial choose
            ((integerBox_finite lo hi).toFinset.card + 1) = some out ∧
          out.Correct a.toData ∧ out.Counts (integerBox_finite lo hi).toFinset.card := by
  exact qualified_basic_first_feasibility a.toData (a.boxBaseRows hx hy) h
    (integerBox_finite lo hi).toFinset (a.target_bound .basic lo hi hl hu) hcq

/-- Full space adds no hard rows. For thesis g-encoded bounds the actual finite
target containment and all-g joint LICQ must still be provided separately. -/
theorem fullSpace_basic_first_feasibility (d : Data n m l)
    (hbase : d.base = Set.univ) (h : Analytic d) (Q : Finset (IntVector m))
    (hb : TargetBound d .basic Q)
    (hcq : ProjectionLICQ d (fullSpaceBaseRows d hbase) Q) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d .basic) ∧
      ∀ (initial : Initialization d) (choose : Selector d .basic),
        ∃ out, procedureWithFuel d .basic initial choose (Q.card + 1) = some out ∧
          out.Correct d ∧ out.Counts Q.card := by
  exact qualified_basic_first_feasibility d (fullSpaceBaseRows d hbase) h Q hb hcq

end Chapter03.FPSearch
