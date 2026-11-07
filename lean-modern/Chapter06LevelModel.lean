module

public import Chapter03FPUnboundedLattice
public import Chapter03OAKKTSource
public import Chapter02MultiplierExistence

@[expose] public section

/-! Source-only Chapter 6 data. The integer box below is derived internally from
compactness of the original affine joint region; the nonlinear objective stays
separate from the zero-objective `ModelData` adapter. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter06.Level

structure Data (n m l r : ℕ) where
  f : Point n m → ℝ
  g : Fin l → Point n m → ℝ
  A : Fin r → RealVector n
  B : Fin r → RealVector m
  b : Fin r → ℝ

variable {n m l r : ℕ}

def intCast (y : IntVector m) : RealVector m := fun i => (y i : ℝ)
def Data.hard (d : Data n m l r) : Set (Point n m) :=
  {p | ∀ i, LinearForm (d.A i) (d.B i) p ≤ d.b i}
def Data.mixed (d : Data n m l r) : Set (Point n m) :=
  {p | p ∈ d.hard ∧ ∃ y : IntVector m, p.2 = intCast y}
def Data.original (d : Data n m l r) : Set (Point n m) :=
  {p | p ∈ d.mixed ∧ ∀ j, d.g j p ≤ 0}
def Data.hardFiber (d : Data n m l r) (y : IntVector m) : Set (Point n m) :=
  {p | p ∈ d.hard ∧ p.2 = intCast y}
def Data.feasibleFiber (d : Data n m l r) (y : IntVector m) : Set (Point n m) :=
  {p | p ∈ d.hardFiber y ∧ ∀ j, d.g j p ≤ 0}
def Data.restoration (d : Data n m l r) (y : IntVector m) : Set (Point n m × ℝ) :=
  {z | z.1 ∈ d.hardFiber y ∧ (∀ j, d.g j z.1 ≤ z.2) ∧ 0 ≤ z.2}

def tangent (f : Point n m → ℝ) (a q : Point n m) : ℝ :=
  f a + fderiv ℝ f a (q-a)
def selectedRows (d : Data n m l r) (a : Point n m) (rho : ℝ)
    (q : Point n m) : Prop := ∀ j, d.g j a = rho → tangent (d.g j) a q ≤ 0

/-- Internal nonemptiness is constructed from the feasible seed at the headline. -/
structure Regularity (d : Data n m l r) : Prop where
  hard_compact : IsCompact d.hard
  hard_nonempty : d.hard.Nonempty
  objective_convex : ConvexOn ℝ Set.univ d.f
  objective_C1 : ContDiff ℝ 1 d.f
  constraint_convex : ∀ j, ConvexOn ℝ Set.univ (d.g j)
  constraint_C1 : ∀ j, ContDiff ℝ 1 (d.g j)
  fiber_slater : ∀ y, (d.feasibleFiber y).Nonempty →
    ∃ p ∈ d.hardFiber y, ∀ j, d.g j p < 0

def radius (d : Data n m l r) (hr : Regularity d) : ℝ :=
  Classical.choose (Chapter03.FPUnbounded.compact_projected_radius hr.hard_compact)
theorem radius_spec (d : Data n m l r) (hr : Regularity d) :
    1 ≤ radius d hr ∧ ∀ p ∈ d.hard, ‖Chapter03.yMap n m p‖ ≤ radius d hr :=
  Classical.choose_spec (Chapter03.FPUnbounded.compact_projected_radius hr.hard_compact)

def boxedModel (d : Data n m l r) (hr : Regularity d) : ModelData n m l r where
  g := d.g
  A := d.A
  B := d.B
  rhs := d.b
  c1 := 0
  c2 := 0
  lo := fun _ => -radius d hr
  hi := fun _ => radius d hr

def targets (d : Data n m l r) (hr : Regularity d) : Finset (IntVector m) :=
  (Chapter03.FPUnbounded.compact_integer_projection_finite hr.hard_compact).toFinset

theorem mem_targets (d : Data n m l r) (hr : Regularity d) (y : IntVector m) :
    y ∈ targets d hr ↔ ∃ p ∈ d.hard, p.2 = intCast y := by
  change y ∈ (Chapter03.FPUnbounded.compact_integer_projection_finite hr.hard_compact).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  rfl

theorem intCast_eq_fp (y : IntVector m) : intCast y = Chapter03.FP.intCast y := rfl
theorem intCast_eq_oa (y : IntVector m) : intCast y = Chapter03.OAKKT.intCast y := rfl
theorem intCast_injective : Function.Injective (intCast (m := m)) := by
  intro y z h
  funext i
  exact Int.cast_injective (congrFun h i)

theorem queried_integer_bounds (d : Data n m l r) (hr : Regularity d)
    {p : Point n m} {y : IntVector m} (hp : p ∈ d.hard) (hy : p.2 = intCast y) :
    y ∈ IntegerBox (boxedModel d hr).lo (boxedModel d hr).hi := by
  have he : Chapter03.yMap n m p = Chapter03.FP.intY y := by
    change (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm p.2 = _
    rw [hy]
    rfl
  have hnorm := (radius_spec d hr).2 p hp
  rw [he] at hnorm
  exact Chapter03.FPUnbounded.mem_proofLatticeBox.mp
    (Chapter03.FPUnbounded.intY_norm_mem_proofLatticeBox hnorm)

theorem integerCylinder_closed (lo hi : RealVector m) :
    IsClosed (IntegerCylinder (n := n) lo hi) := by
  have he : IntegerCylinder (n := n) lo hi =
      Prod.snd ⁻¹' (intCast '' IntegerBox lo hi) := by
    ext p
    simp only [IntegerCylinder, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,he.symm⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,he.symm⟩
  rw [he]
  exact ((integerBox_finite lo hi).image intCast).isClosed.preimage continuous_snd

theorem boxed_base_eq (d : Data n m l r) (hr : Regularity d) :
    (boxedModel d hr).linearRegion ∩
      IntegerCylinder (n := n) (boxedModel d hr).lo (boxedModel d hr).hi = d.mixed := by
  ext p
  constructor
  · rintro ⟨hp,y,hy,he⟩
    exact ⟨hp,y,he⟩
  · rintro ⟨hp,y,he⟩
    exact ⟨hp,y,queried_integer_bounds d hr hp he,he⟩

theorem mixed_compact (d : Data n m l r) (hr : Regularity d) : IsCompact d.mixed := by
  rw [← boxed_base_eq d hr]
  exact hr.hard_compact.inter_right (integerCylinder_closed _ _)

theorem boxed_original_eq (d : Data n m l r) (hr : Regularity d) :
    (boxedModel d hr).feasibleOn Set.univ = d.original := by
  ext p
  rw [source_feasible_iff]
  constructor
  · rintro ⟨_,hg,hp,y,hy,he⟩
    exact ⟨⟨hp,y,he⟩,hg⟩
  · rintro ⟨⟨hp,y,he⟩,hg⟩
    exact ⟨Set.mem_univ _,hg,hp,y,queried_integer_bounds d hr hp he,he⟩

theorem boxed_hardFiber_eq (d : Data n m l r) (hr : Regularity d) (y : IntVector m) :
    (boxedModel d hr).fixedLinearFiber (intCast y) = d.hardFiber y := rfl

theorem boxed_feasibleFiber_eq (d : Data n m l r) (hr : Regularity d)
    (y : IntVector m) :
    (boxedModel d hr).fixedNonlinearFiber (intCast y) = d.feasibleFiber y := rfl

/-- Instantiating `P` by the master rows or by rows and the level bound preserves
exactly the source search set, including the epigraph height coordinate. -/
theorem boxed_restriction_eq (d : Data n m l r) (hr : Regularity d)
    (P : Point n m × ℝ → Prop) :
    {z | z.1 ∈ (boxedModel d hr).linearRegion ∩
      IntegerCylinder (n := n) (boxedModel d hr).lo (boxedModel d hr).hi ∧ P z} =
      {z | z.1 ∈ d.mixed ∧ P z} := by rw [boxed_base_eq]

theorem original_subset_mixed (d : Data n m l r) : d.original ⊆ d.mixed := fun _ h => h.1

theorem feasibleFiber_original (d : Data n m l r) (y : IntVector m)
    {p : Point n m} (hp : p ∈ d.feasibleFiber y) : p ∈ d.original :=
  ⟨⟨hp.1.1,y,hp.1.2⟩,hp.2⟩

theorem hardFiber_compact (d : Data n m l r) (hr : Regularity d) (y : IntVector m) :
    IsCompact (d.hardFiber y) :=
  hr.hard_compact.inter_right (isClosed_eq continuous_snd continuous_const)

theorem feasibleFiber_compact (d : Data n m l r) (hr : Regularity d)
    (y : IntVector m) : IsCompact (d.feasibleFiber y) := by
  have hc : IsClosed {p | ∀ j, d.g j p ≤ 0} := by
    have he : {p | ∀ j, d.g j p ≤ 0} = ⋂ j, {p | d.g j p ≤ 0} := by ext p; simp
    rw [he]
    exact isClosed_iInter fun j => isClosed_le (hr.constraint_C1 j).continuous continuous_const
  exact (hardFiber_compact d hr y).inter_right hc

theorem tangent_continuous (f : Point n m → ℝ) (a : Point n m) :
    Continuous (tangent f a) :=
  continuous_const.add ((fderiv ℝ f a).continuous.comp (continuous_id.sub continuous_const))

theorem tangent_support {f : Point n m → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hd : ContDiff ℝ 1 f) (a q : Point n m) :
    tangent f a q ≤ f q :=
  tangent_underestimator_on hc (Set.mem_univ _) (Set.mem_univ _)
    ((hd.differentiable (by norm_num)).differentiableAt.hasFDerivAt)

theorem selectedRows_closed (d : Data n m l r) (a : Point n m) (rho : ℝ) :
    IsClosed {q | selectedRows d a rho q} := by
  have he : {q | selectedRows d a rho q} =
      ⋂ j, ⋂ (_ : d.g j a = rho), {q | tangent (d.g j) a q ≤ 0} := by
    ext q
    simp [selectedRows]
  rw [he]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (tangent_continuous _ _) continuous_const

theorem selectedRows_original (d : Data n m l r) (hr : Regularity d)
    (a : Point n m) (rho : ℝ) {q : Point n m} (hq : q ∈ d.original) :
    selectedRows d a rho q := by
  intro j _
  exact (tangent_support (hr.constraint_convex j) (hr.constraint_C1 j) a q).trans (hq.2 j)

theorem feasibleFiber_attained (d : Data n m l r) (hr : Regularity d)
    (y : IntVector m) (hne : (d.feasibleFiber y).Nonempty) :
    ∃ a, IsMinimizer (d.feasibleFiber y) d.f a :=
  compact_feasible_attainment (feasibleFiber_compact d hr y) hne
    hr.objective_C1.continuous.continuousOn

end Chapter06.Level
