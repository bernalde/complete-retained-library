module

public import Chapter03FPSearchCQ
public import Chapter03FPSearchModel

@[expose] public section

/-! The basic bridge's domain is exactly a finite indexed affine intersection.
No row deletion or irredundancy is assumed. A zero, repeated or opposed active
row can make LICQ false; this does not alter the represented feasible domain. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch
variable {n m l r : ℕ}

structure BaseRows (d : Data n m l) (r : ℕ) where
  linear : Fin r → Point n m →L[ℝ] ℝ
  offset : Fin r → ℝ
  exact_base : ∀ p, p ∈ d.base ↔ ∀ i, linear i p + offset i ≤ 0

variable {d : Data n m l}

def BaseRows.residual (b : BaseRows d r) (i : Fin r) (p : Point n m) : ℝ :=
  b.linear i p + b.offset i

theorem BaseRows.derivative (b : BaseRows d r) (i : Fin r) (p : Point n m) :
    HasFDerivAt (b.residual i) (b.linear i) p :=
  (b.linear i).hasFDerivAt.add_const (b.offset i)

/-- Sum indices retain every actual base residual and every original g row. -/
def jointRows (d : Data n m l) (b : BaseRows d r) :
    (Fin r ⊕ Fin l) → Point n m → ℝ := Sum.elim b.residual d.g

def jointRowD (d : Data n m l) (b : BaseRows d r) (p : Point n m) :
    (Fin r ⊕ Fin l) → Point n m →L[ℝ] ℝ :=
  Sum.elim b.linear (fun j => d.Dg j p)

theorem jointRows_relaxation (d : Data n m l) (b : BaseRows d r) :
    {p | ∀ i, jointRows d b i p ≤ 0} = d.relaxation := by
  ext p
  constructor
  · intro h
    exact ⟨(b.exact_base p).mpr (fun i => h (.inl i)),fun j => h (.inr j)⟩
  · rintro ⟨hb,hg⟩ i
    cases i with
    | inl i => exact (b.exact_base p).mp hb i
    | inr j => exact hg j

theorem jointRows_derivative (d : Data n m l) (b : BaseRows d r)
    (h : Analytic d) (p : Point n m) (hp : p ∈ d.base) :
    ∀ i, HasFDerivAt (jointRows d b i) (jointRowD d b p i) p := by
  intro i
  cases i with
  | inl i => exact b.derivative i p
  | inr j => exact h.derivative_g j p hp

/-- A base-feasible comparison point satisfies all active base linearizations. -/
theorem BaseRows.active_direction (b : BaseRows d r) (p z : Point n m)
    (hz : z ∈ d.base) (i : Fin r) (hi : b.residual i p = 0) :
    b.linear i (z-p) ≤ 0 := by
  have hz' := (b.exact_base z).mp hz i
  simp only [BaseRows.residual] at hi
  rw [map_sub]
  linarith

/-- Uniform at every selectable projection minimum, not one convenient choice. -/
def ProjectionLICQ (d : Data n m l) (b : BaseRows d r)
    (Q : Finset (IntVector m)) : Prop :=
  ∀ q ∈ Q, ∀ p, IsMinimizer d.relaxation (distance q) p →
    JointLICQ (jointRows d b) (jointRowD d b p) p

/-- Actual projection optimality plus all-row joint LICQ gives the normal on
base points satisfying each active g tangent. No normal is a hypothesis. -/
theorem affine_base_projection_normal (d : Data n m l) (b : BaseRows d r)
    (h : Analytic d) (q : IntVector m) (p z : Point n m)
    (hp : IsMinimizer d.relaxation (distance q) p)
    (hcq : JointLICQ (jointRows d b) (jointRowD d b p) p)
    (hz : z ∈ d.base)
    (hg : ∀ j, d.g j p = 0 → d.Dg j p (z-p) ≤ 0) :
    0 ≤ @inner ℝ _ _ (Chapter03.yMap n m p - intY q)
      (Chapter03.yMap n m z - Chapter03.yMap n m p) := by
  apply joint_projection_normal_of_licq (jointRows d b) (jointRowD d b p) q p z
  · simpa only [jointRows_relaxation d b] using hp
  · exact jointRows_derivative d b h p hp.1.1
  · exact hcq
  · intro i hi
    cases i with
    | inl i => exact b.active_direction p z hz i hi
    | inr j => exact hg j hi

end Chapter03.FPSearch
