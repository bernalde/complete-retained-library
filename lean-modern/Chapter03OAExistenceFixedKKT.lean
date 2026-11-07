module

public import Chapter03OAExistenceCQ

@[expose] public section

/-! The literal fixed-x active-family LICQ supplies the existing FixedKKT
certificate at every actual minimum satisfying it. This proves necessity from
pointwise ambient derivatives, without convexity, Slater or an attainment input
other than the same actual minimum. No original row is deleted. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAExistence
namespace Chapter03.OAKKT
variable {n m l r : ℕ}

theorem fixed_rows_fiber_iff (d : ModelData n m l r)
    (y : RealVector m) (x : RealVector n) :
    (∀ i, fixedRows d y i x ≤ 0) ↔ x ∈ fiber d y := by
  rw [fiber_iff]
  constructor
  · intro h
    exact ⟨fun i => h (Sum.inr i), fun j => h (Sum.inl j)⟩
  · rintro ⟨hh, hs⟩ i
    cases i with
    | inl j => exact hs j
    | inr j => exact hh j

theorem fixed_rows_derivative (d : ModelData n m l r)
    (x : RealVector n) (y : RealVector m)
    (Dg : Fin l → Point n m →L[ℝ] ℝ)
    (hDg : ∀ j, HasFDerivAt (d.g j) (Dg j) (x,y)) :
    ∀ i, HasFDerivAt (fixedRows d y i) (fixedRowD d Dg i) x := by
  intro i
  cases i with
  | inl j => exact fiber_derivative (hDg j)
  | inr j => exact hard_derivative d y j x

theorem fixed_mfcq_of_licq (d : ModelData n m l r)
    (x : RealVector n) (y : RealVector m)
    (Dg : Fin l → Point n m →L[ℝ] ℝ)
    (hlicq : FixedLICQ d x y Dg) : FixedMFCQ d x y Dg :=
  strict_direction_of_active_independent (fixedRows d y) (fixedRowD d Dg) x hlicq

/-- A pointwise MFCQ suffices to construct every field of the accepted
certificate for this actual minimizer and these actual ambient derivatives. -/
theorem fixed_kkt_exists_of_mfcq (d : ModelData n m l r)
    (f : Point n m → ℝ) (x : RealVector n) (y : RealVector m)
    (Df : Point n m →L[ℝ] ℝ)
    (Dg : Fin l → Point n m →L[ℝ] ℝ)
    (hDf : HasFDerivAt f Df (x,y))
    (hDg : ∀ j, HasFDerivAt (d.g j) (Dg j) (x,y))
    (hmin : IsMinimizer (fiber d y) (fiberObjective f y) x)
    (hmfcq : FixedMFCQ d x y Dg) : Nonempty (FixedKKT d f x y) := by
  have hmin' : IsMinimizer {z | ∀ i, fixedRows d y i z ≤ 0}
      (fiberObjective f y) x :=
    ⟨(fixed_rows_fiber_iff d y x).mpr hmin.1,
      fun z hz => hmin.2 z ((fixed_rows_fiber_iff d y z).mp hz)⟩
  obtain ⟨weights, hw, hc, hstat⟩ := minimum_multipliers_of_mfcq
    (fixedRows d y) (fixedRowD d Dg) x (fiberObjective f y) (restrict Df)
    hmin' (fiber_derivative hDf) (fixed_rows_derivative d x y Dg hDg) hmfcq
  refine ⟨{
    Df := Df, Dg := Dg
    lambda := fun j => weights (Sum.inl j)
    mu := fun i => weights (Sum.inr i)
    primal := hmin.1
    derivative_f := hDf
    derivative_g := hDg
    lambda_nonneg := fun j => hw (Sum.inl j)
    mu_nonneg := fun i => hw (Sum.inr i)
    soft_compl := fun j => hc (Sum.inl j)
    hard_compl := fun i => hc (Sum.inr i)
    stationarity := ?_
  }⟩
  simpa [Fintype.sum_sum_type, fixedRowD, add_assoc] using hstat

/-- Every actual fixed-fiber minimum satisfying LICQ of all active x normals
has the existing FixedKKT certificate. Constant soft rows and hard bounds are
retained. No positivity of dimensions, Slater point, or convexity is required. -/
theorem fixed_kkt_exists_of_licq (d : ModelData n m l r)
    (f : Point n m → ℝ) (x : RealVector n) (y : RealVector m)
    (Df : Point n m →L[ℝ] ℝ)
    (Dg : Fin l → Point n m →L[ℝ] ℝ)
    (hDf : HasFDerivAt f Df (x,y))
    (hDg : ∀ j, HasFDerivAt (d.g j) (Dg j) (x,y))
    (hmin : IsMinimizer (fiber d y) (fiberObjective f y) x)
    (hlicq : FixedLICQ d x y Dg) : Nonempty (FixedKKT d f x y) :=
  fixed_kkt_exists_of_mfcq d f x y Df Dg hDf hDg hmin
    (fixed_mfcq_of_licq d x y Dg hlicq)

end Chapter03.OAKKT

#check Chapter03.OAKKT.fixed_kkt_exists_of_licq
#print axioms Chapter03.OAKKT.fixed_kkt_exists_of_licq
