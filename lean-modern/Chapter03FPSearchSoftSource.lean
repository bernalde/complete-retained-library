module

public import Chapter03FPSearchSource

@[expose] public section

/-! Actual all-soft first-search master correspondence from the accepted bound
row metadata. All original g rows and their retained-history selections survive.
No objective epigraph, cutoff or added projection row is used in this proof. -/
noncomputable section
open Chapter02 Chapter03.FP Chapter03.OAKKT
namespace Chapter03.FPSearch
variable {n m l : ℕ} {d : Data n m l} {x : Bounds n} {y : Bounds m}

/-- Every present finite side is an actual global affine residual among g.
The accepted metadata retains Valid, including its wrong-infinity exclusion. -/
abbrev SoftBoundRows (d : Data n m l) (x : Bounds n) (y : Bounds m) :=
  FPUnbounded.SoftBoundRows d.toUnbounded x y

theorem SoftBoundRows.relaxation_iff (B : SoftBoundRows d x y) (p : Point n m) :
    p ∈ d.relaxation ↔ ∀ j, d.g j p ≤ 0 :=
  FPUnbounded.SoftBoundRows.relaxation_iff B p

theorem SoftBoundRows.original_iff (B : SoftBoundRows d x y) (p : Point n m) :
    p ∈ d.original ↔ (∀ j, d.g j p ≤ 0) ∧ Integral p :=
  FPUnbounded.SoftBoundRows.original_iff B p

/-- The initial all-g tangent family enforces the actual box. Later selected
rows are retained unchanged, and no feasible-history premise is needed here. -/
theorem SoftBoundRows.base_of_initial_rows (B : SoftBoundRows d x y)
    (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    {p : Point n m} (hp : Rows d s p) : p ∈ d.base := by
  rw [show d.base = _ from B.base_eq]
  constructor
  · apply FPUnbounded.bounds_of_present_sides x B.xValid p.1
    · intro i a ha
      obtain ⟨j,hj⟩ := B.xLower i a ha
      change ∀ p, d.g j p = a - p.1 i at hj
      have haf : AffineRow (d.g j) := by
        rw [funext hj]
        exact FPUnbounded.x_lower_affine i a
      have h := affine_row_of_rows d s hp j haf (hd j)
      exact sub_nonpos.mp (by simpa only [hj] using h)
    · intro i a ha
      obtain ⟨j,hj⟩ := B.xUpper i a ha
      change ∀ p, d.g j p = p.1 i - a at hj
      have haf : AffineRow (d.g j) := by
        rw [funext hj]
        exact FPUnbounded.x_upper_affine i a
      have h := affine_row_of_rows d s hp j haf (hd j)
      exact sub_nonpos.mp (by simpa only [hj] using h)
  · apply FPUnbounded.bounds_of_present_sides y B.yValid p.2
    · intro i a ha
      obtain ⟨j,hj⟩ := B.yLower i a ha
      change ∀ p, d.g j p = a - p.2 i at hj
      have haf : AffineRow (d.g j) := by
        rw [funext hj]
        exact FPUnbounded.y_lower_affine i a
      have h := affine_row_of_rows d s hp j haf (hd j)
      exact sub_nonpos.mp (by simpa only [hj] using h)
    · intro i a ha
      obtain ⟨j,hj⟩ := B.yUpper i a ha
      change ∀ p, d.g j p = p.2 i - a at hj
      have haf : AffineRow (d.g j) := by
        rw [funext hj]
        exact FPUnbounded.y_upper_affine i a
      have h := affine_row_of_rows d s hp j haf (hd j)
      exact sub_nonpos.mp (by simpa only [hj] using h)

/-- Full master identity in both modes, with every original history row intact. -/
theorem SoftBoundRows.master_iff (B : SoftBoundRows d x y)
    (mode : Mode) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) (p : Point n m) :
    p ∈ master d mode s ↔ p ∈ softMaster d mode s := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨B.base_of_initial_rows s hd h.2.1,h⟩

theorem SoftBoundRows.master_eq_soft (B : SoftBoundRows d x y)
    (mode : Mode) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) :
    master d mode s = softMaster d mode s :=
  Set.ext (B.master_iff mode s hd)

/-- The objective is exactly the same y-only L1 distance; all ties are preserved. -/
theorem SoftBoundRows.master_minimizer_iff (B : SoftBoundRows d x y)
    (mode : Mode) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) (p : Point n m) :
    IsMinimizer (master d mode s) (masterCost s) p ↔
      IsMinimizer (softMaster d mode s) (masterCost s) p := by
  rw [B.master_eq_soft mode s hd]

/-- On every actual valid history the analytic derivative assumptions supply
the seed derivatives, rather than assuming the source-master identity. -/
theorem SoftBoundRows.master_eq_soft_of_valid (B : SoftBoundRows d x y)
    (h : Analytic d) (mode : Mode) (s : State n m) (hs : Valid d s) :
    master d mode s = softMaster d mode s :=
  B.master_eq_soft mode s (fun j => h.derivative_g j s.seed hs.seed.1)

/-- Source finite-Y containment is derived even on the literal all-soft master.
No bound is inferred merely from boundedness of the nonlinear feasible region. -/
theorem SoftBoundRows.soft_target_mem (B : SoftBoundRows d x y)
    (mode : Mode) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed)
    (lo hi : RealVector m)
    (hl : ∀ i, y.lower i = .finite (lo i))
    (hu : ∀ i, y.upper i = .finite (hi i))
    {p : Point n m} (hp : p ∈ softMaster d mode s)
    (q : IntVector m) (hq : p.2 = FP.intCast q) :
    q ∈ (integerBox_finite lo hi).toFinset := by
  have hb := B.base_of_initial_rows s hd hp.2.1
  rw [show d.base = _ from B.base_eq] at hb
  rw [Set.Finite.mem_toFinset]
  intro i
  have hi' := hb.2 i
  simpa only [hl i,hu i,ExtendedBound.lowerHolds,ExtendedBound.upperHolds,
    hq,FP.intCast] using hi'

end Chapter03.FPSearch
