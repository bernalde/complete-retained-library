module

public import Chapter02Initializer
public import Chapter02MultiplierEdgeExamples

@[expose] public section

/-! Exact consumers of the relative initializer interface. Scalar controls use
actual feasible pairs and universal bounds. Empty rows and zero-dimensional
positive-row models remain distinct; no solver produces these witnesses. -/
noncomputable section
open Chapter02
namespace Chapter02InitializerExamples

def jumpRow (x : ℝ) : ℝ := if x < 0 then 1 else x - 1

def scalarRows (_ : Fin 1) (x : ℝ) : ℝ := x - 1

def oneRows (_ : Fin 1) (_ : ℝ) : ℝ := 1

def zeroRows (_ : Fin 1) (_ : ℝ) : ℝ := 0

private theorem jump_relative : ContinuousOn jumpRow (Set.Icc (0 : ℝ) 2) := by
  have h : Continuous (fun x : ℝ => x - 1) := continuous_id.sub continuous_const
  apply h.continuousOn.congr
  intro x hx
  simp [jumpRow, not_lt_of_ge hx.1]

private theorem jump_discontinuous : ¬ ContinuousAt jumpRow 0 := by
  intro hc
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc 1 (by norm_num)
  have hneg : -δ / 2 < 0 := by linarith
  have hnear : dist (-δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg hneg]
    linarith
  have hbad := hclose hnear
  norm_num [jumpRow, hneg, Real.dist_eq] at hbad

/-- G1/G2 apply to a row with an actual ambient jump at the domain boundary. -/
theorem relative_attainment_control :
    ContinuousOn jumpRow (Set.Icc (0 : ℝ) 2) ∧ ¬ ContinuousAt jumpRow 0 ∧
    ContinuousOn (eshMaximum (fun _ : Fin 1 => jumpRow)) (Set.Icc (0 : ℝ) 2) ∧
    ∃ p, IsMinimizer (Set.Icc (0 : ℝ) 2) (eshMaximum (fun _ : Fin 1 => jumpRow)) p ∧
      IsMinimizer (RestorationPairs (Set.Icc (0 : ℝ) 2) (fun _ : Fin 1 => jumpRow))
        Prod.snd (p, eshMaximum (fun _ : Fin 1 => jumpRow) p) := by
  refine ⟨jump_relative, jump_discontinuous,
    initializer_maximum_continuousOn (fun _ => jump_relative), ?_⟩
  exact initializer_minimum_attained isCompact_Icc
    ⟨0, by norm_num⟩ (fun _ => jump_relative)

/-- A positive feasible height coexists with strictness; a nonoptimal negative
height is consumed directly, without an assumed optimizer. -/
theorem feasible_height_control :
    ((2, 1) : ℝ × ℝ) ∈ RestorationPairs (Set.Icc (0 : ℝ) 2) scalarRows ∧
    (∀ j, scalarRows j 0 < 0) ∧
    (((1/2, -1/2) : ℝ × ℝ) ∈ RestorationPairs (Set.Icc (0 : ℝ) 2) scalarRows) ∧
    (∀ j, scalarRows j (1/2) < 0) ∧
    ¬ IsMinimizer (RestorationPairs (Set.Icc (0 : ℝ) 2) scalarRows) Prod.snd
      ((1/2, -1/2) : ℝ × ℝ) := by
  have hneg : ((1/2, -1/2) : ℝ × ℝ) ∈
      RestorationPairs (Set.Icc (0 : ℝ) 2) scalarRows := by
    norm_num [RestorationPairs, scalarRows]
  have hsign := (initializer_feasible_height hneg).2.1 (by norm_num)
  refine ⟨by norm_num [RestorationPairs, scalarRows], by intro j; norm_num [scalarRows],
    hneg, hsign, ?_⟩
  intro hmin
  have hbetter := hmin.2 ((0, -1) : ℝ × ℝ) (by norm_num [RestorationPairs, scalarRows])
  norm_num at hbetter

/-- A zero lower bound is not a primal witness, even on a compact interval.
The positive bound invokes the new infeasibility consumer. -/
theorem zero_and_positive_bound_control :
    IsLowerBound (RestorationPairs (Set.Icc (0 : ℝ) 1) oneRows) Prod.snd 0 ∧
    IsLowerBound (RestorationPairs (Set.Icc (0 : ℝ) 1) oneRows) Prod.snd 1 ∧
    {p | p ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, oneRows j p ≤ 0} = ∅ := by
  have hpos : IsLowerBound (RestorationPairs (Set.Icc (0 : ℝ) 1) oneRows) Prod.snd 1 := by
    intro q hq
    exact hq.2 0
  refine ⟨?_, hpos, initializer_positive_bound_empty hpos (by norm_num)⟩
  intro q hq
  exact (by norm_num : (0 : ℝ) ≤ 1).trans (hpos q hq)

/-- Actual attained zero is classified by the already accepted sign theorem. -/
theorem attained_zero_control :
    ∃ p, IsMinimizer (Set.Icc (0 : ℝ) 1) (eshMaximum zeroRows) p ∧
      IsMinimizer (RestorationPairs (Set.Icc (0 : ℝ) 1) zeroRows) Prod.snd
        (p, eshMaximum zeroRows p) ∧
      eshMaximum zeroRows p = 0 ∧
      (∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ j, zeroRows j x ≤ 0) ∧
      ¬ ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ j, zeroRows j x < 0 := by
  obtain ⟨p, hp, hpair⟩ := initializer_minimum_attained (g := zeroRows)
    (S := Set.Icc (0 : ℝ) 1) isCompact_Icc ⟨0, by norm_num⟩
    (fun _ => continuous_const.continuousOn)
  obtain ⟨j, hj⟩ := eshMaximum_attained zeroRows p
  have hz : eshMaximum zeroRows p = 0 := hj
  exact ⟨p, hp, hpair, hz, (signedMinimum_zero_iff hp).mp hz⟩

/-- Empty rows preserve a nonempty domain and allow arbitrary heights; they do
not receive a fabricated signed maximum or minimizer. -/
theorem empty_rows_control :
    (((0, -1) : ℝ × ℝ) ∈ RestorationPairs (Set.Icc (0 : ℝ) 1)
      (fun j : Fin 0 => Fin.elim0 j)) ∧
    (∀ j : Fin 0, (Fin.elim0 j : ℝ → ℝ) 0 < 0) ∧
    (∀ v : ℝ, ∃ q ∈ RestorationPairs (Set.Icc (0 : ℝ) 1)
      (fun j : Fin 0 => Fin.elim0 j), q.2 < v) ∧
    ¬ ∃ q, IsMinimizer (RestorationPairs (Set.Icc (0 : ℝ) 1)
      (fun j : Fin 0 => Fin.elim0 j)) Prod.snd q := by
  have hpair : ((0, -1) : ℝ × ℝ) ∈ RestorationPairs (Set.Icc (0 : ℝ) 1)
      (fun j : Fin 0 => Fin.elim0 j) := by
    refine ⟨by norm_num, fun j => Fin.elim0 j⟩
  refine ⟨hpair, (initializer_feasible_height hpair).2.1 (by norm_num), ?_, ?_⟩
  · exact restorationPairs_unbounded_empty_rows _ ⟨0, by norm_num⟩
  · exact restorationPairs_no_minimizer_empty_rows _ _

/-- A prior one-row minimum in dimension zero supplies a real positive lower
bound to E2. This is a new consumer call, not a new minimum certificate. -/
theorem zero_dimension_bound_control :
    {p | p ∈ Chapter02MultiplierEdgeExamples.zeroDimensionModel.fixedLinearFiber
          (0 : RealVector 0) ∧
      ∀ j, Chapter02MultiplierEdgeExamples.zeroDimensionModel.g j p ≤ 0} = ∅ := by
  have hb := minimizer_is_lowerBound
    Chapter02MultiplierEdgeExamples.zeroDimension_restoration_minimum
  exact initializer_positive_bound_empty hb (by norm_num)

end Chapter02InitializerExamples

#print axioms Chapter02InitializerExamples.relative_attainment_control
#print axioms Chapter02InitializerExamples.feasible_height_control
#print axioms Chapter02InitializerExamples.zero_and_positive_bound_control
#print axioms Chapter02InitializerExamples.attained_zero_control
#print axioms Chapter02InitializerExamples.empty_rows_control
#print axioms Chapter02InitializerExamples.zero_dimension_bound_control
