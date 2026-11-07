module

public import Chapter02BBNodes
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Infinite-bound ablations, explicitly outside finite-bound ModelData.
These exact examples test the load-bearing finite-bound hypothesis of the
mixed-to-continuous compactness bridge. Execution statements are added only
for a literal extended-bound process, never inferred from these sets alone. -/
noncomputable section
namespace Chapter02

def bbAllInteger (z : RealVector 2) : Prop := ∀ i, ∃ k : ℤ, (k : ℝ) = z i

def bbHalfLine : Set (RealVector 2) := {z | z 0 - z 1 = 1 / 2}

def bbHalfPoint (t : ℝ) : RealVector 2 := ![t + 1 / 2, t]

theorem bb_half_point_mem (t : ℝ) : bbHalfPoint t ∈ bbHalfLine := by
  simp [bbHalfPoint, bbHalfLine]

theorem bb_half_point_unique {z : RealVector 2} (hz : z ∈ bbHalfLine) :
    z = bbHalfPoint (z 1) := by
  funext i
  fin_cases i
  · change z 0 = z 1 + 1 / 2
    change z 0 - z 1 = 1 / 2 at hz
    linarith
  · rfl

theorem bb_half_no_integer {z : RealVector 2} (hz : z ∈ bbHalfLine) :
    ¬ bbAllInteger z := by
  intro hi
  obtain ⟨a, ha⟩ := hi 0
  obtain ⟨b, hb⟩ := hi 1
  change z 0 - z 1 = 1 / 2 at hz
  have he : ((2 * (a - b) : ℤ) : ℝ) = 1 := by
    push_cast
    rw [ha, hb]
    linarith
  have hh : 2 * (a - b) = 1 := by exact_mod_cast he
  omega

theorem bb_half_mixed_empty : bbHalfLine ∩ {z | bbAllInteger z} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨hz, hi⟩
  exact bb_half_no_integer hz hi

theorem bb_half_mixed_compact : IsCompact (bbHalfLine ∩ {z | bbAllInteger z}) := by
  rw [bb_half_mixed_empty]
  exact isCompact_empty

theorem bb_half_fractional {z : RealVector 2} (hz : z ∈ bbHalfLine) :
    ∃ i, BBFractional (z i) := by
  classical
  by_contra h
  apply bb_half_no_integer hz
  intro i
  by_contra hi
  exact h ⟨i, hi⟩

theorem bb_half_constant_minimum {S : Set (RealVector 2)} {z : RealVector 2}
    (hz : z ∈ S) : IsMinimizer S (fun _ => (0 : ℝ)) z :=
  ⟨hz, fun _ _ => le_rfl⟩

def bbIrrationalLine : Set (RealVector 2) := {z | z 0 = Real.sqrt 2 * z 1}

def bbIrrationalPoint (t : ℝ) : RealVector 2 := ![Real.sqrt 2 * t, t]

theorem bb_irrational_point_mem (t : ℝ) : bbIrrationalPoint t ∈ bbIrrationalLine := rfl

theorem bb_irrational_integer_zero {z : RealVector 2} (hz : z ∈ bbIrrationalLine)
    (hi : bbAllInteger z) : z = 0 := by
  obtain ⟨a, ha⟩ := hi 0
  obtain ⟨b, hb⟩ := hi 1
  change z 0 = Real.sqrt 2 * z 1 at hz
  have hb0 : b = 0 := by
    by_contra h
    apply (irrational_sqrt_two.mul_intCast h).ne_int a
    rw [hb, ← hz, ha]
  have hz1 : z 1 = 0 := by rw [← hb, hb0]; norm_num
  have hz0 : z 0 = 0 := by rw [hz, hz1, mul_zero]
  funext i
  fin_cases i
  · exact hz0
  · exact hz1

theorem bb_irrational_mixed_singleton :
    bbIrrationalLine ∩ {z | bbAllInteger z} = {0} := by
  ext z
  constructor
  · rintro ⟨hz, hi⟩
    exact bb_irrational_integer_zero hz hi
  · intro hz
    have he : z = 0 := hz
    subst z
    exact ⟨by simp [bbIrrationalLine], fun _ => ⟨0, by simp⟩⟩

theorem bb_irrational_mixed_compact :
    IsCompact (bbIrrationalLine ∩ {z | bbAllInteger z}) := by
  rw [bb_irrational_mixed_singleton]
  exact isCompact_singleton

theorem bb_irrational_mixed_nonempty :
    (bbIrrationalLine ∩ {z | bbAllInteger z}).Nonempty := by
  rw [bb_irrational_mixed_singleton]
  exact Set.singleton_nonempty _

theorem bb_irrational_relaxation_unbounded :
    ∀ B : ℝ, ∃ z ∈ bbIrrationalLine, -z 1 < B := by
  intro B
  refine ⟨bbIrrationalPoint (1 - B), bb_irrational_point_mem _, ?_⟩
  change -(1 - B) < B
  linarith

theorem bb_irrational_relaxation_noncompact : ¬ IsCompact bbIrrationalLine := by
  intro hc
  have hf : Continuous (fun z : RealVector 2 => -z 1) := by fun_prop
  obtain ⟨B, hB⟩ := (hc.image hf).bddBelow
  obtain ⟨z, hz, hlt⟩ := bb_irrational_relaxation_unbounded B
  exact (not_lt_of_ge (hB ⟨z, hz, rfl⟩)) hlt

/-- Compact nonempty mixed base alone does not justify bad-status deletion
when integer coordinates lack finite real bounds. -/
theorem bb_infinite_bounds_bad_discharge_fails :
    IsCompact (bbIrrationalLine ∩ {z | bbAllInteger z}) ∧
      (bbIrrationalLine ∩ {z | bbAllInteger z}).Nonempty ∧
      (∀ B : ℝ, ∃ z ∈ bbIrrationalLine, -z 1 < B) :=
  ⟨bb_irrational_mixed_compact, bb_irrational_mixed_nonempty,
    bb_irrational_relaxation_unbounded⟩

end Chapter02

#print axioms Chapter02.bb_half_point_mem
#print axioms Chapter02.bb_half_point_unique
#print axioms Chapter02.bb_half_no_integer
#print axioms Chapter02.bb_half_mixed_empty
#print axioms Chapter02.bb_half_mixed_compact
#print axioms Chapter02.bb_half_fractional
#print axioms Chapter02.bb_half_constant_minimum
#print axioms Chapter02.bb_irrational_point_mem
#print axioms Chapter02.bb_irrational_integer_zero
#print axioms Chapter02.bb_irrational_mixed_singleton
#print axioms Chapter02.bb_irrational_mixed_compact
#print axioms Chapter02.bb_irrational_mixed_nonempty
#print axioms Chapter02.bb_irrational_relaxation_unbounded
#print axioms Chapter02.bb_irrational_relaxation_noncompact
#print axioms Chapter02.bb_infinite_bounds_bad_discharge_fails
