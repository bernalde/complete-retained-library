module

public import Chapter02FBBTSourceData
public import Mathlib.Tactic

@[expose] public section

/-! Concrete original data for the complete retained-source control. Later
operator/LP applications are required; these arithmetic helpers are uncounted. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02FBBT
namespace Chapter02FBBTControls

def point (x y : ℝ) : RealVector 2 := ![x, y]

def data : BBPolyData 2 1 1 where
  coefficient := fun _ => ![1, 0]
  rhs := fun _ => 1
  c := fun x => ![(x 1)^2 - 1]
  f := fun x => -x 0

def integerCoordinates : Finset (Fin 2) := {1}

def initialX : Bounds (Fin 2) := (point 0 (-2), point 2 2)

def tightenedX : Bounds (Fin 2) := (point 0 (-2), point 1 2)

def optimum : RealVector 2 := point 1 0

lemma initialX_ordered : Ordered initialX := by
  intro i
  fin_cases i <;> norm_num [initialX, point]

lemma tightenedX_ordered : Ordered tightenedX := by
  intro i
  fin_cases i <;> norm_num [tightenedX, point]

lemma actual_initial_row_bounds (i : Fin 1) :
    sourceLower data initialX i = 0 ∧ data.rhs i = 1 := by
  fin_cases i
  norm_num [sourceLower, data, initialX, point, Fin.sum_univ_succ, affineProductLo]

lemma actual_source_optimum :
    IsMinimizer (data.feasible integerCoordinates ∩ members initialX) data.f optimum := by
  constructor
  · constructor
    · refine ⟨?_, ?_, ?_⟩
      · intro i
        fin_cases i
        norm_num [data, optimum, point, Fin.sum_univ_succ]
      · intro j
        fin_cases j
        norm_num [data, optimum, point]
      · rintro ⟨i, hi⟩
        have hi' : i = 1 := by simpa [integerCoordinates] using hi
        subst i
        exact ⟨0, by norm_num [optimum, point]⟩
    · intro i
      fin_cases i <;> norm_num [initialX, optimum, point]
  · intro x hx
    have hrow := hx.1.1 (0 : Fin 1)
    have hx1 : x 0 ≤ 1 := by
      simpa [data, Fin.sum_univ_succ] using hrow
    change -(optimum 0) ≤ -x 0
    norm_num [optimum, point]
    linarith

lemma retained_nonlinear_effective :
    point 0 2 ∈ members tightenedX ∧ ¬ (∀ j, data.c (point 0 2) j ≤ 0) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [tightenedX, point]
  · intro h
    have := h (0 : Fin 1)
    norm_num [data, point] at this

lemma retained_integrality_effective :
    point 0 (1/2) ∈ members tightenedX ∧
      (∀ j, data.c (point 0 (1/2)) j ≤ 0) ∧
      ¬ (∀ i : {i : Fin 2 // i ∈ integerCoordinates},
          ∃ k : ℤ, (k : ℝ) = point 0 (1/2) i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [tightenedX, point]
  · intro j
    fin_cases j
    norm_num [data, point]
  · intro h
    obtain ⟨k, hk⟩ := h ⟨1, by simp [integerCoordinates]⟩
    have hpos : (0 : ℝ) < k := by norm_num [point] at hk; linarith
    have hlt : (k : ℝ) < 1 := by norm_num [point] at hk; linarith
    have hki : 0 < k := by exact_mod_cast hpos
    have hki' : k < 1 := by exact_mod_cast hlt
    omega

end Chapter02FBBTControls
