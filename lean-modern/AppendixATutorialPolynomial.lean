module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
An exact rational-polynomial countercertificate for the final polynomial
displayed in original thesis Example A..2, equation (A.23).

Indices below are zero-based: `alpha i j` is the source's alpha_(i+1,j+1),
and `beta i` is beta_(i+1). The 38 displayed generators and the separate
20 Boolean augmentations are literal finite lists. No omitted basis entry,
unstated generator, replacement basis, or graph-embedding theorem is assumed.
-/

noncomputable section

namespace AppendixATutorialPolynomial

abbrev Variable := (Fin 5 × Fin 3) ⊕ Fin 5
abbrev Polynomial := MvPolynomial Variable ℚ

def alpha (i : Fin 5) (j : Fin 3) : Polynomial :=
  MvPolynomial.X (Sum.inl (i, j))

def beta (i : Fin 5) : Polynomial :=
  MvPolynomial.X (Sum.inr i)

/-- The displayed system, in its printed order: 15 + 5 + 3 + 12 + 3 entries. -/
def displayedGenerators : List Polynomial := [
  alpha 0 0 * alpha 0 1, alpha 0 0 * alpha 0 2, alpha 0 1 * alpha 0 2,
  alpha 1 0 * alpha 1 1, alpha 1 0 * alpha 1 2, alpha 1 1 * alpha 1 2,
  alpha 2 0 * alpha 2 1, alpha 2 0 * alpha 2 2, alpha 2 1 * alpha 2 2,
  alpha 3 0 * alpha 3 1, alpha 3 0 * alpha 3 2, alpha 3 1 * alpha 3 2,
  alpha 4 0 * alpha 4 1, alpha 4 0 * alpha 4 2, alpha 4 1 * alpha 4 2,
  alpha 0 0 + alpha 0 1 + alpha 0 2 - beta 0,
  alpha 1 0 + alpha 1 1 + alpha 1 2 - beta 1,
  alpha 2 0 + alpha 2 1 + alpha 2 2 - beta 2,
  alpha 3 0 + alpha 3 1 + alpha 3 2 - beta 3,
  alpha 4 0 + alpha 4 1 + alpha 4 2 - beta 4,
  -1 + alpha 3 0 * alpha 4 1 + alpha 2 0 * alpha 3 1 +
    alpha 0 0 * alpha 1 1 + alpha 2 1 * alpha 3 0 +
    alpha 0 1 * alpha 1 0 + alpha 0 1 * alpha 3 0 +
    alpha 1 1 * alpha 2 0 + alpha 0 0 * alpha 3 1 +
    alpha 1 0 * alpha 2 1 + alpha 3 1 * alpha 4 0,
  -1 + alpha 2 2 * alpha 3 0 + alpha 0 2 * alpha 1 0 +
    alpha 1 2 * alpha 2 0 + alpha 3 0 * alpha 4 2 +
    alpha 0 2 * alpha 3 0 + alpha 0 0 * alpha 1 2 +
    alpha 3 2 * alpha 4 0 + alpha 1 0 * alpha 2 2 +
    alpha 2 0 * alpha 3 2 + alpha 0 0 * alpha 3 2,
  -1 + alpha 2 2 * alpha 3 1 + alpha 0 1 * alpha 1 2 +
    alpha 0 1 * alpha 3 2 + alpha 0 2 * alpha 1 1 +
    alpha 0 2 * alpha 3 1 + alpha 1 2 * alpha 2 1 +
    alpha 1 1 * alpha 2 2 + alpha 3 1 * alpha 4 2 +
    alpha 2 1 * alpha 3 2 + alpha 3 2 * alpha 4 1,
  -alpha 0 0 * alpha 1 0 * alpha 4 0,
  -alpha 0 0 * alpha 2 0 * alpha 4 0,
  -alpha 0 1 * alpha 1 1 * alpha 4 1,
  -alpha 0 1 * alpha 2 1 * alpha 4 1,
  -alpha 0 2 * alpha 1 2 * alpha 4 2,
  -alpha 0 2 * alpha 2 2 * alpha 4 2,
  -alpha 1 0 * alpha 2 0 * alpha 4 0,
  -alpha 1 0 * alpha 3 0 * alpha 4 0,
  -alpha 1 1 * alpha 2 1 * alpha 4 1,
  -alpha 1 1 * alpha 3 1 * alpha 4 1,
  -alpha 1 2 * alpha 2 2 * alpha 4 2,
  -alpha 1 2 * alpha 3 2 * alpha 4 2,
  alpha 1 0 * alpha 4 0,
  alpha 1 1 * alpha 4 1,
  alpha 1 2 * alpha 4 2]

/-- A separately named augmentation; these are not silently inserted into the displayed system. -/
def booleanGenerators : List Polynomial := [
  alpha 0 0 ^ 2 - alpha 0 0, alpha 0 1 ^ 2 - alpha 0 1,
  alpha 0 2 ^ 2 - alpha 0 2,
  alpha 1 0 ^ 2 - alpha 1 0, alpha 1 1 ^ 2 - alpha 1 1,
  alpha 1 2 ^ 2 - alpha 1 2,
  alpha 2 0 ^ 2 - alpha 2 0, alpha 2 1 ^ 2 - alpha 2 1,
  alpha 2 2 ^ 2 - alpha 2 2,
  alpha 3 0 ^ 2 - alpha 3 0, alpha 3 1 ^ 2 - alpha 3 1,
  alpha 3 2 ^ 2 - alpha 3 2,
  alpha 4 0 ^ 2 - alpha 4 0, alpha 4 1 ^ 2 - alpha 4 1,
  alpha 4 2 ^ 2 - alpha 4 2,
  beta 0 ^ 2 - beta 0, beta 1 ^ 2 - beta 1, beta 2 ^ 2 - beta 2,
  beta 3 ^ 2 - beta 3, beta 4 ^ 2 - beta 4]

def displayedSet : Set Polynomial := {p | p ∈ displayedGenerators}
def booleanSet : Set Polynomial := {p | p ∈ booleanGenerators}
def augmentedSet : Set Polynomial := displayedSet ∪ booleanSet

/-- The literal final printed polynomial, including all signs and the beta_5 terms. -/
def printedPolynomial : Polynomial :=
  -alpha 1 1 * alpha 4 2 - alpha 2 1 * alpha 4 2 +
  alpha 0 1 * beta 4 + alpha 1 1 * beta 4 +
  alpha 2 1 * beta 4 + alpha 2 2 * beta 4 +
  alpha 4 1 + alpha 4 2 - beta 4

/-- Source coordinates alpha12=alpha22=alpha33=alpha41=alpha51=1; every beta=1. -/
def point : Variable → ℚ
  | Sum.inl (i, j) =>
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 2) ∨
        (i = 3 ∧ j = 0) ∨ (i = 4 ∧ j = 0) then 1 else 0
  | Sum.inr _ => 1

def evaluation : Polynomial →+* ℚ := MvPolynomial.eval point

theorem displayed_length : displayedGenerators.length = 38 := rfl

theorem boolean_length : booleanGenerators.length = 20 := rfl

theorem point_binary (v : Variable) : point v = 0 ∨ point v = 1 := by
  rcases v with ⟨i, j⟩ | i
  · simp only [point]
    split_ifs <;> norm_num
  · norm_num [point]

theorem displayed_vanish : ∀ p ∈ displayedGenerators, evaluation p = 0 := by
  have ha00 : evaluation (alpha 0 0) = 0 := by
    calc evaluation (alpha 0 0) = point (Sum.inl (0, 0)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha01 : evaluation (alpha 0 1) = 1 := by
    calc evaluation (alpha 0 1) = point (Sum.inl (0, 1)) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have ha02 : evaluation (alpha 0 2) = 0 := by
    calc evaluation (alpha 0 2) = point (Sum.inl (0, 2)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha10 : evaluation (alpha 1 0) = 0 := by
    calc evaluation (alpha 1 0) = point (Sum.inl (1, 0)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha11 : evaluation (alpha 1 1) = 1 := by
    calc evaluation (alpha 1 1) = point (Sum.inl (1, 1)) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have ha12 : evaluation (alpha 1 2) = 0 := by
    calc evaluation (alpha 1 2) = point (Sum.inl (1, 2)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha20 : evaluation (alpha 2 0) = 0 := by
    calc evaluation (alpha 2 0) = point (Sum.inl (2, 0)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha21 : evaluation (alpha 2 1) = 0 := by
    calc evaluation (alpha 2 1) = point (Sum.inl (2, 1)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha22 : evaluation (alpha 2 2) = 1 := by
    calc evaluation (alpha 2 2) = point (Sum.inl (2, 2)) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have ha30 : evaluation (alpha 3 0) = 1 := by
    calc evaluation (alpha 3 0) = point (Sum.inl (3, 0)) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have ha31 : evaluation (alpha 3 1) = 0 := by
    calc evaluation (alpha 3 1) = point (Sum.inl (3, 1)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha32 : evaluation (alpha 3 2) = 0 := by
    calc evaluation (alpha 3 2) = point (Sum.inl (3, 2)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha40 : evaluation (alpha 4 0) = 1 := by
    calc evaluation (alpha 4 0) = point (Sum.inl (4, 0)) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have ha41 : evaluation (alpha 4 1) = 0 := by
    calc evaluation (alpha 4 1) = point (Sum.inl (4, 1)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha42 : evaluation (alpha 4 2) = 0 := by
    calc evaluation (alpha 4 2) = point (Sum.inl (4, 2)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have hb0 : evaluation (beta 0) = 1 := by
    calc evaluation (beta 0) = point (Sum.inr 0) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have hb1 : evaluation (beta 1) = 1 := by
    calc evaluation (beta 1) = point (Sum.inr 1) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have hb2 : evaluation (beta 2) = 1 := by
    calc evaluation (beta 2) = point (Sum.inr 2) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have hb3 : evaluation (beta 3) = 1 := by
    calc evaluation (beta 3) = point (Sum.inr 3) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have hb4 : evaluation (beta 4) = 1 := by
    calc evaluation (beta 4) = point (Sum.inr 4) := MvPolynomial.eval_X _
         _ = 1 := rfl
  norm_num [displayedGenerators, List.forall_mem_cons, ha00, ha01, ha02, ha10, ha11, ha12, ha20, ha21, ha22, ha30, ha31, ha32, ha40, ha41, ha42, hb0, hb1, hb2, hb3, hb4]

theorem boolean_vanish : ∀ p ∈ booleanGenerators, evaluation p = 0 := by
  norm_num [booleanGenerators, List.forall_mem_cons, evaluation, alpha, beta, point]

theorem printed_value : evaluation printedPolynomial = 2 := by
  have ha11 : evaluation (alpha 1 1) = 1 := by
    calc evaluation (alpha 1 1) = point (Sum.inl (1, 1)) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have ha42 : evaluation (alpha 4 2) = 0 := by
    calc evaluation (alpha 4 2) = point (Sum.inl (4, 2)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha21 : evaluation (alpha 2 1) = 0 := by
    calc evaluation (alpha 2 1) = point (Sum.inl (2, 1)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have ha01 : evaluation (alpha 0 1) = 1 := by
    calc evaluation (alpha 0 1) = point (Sum.inl (0, 1)) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have ha22 : evaluation (alpha 2 2) = 1 := by
    calc evaluation (alpha 2 2) = point (Sum.inl (2, 2)) := MvPolynomial.eval_X _
         _ = 1 := rfl
  have ha41 : evaluation (alpha 4 1) = 0 := by
    calc evaluation (alpha 4 1) = point (Sum.inl (4, 1)) := MvPolynomial.eval_X _
         _ = 0 := rfl
  have hb4 : evaluation (beta 4) = 1 := by
    calc evaluation (beta 4) = point (Sum.inr 4) := MvPolynomial.eval_X _
         _ = 1 := rfl
  norm_num [printedPolynomial, ha11, ha42, ha21, ha01, ha22, ha41, hb4]

theorem displayed_span_le_kernel :
    Ideal.span displayedSet ≤ RingHom.ker evaluation := by
  apply Ideal.span_le.mpr
  intro p hp
  exact RingHom.mem_ker.mpr (displayed_vanish p hp)

theorem augmented_span_le_kernel :
    Ideal.span augmentedSet ≤ RingHom.ker evaluation := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with hp | hp
  · exact RingHom.mem_ker.mpr (displayed_vanish p hp)
  · exact RingHom.mem_ker.mpr (boolean_vanish p hp)

theorem printed_not_mem_displayed :
    printedPolynomial ∉ Ideal.span displayedSet := by
  intro hp
  have hzero : evaluation printedPolynomial = 0 :=
    RingHom.mem_ker.mp (displayed_span_le_kernel hp)
  rw [printed_value] at hzero
  norm_num at hzero

theorem printed_not_mem_augmented :
    printedPolynomial ∉ Ideal.span augmentedSet := by
  intro hp
  have hzero : evaluation printedPolynomial = 0 :=
    RingHom.mem_ker.mp (augmented_span_le_kernel hp)
  rw [printed_value] at hzero
  norm_num at hzero

/-- One bounded result: failure of ideal membership for both explicitly specified systems. -/
theorem displayed_basis_member_countercertificate :
    printedPolynomial ∉ Ideal.span displayedSet ∧
      printedPolynomial ∉ Ideal.span augmentedSet :=
  ⟨printed_not_mem_displayed, printed_not_mem_augmented⟩

end AppendixATutorialPolynomial
