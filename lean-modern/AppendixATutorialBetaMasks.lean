module

public import AppendixATutorialPolynomial
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
Proposed exact rational beta projection of the separately specified Boolean
augmentation of the 38 literal tutorial generators. No assertion about the
printed basis, elimination ideal, complex zeros, or graph-model equivalence.

The four finite missing-vertex lemmas use exhaustive Option (Fin 3) cases and
simplification. The only `decide` calls discharge literal list-index bounds.
-/

noncomputable section

namespace AppendixATutorialBetaMasks

open AppendixATutorialPolynomial

def AugZero (v : Variable → ℚ) : Prop :=
  ∀ p ∈ augmentedSet, MvPolynomial.eval v p = 0

@[simp] theorem eval_alpha (v : Variable → ℚ) (i : Fin 5) (j : Fin 3) :
    MvPolynomial.eval v (alpha i j) = v (Sum.inl (i, j)) :=
  MvPolynomial.eval_X _

@[simp] theorem eval_beta (v : Variable → ℚ) (i : Fin 5) :
    MvPolynomial.eval v (beta i) = v (Sum.inr i) :=
  MvPolynomial.eval_X _

theorem coordinate_binary {v : Variable → ℚ} (h : AugZero v) (x : Variable) :
    v x = 0 ∨ v x = 1 := by
  have hm : (MvPolynomial.X x ^ 2 - MvPolynomial.X x : Polynomial) ∈
      booleanGenerators := by
    rcases x with ⟨i, j⟩ | i
    · fin_cases i <;> fin_cases j <;> simp [booleanGenerators, alpha, beta]
    · fin_cases i <;> simp [booleanGenerators, alpha, beta]
  have hz : v x ^ 2 - v x = 0 := by
    simpa using h _ (Or.inr hm)
  have hp : v x * (v x - 1) = 0 := by
    simpa only [mul_sub, mul_one, ← pow_two] using hz
  rcases mul_eq_zero.mp hp with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem row_products {v : Variable → ℚ} (h : AugZero v) (i : Fin 5) :
    v (Sum.inl (i, 0)) * v (Sum.inl (i, 1)) = 0 ∧
    v (Sum.inl (i, 0)) * v (Sum.inl (i, 2)) = 0 ∧
    v (Sum.inl (i, 1)) * v (Sum.inl (i, 2)) = 0 := by
  have h01 := h (alpha i 0 * alpha i 1) (Or.inl (by
    fin_cases i <;> simp [displayedSet, displayedGenerators]))
  have h02 := h (alpha i 0 * alpha i 2) (Or.inl (by
    fin_cases i <;> simp [displayedSet, displayedGenerators]))
  have h12 := h (alpha i 1 * alpha i 2) (Or.inl (by
    fin_cases i <;> simp [displayedSet, displayedGenerators]))
  exact ⟨by simpa using h01, by simpa using h02, by simpa using h12⟩

theorem row_sum {v : Variable → ℚ} (h : AugZero v) (i : Fin 5) :
    v (Sum.inl (i, 0)) + v (Sum.inl (i, 1)) + v (Sum.inl (i, 2)) =
      v (Sum.inr i) := by
  have hp := h (alpha i 0 + alpha i 1 + alpha i 2 - beta i) (Or.inl (by
    fin_cases i <;> simp [displayedSet, displayedGenerators]))
  have hz : v (Sum.inl (i, 0)) + v (Sum.inl (i, 1)) +
      v (Sum.inl (i, 2)) - v (Sum.inr i) = 0 := by simpa using hp
  exact sub_eq_zero.mp hz

theorem row_one_four_product {v : Variable → ℚ} (h : AugZero v) (j : Fin 3) :
    v (Sum.inl (1, j)) * v (Sum.inl (4, j)) = 0 := by
  have hp := h (alpha 1 j * alpha 4 j) (Or.inl (by
    fin_cases j <;> simp [displayedSet, displayedGenerators]))
  simpa using hp

/-- A local three-coordinate decoder; no graph embedding is assumed. -/
def rowLabel (v : Variable → ℚ) (i : Fin 5) : Option (Fin 3) :=
  if v (Sum.inl (i, 0)) = 1 then some 0
  else if v (Sum.inl (i, 1)) = 1 then some 1
  else if v (Sum.inl (i, 2)) = 1 then some 2
  else none

theorem rowLabel_some_iff {v : Variable → ℚ} (h : AugZero v)
    (i : Fin 5) (j : Fin 3) :
    rowLabel v i = some j ↔ v (Sum.inl (i, j)) = 1 := by
  obtain ⟨hp01, hp02, hp12⟩ := row_products h i
  rcases coordinate_binary h (Sum.inl (i, 0)) with h0 | h0 <;>
    rcases coordinate_binary h (Sum.inl (i, 1)) with h1 | h1 <;>
    rcases coordinate_binary h (Sum.inl (i, 2)) with h2 | h2 <;>
    fin_cases j <;> simp_all [rowLabel]

theorem beta_eq_activity {v : Variable → ℚ} (h : AugZero v) (i : Fin 5) :
    v (Sum.inr i) = if (rowLabel v i).isSome then 1 else 0 := by
  obtain ⟨hp01, hp02, hp12⟩ := row_products h i
  have hs := row_sum h i
  rw [← hs]
  clear hs
  rcases coordinate_binary h (Sum.inl (i, 0)) with h0 | h0 <;>
    rcases coordinate_binary h (Sum.inl (i, 1)) with h1 | h1 <;>
    rcases coordinate_binary h (Sum.inl (i, 2)) with h2 | h2 <;>
    simp_all [rowLabel]

def crossTerm (v : Variable → ℚ) (i r : Fin 5) (j k : Fin 3) : ℚ :=
  v (Sum.inl (i, j)) * v (Sum.inl (r, k)) +
    v (Sum.inl (i, k)) * v (Sum.inl (r, j))

/-- Zero-based physical pairs 01,12,23,03,34, each counted once. -/
def crossSum (v : Variable → ℚ) (j k : Fin 3) : ℚ :=
  crossTerm v 0 1 j k + crossTerm v 1 2 j k + crossTerm v 2 3 j k +
    crossTerm v 0 3 j k + crossTerm v 3 4 j k

theorem crossing_sums {v : Variable → ℚ} (h : AugZero v) :
    crossSum v 0 1 = 1 ∧ crossSum v 0 2 = 1 ∧ crossSum v 1 2 = 1 := by
  have h01 := h (displayedGenerators[20]'(by decide)) (Or.inl (by
    simp [displayedSet, displayedGenerators]))
  have h02 := h (displayedGenerators[21]'(by decide)) (Or.inl (by
    simp [displayedSet, displayedGenerators]))
  have h12 := h (displayedGenerators[22]'(by decide)) (Or.inl (by
    simp [displayedSet, displayedGenerators]))
  change MvPolynomial.eval v
    (-1 + alpha 3 0 * alpha 4 1 + alpha 2 0 * alpha 3 1 +
      alpha 0 0 * alpha 1 1 + alpha 2 1 * alpha 3 0 +
      alpha 0 1 * alpha 1 0 + alpha 0 1 * alpha 3 0 +
      alpha 1 1 * alpha 2 0 + alpha 0 0 * alpha 3 1 +
      alpha 1 0 * alpha 2 1 + alpha 3 1 * alpha 4 0) = 0 at h01
  change MvPolynomial.eval v
    (-1 + alpha 2 2 * alpha 3 0 + alpha 0 2 * alpha 1 0 +
      alpha 1 2 * alpha 2 0 + alpha 3 0 * alpha 4 2 +
      alpha 0 2 * alpha 3 0 + alpha 0 0 * alpha 1 2 +
      alpha 3 2 * alpha 4 0 + alpha 1 0 * alpha 2 2 +
      alpha 2 0 * alpha 3 2 + alpha 0 0 * alpha 3 2) = 0 at h02
  change MvPolynomial.eval v
    (-1 + alpha 2 2 * alpha 3 1 + alpha 0 1 * alpha 1 2 +
      alpha 0 1 * alpha 3 2 + alpha 0 2 * alpha 1 1 +
      alpha 0 2 * alpha 3 1 + alpha 1 2 * alpha 2 1 +
      alpha 1 1 * alpha 2 2 + alpha 3 1 * alpha 4 2 +
      alpha 2 1 * alpha 3 2 + alpha 3 2 * alpha 4 1) = 0 at h12
  simp only [map_add, map_mul, map_neg, map_one, eval_alpha] at h01 h02 h12
  refine ⟨?_, ?_, ?_⟩
  · dsimp [crossSum, crossTerm]
    linear_combination h01
  · dsimp [crossSum, crossTerm]
    linear_combination h02
  · dsimp [crossSum, crossTerm]
    linear_combination h12

def Crosses (a b : Option (Fin 3)) (j k : Fin 3) : Prop :=
  (a = some j ∧ b = some k) ∨ (a = some k ∧ b = some j)

def PairCovered (p : Fin 5 → Option (Fin 3)) (j k : Fin 3) : Prop :=
  Crosses (p 0) (p 1) j k ∨ Crosses (p 1) (p 2) j k ∨
    Crosses (p 2) (p 3) j k ∨ Crosses (p 0) (p 3) j k ∨
    Crosses (p 3) (p 4) j k

def ThreeCovered (p : Fin 5 → Option (Fin 3)) : Prop :=
  PairCovered p 0 1 ∧ PairCovered p 0 2 ∧ PairCovered p 1 2

theorem binary_product_zero (a b : ℚ)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hn : ¬ (a = 1 ∧ b = 1)) : a * b = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num at *

theorem crossTerm_zero_of_not_cross {v : Variable → ℚ} (h : AugZero v)
    (i r : Fin 5) (j k : Fin 3)
    (hn : ¬ Crosses (rowLabel v i) (rowLabel v r) j k) :
    crossTerm v i r j k = 0 := by
  have hleft : v (Sum.inl (i, j)) * v (Sum.inl (r, k)) = 0 := by
    apply binary_product_zero _ _ (coordinate_binary h _) (coordinate_binary h _)
    rintro ⟨hi, hr⟩
    exact hn (Or.inl ⟨(rowLabel_some_iff h i j).mpr hi,
      (rowLabel_some_iff h r k).mpr hr⟩)
  have hright : v (Sum.inl (i, k)) * v (Sum.inl (r, j)) = 0 := by
    apply binary_product_zero _ _ (coordinate_binary h _) (coordinate_binary h _)
    rintro ⟨hi, hr⟩
    exact hn (Or.inr ⟨(rowLabel_some_iff h i k).mpr hi,
      (rowLabel_some_iff h r j).mpr hr⟩)
  simp only [crossTerm, hleft, hright, add_zero]

theorem pairCovered_of_sum {v : Variable → ℚ} (h : AugZero v)
    (j k : Fin 3) (hs : crossSum v j k = 1) :
    PairCovered (rowLabel v) j k := by
  by_contra hn
  have h01 : ¬ Crosses (rowLabel v 0) (rowLabel v 1) j k :=
    fun hc => hn (Or.inl hc)
  have h12 : ¬ Crosses (rowLabel v 1) (rowLabel v 2) j k :=
    fun hc => hn (Or.inr (Or.inl hc))
  have h23 : ¬ Crosses (rowLabel v 2) (rowLabel v 3) j k :=
    fun hc => hn (Or.inr (Or.inr (Or.inl hc)))
  have h03 : ¬ Crosses (rowLabel v 0) (rowLabel v 3) j k :=
    fun hc => hn (Or.inr (Or.inr (Or.inr (Or.inl hc))))
  have h34 : ¬ Crosses (rowLabel v 3) (rowLabel v 4) j k :=
    fun hc => hn (Or.inr (Or.inr (Or.inr (Or.inr hc))))
  have hz : crossSum v j k = 0 := by
    simp only [crossSum, crossTerm_zero_of_not_cross h 0 1 j k h01,
      crossTerm_zero_of_not_cross h 1 2 j k h12,
      crossTerm_zero_of_not_cross h 2 3 j k h23,
      crossTerm_zero_of_not_cross h 0 3 j k h03,
      crossTerm_zero_of_not_cross h 3 4 j k h34, add_zero]
  rw [hz] at hs
  norm_num at hs

theorem threeCovered_of_zero {v : Variable → ℚ} (h : AugZero v) :
    ThreeCovered (rowLabel v) := by
  obtain ⟨h01, h02, h12⟩ := crossing_sums h
  exact ⟨pairCovered_of_sum h 0 1 h01, pairCovered_of_sum h 0 2 h02,
    pairCovered_of_sum h 1 2 h12⟩

def labels (a b c d e : Option (Fin 3)) : Fin 5 → Option (Fin 3) :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c
    else if i = 3 then d else e

theorem labels_eta (p : Fin 5 → Option (Fin 3)) :
    labels (p 0) (p 1) (p 2) (p 3) (p 4) = p := by
  funext i
  fin_cases i <;> rfl

/- These closed lemmas have four Option(Fin 3) inputs each. They express the
two paths, star and two-edge obstruction after one fixed vertex is absent.
They neither enumerate rational assignments nor assert an embedding count. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem missing_zero_path :
    ∀ b c d e : Option (Fin 3), ThreeCovered (labels none b c d e) →
      ∃ j : Fin 3, b = some j ∧ e = some j := by
  have cases_label : ∀ q : Option (Fin 3),
      q = none ∨ q = some 0 ∨ q = some 1 ∨ q = some 2 := by
    intro q
    cases q with
    | none => exact Or.inl rfl
    | some j => fin_cases j <;> simp
  intro b c d e
  rcases cases_label b with rfl | rfl | rfl | rfl <;>
  rcases cases_label c with rfl | rfl | rfl | rfl <;>
  rcases cases_label d with rfl | rfl | rfl | rfl <;>
  rcases cases_label e with rfl | rfl | rfl | rfl <;>
    simp [ThreeCovered, PairCovered, Crosses, labels]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem missing_one_star :
    ∀ a c d e : Option (Fin 3), ¬ ThreeCovered (labels a none c d e) := by
  have cases_label : ∀ q : Option (Fin 3),
      q = none ∨ q = some 0 ∨ q = some 1 ∨ q = some 2 := by
    intro q
    cases q with
    | none => exact Or.inl rfl
    | some j => fin_cases j <;> simp
  intro a c d e
  rcases cases_label a with rfl | rfl | rfl | rfl <;>
  rcases cases_label c with rfl | rfl | rfl | rfl <;>
  rcases cases_label d with rfl | rfl | rfl | rfl <;>
  rcases cases_label e with rfl | rfl | rfl | rfl <;>
    simp [ThreeCovered, PairCovered, Crosses, labels]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem missing_two_path :
    ∀ a b d e : Option (Fin 3), ThreeCovered (labels a b none d e) →
      ∃ j : Fin 3, b = some j ∧ e = some j := by
  have cases_label : ∀ q : Option (Fin 3),
      q = none ∨ q = some 0 ∨ q = some 1 ∨ q = some 2 := by
    intro q
    cases q with
    | none => exact Or.inl rfl
    | some j => fin_cases j <;> simp
  intro a b d e
  rcases cases_label a with rfl | rfl | rfl | rfl <;>
  rcases cases_label b with rfl | rfl | rfl | rfl <;>
  rcases cases_label d with rfl | rfl | rfl | rfl <;>
  rcases cases_label e with rfl | rfl | rfl | rfl <;>
    simp [ThreeCovered, PairCovered, Crosses, labels]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem missing_three_two_edges :
    ∀ a b c e : Option (Fin 3), ¬ ThreeCovered (labels a b c none e) := by
  have cases_label : ∀ q : Option (Fin 3),
      q = none ∨ q = some 0 ∨ q = some 1 ∨ q = some 2 := by
    intro q
    cases q with
    | none => exact Or.inl rfl
    | some j => fin_cases j <;> simp
  intro a b c e
  rcases cases_label a with rfl | rfl | rfl | rfl <;>
  rcases cases_label b with rfl | rfl | rfl | rfl <;>
  rcases cases_label c with rfl | rfl | rfl | rfl <;>
  rcases cases_label e with rfl | rfl | rfl | rfl <;>
    simp [ThreeCovered, PairCovered, Crosses, labels]

theorem one_four_labels_differ {v : Variable → ℚ} (h : AugZero v) (j : Fin 3) :
    ¬ (rowLabel v 1 = some j ∧ rowLabel v 4 = some j) := by
  rintro ⟨h1, h4⟩
  have ha1 := (rowLabel_some_iff h 1 j).mp h1
  have ha4 := (rowLabel_some_iff h 4 j).mp h4
  have hp := row_one_four_product h j
  norm_num [ha1, ha4] at hp

theorem cycle_labels_active {v : Variable → ℚ} (h : AugZero v) (i : Fin 4) :
    (rowLabel v i.castSucc).isSome = true := by
  let p := rowLabel v
  have hc : ThreeCovered (labels (p 0) (p 1) (p 2) (p 3) (p 4)) := by
    simpa only [labels_eta] using threeCovered_of_zero h
  have hn0 : p 0 ≠ none := by
    intro hp
    obtain ⟨j, h1, h4⟩ := missing_zero_path (p 1) (p 2) (p 3) (p 4)
      (by simpa only [hp] using hc)
    exact one_four_labels_differ h j ⟨h1, h4⟩
  have hn1 : p 1 ≠ none := by
    intro hp
    exact missing_one_star (p 0) (p 2) (p 3) (p 4) (by simpa only [hp] using hc)
  have hn2 : p 2 ≠ none := by
    intro hp
    obtain ⟨j, h1, h4⟩ := missing_two_path (p 0) (p 1) (p 3) (p 4)
      (by simpa only [hp] using hc)
    exact one_four_labels_differ h j ⟨h1, h4⟩
  have hn3 : p 3 ≠ none := by
    intro hp
    exact missing_three_two_edges (p 0) (p 1) (p 2) (p 4)
      (by simpa only [hp] using hc)
  have hs : ∀ q : Option (Fin 3), q ≠ none → q.isSome = true := by
    intro q hq
    cases q <;> simp_all
  fin_cases i
  · exact hs (p 0) hn0
  · exact hs (p 1) hn1
  · exact hs (p 2) hn2
  · exact hs (p 3) hn3

theorem cycle_beta_one {v : Variable → ℚ} (h : AugZero v) (i : Fin 4) :
    v (Sum.inr i.castSucc) = 1 := by
  rw [beta_eq_activity h i.castSucc, cycle_labels_active h i]
  rfl

/-- Source-indexed alpha12=alpha22=alpha33=alpha41=1, alpha51=t. -/
def parameterPoint (t : ℚ) : Variable → ℚ
  | Sum.inl (i, j) =>
      if i = 4 ∧ j = 0 then t
      else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1) ∨
        (i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 0) then 1 else 0
  | Sum.inr i => if i = 4 then t else 1

theorem parameter_displayed_vanish (t : ℚ) :
    ∀ p ∈ displayedGenerators, MvPolynomial.eval (parameterPoint t) p = 0 := by
  have ha00 : MvPolynomial.eval (parameterPoint t) (alpha 0 0) = 0 := by
    rw [eval_alpha]
    rfl
  have ha01 : MvPolynomial.eval (parameterPoint t) (alpha 0 1) = 1 := by
    rw [eval_alpha]
    rfl
  have ha02 : MvPolynomial.eval (parameterPoint t) (alpha 0 2) = 0 := by
    rw [eval_alpha]
    rfl
  have ha10 : MvPolynomial.eval (parameterPoint t) (alpha 1 0) = 0 := by
    rw [eval_alpha]
    rfl
  have ha11 : MvPolynomial.eval (parameterPoint t) (alpha 1 1) = 1 := by
    rw [eval_alpha]
    rfl
  have ha12 : MvPolynomial.eval (parameterPoint t) (alpha 1 2) = 0 := by
    rw [eval_alpha]
    rfl
  have ha20 : MvPolynomial.eval (parameterPoint t) (alpha 2 0) = 0 := by
    rw [eval_alpha]
    rfl
  have ha21 : MvPolynomial.eval (parameterPoint t) (alpha 2 1) = 0 := by
    rw [eval_alpha]
    rfl
  have ha22 : MvPolynomial.eval (parameterPoint t) (alpha 2 2) = 1 := by
    rw [eval_alpha]
    rfl
  have ha30 : MvPolynomial.eval (parameterPoint t) (alpha 3 0) = 1 := by
    rw [eval_alpha]
    rfl
  have ha31 : MvPolynomial.eval (parameterPoint t) (alpha 3 1) = 0 := by
    rw [eval_alpha]
    rfl
  have ha32 : MvPolynomial.eval (parameterPoint t) (alpha 3 2) = 0 := by
    rw [eval_alpha]
    rfl
  have ha40 : MvPolynomial.eval (parameterPoint t) (alpha 4 0) = t := by
    rw [eval_alpha]
    rfl
  have ha41 : MvPolynomial.eval (parameterPoint t) (alpha 4 1) = 0 := by
    rw [eval_alpha]
    rfl
  have ha42 : MvPolynomial.eval (parameterPoint t) (alpha 4 2) = 0 := by
    rw [eval_alpha]
    rfl
  have hb0 : MvPolynomial.eval (parameterPoint t) (beta 0) = 1 := by
    rw [eval_beta]
    rfl
  have hb1 : MvPolynomial.eval (parameterPoint t) (beta 1) = 1 := by
    rw [eval_beta]
    rfl
  have hb2 : MvPolynomial.eval (parameterPoint t) (beta 2) = 1 := by
    rw [eval_beta]
    rfl
  have hb3 : MvPolynomial.eval (parameterPoint t) (beta 3) = 1 := by
    rw [eval_beta]
    rfl
  have hb4 : MvPolynomial.eval (parameterPoint t) (beta 4) = t := by
    rw [eval_beta]
    rfl
  norm_num [displayedGenerators, List.forall_mem_cons, ha00, ha01, ha02, ha10, ha11, ha12, ha20, ha21, ha22, ha30, ha31, ha32, ha40, ha41, ha42, hb0, hb1, hb2, hb3, hb4]

theorem parameter_boolean_vanish (t : ℚ) (ht : t = 0 ∨ t = 1) :
    ∀ p ∈ booleanGenerators, MvPolynomial.eval (parameterPoint t) p = 0 := by
  have hv (x : Variable) : parameterPoint t x = 0 ∨ parameterPoint t x = 1 := by
    rcases x with ⟨i, j⟩ | i
    · simp only [parameterPoint]
      split_ifs <;> first | exact ht | norm_num
    · simp only [parameterPoint]
      split_ifs <;> first | exact ht | norm_num
  have hx (x : Variable) : parameterPoint t x ^ 2 - parameterPoint t x = 0 := by
    rcases hv x with hval | hval <;> norm_num [hval]
  simp [booleanGenerators, List.forall_mem_cons, alpha, beta, hx]

theorem parameter_augmented_iff (t : ℚ) :
    AugZero (parameterPoint t) ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    simpa [parameterPoint] using coordinate_binary h (Sum.inr 4)
  · intro ht p hp
    rcases hp with hp | hp
    · exact parameter_displayed_vanish t p hp
    · exact parameter_boolean_vanish t ht p hp

theorem parameter_one_eq_point : parameterPoint 1 = point := by
  funext x
  rcases x with ⟨i, j⟩ | i
  · fin_cases i <;> fin_cases j <;> rfl
  · fin_cases i <;> rfl

theorem zero_mask_witness :
    AugZero (parameterPoint 0) ∧
      (∀ i : Fin 4, parameterPoint 0 (Sum.inr i.castSucc) = 1) ∧
      parameterPoint 0 (Sum.inr 4) = 0 := by
  refine ⟨(parameter_augmented_iff 0).mpr (Or.inl rfl), ?_, rfl⟩
  intro i
  fin_cases i <;> rfl

theorem one_mask_witness :
    AugZero (parameterPoint 1) ∧
      (∀ i : Fin 4, parameterPoint 1 (Sum.inr i.castSucc) = 1) ∧
      parameterPoint 1 (Sum.inr 4) = 1 := by
  refine ⟨(parameter_augmented_iff 1).mpr (Or.inr rfl), ?_, rfl⟩
  intro i
  fin_cases i <;> rfl

/-- Literal-system qualification control, not a refutation of intended binary masks. -/
theorem half_parameter_control :
    (∀ p ∈ displayedGenerators,
      MvPolynomial.eval (parameterPoint (1 / 2)) p = 0) ∧
    ¬ AugZero (parameterPoint (1 / 2)) ∧
    parameterPoint (1 / 2) (Sum.inr 4) = (1 / 2 : ℚ) := by
  refine ⟨parameter_displayed_vanish (1 / 2), ?_, rfl⟩
  rw [parameter_augmented_iff]
  norm_num

/-- One projected-zero-set family for the explicitly augmented rational system. -/
theorem augmented_beta_projection (b : Fin 5 → ℚ) :
    (∃ v : Variable → ℚ, AugZero v ∧ ∀ i, v (Sum.inr i) = b i) ↔
      ((∀ i : Fin 4, b i.castSucc = 1) ∧ (b 4 = 0 ∨ b 4 = 1)) := by
  constructor
  · rintro ⟨v, hv, hb⟩
    constructor
    · intro i
      rw [← hb i.castSucc]
      exact cycle_beta_one hv i
    · rw [← hb 4]
      exact coordinate_binary hv (Sum.inr 4)
  · rintro ⟨hfirst, hlast⟩
    refine ⟨parameterPoint (b 4), (parameter_augmented_iff (b 4)).mpr hlast, ?_⟩
    intro i
    fin_cases i
    · exact (hfirst 0).symm
    · exact (hfirst 1).symm
    · exact (hfirst 2).symm
    · exact (hfirst 3).symm
    · rfl

end AppendixATutorialBetaMasks
