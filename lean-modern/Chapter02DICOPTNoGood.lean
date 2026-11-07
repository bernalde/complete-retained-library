module

public import Mathlib.Tactic
public import Mathlib.Data.Finset.Card

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter02.DICOPT

/-- Literal source no-good inequality, written on the real casts of binary
assignments. The two signed sums and cardinality offset are preserved. -/
theorem binary_no_good_formula_iff {m : ℕ} (b z : Fin m → Bool) :
    (∑ i, if b i then (if z i then (1 : ℝ) else 0) else 0) -
      (∑ i, if b i then (0 : ℝ) else (if z i then 1 else 0)) -
      ((∑ i, if b i then (1 : ℝ) else 0) - 1) ≤ 0 ↔ z ≠ b := by
  classical
  have hid :
      (∑ i, if b i then (if z i then (1 : ℝ) else 0) else 0) -
        (∑ i, if b i then (0 : ℝ) else (if z i then 1 else 0)) -
        ((∑ i, if b i then (1 : ℝ) else 0) - 1) =
        1 - ∑ i, if z i = b i then (0 : ℝ) else 1 := by
    have hsum :
        (∑ i, if b i then (if z i then (1 : ℝ) else 0) else 0) -
          (∑ i, if b i then (0 : ℝ) else (if z i then 1 else 0)) -
          (∑ i, if b i then (1 : ℝ) else 0) =
          - ∑ i, if z i = b i then (0 : ℝ) else 1 := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      cases hb : b i <;> cases hz : z i <;> simp [hb, hz]
    linarith
  rw [hid]
  constructor
  · intro h heq
    subst z
    simp at h
    linarith
  · intro hne
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ b i := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hsum : (1 : ℝ) ≤ ∑ j, if z j = b j then (0 : ℝ) else 1 := by
      have hle := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) => show (0 : ℝ) ≤ (if z j = b j then 0 else 1) by split <;> norm_num)
        (Finset.mem_univ i)
      simpa [hi] using hle
    linarith

/-- The finite rank used by the actual source procedure. The inserted
assignment is known fresh from the literal no-good row, not from a selector field. -/
theorem binary_remaining_insert_lt {m : ℕ} (seen : Finset (Fin m → Bool))
    (b : Fin m → Bool) (hb : b ∉ seen) :
    (Finset.univ \ insert b seen).card < (Finset.univ \ seen).card := by
  classical
  have heq : Finset.univ \ insert b seen = (Finset.univ \ seen).erase b := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_univ, true_and, not_or]
  rw [heq]
  exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩)

end Chapter02.DICOPT
