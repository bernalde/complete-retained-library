module

public import Chapter08

@[expose] public section

/-! Exact Boolean clauses and their real binary encodings for Chapter 8.
No geometric projection is used to discard the selector assignment. -/
noncomputable section
open scoped BigOperators

namespace Chapter08.GDP

def bit (b : Bool) : ℝ := if b then 1 else 0

def decode (y : ℝ) : Bool := decide (y = 1)

theorem bit_binary (b : Bool) : bit b = 0 ∨ bit b = 1 := by
  cases b <;> simp [bit]

theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by
  cases b <;> norm_num [bit]

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by
  cases b <;> norm_num [bit]

theorem bit_eq_one_iff (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

theorem bit_eq_zero_iff (b : Bool) : bit b = 0 ↔ b = false := by
  cases b <;> simp [bit]

theorem bit_decode (y : ℝ) (hy : y = 0 ∨ y = 1) : bit (decode y) = y := by
  rcases hy with rfl | rfl <;> norm_num [bit, decode]

theorem decode_bit (b : Bool) : decode (bit b) = b := by
  cases b <;> simp [bit, decode]

structure Clause (ι : Type*) where
  positive : Finset ι
  negative : Finset ι

def Clause.Holds {ι : Type*} (c : Clause ι) (Y : ι → Bool) : Prop :=
  (∃ i ∈ c.positive, Y i = true) ∨ (∃ i ∈ c.negative, Y i = false)

def Clause.Linear {ι : Type*} (c : Clause ι) (y : ι → ℝ) : Prop :=
  1 ≤ (∑ i ∈ c.positive, y i) + ∑ i ∈ c.negative, (1 - y i)

theorem clause_encoding {ι : Type*} (c : Clause ι) (Y : ι → Bool) :
    c.Holds Y ↔ c.Linear (fun i => bit (Y i)) := by
  classical
  have hp : 0 ≤ ∑ i ∈ c.positive, bit (Y i) :=
    Finset.sum_nonneg fun i _ => bit_nonneg (Y i)
  have hn : 0 ≤ ∑ i ∈ c.negative, (1 - bit (Y i)) :=
    Finset.sum_nonneg fun i _ => sub_nonneg.mpr (bit_le_one (Y i))
  constructor
  · intro h
    rcases h with ⟨i, hi, hY⟩ | ⟨i, hi, hY⟩
    · have hsum := Finset.single_le_sum (fun j (_ : j ∈ c.positive) =>
        bit_nonneg (Y j)) hi
      have hb : bit (Y i) = 1 := by simp [hY, bit]
      dsimp [Clause.Linear]
      linarith
    · have hsum := Finset.single_le_sum (fun j (_ : j ∈ c.negative) =>
        sub_nonneg.mpr (bit_le_one (Y j))) hi
      have hb : bit (Y i) = 0 := by simp [hY, bit]
      dsimp [Clause.Linear]
      linarith
  · intro h
    by_contra hfalse
    have hpos : ∀ i ∈ c.positive, Y i = false := by
      intro i hi
      cases hY : Y i with
      | false => rfl
      | true => exact False.elim (hfalse (Or.inl ⟨i, hi, hY⟩))
    have hneg : ∀ i ∈ c.negative, Y i = true := by
      intro i hi
      cases hY : Y i with
      | true => rfl
      | false => exact False.elim (hfalse (Or.inr ⟨i, hi, hY⟩))
    have hp0 : (∑ i ∈ c.positive, bit (Y i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hpos i hi, bit]
    have hn0 : (∑ i ∈ c.negative, (1 - bit (Y i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hneg i hi, bit]
    norm_num [Clause.Linear, hp0, hn0] at h

def CNF {ι κ : Type*} (clauses : κ → Clause ι) (Y : ι → Bool) : Prop :=
  ∀ k, (clauses k).Holds Y

def LinearCNF {ι κ : Type*} (clauses : κ → Clause ι) (y : ι → ℝ) : Prop :=
  ∀ k, (clauses k).Linear y

theorem cnf_encoding {ι κ : Type*} (clauses : κ → Clause ι) (Y : ι → Bool) :
    CNF clauses Y ↔ LinearCNF clauses (fun i => bit (Y i)) := by
  constructor
  · intro h k
    exact (clause_encoding (clauses k) Y).mp (h k)
  · intro h k
    exact (clause_encoding (clauses k) Y).mpr (h k)

theorem cnf_decoding {ι κ : Type*} (clauses : κ → Clause ι) (y : ι → ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) :
    CNF clauses (fun i => decode (y i)) ↔ LinearCNF clauses y := by
  have heq : (fun i => bit (decode (y i))) = y := by
    funext i
    exact bit_decode (y i) (hy i)
  rw [cnf_encoding, heq]

def OneHot {ι : Type*} (Y : ι → Bool) : Prop := ∃! i, Y i = true

theorem binary_sum_one_hot {ι : Type*} [Fintype ι] (y : ι → ℝ)
    (hb : ∀ i, y i = 0 ∨ y i = 1) (hs : (∑ i, y i) = 1) :
    ∃ i, y i = 1 ∧ ∀ j, j ≠ i → y j = 0 := by
  classical
  have hn : ∃ i, y i ≠ 0 := by
    by_contra h
    have hz : ∀ i, y i = 0 := by simpa using h
    simp [hz] at hs
  obtain ⟨i, hi⟩ := hn
  have hi1 : y i = 1 := (hb i).resolve_left hi
  refine ⟨i, hi1, ?_⟩
  intro j hji
  rcases hb j with hj | hj
  · exact hj
  · have hnonneg : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ y k := by
      intro k _
      rcases hb k with hk | hk <;> simp [hk]
    have htwo : y i + y j ≤ ∑ k, y k := by
      have hsub : ({i,j} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
      have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro k _ _
        exact hnonneg k (Finset.mem_univ k))
      simpa [Finset.sum_pair (Ne.symm hji)] using h
    rw [hi1, hj, hs] at htwo
    norm_num at htwo

theorem one_hot_encoding {ι : Type*} [Fintype ι] (Y : ι → Bool) :
    OneHot Y ↔ (∑ i, bit (Y i)) = 1 := by
  classical
  constructor
  · rintro ⟨i, hi, hu⟩
    have hz : ∀ j, j ≠ i → bit (Y j) = 0 := by
      intro j hji
      cases hY : Y j with
      | false => simp [hY, bit]
      | true => exact False.elim (hji (hu j hY))
    calc
      (∑ j, bit (Y j)) = bit (Y i) := Finset.sum_eq_single i
        (by intro j _ hji; exact hz j hji)
        (by intro h; exact False.elim (h (Finset.mem_univ i)))
      _ = 1 := by simp [hi, bit]
  · intro hs
    obtain ⟨i, hi, hz⟩ := binary_sum_one_hot (fun i => bit (Y i))
      (fun i => bit_binary (Y i)) hs
    refine ⟨i, (bit_eq_one_iff _).mp hi, ?_⟩
    intro j hj
    by_contra hji
    have h0 := hz j hji
    simp [hj, bit] at h0

theorem one_hot_decoding {ι : Type*} [Fintype ι] (y : ι → ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) :
    OneHot (fun i => decode (y i)) ↔ (∑ i, y i) = 1 := by
  rw [one_hot_encoding]
  simp only [bit_decode _ (hy _)]

theorem empty_clause_false {ι : Type*} (Y : ι → Bool) :
    ¬(Clause.mk (∅ : Finset ι) ∅).Holds Y := by
  simp [Clause.Holds]

theorem empty_cnf_true {ι : Type*} (clauses : Empty → Clause ι) (Y : ι → Bool) :
    CNF clauses Y := by
  intro k
  exact Empty.elim k

theorem empty_disjunction_infeasible (Y : Empty → Bool) : ¬OneHot Y := by
  rintro ⟨i, _, _⟩
  exact Empty.elim i

#print axioms bit_binary
#print axioms bit_nonneg
#print axioms bit_le_one
#print axioms bit_eq_one_iff
#print axioms bit_eq_zero_iff
#print axioms bit_decode
#print axioms decode_bit
#print axioms clause_encoding
#print axioms cnf_encoding
#print axioms cnf_decoding
#print axioms binary_sum_one_hot
#print axioms one_hot_encoding
#print axioms one_hot_decoding
#print axioms empty_clause_false
#print axioms empty_cnf_true
#print axioms empty_disjunction_infeasible

end Chapter08.GDP
