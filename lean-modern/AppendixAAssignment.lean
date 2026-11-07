module

public import AppendixAModel

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AppendixATheory

def Exclusive {n m : ℕ} (A : Alpha n m) : Prop :=
  ∀ i j l, A i j = true → A i l = true → j = l

theorem row_card_iff_exclusive {n m : ℕ} (A : Alpha n m) :
    (∀ i, (Finset.univ.filter (fun j => A i j = true)).card ≤ 1) ↔ Exclusive A := by
  simp only [Finset.card_le_one, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h i j l hj hl => h i j hj l hl, fun h i j hj l hl => h i j l hj hl⟩

theorem exclusive_iff_disjoint {n m : ℕ} (A : Alpha n m) :
    Exclusive A ↔ ∀ j l, j ≠ l → Disjoint (fiber A j) (fiber A l) := by
  constructor
  · intro h j l hne
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hne (h i j l ((mem_fiber A i j).mp hi) ((mem_fiber A i l).mp hj))
  · intro h i j l hj hl
    by_contra hne
    exact Finset.disjoint_left.mp (h j l hne) ((mem_fiber A i j).mpr hj)
      ((mem_fiber A i l).mpr hl)

def alphaOfAssignment {n m : ℕ} (p : Fin n → Option (Fin m)) : Alpha n m :=
  fun i j => decide (p i = some j)

theorem assignment_exclusive {n m : ℕ} (p : Fin n → Option (Fin m)) :
    Exclusive (alphaOfAssignment p) := by
  intro i j l hj hl
  simp only [alphaOfAssignment, decide_eq_true_eq] at hj hl
  exact Option.some.inj (hj.symm.trans hl)

def assignmentOfAlpha {n m : ℕ} (A : Alpha n m) : Fin n → Option (Fin m) :=
  fun i => if h : ∃ j, A i j = true then some (Classical.choose h) else none

theorem assignmentOfAlpha_some_iff {n m : ℕ} (A : Alpha n m) (h : Exclusive A)
    (i : Fin n) (j : Fin m) : assignmentOfAlpha A i = some j ↔ A i j = true := by
  classical
  unfold assignmentOfAlpha
  split_ifs with hex
  · constructor
    · intro heq
      have he := Option.some.inj heq
      simpa [he] using Classical.choose_spec hex
    · intro hj
      congr 1
      exact h i _ j (Classical.choose_spec hex) hj
  · simp only [Option.noConfusion, false_iff]
    exact fun hj => hex ⟨j, hj⟩

theorem alpha_assignment_roundtrip {n m : ℕ} (A : Alpha n m) (h : Exclusive A) :
    alphaOfAssignment (assignmentOfAlpha A) = A := by
  funext i j
  apply Bool.eq_iff_iff.mpr
  simp only [alphaOfAssignment, decide_eq_true_eq]
  exact assignmentOfAlpha_some_iff A h i j

theorem assignment_alpha_roundtrip {n m : ℕ} (p : Fin n → Option (Fin m)) :
    assignmentOfAlpha (alphaOfAssignment p) = p := by
  funext i
  cases hp : p i with
  | none =>
    simp [assignmentOfAlpha, alphaOfAssignment, hp]
  | some j =>
    exact (assignmentOfAlpha_some_iff _ (assignment_exclusive p) i j).mpr
      (by simp [alphaOfAssignment, hp])

theorem exists_partial_assignment_iff {n m : ℕ} (A : Alpha n m) :
    (∃ p, alphaOfAssignment p = A) ↔ Exclusive A := by
  constructor
  · rintro ⟨p, rfl⟩; exact assignment_exclusive p
  · intro h; exact ⟨assignmentOfAlpha A, alpha_assignment_roundtrip A h⟩

def BranchModel {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (F : Fin m → Finset (Fin n)) : Prop :=
  (∀ j, (F j).Nonempty ∧ (F j).card ≤ k ∧ AppendixA.connected E (F j)) ∧
  (∀ j l, j ≠ l → Disjoint (F j) (F l)) ∧
  ∀ j l, AppendixA.adjacent L j l →
    ∃ a ∈ F j, ∃ b ∈ F l, AppendixA.adjacent E a b

theorem embedding_iff_branchModel {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) :
    Embedding E L k A ↔ BranchModel E L k (fiber A) := by
  constructor
  · intro h
    exact ⟨fun j => ⟨(h.1.2 j).1, (h.1.2 j).2, h.2.2 j⟩,
      (exclusive_iff_disjoint A).mp ((row_card_iff_exclusive A).mp h.1.1), h.2.1⟩
  · intro h
    exact ⟨⟨(row_card_iff_exclusive A).mpr ((exclusive_iff_disjoint A).mpr h.2.1),
      fun j => ⟨(h.1 j).1, (h.1 j).2.1⟩⟩, h.2.2, fun j => (h.1 j).2.2⟩

def alphaOfFibers {n m : ℕ} (F : Fin m → Finset (Fin n)) : Alpha n m :=
  fun i j => decide (i ∈ F j)

@[simp] theorem fiber_alphaOfFibers {n m : ℕ} (F : Fin m → Finset (Fin n)) :
    fiber (alphaOfFibers F) = F := by
  funext j; ext i; simp [fiber, alphaOfFibers]

theorem branchModel_alpha_projection {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (F : Fin m → Finset (Fin n)) :
    (∃ A, fiber A = F ∧ Embedding E L k A) ↔ BranchModel E L k F := by
  constructor
  · rintro ⟨A, rfl, h⟩; exact (embedding_iff_branchModel E L k A).mp h
  · intro h
    refine ⟨alphaOfFibers F, fiber_alphaOfFibers F, ?_⟩
    apply (embedding_iff_branchModel E L k _).mpr
    simpa using h

theorem sum_fiber_card_eq_footprint {n m : ℕ} (A : Alpha n m) (h : Exclusive A) :
    (∑ j, (fiber A j).card) = footprint A := by
  classical
  have hd : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint (fiber A) := by
    intro j _ l _ hne
    exact (exclusive_iff_disjoint A).mp h j l hne
  rw [← Finset.card_biUnion hd]
  congr 1
  ext i
  simp [footprint, fiber]

theorem footprint_le_physical {n m : ℕ} (A : Alpha n m) : footprint A ≤ n := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun i : Fin n => ∃ j, A i j = true) Finset.univ)
  simpa [footprint] using h

theorem rowBounds_size_bounds {n m : ℕ} (k : ℕ) (A : Alpha n m) (h : RowBounds k A) :
    m ≤ footprint A ∧ footprint A ≤ n := by
  refine ⟨?_, footprint_le_physical A⟩
  rw [← sum_fiber_card_eq_footprint A ((row_card_iff_exclusive A).mp h.1)]
  calc
    m = ∑ _j : Fin m, 1 := by simp
    _ ≤ ∑ j, (fiber A j).card := Finset.sum_le_sum (fun j _ => (h.2 j).1.card_pos)

theorem too_many_logical_impossible {n m : ℕ} (k : ℕ) (A : Alpha n m)
    (h : n < m) : ¬ RowBounds k A := by
  intro hr
  obtain ⟨hlo, hhi⟩ := rowBounds_size_bounds k A hr
  omega

theorem positive_logical_zero_cap {n m : ℕ} (A : Alpha n m) (hm : 0 < m) :
    ¬ RowBounds 0 A := by
  intro h
  have hj := h.2 ⟨0, hm⟩
  have hp := hj.1.card_pos
  omega

theorem cap_one_singletons {n m : ℕ} (A : Alpha n m) (h : RowBounds 1 A) :
    ∀ j, ∃ a, fiber A j = {a} := by
  intro j
  have hp := (h.2 j).1.card_pos
  have hc : (fiber A j).card = 1 := by have := (h.2 j).2; omega
  exact Finset.card_eq_one.mp hc

end AppendixATheory

#print axioms AppendixATheory.exists_partial_assignment_iff
#print axioms AppendixATheory.branchModel_alpha_projection
#print axioms AppendixATheory.sum_fiber_card_eq_footprint
#print axioms AppendixATheory.rowBounds_size_bounds
#print axioms AppendixATheory.cap_one_singletons
