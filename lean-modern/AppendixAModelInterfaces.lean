module

public import AppendixAMaster

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AppendixATheory

def DeltaExclusiveRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (D : EdgeAux n m) : Prop :=
  ∀ l ∈ L, ∀ e ∈ E,
    Chapter10.bit (D l (e,false)) + Chapter10.bit (D l (e,true)) ≤ 1

theorem delta_exclusive_of_rows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) (D : EdgeAux n m)
    (hr : RowBounds k A) (hl : LoopFree L) (hd : DeltaRows E L A D) :
    DeltaExclusiveRows E L D := by
  intro l hL e hE
  have hexc := (row_card_iff_exclusive A).mp hr.1
  cases hf : D l (e,false) <;> cases ht : D l (e,true) <;>
    norm_num [hf,ht,Chapter10.bit]
  have hfp := (productRows_iff _ _ _).mp (hd.1 l hL (e,false) (by simpa using hE))
  have htp := (productRows_iff _ _ _).mp (hd.1 l hL (e,true) (by simpa using hE))
  have hp : A e.1 l.1 = true ∧ A e.2 l.2 = true := by
    simpa [firstEnd,secondEnd,hf] using hfp.symm
  have hq : A e.2 l.1 = true ∧ A e.1 l.2 = true := by
    simpa [firstEnd,secondEnd,ht] using htp.symm
  have heq := hexc e.1 l.1 l.2 hp.1 hq.2
  have hL' : (l.1,l.2) ∈ L := hL
  rw [← heq] at hL'
  exact hl l.1 (Or.inl hL')

def FullDeltaRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) (D : EdgeAux n m) : Prop :=
  DeltaRows E L A D ∧ DeltaExclusiveRows E L D

theorem full_delta_projection {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m)
    (hr : RowBounds k A) (hl : LoopFree L) :
    (∃ D, FullDeltaRows E L A D) ↔ EdgeCoverage E L A := by
  constructor
  · rintro ⟨D,hd,_⟩
    exact (delta_projection E L A).mp ⟨D,hd⟩
  · intro h
    obtain ⟨D,hd⟩ := (delta_projection E L A).mpr h
    exact ⟨D,hd,delta_exclusive_of_rows E L k A D hr hl hd⟩

theorem partial_assignment_branch_projection {n m : ℕ}
    (E : Finset (Fin n × Fin n)) (L : Finset (Fin m × Fin m)) (k : ℕ)
    (F : Fin m → Finset (Fin n)) :
    (∃ p : Fin n → Option (Fin m),
      fiber (alphaOfAssignment p) = F ∧ Embedding E L k (alphaOfAssignment p)) ↔
      BranchModel E L k F := by
  constructor
  · rintro ⟨p,hF,h⟩
    exact (branchModel_alpha_projection E L k F).mp ⟨alphaOfAssignment p,hF,h⟩
  · intro h
    obtain ⟨A,hF,hA⟩ := (branchModel_alpha_projection E L k F).mpr h
    obtain ⟨p,hp⟩ := (exists_partial_assignment_iff A).mpr
      ((row_card_iff_exclusive A).mp hA.1.1)
    exact ⟨p,by simpa [hp] using hF,by simpa [hp] using hA⟩

theorem literal_footprint_sum {n m : ℕ} (A : Alpha n m) (h : Exclusive A) :
    (∑ i, ∑ j, Chapter10.bit (A i j)) = (footprint A : ℝ) := by
  calc
    (∑ i, ∑ j, Chapter10.bit (A i j)) = ∑ j, ∑ i, Chapter10.bit (A i j) :=
      Finset.sum_comm
    _ = ∑ j, ((fiber A j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact bit_sum_count _ _
    _ = ((∑ j, (fiber A j).card : ℕ) : ℝ) := by simp
    _ = (footprint A : ℝ) := by rw [sum_fiber_card_eq_footprint A h]

def AggregatedSelectedRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) (Z : EdgeAux n m) : Prop :=
  ∀ l ∈ L, (∑ x ∈ edgeOptions E, Chapter10.bit (Z l x)) = 1 ∧
    ∀ x ∈ edgeOptions E,
      2 * Chapter10.bit (Z l x) ≤
        Chapter10.bit (A (firstEnd x) l.1) + Chapter10.bit (A (secondEnd x) l.2)

theorem selected_aggregate_equivalence {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) (Z : EdgeAux n m) :
    AggregatedSelectedRows E L A Z ↔ SelectedEdgeRows E L A Z := by
  unfold AggregatedSelectedRows SelectedEdgeRows
  simp only [AppendixA.binary_aggregated_link]

theorem aggregated_master_projection {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) :
    (∃ Z w, RowBounds k A ∧ AggregatedSelectedRows E L A Z ∧ WRows E A w) ↔
      RelaxedMaster E L k A := by
  simp only [selected_aggregate_equivalence]
  exact repaired_master_projection E L k A

def LiteralAlphaRows {n m : ℕ} (k : ℕ) (A : Alpha n m) : Prop :=
  (∀ i, (∑ j, Chapter10.bit (A i j)) ≤ 1) ∧
  ∀ j, (1 : ℝ) ≤ (∑ i, Chapter10.bit (A i j)) ∧
    (∑ i, Chapter10.bit (A i j)) ≤ (k : ℝ)

theorem rowBounds_iff_literal_alpha_rows {n m : ℕ} (k : ℕ) (A : Alpha n m) :
    RowBounds k A ↔ LiteralAlphaRows k A := by
  constructor
  · rintro ⟨hr,hf⟩
    refine ⟨?_,?_⟩
    · intro i
      rw [bit_sum_count]
      exact_mod_cast hr i
    · intro j
      have hpos := (hf j).1.card_pos
      have hcap := (hf j).2
      rw [bit_sum_count]
      change (1 : ℝ) ≤ ((fiber A j).card : ℝ) ∧ ((fiber A j).card : ℝ) ≤ (k : ℝ)
      constructor
      · have : 1 ≤ (fiber A j).card := hpos
        exact_mod_cast this
      · exact_mod_cast hcap
  · rintro ⟨hr,hf⟩
    refine ⟨?_,?_⟩
    · intro i
      have hi := hr i
      rw [bit_sum_count] at hi
      exact_mod_cast hi
    · intro j
      have hj := hf j
      rw [bit_sum_count] at hj
      change (1 : ℝ) ≤ ((fiber A j).card : ℝ) ∧ ((fiber A j).card : ℝ) ≤ (k : ℝ) at hj
      have hpos : 1 ≤ (fiber A j).card := by exact_mod_cast hj.1
      exact ⟨Finset.card_pos.mp hpos, by exact_mod_cast hj.2⟩

theorem literal_total_size_bounds {n m : ℕ} (k : ℕ) (A : Alpha n m)
    (h : RowBounds k A) :
    (m : ℝ) ≤ (∑ i, ∑ j, Chapter10.bit (A i j)) ∧
      (∑ i, ∑ j, Chapter10.bit (A i j)) ≤ (n : ℝ) := by
  rw [literal_footprint_sum A ((row_card_iff_exclusive A).mp h.1)]
  exact_mod_cast rowBounds_size_bounds k A h

end AppendixATheory

#print axioms AppendixATheory.delta_exclusive_of_rows
#print axioms AppendixATheory.full_delta_projection
#print axioms AppendixATheory.partial_assignment_branch_projection
#print axioms AppendixATheory.literal_footprint_sum
#print axioms AppendixATheory.aggregated_master_projection
#print axioms AppendixATheory.rowBounds_iff_literal_alpha_rows
#print axioms AppendixATheory.literal_total_size_bounds
