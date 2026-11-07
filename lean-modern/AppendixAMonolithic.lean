module

public import AppendixAModelInterfaces
public import AppendixASelectors
public import AppendixAProcedure

@[expose] public section

/-! All-auxiliary projection and objective bridges for the explicitly qualified
vertex-bounded selectable-path interpretation. Original product identity and
malformed printed master indexes are not certified by these statements. -/
noncomputable section
open scoped BigOperators
namespace AppendixATheory

abbrev FiberGamma (n m : ℕ) := Fin m → AppendixAPaths.Gamma n

def MonolithicRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m)
    (D : EdgeAux n m) (G : FiberGamma n m) : Prop :=
  LiteralAlphaRows k A ∧ FullDeltaRows E L A D ∧
    ∀ j, AppendixAPaths.FullSelectorRows E (fiber A j) k (G j)

theorem monolithic_projection {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) (hl : LoopFree L) :
    (∃ D G, MonolithicRows E L k A D G) ↔ Embedding E L k A := by
  constructor
  · rintro ⟨D,G,hr,hd,hg⟩
    have hb := (rowBounds_iff_literal_alpha_rows k A).mpr hr
    refine ⟨hb, (full_delta_projection E L k A hb hl).mp ⟨D,hd⟩, ?_⟩
    intro j
    exact (AppendixAPaths.full_selector_exists_iff_connected E (fiber A j) k
      (hb.2 j).2).mp ⟨G j,hg j⟩
  · intro hA
    obtain ⟨D,hd⟩ := (full_delta_projection E L k A hA.1 hl).mpr hA.2.1
    refine ⟨D, (fun j => AppendixAPaths.chosenGamma E (fiber A j) k),
      (rowBounds_iff_literal_alpha_rows k A).mp hA.1, hd, ?_⟩
    intro j
    exact AppendixAPaths.chosenGamma_full_rows E (fiber A j) k (hA.1.2 j).2 (hA.2.2 j)

def totalSize {n m : ℕ} (A : Alpha n m) : ℝ := ∑ i, ∑ j, Chapter10.bit (A i j)

theorem monolithic_totalSize {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m)
    (D : EdgeAux n m) (G : FiberGamma n m) (h : MonolithicRows E L k A D G) :
    totalSize A = (footprint A : ℝ) :=
  literal_footprint_sum A ((row_card_iff_exclusive A).mp
    ((rowBounds_iff_literal_alpha_rows k A).mpr h.1).1)

def MonolithicOptimal {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m)
    (D : EdgeAux n m) (G : FiberGamma n m) : Prop :=
  MonolithicRows E L k A D G ∧ ∀ B D' G', MonolithicRows E L k B D' G' → totalSize A ≤ totalSize B

theorem monolithic_optimal_projection {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) (hl : LoopFree L) :
    (∃ D G, MonolithicOptimal E L k A D G) ↔
      Embedding E L k A ∧ ∀ B, Embedding E L k B → footprint A ≤ footprint B := by
  constructor
  · rintro ⟨D,G,hr,ho⟩
    refine ⟨(monolithic_projection E L k A hl).mp ⟨D,G,hr⟩, ?_⟩
    intro B hB
    obtain ⟨D',G',hr'⟩ := (monolithic_projection E L k B hl).mpr hB
    have h := ho B D' G' hr'
    rw [monolithic_totalSize E L k A D G hr, monolithic_totalSize E L k B D' G' hr'] at h
    exact_mod_cast h
  · rintro ⟨hA,ho⟩
    obtain ⟨D,G,hr⟩ := (monolithic_projection E L k A hl).mpr hA
    refine ⟨D,G,hr,?_⟩
    intro B D' G' hr'
    rw [monolithic_totalSize E L k A D G hr, monolithic_totalSize E L k B D' G' hr']
    exact_mod_cast ho B ((monolithic_projection E L k B hl).mp ⟨D',G',hr'⟩)

theorem monolithic_infeasible_iff {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (hl : LoopFree L) :
    (¬ ∃ A D G, MonolithicRows E L k A D G) ↔ ¬ ∃ A, Embedding E L k A := by
  simp only [monolithic_projection E L k _ hl]

theorem masterPool_iff_source_rows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (history : List (FiberCut n m))
    (A : Alpha n m) : A ∈ masterPool E L k history ↔
      ∃ Z w, RepairedMasterRows E L k A Z w ∧ ∀ c ∈ history, sourceCutRow E c A := by
  rw [mem_masterPool]
  constructor
  · rintro ⟨hm,hh⟩
    obtain ⟨Z,w,hr⟩ := (repaired_master_projection E L k A).mpr hm
    exact ⟨Z,w,hr,fun c hc => (cutHolds_iff_sourceCutRow E c A).mp (hh c hc)⟩
  · rintro ⟨Z,w,hr,hh⟩
    exact ⟨(repaired_master_projection E L k A).mp ⟨Z,w,hr⟩,
      fun c hc => (cutHolds_iff_sourceCutRow E c A).mpr (hh c hc)⟩

theorem returned_monolithic_optimum {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (hl : LoopFree L) (A : Alpha n m)
    (ha : (solveEmbedding E L k).answer = some A) :
    ∃ D G, MonolithicOptimal E L k A D G :=
  (monolithic_optimal_projection E L k A hl).mpr (solveEmbedding_some_optimal E L k A ha)

theorem returned_none_iff_monolithic_infeasible {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (hl : LoopFree L) :
    (solveEmbedding E L k).answer = none ↔ ¬ ∃ A D G, MonolithicRows E L k A D G := by
  rw [solveEmbedding_none_iff, monolithic_infeasible_iff E L k hl]

end AppendixATheory

#print axioms AppendixATheory.monolithic_projection
#print axioms AppendixATheory.monolithic_totalSize
#print axioms AppendixATheory.monolithic_optimal_projection
#print axioms AppendixATheory.monolithic_infeasible_iff
#print axioms AppendixATheory.masterPool_iff_source_rows
#print axioms AppendixATheory.returned_monolithic_optimum
#print axioms AppendixATheory.returned_none_iff_monolithic_infeasible
