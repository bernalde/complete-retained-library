module

public import AppendixAAssignment

@[expose] public section

/-! Draft: literal K6-minus-one-edge and K6 in the fixed cell K4,4.
The target parameter is four, not an arbitrary Chimera shore size.
All branch caps are quantified; no solver, minimum or runtime claim. -/
noncomputable section
open scoped BigOperators
namespace AppendixASingleCell
open AppendixATheory

/-- Physical vertices 0,1,2,3 form one shore; 4,5,6,7 form the other. -/
def shore (u : Fin 8) : Bool := decide (u.val < 4)

def cellEdges : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun e => shore e.1 ≠ shore e.2)

theorem cell_adjacent_iff (u v : Fin 8) :
    AppendixA.adjacent cellEdges u v ↔ shore u ≠ shore v := by
  simp only [AppendixA.adjacent, cellEdges, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨fun h => h.elim id Ne.symm, Or.inl⟩

theorem cell_loopFree : LoopFree cellEdges := by
  intro u h
  exact ((cell_adjacent_iff u u).mp h) rfl

theorem cell_triangle_free (u v w : Fin 8) :
    ¬ (AppendixA.adjacent cellEdges u v ∧
       AppendixA.adjacent cellEdges v w ∧
       AppendixA.adjacent cellEdges u w) := by
  rintro ⟨huv, hvw, huw⟩
  have h1 := (cell_adjacent_iff u v).mp huv
  have h2 := (cell_adjacent_iff v w).mp hvw
  have h3 := (cell_adjacent_iff u w).mp huw
  cases hu : shore u <;> cases hv : shore v <;> cases hw : shore w <;> simp_all

/-- Both orientations are stored; this is sixteen undirected edges. -/
theorem cell_oriented_edge_count : cellEdges.card = 32 := by decide

def MinusAdj (j l : Fin 6) : Prop :=
  j ≠ l ∧ ¬ (j = 0 ∧ l = 1) ∧ ¬ (j = 1 ∧ l = 0)

instance instDecidableMinusAdj (j l : Fin 6) : Decidable (MinusAdj j l) :=
  inferInstanceAs (Decidable (j ≠ l ∧ ¬ (j = 0 ∧ l = 1) ∧ ¬ (j = 1 ∧ l = 0)))

def minusEdges : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun e => MinusAdj e.1 e.2)

theorem minus_symmetric : Symmetric MinusAdj := by
  intro j l h
  refine ⟨h.1.symm, ?_, ?_⟩
  · rintro ⟨hl, hj⟩
    exact h.2.2 ⟨hj, hl⟩
  · rintro ⟨hl, hj⟩
    exact h.2.1 ⟨hj, hl⟩

theorem minus_adjacent_iff (j l : Fin 6) :
    AppendixA.adjacent minusEdges j l ↔ MinusAdj j l := by
  simp only [AppendixA.adjacent, minusEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun h => minus_symmetric h), Or.inl⟩

theorem minus_oriented_edge_count : minusEdges.card = 28 := by decide

def completeEdges (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => e.1 ≠ e.2)

theorem complete_adjacent_iff (m : ℕ) (j l : Fin m) :
    AppendixA.adjacent (completeEdges m) j l ↔ j ≠ l := by
  simp only [AppendixA.adjacent, completeEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id Ne.symm, Or.inl⟩

theorem complete_six_oriented_edge_count : (completeEdges 6).card = 30 := by decide

/-- A logical triangle cannot have three singleton fibers in this target. -/
theorem triangle_fiber_sum {m k : ℕ} (L : Finset (Fin m × Fin m))
    (A : Alpha 8 m) (hr : RowBounds k A) (he : EdgeCoverage cellEdges L A)
    (i j l : Fin m) (hij : AppendixA.adjacent L i j)
    (hjl : AppendixA.adjacent L j l) (hil : AppendixA.adjacent L i l) :
    4 ≤ (fiber A i).card + (fiber A j).card + (fiber A l).card := by
  by_contra hsmall
  have hi := (hr.2 i).1.card_pos
  have hj := (hr.2 j).1.card_pos
  have hl := (hr.2 l).1.card_pos
  have ci : (fiber A i).card = 1 := by omega
  have cj : (fiber A j).card = 1 := by omega
  have cl : (fiber A l).card = 1 := by omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp ci
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp cj
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp cl
  have singleton_edge : ∀ a b x y, fiber A a = {x} → fiber A b = {y} →
      AppendixA.adjacent L a b → AppendixA.adjacent cellEdges x y := by
    intro a b x y ha hb hab
    obtain ⟨p, hp, q, hq, hpq⟩ := he a b hab
    rw [ha] at hp
    rw [hb] at hq
    have ep := Finset.mem_singleton.mp hp
    have eq := Finset.mem_singleton.mp hq
    simpa [ep, eq] using hpq
  exact cell_triangle_free u v w
    ⟨singleton_edge i j u v hu hv hij,
     singleton_edge j l v w hv hw hjl,
     singleton_edge i l u w hu hw hil⟩

/-- Six positive fiber sizes satisfying the actual sixteen triangle
inequalities of K6-minus-{0,1} have sum at least nine. -/
theorem six_triangle_count (c : Fin 6 → ℕ) (positive : ∀ i, 1 ≤ c i)
    (triangles : ∀ i j l, MinusAdj i j → MinusAdj j l → MinusAdj i l →
      4 ≤ c i + c j + c l) : 9 ≤ ∑ i, c i := by
  have h0 := positive 0
  have h1 := positive 1
  have h2 := positive 2
  have h3 := positive 3
  have h4 := positive 4
  have h5 := positive 5
  have h023 := triangles 0 2 3 (by decide) (by decide) (by decide)
  have h024 := triangles 0 2 4 (by decide) (by decide) (by decide)
  have h025 := triangles 0 2 5 (by decide) (by decide) (by decide)
  have h034 := triangles 0 3 4 (by decide) (by decide) (by decide)
  have h035 := triangles 0 3 5 (by decide) (by decide) (by decide)
  have h045 := triangles 0 4 5 (by decide) (by decide) (by decide)
  have h123 := triangles 1 2 3 (by decide) (by decide) (by decide)
  have h124 := triangles 1 2 4 (by decide) (by decide) (by decide)
  have h125 := triangles 1 2 5 (by decide) (by decide) (by decide)
  have h134 := triangles 1 3 4 (by decide) (by decide) (by decide)
  have h135 := triangles 1 3 5 (by decide) (by decide) (by decide)
  have h145 := triangles 1 4 5 (by decide) (by decide) (by decide)
  have h234 := triangles 2 3 4 (by decide) (by decide) (by decide)
  have h235 := triangles 2 3 5 (by decide) (by decide) (by decide)
  have h245 := triangles 2 4 5 (by decide) (by decide) (by decide)
  have h345 := triangles 3 4 5 (by decide) (by decide) (by decide)
  have expand : (∑ i : Fin 6, c i) = c 0 + c 1 + c 2 + c 3 + c 4 + c 5 := by
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  rw [expand]
  omega

/-- Already impossible with row bounds and crossing-edge coverage;
the accepted model's connectivity requirement is not needed to refute it. -/
theorem minus_rows_coverage_impossible (k : ℕ) (A : Alpha 8 6)
    (hr : RowBounds k A) (he : EdgeCoverage cellEdges minusEdges A) : False := by
  have lower : 9 ≤ ∑ j : Fin 6, (fiber A j).card := by
    apply six_triangle_count
    · intro j
      exact (hr.2 j).1.card_pos
    · intro i j l hij hjl hil
      exact triangle_fiber_sum minusEdges A hr he i j l
        ((minus_adjacent_iff i j).mpr hij)
        ((minus_adjacent_iff j l).mpr hjl)
        ((minus_adjacent_iff i l).mpr hil)
  have sum_eq := sum_fiber_card_eq_footprint A ((row_card_iff_exclusive A).mp hr.1)
  have upper := footprint_le_physical A
  omega

theorem minus_no_embedding (k : ℕ) (A : Alpha 8 6) :
    ¬ Embedding cellEdges minusEdges k A := by
  intro h
  exact minus_rows_coverage_impossible k A h.1 h.2.1

theorem complete_no_embedding (k : ℕ) (A : Alpha 8 6) :
    ¬ Embedding cellEdges (completeEdges 6) k A := by
  intro h
  apply minus_rows_coverage_impossible k A h.1
  intro j l hjl
  apply h.2.1 j l
  exact (complete_adjacent_iff 6 j l).mpr ((minus_adjacent_iff j l).mp hjl).1

theorem minus_no_branchModel (k : ℕ) (F : Fin 6 → Finset (Fin 8)) :
    ¬ BranchModel cellEdges minusEdges k F := by
  intro h
  obtain ⟨A, _, hA⟩ := (branchModel_alpha_projection cellEdges minusEdges k F).mpr h
  exact minus_no_embedding k A hA

theorem complete_no_branchModel (k : ℕ) (F : Fin 6 → Finset (Fin 8)) :
    ¬ BranchModel cellEdges (completeEdges 6) k F := by
  intro h
  obtain ⟨A, _, hA⟩ :=
    (branchModel_alpha_projection cellEdges (completeEdges 6) k F).mpr h
  exact complete_no_embedding k A hA

theorem literal_gadgets_no_embedding :
    (∀ k, ¬ ∃ A : Alpha 8 6, Embedding cellEdges minusEdges k A) ∧
    (∀ k, ¬ ∃ A : Alpha 8 6, Embedding cellEdges (completeEdges 6) k A) := by
  constructor
  · rintro k ⟨A, hA⟩
    exact minus_no_embedding k A hA
  · rintro k ⟨A, hA⟩
    exact complete_no_embedding k A hA

/-- Explicit positive control: three cross-shore pairs and two singletons. -/
def k5Branches (j : Fin 5) : Finset (Fin 8) :=
  match j.val with
  | 0 => {0, 4}
  | 1 => {1, 5}
  | 2 => {2, 6}
  | 3 => {3}
  | _ => {7}

theorem k5_branch_pairs (j : Fin 5) :
    ∃ u v, k5Branches j = {u, v} ∧
      (u = v ∨ AppendixA.adjacent cellEdges u v) := by
  fin_cases j
  · exact ⟨0, 4, rfl, Or.inr ((cell_adjacent_iff _ _).mpr (by decide))⟩
  · exact ⟨1, 5, rfl, Or.inr ((cell_adjacent_iff _ _).mpr (by decide))⟩
  · exact ⟨2, 6, rfl, Or.inr ((cell_adjacent_iff _ _).mpr (by decide))⟩
  · exact ⟨3, 3, by simp [k5Branches], Or.inl rfl⟩
  · exact ⟨7, 7, by simp [k5Branches], Or.inl rfl⟩

theorem k5_branch_connected (j : Fin 5) :
    AppendixA.connected cellEdges (k5Branches j) := by
  obtain ⟨u, v, hF, huv⟩ := k5_branch_pairs j
  rw [hF]
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · rcases huv with rfl | huv
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by simp, by simp, huv⟩
  · rcases huv with rfl | huv
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        ⟨by simp, by simp, AppendixA.adjacent_symmetric cellEdges huv⟩
  · exact Relation.ReflTransGen.refl

theorem k5_branches_disjoint (j l : Fin 5) (hne : j ≠ l) :
    Disjoint (k5Branches j) (k5Branches l) := by
  fin_cases j <;> fin_cases l <;> simp_all [k5Branches, Finset.disjoint_left]

theorem k5_edges_covered (j l : Fin 5)
    (h : AppendixA.adjacent (completeEdges 5) j l) :
    ∃ u ∈ k5Branches j, ∃ v ∈ k5Branches l, AppendixA.adjacent cellEdges u v := by
  have hne := (complete_adjacent_iff 5 j l).mp h
  fin_cases j <;> fin_cases l <;> simp_all [k5Branches, cell_adjacent_iff, shore] <;> decide

theorem k5_branchModel : BranchModel cellEdges (completeEdges 5) 2 k5Branches := by
  refine ⟨?_, k5_branches_disjoint, k5_edges_covered⟩
  intro j
  obtain ⟨u, v, hF, _⟩ := k5_branch_pairs j
  refine ⟨?_, ?_, k5_branch_connected j⟩
  · rw [hF]
    exact Finset.insert_nonempty _ _
  · rw [hF]
    exact (Finset.card_insert_le u {v}).trans (by simp)

def k5Assignment : Alpha 8 5 := alphaOfFibers k5Branches

theorem k5_embedding : Embedding cellEdges (completeEdges 5) 2 k5Assignment := by
  apply (embedding_iff_branchModel cellEdges (completeEdges 5) 2 k5Assignment).mpr
  simpa [k5Assignment] using k5_branchModel

theorem k5_footprint : footprint k5Assignment = 8 := by
  rw [← sum_fiber_card_eq_footprint k5Assignment
    ((row_card_iff_exclusive k5Assignment).mp k5_embedding.1.1)]
  simp [k5Assignment, k5Branches, Fin.sum_univ_succ]

end AppendixASingleCell
