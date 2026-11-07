/-
Copyright (c) 2026 David E. Bernal Neira. Released under Apache 2.0.
Companion proof following the Chapter 9 single-conflict deletion argument.
The accepted simultaneous-cover proofs and their qualified inputs are unchanged.
-/
module

public import Chapter09ConflictDeletion
public import Chapter09Nonlinear

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Chapter09.SourceProcedure

variable {α : Type*} [DecidableEq α]

/-- Delete one endpoint of one currently active conflict. The saved penalty pays
for the one lost selected slot, exactly the local improvement used in the text. -/
theorem score_erase_gain (E : Finset (α × α)) (w : α × α → ℝ)
    (S : Finset α) (a : α) (hn : ∀ e ∈ E, 0 ≤ w e)
    (e : α × α) (he : e ∈ E) (ha : e.1 ∈ S) (hb : e.2 ∈ S)
    (hinc : a = e.1 ∨ a = e.2) :
    score E w S + w e - 1 ≤ score E w (S.erase a) := by
  have ham : a ∈ S := by rcases hinc with rfl | rfl <;> assumption
  have hec : e ∈ conflicts E S := Finset.mem_filter.mpr ⟨he, ha, hb⟩
  have hen : e ∉ conflicts E (S.erase a) := by
    intro h
    have hh := (Finset.mem_filter.mp h).2
    rcases hinc with rfl | rfl
    · exact Finset.notMem_erase e.1 S hh.1
    · exact Finset.notMem_erase e.2 S hh.2
  have hsub : insert e (conflicts E (S.erase a)) ⊆ conflicts E S := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hec
    · exact ConflictDeletion.conflicts_mono E (Finset.erase_subset a S) hf
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun f hf _ => hn f (Finset.mem_filter.mp hf).1)
  rw [Finset.sum_insert hen] at hs
  have hc : ((S.erase a).card : ℝ) + 1 = (S.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one ham
  unfold score
  linarith

theorem score_erase_strict (E : Finset (α × α)) (w : α × α → ℝ)
    (S : Finset α) (a : α) (hn : ∀ e ∈ E, 0 ≤ w e)
    (e : α × α) (he : e ∈ E) (ha : e.1 ∈ S) (hb : e.2 ∈ S)
    (hinc : a = e.1 ∨ a = e.2) (hw : 1 < w e) :
    score E w S < score E w (S.erase a) := by
  have h := score_erase_gain E w S a hn e he ha hb hinc
  linarith

/-- Source proof: choose one conflict in an alleged infeasible maximizer,
delete its first endpoint, and contradict maximality by a strict local gain. -/
theorem strict_optimizer_feasible_by_single_deletion
    (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 < w e) (S : Finset α) (hmax : isScoreMax E w S) :
    feasible E S := by
  by_contra hbad
  have hex : ∃ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S := by
    by_contra hn
    apply hbad
    intro e he hab
    exact hn ⟨e, he, hab⟩
  obtain ⟨e, he, ha, hb⟩ := hex
  have hg := score_erase_strict E w S e.1
    (fun f hf => (hw f hf).le.trans' zero_le_one) e he ha hb (Or.inl rfl) (hw e he)
  exact (not_lt_of_ge (hmax (S.erase e.1))) hg

theorem strict_optimizer_optimal_by_single_deletion
    (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 < w e) (S : Finset α) (hmax : isScoreMax E w S) :
    feasible E S ∧ ∀ T : Finset α, feasible E T → (T.card : ℝ) ≤ (S.card : ℝ) := by
  have hf := strict_optimizer_feasible_by_single_deletion E w hw S hmax
  refine ⟨hf, ?_⟩
  intro T hT
  simpa only [feasible_score E w S hf, feasible_score E w T hT] using hmax T

open Source

/-- Literal ordered nonlinear objective, with the original strict hypotheses.
The factor two in the ordered color penalty is retained, not silently dropped. -/
theorem nonlinear_optimizer_by_single_deletion {n k : ℕ} (G : Graph n)
    (c1 c2 : ℝ) (hc1 : 1 < c1) (hc2 : 1 < c2)
    (S : Finset (Slot n k)) (hmax : isNMax G c1 c2 S) :
    Feasible G S ∧ (S.card : ℝ) = alpha G k := by
  obtain ⟨hf, ho⟩ := strict_optimizer_optimal_by_single_deletion
    (conflictPairs G k) (weight c1 (2 * c2))
    (weight_gt_one G c1 (2 * c2) hc1 (by linarith)) S
    ((isNMax_iff_unordered G c1 c2 S).mp hmax)
  refine ⟨hf, le_antisymm (card_le_alpha G S hf) ?_⟩
  obtain ⟨T, hT, he⟩ := alpha_attained G k
  rw [← he]
  exact ho T hT

/-- Same statement as source Theorem 9.3.2, proved through the text's one-slot
improvement rather than the accepted simultaneous-cover proof. -/
theorem theorem_9_3_2_from_text {n k : ℕ} (G : Graph n) (_hk : 0 < k)
    (c1 c2 : ℝ) (hc1 : 1 < c1) (hc2 : 1 < c2) :
    qNonlinear G k c1 c2 = alpha G k ∧
      ∀ S : Finset (Slot n k), isNMax G c1 c2 S →
        Feasible G S ∧ (S.card : ℝ) = alpha G k := by
  have hopt := nonlinear_optimizer_by_single_deletion (k := k) G c1 c2 hc1 hc2
  refine ⟨?_, hopt⟩
  obtain ⟨S, hS⟩ := qNonlinear_attained G k c1 c2
  have hsmax := (isNMax_iff G c1 c2 S).mpr hS
  obtain ⟨hf, hc⟩ := hopt S hsmax
  calc
    qNonlinear G k c1 c2 = nScore G c1 c2 S := hS.symm
    _ = (S.card : ℝ) := feasible_nScore G c1 c2 S hf
    _ = alpha G k := hc

end Chapter09.SourceProcedure

#print axioms Chapter09.SourceProcedure.score_erase_gain
#print axioms Chapter09.SourceProcedure.score_erase_strict
#print axioms Chapter09.SourceProcedure.strict_optimizer_feasible_by_single_deletion
#print axioms Chapter09.SourceProcedure.strict_optimizer_optimal_by_single_deletion
#print axioms Chapter09.SourceProcedure.nonlinear_optimizer_by_single_deletion
#print axioms Chapter09.SourceProcedure.theorem_9_3_2_from_text
