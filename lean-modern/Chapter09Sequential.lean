module

public import Chapter09ConflictDeletion
public import Chapter09Slots
public import Chapter09Nonlinear

@[expose] public section

/-! Literal two-pass Algorithm12 on vertex/color selections. The edge list
contains spatial slot pairs; the second list contains vertex/color slots.
Completeness is explicit, and neither order nor nonrepetition is assumed. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Sequential
open Source ConflictDeletion

variable {n k : ℕ}

def rowStep (S : Finset (Slot n k)) (u : Slot n k) : Finset (Slot n k) :=
  if u ∈ S ∧ ∃ p : Fin k, p ≠ u.2 ∧ (u.1,p) ∈ S then S.erase u else S

def rowScan : List (Slot n k) → Finset (Slot n k) → Finset (Slot n k)
  | [], S => S
  | u :: us, S => rowScan us (rowStep S u)

def algorithm (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (S : Finset (Slot n k)) : Finset (Slot n k) := rowScan LV (edgeScan LE S)

theorem edge_flag_test (S : Finset (Slot n k)) (i j : Fin n) (r : Fin k) :
    1 < flag S i r + flag S j r ↔ (i,r) ∈ S ∧ (j,r) ∈ S := by
  by_cases hi : (i,r) ∈ S <;> by_cases hj : (j,r) ∈ S <;>
    simp [flag,hi,hj]

theorem row_flag_test (S : Finset (Slot n k)) (u : Slot n k) :
    1 ≤ (∑ p : Fin k, if p ≠ u.2 then flag S u.1 p else 0) ↔
      ∃ p : Fin k, p ≠ u.2 ∧ (u.1,p) ∈ S := by
  have hc : (∑ p : Fin k, if p ≠ u.2 then flag S u.1 p else 0) =
      ((Finset.univ.filter (fun p : Fin k => p ≠ u.2 ∧ (u.1,p) ∈ S)).card : ℝ) := by
    calc
      _ = ∑ p : Fin k, if p ≠ u.2 ∧ (u.1,p) ∈ S then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hn : p ≠ u.2 <;> by_cases hm : (u.1,p) ∈ S <;>
          simp [flag,hn,hm]
      _ = _ := by simp
  rw [hc]
  constructor
  · intro h
    have hnat : 1 ≤ (Finset.univ.filter (fun p : Fin k => p ≠ u.2 ∧ (u.1,p) ∈ S)).card := by
      exact_mod_cast h
    obtain ⟨p,hp⟩ := Finset.one_le_card.mp hnat
    exact ⟨p,(Finset.mem_filter.mp hp).2⟩
  · rintro ⟨p,hp⟩
    have hnat : 1 ≤ (Finset.univ.filter (fun p : Fin k => p ≠ u.2 ∧ (u.1,p) ∈ S)).card :=
      Finset.one_le_card.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
    exact_mod_cast hnat

theorem edgeStep_source (S : Finset (Slot n k)) (i j : Fin n) (r : Fin k) :
    edgeStep S ((i,r),(j,r)) =
      if 1 < flag S i r + flag S j r then S.erase (i,r) else S := by
  simp only [edgeStep,edge_flag_test]

theorem rowStep_source (S : Finset (Slot n k)) (i : Fin n) (r : Fin k) :
    rowStep S (i,r) =
      if flag S i r = 1 ∧ 1 ≤ (∑ p : Fin k, if p ≠ r then flag S i p else 0)
      then S.erase (i,r) else S := by
  have ht : (1 ≤ (∑ p : Fin k, if p ≠ r then flag S i p else 0)) ↔
      ∃ p : Fin k, p ≠ r ∧ (i,p) ∈ S := row_flag_test S (i,r)
  simp only [ht]
  by_cases h : (i,r) ∈ S <;> simp [rowStep,flag,h]

theorem row_guard_iff (S : Finset (Slot n k)) (u : Slot n k) :
    (u ∈ S ∧ ∃ p : Fin k, p ≠ u.2 ∧ (u.1,p) ∈ S) ↔
      (u ∈ S ∧ ∃ v ∈ S, (u,v) ∈ colorPairs n k ∨ (v,u) ∈ colorPairs n k) := by
  rcases u with ⟨i,r⟩
  constructor
  · rintro ⟨hu,p,hpr,hp⟩
    refine ⟨hu,(i,p),hp,?_⟩
    rcases lt_or_gt_of_ne hpr with h | h
    · right; exact (mem_colorPairs _).mpr ⟨rfl,h⟩
    · left; exact (mem_colorPairs _).mpr ⟨rfl,h⟩
  · rintro ⟨hu,⟨j,p⟩,hp,h⟩
    refine ⟨hu,p,?_⟩
    rcases h with h | h
    · have hh := (mem_colorPairs _).mp h
      change i = j ∧ r < p at hh
      rcases hh with ⟨rfl,hrp⟩
      exact ⟨ne_of_gt hrp,hp⟩
    · have hh := (mem_colorPairs _).mp h
      change j = i ∧ p < r at hh
      rcases hh with ⟨rfl,hpr⟩
      exact ⟨ne_of_lt hpr,hp⟩

theorem rowStep_eq_vertexStep (S : Finset (Slot n k)) (u : Slot n k) :
    rowStep S u = vertexStep (colorPairs n k) S u := by
  simp only [rowStep,vertexStep,row_guard_iff]

theorem rowScan_eq_vertexScan (L : List (Slot n k)) (S : Finset (Slot n k)) :
    rowScan L S = vertexScan (colorPairs n k) L S := by
  induction L generalizing S with
  | nil => rfl
  | cons u L ih => simp only [rowScan,vertexScan,ih,rowStep_eq_vertexStep]

theorem algorithm_eq_twoPass (LE : List (Slot n k × Slot n k))
    (LV : List (Slot n k)) (S : Finset (Slot n k)) :
    algorithm LE LV S = twoPass (colorPairs n k) LE LV S :=
  rowScan_eq_vertexScan LV (edgeScan LE S)

theorem algorithm_subset (LE : List (Slot n k × Slot n k))
    (LV : List (Slot n k)) (S : Finset (Slot n k)) : algorithm LE LV S ⊆ S := by
  rw [algorithm_eq_twoPass]
  exact twoPass_subset _ _ _ _

theorem algorithm_card_bound (LE : List (Slot n k × Slot n k))
    (LV : List (Slot n k)) (S : Finset (Slot n k)) :
    S.card ≤ (algorithm LE LV S).card + LE.length + LV.length := by
  rw [algorithm_eq_twoPass]
  exact twoPass_card_bound _ _ _ _

theorem algorithm_feasible (G : Graph n) (LE : List (Slot n k × Slot n k))
    (LV : List (Slot n k)) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (S : Finset (Slot n k)) :
    Feasible G (algorithm LE LV S) := by
  rw [algorithm_eq_twoPass]
  exact twoPass_feasible (spatialPairs G k) (colorPairs n k) LE LV hE
    (fun e _ => hV e.1) S

theorem algorithm_score_bound (G : Graph n) (w : (Slot n k × Slot n k) → ℝ)
    (hw : ∀ e ∈ conflictPairs G k, 1 ≤ w e)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (S : Finset (Slot n k)) :
    score (conflictPairs G k) w S ≤ ((algorithm LE LV S).card : ℝ) := by
  rw [algorithm_eq_twoPass]
  exact twoPass_score_bound (spatialPairs G k) (colorPairs n k) w hw LE LV hs hE
    (fun e _ => hV e.1) S

theorem algorithm_uScore_bound (G : Graph n) (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (S : Finset (Slot n k)) :
    uScore G a b S ≤ ((algorithm LE LV S).card : ℝ) :=
  algorithm_score_bound G (weight a b) (weight_ge_one G a b ha hb) LE LV hs hE hV S

theorem algorithm_uScore_bound_k1 (G : Graph n) (a b : ℝ) (ha : 1 ≤ a)
    (LE : List (Slot n 1 × Slot n 1)) (LV : List (Slot n 1))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G 1) (hE : ∀ e ∈ spatialPairs G 1, e ∈ LE)
    (hV : ∀ u : Slot n 1, u ∈ LV) (S : Finset (Slot n 1)) :
    uScore G a b S ≤ ((algorithm LE LV S).card : ℝ) :=
  algorithm_score_bound G (weight a b) (weight_ge_one_k1 G a b ha) LE LV hs hE hV S

theorem algorithm_optimal_return (G : Graph n) (w : (Slot n k × Slot n k) → ℝ)
    (hw : ∀ e ∈ conflictPairs G k, 1 ≤ w e)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (S : Finset (Slot n k))
    (hm : isScoreMax (conflictPairs G k) w S) :
    Feasible G (algorithm LE LV S) ∧
    score (conflictPairs G k) w S = ((algorithm LE LV S).card : ℝ) ∧
    ∀ T : Finset (Slot n k), Feasible G T →
      (T.card : ℝ) ≤ ((algorithm LE LV S).card : ℝ) := by
  rw [algorithm_eq_twoPass]
  exact twoPass_optimal_return (spatialPairs G k) (colorPairs n k) w hw LE LV
    hs hE (fun e _ => hV e.1) S hm

/-- Literal ordered nonlinear objective: the repaired weak color threshold is1/2. -/
theorem algorithm_nonlinear_repaired (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ 2*c2)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (S : Finset (Slot n k))
    (hm : isNMax G c1 c2 S) :
    Feasible G (algorithm LE LV S) ∧
    nScore G c1 c2 S = ((algorithm LE LV S).card : ℝ) ∧
    ((algorithm LE LV S).card : ℝ) = alpha G k ∧
    ∀ T : Finset (Slot n k), Feasible G T →
      (T.card : ℝ) ≤ ((algorithm LE LV S).card : ℝ) := by
  obtain ⟨hf,hval,ho⟩ := algorithm_optimal_return G (weight c1 (2*c2))
    (weight_ge_one G c1 (2*c2) hc1 hc2) LE LV hs hE hV S
    ((isNMax_iff_unordered G c1 c2 S).mp hm)
  have hn : nScore G c1 c2 S = ((algorithm LE LV S).card : ℝ) := by
    rw [nScore_eq_uScore]
    exact hval
  refine ⟨hf,hn,?_,ho⟩
  rw [← hn,(isNMax_iff G c1 c2 S).mp hm,qNonlinear_eq_alpha G k c1 c2 hc1 hc2]

/-- Source Corollary9.3.1: the stated unit boundary with its actual Algorithm12. -/
theorem corollary_9_3_1 (G : Graph n) (hk : 0 < k) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) (hunit : c1 = 1 ∨ c2 = 1)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (S : Finset (Slot n k))
    (hm : isNMax G c1 c2 S) :
    qNonlinear G k c1 c2 = alpha G k ∧
    Feasible G (algorithm LE LV S) ∧
    ((algorithm LE LV S).card : ℝ) = alpha G k := by
  obtain ⟨hf,_,ha,_⟩ := algorithm_nonlinear_repaired G c1 c2 hc1
    (by linarith) LE LV hs hE hV S hm
  exact ⟨corollary_9_3_1_value G hk c1 c2 hc1 hc2 hunit,hf,ha⟩

/-- k=1 genuinely has no color-penalty hypothesis. -/
theorem algorithm_nonlinear_k1 (G : Graph n) (c1 c2 : ℝ) (hc1 : 1 ≤ c1)
    (LE : List (Slot n 1 × Slot n 1)) (LV : List (Slot n 1))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G 1) (hE : ∀ e ∈ spatialPairs G 1, e ∈ LE)
    (hV : ∀ u : Slot n 1, u ∈ LV) (S : Finset (Slot n 1))
    (hm : isNMax G c1 c2 S) :
    Feasible G (algorithm LE LV S) ∧
    nScore G c1 c2 S = ((algorithm LE LV S).card : ℝ) ∧
    ((algorithm LE LV S).card : ℝ) = alpha G 1 := by
  obtain ⟨hf,hval,_⟩ := algorithm_optimal_return G (weight c1 (2*c2))
    (weight_ge_one_k1 G c1 (2*c2) hc1) LE LV hs hE hV S
    ((isNMax_iff_unordered G c1 c2 S).mp hm)
  have hn : nScore G c1 c2 S = ((algorithm LE LV S).card : ℝ) := by
    rw [nScore_eq_uScore]
    exact hval
  refine ⟨hf,hn,?_⟩
  rw [← hn,(isNMax_iff G c1 c2 S).mp hm,qNonlinear_one_color G c1 c2 hc1]

end Chapter09.Sequential

#print axioms Chapter09.Sequential.edge_flag_test
#print axioms Chapter09.Sequential.row_flag_test
#print axioms Chapter09.Sequential.edgeStep_source
#print axioms Chapter09.Sequential.rowStep_source
#print axioms Chapter09.Sequential.algorithm_eq_twoPass
#print axioms Chapter09.Sequential.algorithm_subset
#print axioms Chapter09.Sequential.algorithm_card_bound
#print axioms Chapter09.Sequential.algorithm_feasible
#print axioms Chapter09.Sequential.algorithm_uScore_bound
#print axioms Chapter09.Sequential.algorithm_uScore_bound_k1
#print axioms Chapter09.Sequential.algorithm_optimal_return
#print axioms Chapter09.Sequential.algorithm_nonlinear_repaired
#print axioms Chapter09.Sequential.corollary_9_3_1
#print axioms Chapter09.Sequential.algorithm_nonlinear_k1
