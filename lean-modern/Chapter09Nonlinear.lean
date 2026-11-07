module

public import Chapter09SlotSums

@[expose] public section

/-! Actual finite optima for the literal ordered-pair nonlinear formulation,
thesis (9.19), (9.20), Theorem 9.3.2. The weak factor-two threshold is stated
separately from the stronger printed sufficient hypotheses. The simultaneous
repair reused below is an auxiliary construction, not source Algorithm 12. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Source

def arrayNScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (x : Fin n → Fin k → ℝ) : ℝ :=
  (∑ i, ∑ r, x i r ^ 2) - c1 * (∑ e ∈ G.edges, ∑ r, x e.1 r * x e.2 r) -
    c2 * (∑ i, ∑ r, ∑ p, if p ≠ r then x i r * x i p else 0)

@[simp] theorem arrayNScore_flag {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (S : Finset (Slot n k)) : arrayNScore G c1 c2 (flag S) = nScore G c1 c2 S := rfl

theorem arrayNScore_selected {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (x : Fin n → Fin k → ℝ) (hx : Binary x) :
    nScore G c1 c2 (selected x) = arrayNScore G c1 c2 x := by
  rw [← arrayNScore_flag,flag_selected x hx]

def qNonlinear {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) : ℝ :=
  finiteMax (nScore (k := k) G c1 c2)

def isNMax {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) : Prop :=
  ∀ T : Finset (Slot n k), nScore G c1 c2 T ≤ nScore G c1 c2 S

theorem qNonlinear_attained {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) :
    ∃ S : Finset (Slot n k), nScore G c1 c2 S = qNonlinear G k c1 c2 :=
  finiteMax_attained _

theorem nScore_le_qNonlinear {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (S : Finset (Slot n k)) : nScore G c1 c2 S ≤ qNonlinear G k c1 c2 :=
  le_finiteMax _ S

theorem isNMax_iff {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) :
    isNMax G c1 c2 S ↔ nScore G c1 c2 S = qNonlinear G k c1 c2 := by
  constructor
  · intro h
    obtain ⟨T,hT⟩ := qNonlinear_attained G k c1 c2
    exact le_antisymm (nScore_le_qNonlinear G c1 c2 S) (by rw [← hT]; exact h T)
  · intro h T
    rw [h]; exact nScore_le_qNonlinear G c1 c2 T

theorem isNMax_iff_unordered {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) :
    isNMax G c1 c2 S ↔ Chapter09.isScoreMax (conflictPairs G k) (weight c1 (2*c2)) S := by
  simp only [isNMax,Chapter09.isScoreMax,nScore_eq_uScore,uScore]

/-- The finite set domain is exactly the full binary array domain, including n=0 or k=0. -/
theorem qNonlinear_binary_maximum {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) :
    (∃ x : Fin n → Fin k → ℝ, Binary x ∧ arrayNScore G c1 c2 x = qNonlinear G k c1 c2) ∧
    ∀ x : Fin n → Fin k → ℝ, Binary x → arrayNScore G c1 c2 x ≤ qNonlinear G k c1 c2 := by
  constructor
  · obtain ⟨S,hS⟩ := qNonlinear_attained G k c1 c2
    exact ⟨flag S,fun i r => flag_binary S i r,by simpa using hS⟩
  · intro x hx
    rw [← arrayNScore_selected G c1 c2 x hx]
    exact nScore_le_qNonlinear G c1 c2 (selected x)

theorem feasible_nScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k))
    (h : Feasible G S) : nScore G c1 c2 S = (S.card : ℝ) := by
  rw [nScore_eq_uScore,feasible_uScore G c1 (2*c2) S h]

theorem alpha_le_qNonlinear {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) :
    alpha G k ≤ qNonlinear G k c1 c2 := by
  obtain ⟨S,hS,hcard⟩ := alpha_attained G k
  rw [← hcard,← feasible_nScore G c1 c2 S hS]
  exact nScore_le_qNonlinear G c1 c2 S

theorem uScore_le_alpha_of_weights {n k : ℕ} (G : Graph n) (a b : ℝ)
    (hw : ∀ e ∈ conflictPairs G k, 1 ≤ weight a b e) (S : Finset (Slot n k)) :
    uScore G a b S ≤ alpha G k :=
  (Chapter09.weighted_repair_bound _ _ hw S).trans
    (card_le_alpha G _ (Chapter09.repair_feasible _ S))

theorem qNonlinear_eq_alpha_of_weights {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ)
    (hw : ∀ e ∈ conflictPairs G k, 1 ≤ weight c1 (2*c2) e) :
    qNonlinear G k c1 c2 = alpha G k := by
  apply le_antisymm _ (alpha_le_qNonlinear G k c1 c2)
  obtain ⟨S,hS⟩ := qNonlinear_attained G k c1 c2
  rw [← hS,nScore_eq_uScore]
  exact uScore_le_alpha_of_weights G c1 (2*c2) hw S

/-- Generalized weak threshold for the literal ordered color sum. -/
theorem qNonlinear_eq_alpha {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ 2*c2) : qNonlinear G k c1 c2 = alpha G k :=
  qNonlinear_eq_alpha_of_weights G k c1 c2 (weight_ge_one G c1 (2*c2) hc1 hc2)

theorem nonlinear_optimizer_repair_of_weights {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hw : ∀ e ∈ conflictPairs G k, 1 ≤ weight c1 (2*c2) e)
    (S : Finset (Slot n k)) (hmax : isNMax G c1 c2 S) :
    Feasible G (Chapter09.repair (conflictPairs G k) S) ∧
    ((Chapter09.repair (conflictPairs G k) S).card : ℝ) = alpha G k := by
  obtain ⟨hf,he,_⟩ := Chapter09.weak_penalty_optimum_repair _ _ hw S
    ((isNMax_iff_unordered G c1 c2 S).mp hmax)
  refine ⟨hf,?_⟩
  calc
    ((Chapter09.repair (conflictPairs G k) S).card : ℝ) = nScore G c1 c2 S := by
      rw [nScore_eq_uScore]; exact he.symm
    _ = qNonlinear G k c1 c2 := (isNMax_iff G c1 c2 S).mp hmax
    _ = alpha G k := qNonlinear_eq_alpha_of_weights G k c1 c2 hw

theorem nonlinear_optimizer_repair {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ 2*c2) (S : Finset (Slot n k)) (hmax : isNMax G c1 c2 S) :
    Feasible G (Chapter09.repair (conflictPairs G k) S) ∧
    ((Chapter09.repair (conflictPairs G k) S).card : ℝ) = alpha G k :=
  nonlinear_optimizer_repair_of_weights G c1 c2 (weight_ge_one G c1 (2*c2) hc1 hc2) S hmax

theorem nonlinear_optimizer_strict_of_weights {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hw : ∀ e ∈ conflictPairs G k, 1 < weight c1 (2*c2) e)
    (S : Finset (Slot n k)) (hmax : isNMax G c1 c2 S) :
    Feasible G S ∧ (S.card : ℝ) = alpha G k := by
  obtain ⟨hf,hcard⟩ := Chapter09.strict_penalty_optimizer_feasible _ _ hw S
    ((isNMax_iff_unordered G c1 c2 S).mp hmax)
  refine ⟨hf,le_antisymm (card_le_alpha G S hf) ?_⟩
  obtain ⟨T,hT,he⟩ := alpha_attained G k
  rw [← he]; exact hcard T hT

/-- Generalized strict threshold: every optimizer itself is a maximum coloring. -/
theorem nonlinear_optimizer_strict {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 < c1) (hc2 : 1 < 2*c2) (S : Finset (Slot n k)) (hmax : isNMax G c1 c2 S) :
    Feasible G S ∧ (S.card : ℝ) = alpha G k :=
  nonlinear_optimizer_strict_of_weights G c1 c2 (weight_gt_one G c1 (2*c2) hc1 hc2) S hmax

/-- Genuine one-color result; c2 is unrestricted because the full ordered color sum vanishes. -/
theorem qNonlinear_one_color {n : ℕ} (G : Graph n) (c1 c2 : ℝ) (hc1 : 1 ≤ c1) :
    qNonlinear G 1 c1 c2 = alpha G 1 :=
  qNonlinear_eq_alpha_of_weights G 1 c1 c2 (weight_ge_one_k1 G c1 (2*c2) hc1)

theorem nonlinear_one_color_strict {n : ℕ} (G : Graph n) (c1 c2 : ℝ) (hc1 : 1 < c1)
    (S : Finset (Slot n 1)) (hmax : isNMax G c1 c2 S) :
    Feasible G S ∧ (S.card : ℝ) = alpha G 1 :=
  nonlinear_optimizer_strict_of_weights G c1 c2 (weight_gt_one_k1 G c1 (2*c2) hc1) S hmax

theorem nonlinear_one_color_repair {n : ℕ} (G : Graph n) (c1 c2 : ℝ) (hc1 : 1 ≤ c1)
    (S : Finset (Slot n 1)) (hmax : isNMax G c1 c2 S) :
    Feasible G (Chapter09.repair (conflictPairs G 1) S) ∧
    ((Chapter09.repair (conflictPairs G 1) S).card : ℝ) = alpha G 1 :=
  nonlinear_optimizer_repair_of_weights G c1 c2 (weight_ge_one_k1 G c1 (2*c2) hc1) S hmax

/-- The source's stronger sufficient hypotheses, with the actual full-slot finite optimum. -/
theorem theorem_9_3_2 {n k : ℕ} (G : Graph n) (_hk : 0 < k) (c1 c2 : ℝ)
    (hc1 : 1 < c1) (hc2 : 1 < c2) :
    qNonlinear G k c1 c2 = alpha G k ∧
    ∀ S : Finset (Slot n k), isNMax G c1 c2 S → Feasible G S ∧ (S.card : ℝ) = alpha G k := by
  constructor
  · exact qNonlinear_eq_alpha G k c1 c2 hc1.le (by linarith)
  · intro S hS; exact nonlinear_optimizer_strict G c1 c2 hc1 (by linarith) S hS

/-- Value component of source Corollary 9.3.1. Algorithm 12 is treated in the sequential module. -/
theorem corollary_9_3_1_value {n k : ℕ} (G : Graph n) (_hk : 0 < k) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) (_hunit : c1 = 1 ∨ c2 = 1) :
    qNonlinear G k c1 c2 = alpha G k :=
  qNonlinear_eq_alpha G k c1 c2 hc1 (by linarith)

end Chapter09.Source
#print axioms Chapter09.Source.qNonlinear_binary_maximum
#print axioms Chapter09.Source.qNonlinear_eq_alpha
#print axioms Chapter09.Source.nonlinear_optimizer_repair
#print axioms Chapter09.Source.nonlinear_optimizer_strict
#print axioms Chapter09.Source.qNonlinear_one_color
#print axioms Chapter09.Source.nonlinear_one_color_strict
#print axioms Chapter09.Source.theorem_9_3_2
#print axioms Chapter09.Source.corollary_9_3_1_value
