module

public import Chapter09SlotSums
public import Chapter09Sequential

@[expose] public section

/-! Literal Chapter 9 binary slack bounds. Development source only. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Source

/-- The squared row residual dominates the number of unordered color conflicts.
The count is integral; the inequality would fail for unrestricted real counts. -/
theorem row_slack_pair_bound (m : ℕ) (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (m : ℝ) * ((m : ℝ) - 1) / 2 ≤ ((m : ℝ) + t - 1) ^ 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases ht with rfl | rfl
  · by_cases hzero : m = 0
    · subst m
      norm_num
    by_cases hone : m = 1
    · subst m
      norm_num
    have hm2 : 2 ≤ m := by omega
    have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hprod := mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) - 1 by linarith)
      (show (0 : ℝ) ≤ (m : ℝ) - 2 by linarith)
    nlinarith
  · nlinarith [sq_nonneg (m : ℝ)]

/-- A canonical binary row slack is one exactly for an empty row. -/
def rowSlack (m : ℕ) : ℝ := if m = 0 then 1 else 0

theorem rowSlack_binary (m : ℕ) : rowSlack m = 0 ∨ rowSlack m = 1 := by
  unfold rowSlack
  split_ifs <;> simp

theorem rowSlack_residual (m : ℕ) :
    ((m : ℝ) + rowSlack m - 1) ^ 2 = ((m - 1 : ℕ) : ℝ) ^ 2 := by
  cases m with
  | zero => norm_num [rowSlack]
  | succ m => simp [rowSlack, Nat.cast_add, Nat.cast_one]

theorem rowSlack_minimizes (m : ℕ) (t : ℝ) (ht : t = 0 ∨ t = 1) :
    ((m : ℝ) + rowSlack m - 1) ^ 2 ≤ ((m : ℝ) + t - 1) ^ 2 := by
  cases m with
  | zero => simp [rowSlack]; positivity
  | succ m =>
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rcases ht with rfl | rfl <;> simp [rowSlack, Nat.cast_add, Nat.cast_one] <;>
      nlinarith

theorem rowSlack_zero_of_atMostOne (m : ℕ) (hm : m ≤ 1) :
    ((m : ℝ) + rowSlack m - 1) ^ 2 = 0 := by
  rw [rowSlack_residual]
  have h : m - 1 = 0 := Nat.sub_eq_zero_of_le hm
  simp [h]

abbrev EdgeIndex {n : ℕ} (G : Graph n) (k : ℕ) :=
  {e : Fin n × Fin n // e ∈ G.edges} × Fin k

/-- Exactly the source's binary x,s,t domains, represented by selected slots
and Boolean edge/vertex slack arrays. -/
abbrev LState {n : ℕ} (G : Graph n) (k : ℕ) :=
  Finset (Slot n k) × (EdgeIndex G k → Bool) × (Fin n → Bool)

def boolValue (b : Bool) : ℝ := if b = true then 1 else 0

theorem boolValue_binary (b : Bool) : boolValue b = 0 ∨ boolValue b = 1 := by
  cases b <;> simp [boolValue]

def edgeResidual {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (s : EdgeIndex G k → Bool) (er : EdgeIndex G k) : ℝ :=
  flag S er.1.val.1 er.2 + flag S er.1.val.2 er.2 + boolValue (s er) - 1

def edgePenalty {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (s : EdgeIndex G k → Bool) : ℝ := ∑ er, edgeResidual G S s er ^ 2

def vertexPenalty {n k : ℕ} (S : Finset (Slot n k)) (t : Fin n → Bool) : ℝ :=
  ∑ i, ((∑ r, flag S i r) + boolValue (t i) - 1) ^ 2

def lScore {n : ℕ} {k : ℕ} (G : Graph n) (c1 c2 : ℝ) (z : LState G k) : ℝ :=
  (∑ i, ∑ r, flag z.1 i r ^ 2) - c1 * edgePenalty G z.1 z.2.1 -
    c2 * vertexPenalty z.1 z.2.2

def canonicalEdgeSlack {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (er : EdgeIndex G k) : Bool :=
  decide ((er.1.val.1, er.2) ∉ S ∧ (er.1.val.2, er.2) ∉ S)

def canonicalVertexSlack {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) : Bool :=
  decide (rowCount S i = 0)

def canonicalLift {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) : LState G k :=
  (S, canonicalEdgeSlack G S, canonicalVertexSlack S)

@[simp] theorem canonicalLift_selection {n k : ℕ} (G : Graph n)
    (S : Finset (Slot n k)) : (canonicalLift G S).1 = S := rfl

theorem canonicalEdge_residual_product {n k : ℕ} (G : Graph n)
    (S : Finset (Slot n k)) (er : EdgeIndex G k) :
    edgeResidual G S (canonicalEdgeSlack G S) er ^ 2 =
      flag S er.1.val.1 er.2 * flag S er.1.val.2 er.2 := by
  by_cases hi : (er.1.val.1, er.2) ∈ S <;>
    by_cases hj : (er.1.val.2, er.2) ∈ S <;>
      simp [edgeResidual, canonicalEdgeSlack, boolValue, flag, hi, hj]

theorem canonicalVertex_value {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) :
    boolValue (canonicalVertexSlack S i) = rowSlack (rowCount S i) := by
  simp [boolValue, canonicalVertexSlack, rowSlack]

def qLinear {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) : ℝ :=
  finiteMax (lScore (k := k) G c1 c2)

theorem le_qLinear {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (z : LState G k) :
    lScore G c1 c2 z ≤ qLinear G k c1 c2 := le_finiteMax _ z

theorem qLinear_attained {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) :
    ∃ z : LState G k, lScore G c1 c2 z = qLinear G k c1 c2 := finiteMax_attained _

def IsLMax {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (z : LState G k) : Prop :=
  ∀ w : LState G k, lScore G c1 c2 w ≤ lScore G c1 c2 z

theorem isLMax_iff_value {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (z : LState G k) :
    IsLMax G c1 c2 z ↔ lScore G c1 c2 z = qLinear G k c1 c2 := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := qLinear_attained G k c1 c2
    exact le_antisymm (le_qLinear G c1 c2 z) (hw ▸ h w)
  · intro h w
    exact (le_qLinear G c1 c2 w).trans_eq h.symm

theorem edgeIndex_products {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    (∑ er : EdgeIndex G k, flag S er.1.val.1 er.2 * flag S er.1.val.2 er.2) =
      edgeProducts G S := by
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_subtype G.edges (fun _ => Iff.rfl)
    (fun e => ∑ r, flag S e.1 r * flag S e.2 r)).symm

theorem edgePenalty_lower {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (s : EdgeIndex G k → Bool) : edgeProducts G S ≤ edgePenalty G S s := by
  rw [← edgeIndex_products G S]
  apply Finset.sum_le_sum
  intro er _
  exact Chapter09.edge_slack_lower_bound _ _ _ (flag_binary S _ _)
    (flag_binary S _ _) (boolValue_binary (s er))

theorem edgePenalty_canonical {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    edgePenalty G S (canonicalEdgeSlack G S) = edgeProducts G S := by
  simp only [edgePenalty, canonicalEdge_residual_product]
  exact edgeIndex_products G S

theorem vertexPenalty_lower {n k : ℕ} (S : Finset (Slot n k)) (t : Fin n → Bool) :
    (∑ i, (rowCount S i : ℝ) * ((rowCount S i : ℝ) - 1) / 2) ≤
      vertexPenalty S t := by
  apply Finset.sum_le_sum
  intro i _
  rw [← rowCount_sum_flag]
  exact row_slack_pair_bound _ _ (boolValue_binary (t i))

theorem vertexPenalty_canonical {n k : ℕ} (S : Finset (Slot n k)) :
    vertexPenalty S (canonicalVertexSlack S) =
      ∑ i, ((rowCount S i - 1 : ℕ) : ℝ) ^ 2 := by
  simp only [vertexPenalty, ← rowCount_sum_flag, canonicalVertex_value, rowSlack_residual]

/-- Exact score of the canonical source slack assignment. -/
theorem lScore_canonical {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (S : Finset (Slot n k)) :
    lScore G c1 c2 (canonicalLift G S) = (S.card : ℝ) - c1 * edgeProducts G S -
      c2 * ∑ i, ((rowCount S i - 1 : ℕ) : ℝ) ^ 2 := by
  change reward S - c1 * edgePenalty G S (canonicalEdgeSlack G S) -
    c2 * vertexPenalty S (canonicalVertexSlack S) = _
  rw [reward_eq_card, edgePenalty_canonical, vertexPenalty_canonical]

theorem lScore_canonical_feasible {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (S : Finset (Slot n k)) (hS : Feasible G S) :
    lScore G c1 c2 (canonicalLift G S) = (S.card : ℝ) := by
  have he : edgeProducts G S = 0 := by
    have h := feasible_uScore G 1 0 S hS
    rw [uScore_eq_counts] at h
    linarith
  have hr : (∑ i, ((rowCount S i - 1 : ℕ) : ℝ) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [Nat.sub_eq_zero_of_le (feasible_rowCount G S hS i)]
  rw [lScore_canonical, he, hr]
  ring

theorem lScore_le_uScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (z : LState G k) :
    lScore G c1 c2 z ≤ uScore G c1 c2 z.1 := by
  have he := mul_le_mul_of_nonneg_left (edgePenalty_lower G z.1 z.2.1) hc1
  have hr := mul_le_mul_of_nonneg_left (vertexPenalty_lower z.1 z.2.2) hc2
  change reward z.1 - c1 * edgePenalty G z.1 z.2.1 - c2 * vertexPenalty z.1 z.2.2 ≤ _
  rw [reward_eq_card, uScore_eq_counts]
  linarith

theorem alpha_le_qLinear {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) :
    alpha G k ≤ qLinear G k c1 c2 := by
  obtain ⟨S, hS, he⟩ := alpha_attained G k
  have h := le_qLinear G c1 c2 (canonicalLift G S)
  rwa [lScore_canonical_feasible G c1 c2 S hS, he] at h

theorem lScore_le_alpha {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) (z : LState G k) :
    lScore G c1 c2 z ≤ alpha G k := by
  have hb := Chapter09.weighted_repair_bound (conflictPairs G k) (weight c1 c2)
    (weight_ge_one G c1 c2 hc1 hc2) z.1
  exact (lScore_le_uScore G c1 c2 (by linarith) (by linarith) z).trans
    (hb.trans (card_le_alpha G _ (Chapter09.repair_feasible _ _)))

theorem qLinear_eq_alpha {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) : qLinear G k c1 c2 = alpha G k := by
  obtain ⟨z, hz⟩ := qLinear_attained G k c1 c2
  exact le_antisymm (hz ▸ lScore_le_alpha G c1 c2 hc1 hc2 z)
    (alpha_le_qLinear G k c1 c2)

theorem linear_optimizer_feasible {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 < c1) (hc2 : 1 < c2) (z : LState G k) (hz : IsLMax G c1 c2 z) :
    Feasible G z.1 := by
  by_contra hbad
  have hb := Chapter09.strict_weighted_repair_bound (conflictPairs G k) (weight c1 c2)
    (weight_gt_one G c1 c2 hc1 hc2) z.1 hbad
  have hd := lScore_le_uScore G c1 c2 (by linarith) (by linarith) z
  have hm := hz (canonicalLift G (Chapter09.repair (conflictPairs G k) z.1))
  rw [lScore_canonical_feasible G c1 c2 _ (Chapter09.repair_feasible _ _)] at hm
  exact (not_lt_of_ge hm) (lt_of_le_of_lt hd hb)

theorem linear_optimizer_optimal {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 < c1) (hc2 : 1 < c2) (z : LState G k) (hz : IsLMax G c1 c2 z) :
    Feasible G z.1 ∧ (z.1.card : ℝ) = alpha G k := by
  have hf := linear_optimizer_feasible G c1 c2 hc1 hc2 z hz
  have he := (isLMax_iff_value G c1 c2 z).mp hz
  rw [qLinear_eq_alpha G k c1 c2 hc1.le hc2.le] at he
  have hd := lScore_le_uScore G c1 c2 (by linarith) (by linarith) z
  rw [feasible_uScore G c1 c2 z.1 hf, he] at hd
  exact ⟨hf, le_antisymm (card_le_alpha G z.1 hf) hd⟩

theorem vertexPenalty_canonical_minimizes {n k : ℕ} (S : Finset (Slot n k))
    (t : Fin n → Bool) :
    vertexPenalty S (canonicalVertexSlack S) ≤ vertexPenalty S t := by
  apply Finset.sum_le_sum
  intro i _
  simp only [← rowCount_sum_flag, canonicalVertex_value]
  exact rowSlack_minimizes _ _ (boolValue_binary (t i))

/-- For nonnegative penalties the displayed binary lift really maximizes over
all source slack arrays, including noncanonical slack assignments. -/
theorem canonicalLift_maximizes_slacks {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (z : LState G k) :
    lScore G c1 c2 z ≤ lScore G c1 c2 (canonicalLift G z.1) := by
  have he := edgePenalty_lower G z.1 z.2.1
  rw [← edgePenalty_canonical G z.1] at he
  have he' := mul_le_mul_of_nonneg_left he hc1
  have hv := mul_le_mul_of_nonneg_left
    (vertexPenalty_canonical_minimizes z.1 z.2.2) hc2
  unfold lScore canonicalLift
  dsimp
  linarith

theorem rowSlack_pair_eq_of_le_two (m : ℕ) (hm : m ≤ 2) :
    ((m - 1 : ℕ) : ℝ)^2 = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  interval_cases m <;> norm_num

/-- On the sharpness witnesses every row has at most two active colors. Only
on that domain is the optimized linear score the unordered pair score. -/
theorem lScore_canonical_rowCount_le_two {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (S : Finset (Slot n k)) (hS : ∀ i, rowCount S i ≤ 2) :
    lScore G c1 c2 (canonicalLift G S) = uScore G c1 c2 S := by
  rw [lScore_canonical, uScore_eq_counts]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact rowSlack_pair_eq_of_le_two _ (hS i)

theorem lScore_one_color_le_alpha {n : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 0 ≤ c2) (z : LState G 1) :
    lScore G c1 c2 z ≤ alpha G 1 := by
  have hb := Chapter09.weighted_repair_bound (conflictPairs G 1) (weight c1 c2)
    (weight_ge_one_k1 G c1 c2 hc1) z.1
  exact (lScore_le_uScore G c1 c2 (by linarith) hc2 z).trans
    (hb.trans (card_le_alpha G _ (Chapter09.repair_feasible _ _)))

/-- Unlike the nonlinear objective, arbitrary binary row slacks still occur
at k=1, so nonnegativity of their coefficient is retained. -/
theorem qLinear_one_color {n : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 0 ≤ c2) : qLinear G 1 c1 c2 = alpha G 1 := by
  obtain ⟨z, hz⟩ := qLinear_attained G 1 c1 c2
  exact le_antisymm (hz ▸ lScore_one_color_le_alpha G c1 c2 hc1 hc2 z)
    (alpha_le_qLinear G 1 c1 c2)

theorem linear_one_color_strict {n : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 < c1) (hc2 : 0 ≤ c2) (z : LState G 1) (hz : IsLMax G c1 c2 z) :
    Feasible G z.1 ∧ (z.1.card : ℝ) = alpha G 1 := by
  have hf : Feasible G z.1 := by
    by_contra hbad
    have hb := Chapter09.strict_weighted_repair_bound (conflictPairs G 1) (weight c1 c2)
      (weight_gt_one_k1 G c1 c2 hc1) z.1 hbad
    have hd := lScore_le_uScore G c1 c2 (by linarith) hc2 z
    have hm := hz (canonicalLift G (Chapter09.repair (conflictPairs G 1) z.1))
    rw [lScore_canonical_feasible G c1 c2 _ (Chapter09.repair_feasible _ _)] at hm
    exact (not_lt_of_ge hm) (lt_of_le_of_lt hd hb)
  have he := (isLMax_iff_value G c1 c2 z).mp hz
  rw [qLinear_one_color G c1 c2 hc1.le hc2] at he
  have hd := lScore_le_uScore G c1 c2 (by linarith) hc2 z
  rw [feasible_uScore G c1 c2 z.1 hf, he] at hd
  exact ⟨hf, le_antisymm (card_le_alpha G z.1 hf) hd⟩

/-- Source Theorem9.3.1, including the joint binary slack optimization domain. -/
theorem theorem_9_3_1 {n k : ℕ} (G : Graph n) (_hk : 0 < k) (c1 c2 : ℝ)
    (hc1 : 1 < c1) (hc2 : 1 < c2) :
    qLinear G k c1 c2 = alpha G k ∧
    ∀ z : LState G k, IsLMax G c1 c2 z →
      Feasible G z.1 ∧ (z.1.card : ℝ) = alpha G k :=
  ⟨qLinear_eq_alpha G k c1 c2 hc1.le hc2.le,
    fun z hz => linear_optimizer_optimal G c1 c2 hc1 hc2 z hz⟩

def BinaryValues {α : Type*} (f : α → ℝ) : Prop := ∀ a, f a = 0 ∨ f a = 1

def realBool (v : ℝ) : Bool := decide (v = 1)

theorem boolValue_realBool (v : ℝ) (hv : v = 0 ∨ v = 1) :
    boolValue (realBool v) = v := by
  rcases hv with rfl | rfl <;> norm_num [realBool, boolValue]

/-- The literal source objective on real-valued x,s,t arrays. Binary domain
restrictions are stated separately rather than built into this formula. -/
def arrayLScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (x : Fin n → Fin k → ℝ) (s : EdgeIndex G k → ℝ) (t : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ r, x i r ^ 2) -
    c1 * (∑ er : EdgeIndex G k, (x er.1.val.1 er.2 + x er.1.val.2 er.2 + s er - 1)^2) -
    c2 * (∑ i, ((∑ r, x i r) + t i - 1)^2)

def arrayState {n k : ℕ} (G : Graph n) (x : Fin n → Fin k → ℝ)
    (s : EdgeIndex G k → ℝ) (t : Fin n → ℝ) : LState G k :=
  (selected x, fun er => realBool (s er), fun i => realBool (t i))

theorem arrayLScore_of_state {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (z : LState G k) :
    arrayLScore G c1 c2 (flag z.1) (fun er => boolValue (z.2.1 er))
      (fun i => boolValue (z.2.2 i)) = lScore G c1 c2 z := rfl

theorem lScore_arrayState {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (x : Fin n → Fin k → ℝ) (s : EdgeIndex G k → ℝ) (t : Fin n → ℝ)
    (hx : Binary x) (hs : BinaryValues s) (ht : BinaryValues t) :
    lScore G c1 c2 (arrayState G x s t) = arrayLScore G c1 c2 x s t := by
  simp only [lScore, arrayState, edgePenalty, edgeResidual, vertexPenalty,
    flag_selected x hx, boolValue_realBool _ (hs _), boolValue_realBool _ (ht _),
    arrayLScore]

/-- The finite Boolean encoding attains exactly the maximum over all binary
real source arrays. No supplied optimizer or attainment premise is needed. -/
theorem qLinear_binary_maximum {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) :
    ∃ (x : Fin n → Fin k → ℝ) (s : EdgeIndex G k → ℝ) (t : Fin n → ℝ),
      Binary x ∧ BinaryValues s ∧ BinaryValues t ∧
      arrayLScore G c1 c2 x s t = qLinear G k c1 c2 ∧
      ∀ (y : Fin n → Fin k → ℝ) (u : EdgeIndex G k → ℝ) (v : Fin n → ℝ),
        Binary y → BinaryValues u → BinaryValues v →
        arrayLScore G c1 c2 y u v ≤ qLinear G k c1 c2 := by
  obtain ⟨z, hz⟩ := qLinear_attained G k c1 c2
  refine ⟨flag z.1, fun er => boolValue (z.2.1 er), fun i => boolValue (z.2.2 i),
    flag_binary z.1, fun er => boolValue_binary _, fun i => boolValue_binary _, ?_, ?_⟩
  · exact (arrayLScore_of_state G c1 c2 z).trans hz
  · intro y u v hy hu hv
    rw [← lScore_arrayState G c1 c2 y u v hy hu hv]
    exact le_qLinear G c1 c2 _

/-- The actual two-pass source algorithm returns an optimal coloring from any
joint binary maximizer at the weak linear thresholds. -/
theorem algorithm_linear {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (z : LState G k) (hz : IsLMax G c1 c2 z) :
    Feasible G (Sequential.algorithm LE LV z.1) ∧
    lScore G c1 c2 z = ((Sequential.algorithm LE LV z.1).card : ℝ) ∧
    ((Sequential.algorithm LE LV z.1).card : ℝ) = alpha G k := by
  have hf := Sequential.algorithm_feasible G LE LV hE hV z.1
  have hb := Sequential.algorithm_uScore_bound G c1 c2 hc1 hc2 LE LV hs hE hV z.1
  have hd := lScore_le_uScore G c1 c2 (by linarith) (by linarith) z
  have he := (isLMax_iff_value G c1 c2 z).mp hz
  rw [qLinear_eq_alpha G k c1 c2 hc1 hc2] at he
  have hr := card_le_alpha G _ hf
  refine ⟨hf, ?_, ?_⟩ <;> linarith

theorem algorithm_linear_one_color {n : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 0 ≤ c2)
    (LE : List (Slot n 1 × Slot n 1)) (LV : List (Slot n 1))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G 1) (hE : ∀ e ∈ spatialPairs G 1, e ∈ LE)
    (hV : ∀ u : Slot n 1, u ∈ LV) (z : LState G 1) (hz : IsLMax G c1 c2 z) :
    Feasible G (Sequential.algorithm LE LV z.1) ∧
    lScore G c1 c2 z = ((Sequential.algorithm LE LV z.1).card : ℝ) ∧
    ((Sequential.algorithm LE LV z.1).card : ℝ) = alpha G 1 := by
  have hf := Sequential.algorithm_feasible G LE LV hE hV z.1
  have hb := Sequential.algorithm_uScore_bound_k1 G c1 c2 hc1 LE LV hs hE hV z.1
  have hd := lScore_le_uScore G c1 c2 (by linarith) hc2 z
  have he := (isLMax_iff_value G c1 c2 z).mp hz
  rw [qLinear_one_color G c1 c2 hc1 hc2] at he
  have hr := card_le_alpha G _ hf
  refine ⟨hf, ?_, ?_⟩ <;> linarith

theorem corollary_9_3_2 {n k : ℕ} (G : Graph n) (_hk : 0 < k) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) (_hunit : c1 = 1 ∨ c2 = 1)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (z : LState G k) (hz : IsLMax G c1 c2 z) :
    qLinear G k c1 c2 = alpha G k ∧
    Feasible G (Sequential.algorithm LE LV z.1) ∧
    ((Sequential.algorithm LE LV z.1).card : ℝ) = alpha G k := by
  obtain ⟨hf, _, ha⟩ := algorithm_linear G c1 c2 hc1 hc2 LE LV hs hE hV z hz
  exact ⟨qLinear_eq_alpha G k c1 c2 hc1 hc2, hf, ha⟩

end Chapter09.Source

#print axioms Chapter09.Source.row_slack_pair_bound
#print axioms Chapter09.Source.rowSlack_binary
#print axioms Chapter09.Source.rowSlack_residual
#print axioms Chapter09.Source.rowSlack_minimizes
#print axioms Chapter09.Source.rowSlack_zero_of_atMostOne
#print axioms Chapter09.Source.canonicalEdge_residual_product
#print axioms Chapter09.Source.canonicalVertex_value
#print axioms Chapter09.Source.qLinear_attained
#print axioms Chapter09.Source.isLMax_iff_value
#print axioms Chapter09.Source.canonicalLift_maximizes_slacks
#print axioms Chapter09.Source.lScore_canonical_rowCount_le_two
#print axioms Chapter09.Source.qLinear_one_color
#print axioms Chapter09.Source.linear_one_color_strict
#print axioms Chapter09.Source.theorem_9_3_1
#print axioms Chapter09.Source.qLinear_binary_maximum
#print axioms Chapter09.Source.algorithm_linear
#print axioms Chapter09.Source.algorithm_linear_one_color
#print axioms Chapter09.Source.corollary_9_3_2
