module

public import Mathlib.Tactic

@[expose] public section

/-! Chapter9: a finite weighted conflict model with constructive optimum repair,
and literal arithmetic diagnostics. This is not a quantum-device certificate.
The source's vertex/color-slot lift is described separately, not silently assumed.
-/
noncomputable section
open scoped BigOperators
namespace Chapter09

variable {α : Type*} [DecidableEq α]

def conflicts (E : Finset (α × α)) (S : Finset α) : Finset (α × α) :=
  E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)

def feasible (E : Finset (α × α)) (S : Finset α) : Prop :=
  ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)

def score (E : Finset (α × α)) (w : α × α → ℝ) (S : Finset α) : ℝ :=
  (S.card : ℝ) - ∑ e ∈ conflicts E S, w e

def cover (E : Finset (α × α)) (S : Finset α) : Finset α :=
  (conflicts E S).image Prod.fst

def repair (E : Finset (α × α)) (S : Finset α) : Finset α :=
  S \ cover E S

theorem conflicts_empty_iff (E : Finset (α × α)) (S : Finset α) :
    conflicts E S = ∅ ↔ feasible E S := by
  simp only [conflicts, feasible, Finset.filter_eq_empty_iff]

theorem cover_subset (E : Finset (α × α)) (S : Finset α) : cover E S ⊆ S := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  exact (Finset.mem_filter.mp he).2.1

theorem repair_subset (E : Finset (α × α)) (S : Finset α) : repair E S ⊆ S :=
  Finset.sdiff_subset

theorem repair_feasible (E : Finset (α × α)) (S : Finset α) :
    feasible E (repair E S) := by
  intro e he hboth
  have h1 := Finset.mem_sdiff.mp hboth.1
  have h2 := Finset.mem_sdiff.mp hboth.2
  have hec : e ∈ conflicts E S := Finset.mem_filter.mpr ⟨he, h1.1, h2.1⟩
  exact h1.2 (Finset.mem_image.mpr ⟨e, hec, rfl⟩)

theorem feasible_score (E : Finset (α × α)) (w : α × α → ℝ) (S : Finset α)
    (h : feasible E S) : score E w S = (S.card : ℝ) := by
  simp [score, (conflicts_empty_iff E S).mpr h]

theorem weighted_repair_bound (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 ≤ w e) (S : Finset α) :
    score E w S ≤ ((repair E S).card : ℝ) := by
  have hweights : ((conflicts E S).card : ℝ) ≤ ∑ e ∈ conflicts E S, w e := by
    calc
      ((conflicts E S).card : ℝ) = ∑ _e ∈ conflicts E S, (1 : ℝ) := by simp
      _ ≤ ∑ e ∈ conflicts E S, w e := Finset.sum_le_sum (fun e he => hw e (Finset.mem_filter.mp he).1)
  have hcover : ((cover E S).card : ℝ) ≤ ((conflicts E S).card : ℝ) := by
    exact_mod_cast (Finset.card_image_le : (cover E S).card ≤ (conflicts E S).card)
  have hcard : ((repair E S).card : ℝ) + ((cover E S).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (cover_subset E S)
  unfold score
  linarith

theorem strict_weighted_repair_bound (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 < w e) (S : Finset α) (hbad : ¬ feasible E S) :
    score E w S < ((repair E S).card : ℝ) := by
  have hne : (conflicts E S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hz
    exact hbad ((conflicts_empty_iff E S).mp hz)
  obtain ⟨e, he⟩ := hne
  have hweights : ((conflicts E S).card : ℝ) < ∑ e ∈ conflicts E S, w e := by
    calc
      ((conflicts E S).card : ℝ) = ∑ _e ∈ conflicts E S, (1 : ℝ) := by simp
      _ < ∑ e ∈ conflicts E S, w e := Finset.sum_lt_sum
        (fun j hj => (hw j (Finset.mem_filter.mp hj).1).le)
        ⟨e, he, hw e (Finset.mem_filter.mp he).1⟩
  have hcover : ((cover E S).card : ℝ) ≤ ((conflicts E S).card : ℝ) := by
    exact_mod_cast (Finset.card_image_le : (cover E S).card ≤ (conflicts E S).card)
  have hcard : ((repair E S).card : ℝ) + ((cover E S).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (cover_subset E S)
  unfold score
  linarith

def isScoreMax (E : Finset (α × α)) (w : α × α → ℝ) (S : Finset α) : Prop :=
  ∀ T : Finset α, score E w T ≤ score E w S

theorem weak_penalty_optimum_repair (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 ≤ w e) (S : Finset α) (hmax : isScoreMax E w S) :
    feasible E (repair E S) ∧
    score E w S = ((repair E S).card : ℝ) ∧
    ∀ T : Finset α, feasible E T → (T.card : ℝ) ≤ ((repair E S).card : ℝ) := by
  have hf := repair_feasible E S
  have hr := feasible_score E w (repair E S) hf
  have heq : score E w S = ((repair E S).card : ℝ) :=
    le_antisymm (weighted_repair_bound E w hw S) (by simpa [hr] using hmax (repair E S))
  refine ⟨hf, heq, ?_⟩
  intro T ht
  simpa [feasible_score E w T ht, heq] using hmax T

theorem strict_penalty_optimizer_feasible (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 < w e) (S : Finset α) (hmax : isScoreMax E w S) :
    feasible E S ∧ ∀ T : Finset α, feasible E T → (T.card : ℝ) ≤ (S.card : ℝ) := by
  have hf : feasible E S := by
    by_contra hbad
    have hb := strict_weighted_repair_bound E w hw S hbad
    have hr := feasible_score E w (repair E S) (repair_feasible E S)
    have hm := hmax (repair E S)
    rw [hr] at hm
    linarith
  refine ⟨hf, ?_⟩
  intro T ht
  simpa [feasible_score E w T ht, feasible_score E w S hf] using hmax T

def orderedColorPenalty {V : Type*} [Fintype V] (k : ℕ) (x : V → Fin k → ℝ) : ℝ :=
  ∑ i, ∑ r, ∑ p, if p ≠ r then x i r * x i p else 0

theorem one_color_penalty_zero {V : Type*} [Fintype V] (x : V → Fin 1 → ℝ) :
    orderedColorPenalty 1 x = 0 := by
  simp [orderedColorPenalty, Fin.eq_zero]

theorem two_color_ordered_factor (a b : ℝ) : a * b + b * a = 2 * a * b := by ring

theorem ordered_delete_factor_witness :
    ((1 : ℝ) * 1 + 1 * 1) - (0 * 1 + 1 * 0) = 2 ∧ (2 : ℝ) ≠ 1 := by norm_num

theorem effective_color_threshold (c : ℝ) : 1 ≤ 2 * c ↔ (1 / 2 : ℝ) ≤ c := by constructor <;> intro h <;> linarith

theorem binary_pair_equivalence (a b : ℝ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a + b ≤ 1 ↔ a * b = 0 := by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem canonical_edge_slack (a b : ℝ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    ∃ s : ℝ, (s = 0 ∨ s = 1) ∧ (a + b + s - 1)^2 = a * b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact ⟨1, Or.inr rfl, by norm_num⟩
  · exact ⟨0, Or.inl rfl, by norm_num⟩
  · exact ⟨0, Or.inl rfl, by norm_num⟩
  · exact ⟨0, Or.inl rfl, by norm_num⟩

theorem edge_slack_lower_bound (a b s : ℝ) (ha : a = 0 ∨ a = 1)
    (hb : b = 0 ∨ b = 1) (hs : s = 0 ∨ s = 1) : a * b ≤ (a + b + s - 1)^2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num

theorem unit_edge_infeasible_tie : (2 : ℝ) - 1 = 1 := by norm_num

theorem subunit_edge_value_failure (c : ℝ) (hc : c < 1) : (1 : ℝ) < 2 - c := by linarith

theorem color_double_assignment_threshold (c : ℝ) : (2 : ℝ) - 2 * c ≤ 1 ↔ (1 / 2 : ℝ) ≤ c := by
  constructor <;> intro h <;> linarith

theorem literal_clique_minimum_sign_witness : (-2 : ℝ) ≠ 2 := by norm_num

theorem maxcut_wrong_matrix_witness :
    (-3 : ℝ) < -6 + 4 ∧ (3 : ℝ) < 4 := by norm_num

theorem complete_four_wrong_energy_minimum (m : Fin 5) :
    (-3 : ℝ) ≤ -3 * (m.val : ℝ) + 2 * (m.val : ℝ) * ((m.val : ℝ) - 1) := by
  fin_cases m <;> norm_num

theorem complete_four_cut_maximum (m : Fin 5) :
    (m.val : ℝ) * (4 - (m.val : ℝ)) ≤ 4 := by
  fin_cases m <;> norm_num

theorem linear_auxiliary_count (n m k : ℕ) : n*k + m*k + n = k*(n+m+1) + n - k := by
  have h : n*k + m*k + n + k = k*(n+m+1) + n := by ring
  omega

theorem printed_auxiliary_count_witness : (5*2 + 3*2 + 5 : ℕ) ≠ 2*(5+3+1) := by norm_num

theorem confidence_four_runs_insufficient : (1 : ℝ) - (1/2)^4 < 95/100 := by norm_num

theorem confidence_five_runs_sufficient : (95/100 : ℝ) ≤ 1 - (1/2)^5 := by norm_num

end Chapter09

#print axioms Chapter09.conflicts_empty_iff
#print axioms Chapter09.cover_subset
#print axioms Chapter09.repair_subset
#print axioms Chapter09.repair_feasible
#print axioms Chapter09.feasible_score
#print axioms Chapter09.weighted_repair_bound
#print axioms Chapter09.strict_weighted_repair_bound
#print axioms Chapter09.weak_penalty_optimum_repair
#print axioms Chapter09.strict_penalty_optimizer_feasible
#print axioms Chapter09.one_color_penalty_zero
#print axioms Chapter09.two_color_ordered_factor
#print axioms Chapter09.ordered_delete_factor_witness
#print axioms Chapter09.effective_color_threshold
#print axioms Chapter09.binary_pair_equivalence
#print axioms Chapter09.canonical_edge_slack
#print axioms Chapter09.edge_slack_lower_bound
#print axioms Chapter09.unit_edge_infeasible_tie
#print axioms Chapter09.subunit_edge_value_failure
#print axioms Chapter09.color_double_assignment_threshold
#print axioms Chapter09.literal_clique_minimum_sign_witness
#print axioms Chapter09.maxcut_wrong_matrix_witness

#print axioms Chapter09.complete_four_wrong_energy_minimum
#print axioms Chapter09.complete_four_cut_maximum

#print axioms Chapter09.linear_auxiliary_count
#print axioms Chapter09.printed_auxiliary_count_witness
#print axioms Chapter09.confidence_four_runs_insufficient
#print axioms Chapter09.confidence_five_runs_sufficient
