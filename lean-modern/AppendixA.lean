module

public import Chapter10

@[expose] public section

/-! Finite graph boundary cut, actual path reachability, and binary auxiliary
linearization. No certificate of the printed master, separator, or solver. -/
noncomputable section
open scoped BigOperators
namespace AppendixA

def adjacent {n : ℕ} (E : Finset (Fin n × Fin n)) (a b : Fin n) : Prop :=
  (a,b) ∈ E ∨ (b,a) ∈ E

def fiberStep {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (a b : Fin n) : Prop := a ∈ S ∧ b ∈ S ∧ adjacent E a b

def connected {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen (fiberStep E S) a b

def boundary {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun b => b ∉ S ∧ ∃ a ∈ S, adjacent E a b)

theorem adjacent_symmetric {n : ℕ} (E : Finset (Fin n × Fin n)) :
    Symmetric (adjacent E) := fun _ _ h => h.symm

theorem boundary_mem {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n)) (b : Fin n) :
    b ∈ boundary E S ↔ b ∉ S ∧ ∃ a ∈ S, adjacent E a b := by
  classical
  simp [boundary]

theorem boundary_disjoint {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n)) :
    Disjoint S (boundary E S) := by
  apply Finset.disjoint_left.mpr
  intro b hb hs
  exact ((boundary_mem E S b).mp hs).1 hb

theorem reach_without_boundary_stays_inside {n : ℕ} (E : Finset (Fin n × Fin n))
    (S T : Finset (Fin n)) (havoid : ∀ v ∈ T, v ∉ boundary E S)
    {a b : Fin n} (ha : a ∈ S) (h : Relation.ReflTransGen (fiberStep E T) a b) :
    b ∈ S ∧ Relation.ReflTransGen (fiberStep E S) a b := by
  induction h with
  | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
  | @tail b c hab hbc ih =>
    have hc : c ∈ S := by
      by_contra hnot
      exact havoid c hbc.2.1 ((boundary_mem E S c).mpr ⟨hnot,b,ih.1,hbc.2.2⟩)
    exact ⟨hc, ih.2.tail ⟨ih.1,hc,hbc.2.2⟩⟩

theorem connected_subset_without_boundary {n : ℕ} (E : Finset (Fin n × Fin n))
    (S T : Finset (Fin n)) (hsub : S ⊆ T) (hconn : connected E T)
    (havoid : ∀ v ∈ T, v ∉ boundary E S) : connected E S := by
  intro a ha b hb
  exact (reach_without_boundary_stays_inside E S T havoid ha (hconn a (hsub ha) b (hsub hb))).2

theorem disconnected_subset_requires_boundary {n : ℕ} (E : Finset (Fin n × Fin n))
    (S T : Finset (Fin n)) (hbad : ¬ connected E S) (hconn : connected E T)
    (hsub : S ⊆ T) : (boundary E S ∩ T).Nonempty := by
  by_contra hnone
  apply hbad
  apply connected_subset_without_boundary E S T hsub hconn
  intro v hv hboundary
  exact hnone ⟨v,Finset.mem_inter.mpr ⟨hboundary,hv⟩⟩

theorem boundary_cut_valid {n : ℕ} (E : Finset (Fin n × Fin n)) (S T : Finset (Fin n))
    (hbad : ¬ connected E S) (hconn : connected E T) :
    1 ≤ S.card - (S ∩ T).card + (boundary E S ∩ T).card := by
  by_cases hsub : S ⊆ T
  · have hpos := (disconnected_subset_requires_boundary E S T hbad hconn hsub).card_pos
    omega
  · have hproper : S ∩ T ⊂ S := by
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro hreverse
      apply hsub
      intro v hv
      exact (Finset.mem_inter.mp (hreverse hv)).2
    have hlt := Finset.card_lt_card hproper
    omega

theorem real_boundary_cut_valid {n : ℕ} (E : Finset (Fin n × Fin n)) (S T : Finset (Fin n))
    (hbad : ¬ connected E S) (hconn : connected E T) :
    (1 : ℝ) ≤ (S.card : ℝ) - ((S ∩ T).card : ℝ) + ((boundary E S ∩ T).card : ℝ) := by
  have h := boundary_cut_valid E S T hbad hconn
  have hle := Finset.card_le_card (Finset.inter_subset_left : S ∩ T ⊆ S)
  have hc : (1 : ℝ) ≤ ((S.card - (S ∩ T).card + (boundary E S ∩ T).card : ℕ) : ℝ) := by exact_mod_cast h
  simpa only [Nat.cast_add, Nat.cast_sub hle] using hc

theorem boundary_cut_rejects_current {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n)) :
    S.card - (S ∩ S).card + (boundary E S ∩ S).card = 0 := by
  have hd := boundary_disjoint E S
  rw [Finset.inter_self, Finset.disjoint_iff_inter_eq_empty.mp hd.symm]
  simp

theorem selected_sum_is_intersection_card {n : ℕ} (S T : Finset (Fin n)) :
    (∑ v ∈ S, if v ∈ T then (1 : ℕ) else 0) = (S ∩ T).card := by
  have heq : S.filter (fun v => v ∈ T) = S ∩ T := by ext v; simp
  rw [← heq, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem binary_product_linearization (a b g : Bool) :
    (Chapter10.bit g ≤ Chapter10.bit a ∧ Chapter10.bit g ≤ Chapter10.bit b ∧
      Chapter10.bit a + Chapter10.bit b - 1 ≤ Chapter10.bit g) ↔
    Chapter10.bit g = Chapter10.bit a * Chapter10.bit b := by
  cases a <;> cases b <;> cases g <;> norm_num [Chapter10.bit]

def natbit (b : Bool) : ℕ := if b then 1 else 0

theorem natbit_ge_one (b : Bool) : 1 ≤ natbit b ↔ b = true := by
  cases b <;> decide

theorem repaired_finite_and_linearization {n : ℕ} (S : Finset (Fin n))
    (f : Fin n → Bool) (g : Bool) :
    ((∀ i ∈ S, natbit g ≤ natbit (f i)) ∧
      (S.filter (fun i => f i = true)).card + 1 ≤ S.card + natbit g) ↔
    (g = true ↔ ∀ i ∈ S, f i = true) := by
  have hle := Finset.card_filter_le S (fun i => f i = true)
  have heq : (S.filter (fun i => f i = true)).card = S.card ↔ ∀ i ∈ S, f i = true :=
    Finset.card_filter_eq_iff
  have hlt : (S.filter (fun i => f i = true)).card + 1 ≤ S.card ↔ ¬ ∀ i ∈ S, f i = true := by
    constructor
    · intro h ha
      have hh := heq.mpr ha
      omega
    · intro ha
      have hn : (S.filter (fun i => f i = true)).card ≠ S.card := fun hh => ha (heq.mp hh)
      omega
  cases g
  · simpa [natbit] using hlt
  · change ((∀ i ∈ S, 1 ≤ natbit (f i)) ∧
      (S.filter (fun i => f i = true)).card + 1 ≤ S.card + 1) ↔
      (true = true ↔ ∀ i ∈ S, f i = true)
    constructor
    · rintro ⟨hu,_⟩
      exact ⟨fun _ i hi => (natbit_ge_one (f i)).mp (hu i hi), fun _ => rfl⟩
    · intro h
      exact ⟨fun i hi => (natbit_ge_one (f i)).mpr (h.mp rfl i hi), by omega⟩

theorem printed_gamma_short_path_witness :
    (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≥ 1 - (3-1) + 1 ∧ (0 : ℝ) ≠ 1 := by norm_num

theorem printed_gamma_empty_path_witness :
    (0 : ℝ) ≥ 1 - (2-1) ∧ (0 : ℝ) ≠ 1 := by norm_num

theorem upper_fiber_row_allows_no_path : (1 : ℝ) + 1 + (0-1) ≤ 2 := by norm_num

theorem combined_selected_path_rows (q : ℝ) :
    ((1 : ℝ) + 1 + (q-1) ≤ 2 ∧ (1 : ℝ) + 1 - q ≤ 1) ↔ q = 1 := by
  constructor
  · intro h; linarith [h.1,h.2]
  · rintro rfl; norm_num

theorem binary_aggregated_link (a b z : Bool) :
    ((2 : ℝ) * Chapter10.bit z ≤ Chapter10.bit a + Chapter10.bit b) ↔
    (Chapter10.bit z ≤ Chapter10.bit a ∧ Chapter10.bit z ≤ Chapter10.bit b) := by
  cases a <;> cases b <;> cases z <;> norm_num [Chapter10.bit]

theorem square_zero_has_one_root (x : ℝ) : x^2 = 0 ↔ x = 0 := by constructor <;> intro h <;> nlinarith [sq_nonneg x]

theorem integer_square_slack_misses_three : ¬ ∃ d : ℤ, 3 = 1 + d^2 := by
  rintro ⟨d,hd⟩
  have hbound : -2 < d ∧ d < 2 := by constructor <;> nlinarith [sq_nonneg (d+2),sq_nonneg (d-2)]
  obtain ⟨hlo,hhi⟩ := hbound
  interval_cases d <;> norm_num at hd

end AppendixA

#print axioms AppendixA.adjacent_symmetric
#print axioms AppendixA.boundary_mem
#print axioms AppendixA.boundary_disjoint
#print axioms AppendixA.reach_without_boundary_stays_inside
#print axioms AppendixA.connected_subset_without_boundary
#print axioms AppendixA.disconnected_subset_requires_boundary
#print axioms AppendixA.boundary_cut_valid
#print axioms AppendixA.real_boundary_cut_valid
#print axioms AppendixA.boundary_cut_rejects_current
#print axioms AppendixA.selected_sum_is_intersection_card
#print axioms AppendixA.binary_product_linearization
#print axioms AppendixA.natbit_ge_one
#print axioms AppendixA.repaired_finite_and_linearization
#print axioms AppendixA.printed_gamma_short_path_witness
#print axioms AppendixA.printed_gamma_empty_path_witness
#print axioms AppendixA.upper_fiber_row_allows_no_path
#print axioms AppendixA.combined_selected_path_rows
#print axioms AppendixA.binary_aggregated_link
#print axioms AppendixA.square_zero_has_one_root
#print axioms AppendixA.integer_square_slack_misses_three
