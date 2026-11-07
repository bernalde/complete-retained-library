module

public import Chapter10QUBOAlgebra

@[expose] public section

/-! Local affine inventory windows only: no global chronological or horizon
feasibility claim. Natural p denotes completed visits; zero rate is excluded. -/
noncomputable section
namespace Chapter10.Inventory

def supplyOpening (I₀ C Q r : ℝ) (p : ℕ) : ℝ := (Q + p * Q - I₀) / r
def supplyClosing (I₀ C Q r : ℝ) (p : ℕ) : ℝ := (C + p * Q - I₀) / r
def demandOpening (I₀ C Q r : ℝ) (p : ℕ) : ℝ := (C - Q - p * Q - I₀) / r
def demandClosing (I₀ C Q r : ℝ) (p : ℕ) : ℝ := (-p * Q - I₀) / r

theorem supply_window_iff (I₀ C Q r t : ℝ) (p : ℕ) (hr : 0 < r) :
    (supplyOpening I₀ C Q r p ≤ t ∧ t ≤ supplyClosing I₀ C Q r p) ↔
      (Q ≤ I₀ + t * r - p * Q ∧ I₀ + t * r - p * Q ≤ C) := by
  unfold supplyOpening supplyClosing
  rw [div_le_iff₀ hr, le_div_iff₀ hr]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem demand_window_iff (I₀ C Q r t : ℝ) (p : ℕ) (hr : r < 0) :
    (demandOpening I₀ C Q r p ≤ t ∧ t ≤ demandClosing I₀ C Q r p) ↔
      (0 ≤ I₀ + t * r + p * Q ∧ I₀ + t * r + p * Q ≤ C - Q) := by
  unfold demandOpening demandClosing
  rw [div_le_iff_of_neg hr, le_div_iff_of_neg hr]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem supply_window_nonempty (I₀ C Q r : ℝ) (p : ℕ) (hr : 0 < r) (hC : Q ≤ C) :
    supplyOpening I₀ C Q r p ≤ supplyClosing I₀ C Q r p := by
  unfold supplyOpening supplyClosing
  exact (div_le_div_iff_of_pos_right hr).2 (by linarith)

theorem demand_window_nonempty (I₀ C Q r : ℝ) (p : ℕ) (hr : r < 0) (hC : Q ≤ C) :
    demandOpening I₀ C Q r p ≤ demandClosing I₀ C Q r p := by
  unfold demandOpening demandClosing
  exact (div_le_div_right_of_neg hr).2 (by linarith)

theorem supply_capacity_equal (I₀ Q r : ℝ) (p : ℕ) :
    supplyOpening I₀ Q Q r p = supplyClosing I₀ Q Q r p := rfl

theorem demand_capacity_equal (I₀ Q r : ℝ) (p : ℕ) :
    demandOpening I₀ Q Q r p = demandClosing I₀ Q Q r p := by
  simp [demandOpening, demandClosing]

theorem window_subset_horizon_iff (a b H : ℝ) (hab : a ≤ b) :
    Set.Icc a b ⊆ Set.Icc 0 H ↔ 0 ≤ a ∧ b ≤ H := by
  constructor
  · intro h
    exact ⟨(h ⟨le_rfl, hab⟩).1, (h ⟨hab, le_rfl⟩).2⟩
  · rintro ⟨ha, hb⟩ t ⟨hat, htb⟩
    exact ⟨ha.trans hat, htb.trans hb⟩

theorem positive_rate_control :
    supplyOpening 0 2 1 1 0 = 1 ∧ supplyClosing 0 2 1 1 0 = 2 := by
  norm_num [supplyOpening, supplyClosing]

theorem negative_rate_control :
    demandOpening 2 2 1 (-1) 0 = 1 ∧ demandClosing 2 2 1 (-1) 0 = 2 := by
  norm_num [demandOpening, demandClosing]

theorem negative_opening_control :
    supplyOpening 2 3 1 1 0 = -1 ∧ supplyClosing 2 3 1 1 0 ≤ 2 ∧
      ¬ Set.Icc (supplyOpening 2 3 1 1 0) (supplyClosing 2 3 1 1 0) ⊆ Set.Icc 0 2 := by
  norm_num [supplyOpening, supplyClosing, Set.subset_def]
  exact ⟨-1, by norm_num, by norm_num, by norm_num⟩

theorem zero_rate_excluded (r : ℝ) (hr : 0 < r ∨ r < 0) : r ≠ 0 := by
  rcases hr with h | h <;> linarith

end Chapter10.Inventory

#print axioms Chapter10.Inventory.supply_window_iff
#print axioms Chapter10.Inventory.demand_window_iff
