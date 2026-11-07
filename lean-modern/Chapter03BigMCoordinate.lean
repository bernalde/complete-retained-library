module

public import Chapter03

@[expose] public section

/-! Coordinatewise arbitrary-M characterization for a strict interior center.
This concerns the entire real interval, not a coupled feasible region. -/
noncomputable section
namespace Chapter03.BigMCoordinate

/-- The source coordinate lift with two arbitrary real constants. -/
def Lift (lo hi c M1 M2 y w : ℝ) (v : Bool) : Prop :=
  lo ≤ y ∧ y ≤ hi ∧ 0 ≤ w ∧ -w ≤ y-c ∧ y-c ≤ w ∧
  w ≤ y-c+M1*(1-bit v) ∧ w ≤ c-y+M2*bit v

/-- The source disjunction, with the same selector and explicit box bounds. -/
def Disjunction (lo hi c y w : ℝ) (v : Bool) : Prop :=
  lo ≤ y ∧ y ≤ hi ∧
    ((v = false ∧ y ≤ c ∧ w = c-y) ∨ (v = true ∧ c ≤ y ∧ w = y-c))

/-- Exact projection onto the graph of absolute distance on the full interval. -/
def ExactCoordinate (lo hi c M1 M2 : ℝ) : Prop :=
  ∀ y w, (∃ v, Lift lo hi c M1 M2 y w v) ↔
    lo ≤ y ∧ y ≤ hi ∧ w = |y-c|

theorem recommended_lift (lo hi c y w : ℝ) (v : Bool) :
    Lift lo hi c (2*(c-lo)) (2*(hi-c)) y w v ↔
      Chapter03.AbsLift lo hi c y w v := Iff.rfl

theorem lift_sound {lo hi c M1 M2 y w : ℝ} {v : Bool}
    (h : Lift lo hi c M1 M2 y w v) : w = |y-c| := by
  rcases h with ⟨_, _, _, hl, hu, h1, h2⟩
  cases v
  · simp only [bit, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at h2
    rw [abs_of_nonpos (by linarith : y-c ≤ 0)]
    linarith
  · simp only [bit, ↓reduceIte, sub_self, mul_zero, add_zero] at h1
    rw [abs_of_nonneg (by linarith : 0 ≤ y-c)]
    linarith

theorem lower_selector {lo hi c M1 M2 w : ℝ} {v : Bool}
    (hc : lo < c) (h : Lift lo hi c M1 M2 lo w v) : v = false := by
  cases v
  · rfl
  · rcases h with ⟨_, _, _, hl, _, h1, _⟩
    simp only [bit, ↓reduceIte, sub_self, mul_zero, add_zero] at h1
    exfalso
    linarith

theorem upper_selector {lo hi c M1 M2 w : ℝ} {v : Bool}
    (hc : c < hi) (h : Lift lo hi c M1 M2 hi w v) : v = true := by
  cases v
  · rcases h with ⟨_, _, _, _, hu, _, h2⟩
    simp only [bit, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at h2
    exfalso
    linarith
  · rfl

theorem lower_necessary {lo hi c M1 M2 w : ℝ} {v : Bool}
    (hc : lo < c) (h : Lift lo hi c M1 M2 lo w v) : 2*(c-lo) ≤ M1 := by
  have hv := lower_selector hc h
  subst v
  rcases h with ⟨_, _, _, hl, _, h1, _⟩
  simp only [bit, Bool.false_eq_true, ↓reduceIte, sub_zero, mul_one] at h1
  apply Chapter03.bigM_lower_necessary
  linarith

theorem upper_necessary {lo hi c M1 M2 w : ℝ} {v : Bool}
    (hc : c < hi) (h : Lift lo hi c M1 M2 hi w v) : 2*(hi-c) ≤ M2 := by
  have hv := upper_selector hc h
  subst v
  rcases h with ⟨_, _, _, _, hu, _, h2⟩
  simp only [bit, ↓reduceIte, mul_one] at h2
  apply Chapter03.bigM_upper_necessary
  linarith

theorem lift_mono {lo hi c A1 A2 M1 M2 y w : ℝ} {v : Bool}
    (h1 : A1 ≤ M1) (h2 : A2 ≤ M2)
    (h : Lift lo hi c A1 A2 y w v) : Lift lo hi c M1 M2 y w v := by
  rcases h with ⟨hlo, hhi, hw, hl, hu, ha, hb⟩
  refine ⟨hlo, hhi, hw, hl, hu, ?_, ?_⟩
  · have hv : 0 ≤ 1-bit v := by cases v <;> norm_num [bit]
    exact ha.trans (add_le_add_right (mul_le_mul_of_nonneg_right h1 hv) _)
  · have hv : 0 ≤ bit v := by cases v <;> norm_num [bit]
    exact hb.trans (add_le_add_right (mul_le_mul_of_nonneg_right h2 hv) _)

theorem sufficient {lo hi c M1 M2 : ℝ}
    (h1 : 2*(c-lo) ≤ M1) (h2 : 2*(hi-c) ≤ M2) :
    ExactCoordinate lo hi c M1 M2 := by
  intro y w
  constructor
  · rintro ⟨v, h⟩
    exact ⟨h.1, h.2.1, lift_sound h⟩
  · rintro ⟨hlo, hhi, rfl⟩
    obtain ⟨v, hv⟩ := Chapter03.general_abs_lift_complete (c := c) hlo hhi
    exact ⟨v, lift_mono h1 h2 ((recommended_lift lo hi c y |y-c| v).mpr hv)⟩

/-- Same-selector source correspondence, including both selectors at the center. -/
theorem lift_iff_disjunction {lo hi c M1 M2 y w : ℝ} {v : Bool}
    (h1 : 2*(c-lo) ≤ M1) (h2 : 2*(hi-c) ≤ M2) :
    Lift lo hi c M1 M2 y w v ↔ Disjunction lo hi c y w v := by
  constructor
  · rintro ⟨hlo, hhi, hw, hl, hu, ha, hb⟩
    refine ⟨hlo, hhi, ?_⟩
    cases v
    · simp only [bit, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] at hb
      exact Or.inl ⟨rfl, by linarith, by linarith⟩
    · simp only [bit, ↓reduceIte, sub_self, mul_zero, add_zero] at ha
      exact Or.inr ⟨rfl, by linarith, by linarith⟩
  · rintro ⟨hlo, hhi, (⟨rfl, hy, rfl⟩ | ⟨rfl, hy, rfl⟩)⟩
    · simp only [Lift, bit, Bool.false_eq_true, ↓reduceIte, sub_zero,
        mul_one, mul_zero, add_zero]
      exact ⟨hlo, hhi, by linarith, by linarith, by linarith,
        by linarith, le_refl _⟩
    · simp only [Lift, bit, ↓reduceIte, sub_self, mul_zero, mul_one, add_zero]
      exact ⟨hlo, hhi, by linarith, by linarith, by linarith,
        le_refl _, by linarith⟩

/-- One headline: full-coordinate exactness holds precisely at or above the
source constants for a strict interior center. No coupled-model minimality. -/
theorem exact_coordinate_iff {lo hi c M1 M2 : ℝ}
    (hl : lo < c) (hu : c < hi) :
    ExactCoordinate lo hi c M1 M2 ↔ 2*(c-lo) ≤ M1 ∧ 2*(hi-c) ≤ M2 := by
  constructor
  · intro h
    have hbox : lo ≤ hi := le_of_lt (lt_trans hl hu)
    obtain ⟨vl, hvl⟩ := (h lo |lo-c|).mpr ⟨le_refl lo, hbox, rfl⟩
    obtain ⟨vu, hvu⟩ := (h hi |hi-c|).mpr ⟨hbox, le_refl hi, rfl⟩
    exact ⟨lower_necessary hl hvl, upper_necessary hu hvu⟩
  · rintro ⟨h1, h2⟩
    exact sufficient h1 h2

/-- Uncounted asymmetric, nondegenerate two-branch control invoking the headline. -/
theorem two_branch_control :
    ExactCoordinate (-1) 4 1 4 6 ∧
    Lift (-1) 4 1 4 6 (-1) 2 false ∧
    Lift (-1) 4 1 4 6 4 3 true ∧
    (∀ w v, Lift (-1) 4 1 4 6 (-1) w v → v = false) ∧
    (∀ w v, Lift (-1) 4 1 4 6 4 w v → v = true) ∧
    ¬ ExactCoordinate (-1) 4 1 3 6 ∧
    ¬ ExactCoordinate (-1) 4 1 4 5 ∧
    Lift (-1) 4 1 4 6 1 0 false ∧
    Lift (-1) 4 1 4 6 1 0 true := by
  refine ⟨(exact_coordinate_iff (by norm_num) (by norm_num)).mpr (by norm_num),
    by norm_num [Lift, bit], by norm_num [Lift, bit], ?_, ?_, ?_, ?_,
    by norm_num [Lift, bit], by norm_num [Lift, bit]⟩
  · intro w v h
    exact lower_selector (by norm_num) h
  · intro w v h
    exact upper_selector (by norm_num) h
  · rw [exact_coordinate_iff (by norm_num) (by norm_num)]
    norm_num
  · rw [exact_coordinate_iff (by norm_num) (by norm_num)]
    norm_num

end Chapter03.BigMCoordinate
