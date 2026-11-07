module

public import Chapter08SecondOrderCone

@[expose] public section

/-! Literal finite quadratic rows, with all scale/radius/coefficient signs
retained. These are row equivalences, not whole unbounded application models. -/
noncomputable section
open scoped BigOperators
namespace Chapter08.SecondOrder

theorem square_epigraph {n : ℕ} (w : Tail n) (t : ℝ) :
    rsoc (1/2) t w ↔ squares w ≤ t := by
  constructor
  · intro h
    have := h.2.2
    nlinarith
  · intro h
    exact ⟨by norm_num, (squares_nonneg w).trans h, by nlinarith⟩

theorem norm_square_epigraph {n : ℕ} (w : Tail n) (t : ℝ) :
    rsoc (1/2) t w ↔ ‖w‖^2 ≤ t := by
  rw [square_epigraph, squares_eq_norm_sq]

/-- Nonnegative t remains explicit, including y=0. -/
theorem square_perspective {n : ℕ} (w : Tail n) (t y : ℝ)
    (hy : 0 ≤ y) (ht : 0 ≤ t) :
    rsoc (y/2) t w ↔ squares w ≤ t*y := by
  constructor
  · intro h
    have := h.2.2
    nlinarith
  · intro h
    exact ⟨by linarith,ht,by nlinarith⟩

theorem square_perspective_positive {n : ℕ} (w : Tail n) (t y : ℝ)
    (hy : 0 < y) :
    rsoc (y/2) t w ↔ squares w/y ≤ t := by
  constructor
  · intro h
    apply (div_le_iff₀ hy).mpr
    have := h.2.2
    nlinarith
  · intro h
    have hw := (div_le_iff₀ hy).mp h
    have ht : 0 ≤ t := by
      by_contra hn
      have hn' : t < 0 := lt_of_not_ge hn
      have := mul_neg_of_neg_of_pos hn' hy
      nlinarith [squares_nonneg w]
    exact (square_perspective w t y hy.le ht).mpr hw

theorem square_perspective_zero {n : ℕ} (w : Tail n) (t : ℝ) :
    rsoc 0 t w ↔ w=0 ∧ 0≤t := by
  constructor
  · intro h
    have hs : ‖w‖^2 ≤ 0 := by simpa [squares_eq_norm_sq] using h.2.2
    have hn : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact ⟨norm_eq_zero.mp hn,h.2.1⟩
  · rintro ⟨rfl,ht⟩
    simp [rsoc,squares,ht]

theorem radius_row {n : ℕ} (r : ℝ) (w : Tail n) (hr : 0 ≤ r) :
    soc r w ↔ squares w ≤ r^2 := by
  rw [soc_iff_squares]
  exact and_iff_right hr

def weightedTail {n : ℕ} (a : Fin n → ℝ) (x : Tail n) : Tail n :=
  ofCoords (fun i => Real.sqrt (a i) * x i)

theorem weighted_squares {n : ℕ} (a : Fin n → ℝ) (x : Tail n)
    (ha : ∀ i, 0 ≤ a i) :
    squares (weightedTail a x) = ∑ i, a i * (x i)^2 := by
  unfold squares weightedTail
  apply Finset.sum_congr rfl
  intro i _
  simp only [ofCoords_apply,mul_pow,Real.sq_sqrt (ha i)]

theorem weighted_square_epigraph {n : ℕ} (a : Fin n → ℝ) (x : Tail n) (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    rsoc (1/2) t (weightedTail a x) ↔ (∑ i, a i*(x i)^2) ≤ t := by
  rw [square_epigraph,weighted_squares a x ha]

theorem weighted_square_perspective {n : ℕ} (a : Fin n → ℝ) (x : Tail n)
    (t y : ℝ) (ha : ∀ i, 0 ≤ a i) (hy : 0 ≤ y) (ht : 0 ≤ t) :
    rsoc (y/2) t (weightedTail a x) ↔ (∑ i, a i*(x i)^2) ≤ t*y := by
  rw [square_perspective _ _ _ hy ht,weighted_squares a x ha]

/-- Literal random quadratic source row: the affine terms remain present in
the auxiliary system and coefficients of the squared terms are nonnegative. -/
theorem weighted_quadratic_row {n : ℕ} (a b : Fin n → ℝ) (c : ℝ) (x : Tail n)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, (a i*(x i)^2+b i*x i))+c ≤ 1 ↔
      ∃ t : ℝ, rsoc (1/2) t (weightedTail a x) ∧
        t+(∑ i, b i*x i)+c ≤ 1 := by
  rw [Finset.sum_add_distrib]
  constructor
  · intro h
    exact ⟨∑ i, a i*(x i)^2,
      (weighted_square_epigraph a x _ ha).mpr le_rfl,h⟩
  · rintro ⟨t,ht,hrow⟩
    have hq := (weighted_square_epigraph a x t ha).mp ht
    linarith

def distanceTail {n : ℕ} (p c : Tail n) : Tail n :=
  ofCoords (fun i => p i-c i)

theorem squared_distance_row {n : ℕ} (p c : Tail n) (d : ℝ) :
    (∑ i, (p i-c i)^2) ≤ d ↔ rsoc (1/2) d (distanceTail p c) := by
  rw [square_epigraph]
  rfl

theorem squared_distance_perspective {n : ℕ} (p c : Tail n) (d y : ℝ)
    (hy : 0 ≤ y) (hd : 0 ≤ d) :
    rsoc (y/2) d (ofCoords (fun i => y*p i-c i)) ↔
      (∑ i, (y*p i-c i)^2) ≤ d*y := by
  rw [square_perspective _ _ _ hy hd]
  rfl

theorem distance_expansion {n : ℕ} (p c : Tail n) :
    (∑ i, (p i-c i)^2) =
      (∑ i, (c i)^2) - 2*(∑ i, p i*c i) + ∑ i, (p i)^2 := by
  calc
    (∑ i, (p i-c i)^2) = ∑ i, ((c i)^2-2*(p i*c i)+(p i)^2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]

/-- One literal circle-placement row; r≥0 is essential for the squared-radius
to-Lorentz equivalence. Four such sign choices describe the source rectangle. -/
theorem layout_circle_row (r x y dx dy xc yc : ℝ) (hr : 0 ≤ r) :
    (x+dx-xc)^2+(y+dy-yc)^2 ≤ r^2 ↔
      soc r (ofCoords ![x+dx-xc,y+dy-yc]) := by
  rw [radius_row _ _ hr]
  simp [squares,Fin.sum_univ_two]

end Chapter08.SecondOrder

#print axioms Chapter08.SecondOrder.square_epigraph
#print axioms Chapter08.SecondOrder.norm_square_epigraph
#print axioms Chapter08.SecondOrder.square_perspective
#print axioms Chapter08.SecondOrder.square_perspective_positive
#print axioms Chapter08.SecondOrder.square_perspective_zero
#print axioms Chapter08.SecondOrder.radius_row
#print axioms Chapter08.SecondOrder.weighted_squares
#print axioms Chapter08.SecondOrder.weighted_square_epigraph
#print axioms Chapter08.SecondOrder.weighted_square_perspective
#print axioms Chapter08.SecondOrder.weighted_quadratic_row
#print axioms Chapter08.SecondOrder.squared_distance_row
#print axioms Chapter08.SecondOrder.squared_distance_perspective
#print axioms Chapter08.SecondOrder.distance_expansion
#print axioms Chapter08.SecondOrder.layout_circle_row
