module

public import Chapter08
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Actual finite Euclidean Lorentz and corrected rotated cones. The ordinary
function-space supremum norm is never used for the tail. Original accepted
scalar definitions remain unchanged. -/
noncomputable section
open scoped BigOperators
namespace Chapter08.SecondOrder

abbrev Tail (n : ℕ) := EuclideanSpace ℝ (Fin n)

def ofCoords {n : ℕ} (x : Fin n → ℝ) : Tail n :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm x

@[simp] theorem ofCoords_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    ofCoords x i = x i := rfl

def squares {n : ℕ} (w : Tail n) : ℝ := ∑ i, (w i)^2

theorem squares_nonneg {n : ℕ} (w : Tail n) : 0 ≤ squares w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem squares_eq_norm_sq {n : ℕ} (w : Tail n) : squares w = ‖w‖^2 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  exact (Real.sq_sqrt (squares_nonneg w)).symm

theorem norm_eq_sqrt_squares {n : ℕ} (w : Tail n) : ‖w‖ = Real.sqrt (squares w) := by
  simpa [squares, Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_eq w

def cons {n : ℕ} (t : ℝ) (w : Tail n) : Tail (n+1) :=
  ofCoords (Fin.cons t (fun i => w i))

@[simp] theorem cons_zero {n : ℕ} (t : ℝ) (w : Tail n) : cons t w 0 = t := rfl
@[simp] theorem cons_succ {n : ℕ} (t : ℝ) (w : Tail n) (i : Fin n) :
    cons t w i.succ = w i := rfl

theorem squares_cons {n : ℕ} (t : ℝ) (w : Tail n) :
    squares (cons t w) = t^2 + squares w := by
  simp [squares, Fin.sum_univ_succ]

theorem cons_linear {n : ℕ} (s t a b : ℝ) (w z : Tail n) :
    cons (a*s+b*t) (a • w+b • z) = a • cons s w+b • cons t z := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [cons, ofCoords]

def soc {n : ℕ} (s : ℝ) (w : Tail n) : Prop := ‖w‖ ≤ s
def rsoc {n : ℕ} (u v : ℝ) (w : Tail n) : Prop :=
  0 ≤ u ∧ 0 ≤ v ∧ squares w ≤ 2*u*v
def socSet (n : ℕ) : Set (ℝ × Tail n) := {p | soc p.1 p.2}
def rsocSet (n : ℕ) : Set (ℝ × ℝ × Tail n) := {p | rsoc p.1 p.2.1 p.2.2}

theorem soc_iff_squares {n : ℕ} (s : ℝ) (w : Tail n) :
    soc s w ↔ 0 ≤ s ∧ squares w ≤ s^2 := by
  rw [squares_eq_norm_sq]
  constructor
  · intro h
    change ‖w‖ ≤ s at h
    exact ⟨(norm_nonneg w).trans h, by nlinarith [norm_nonneg w]⟩
  · rintro ⟨hs, hw⟩
    dsimp [soc]
    nlinarith [norm_nonneg w]

theorem soc_nonnegative_scale {n : ℕ} (s a : ℝ) (w : Tail n)
    (h : soc s w) (ha : 0 ≤ a) : soc (a*s) (a • w) := by
  dsimp [soc] at *
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] using
    mul_le_mul_of_nonneg_left h ha

theorem soc_add {n : ℕ} (s t : ℝ) (w z : Tail n)
    (h : soc s w) (k : soc t z) : soc (s+t) (w+z) :=
  (norm_add_le _ _).trans (add_le_add h k)

theorem soc_convex (n : ℕ) : Convex ℝ (socSet n) := by
  intro p hp q hq a b ha hb _
  exact soc_add _ _ _ _ (soc_nonnegative_scale p.1 a p.2 hp ha)
    (soc_nonnegative_scale q.1 b q.2 hq hb)

theorem soc_closed (n : ℕ) : IsClosed (socSet n) :=
  isClosed_le continuous_snd.norm continuous_fst

theorem rsoc_nonnegative_scale {n : ℕ} (u v a : ℝ) (w : Tail n)
    (h : rsoc u v w) (ha : 0 ≤ a) : rsoc (a*u) (a*v) (a • w) := by
  refine ⟨mul_nonneg ha h.1, mul_nonneg ha h.2.1, ?_⟩
  have hs : squares (a • w) = a^2 * squares w := by
    simp only [squares, PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hs]
  have hh := mul_le_mul_of_nonneg_left h.2.2 (sq_nonneg a)
  nlinarith

/-- The source's higher-dimensional alternate embedding, using the repaired
sum-of-squares rotated cone rather than its printed outer square root. -/
theorem rsoc_iff_alternate_embedding {n : ℕ} (u v : ℝ) (w : Tail n) :
    rsoc u v w ↔ soc (u+v) (cons u (cons v w)) := by
  rw [soc_iff_squares, squares_cons, squares_cons]
  constructor
  · rintro ⟨hu,hv,hw⟩
    exact ⟨add_nonneg hu hv, by nlinarith⟩
  · rintro ⟨hs,hw⟩
    have hp : 0 ≤ u*v := by nlinarith [squares_nonneg w]
    have hu : 0 ≤ u := by
      by_contra h
      have hn : u < 0 := lt_of_not_ge h
      have hv : 0 < v := by linarith
      have := mul_neg_of_neg_of_pos hn hv
      linarith
    have hv : 0 ≤ v := by
      by_contra h
      have hn : v < 0 := lt_of_not_ge h
      have hu' : 0 < u := by linarith
      have := mul_neg_of_pos_of_neg hu' hn
      linarith
    exact ⟨hu,hv,by nlinarith⟩

theorem rsoc_convex (n : ℕ) : Convex ℝ (rsocSet n) := by
  intro p hp q hq a b ha hb _
  apply (rsoc_iff_alternate_embedding _ _ _).mpr
  have h := soc_add _ _ _ _
    (soc_nonnegative_scale (p.1+p.2.1) a (cons p.1 (cons p.2.1 p.2.2))
      ((rsoc_iff_alternate_embedding _ _ _).mp hp) ha)
    (soc_nonnegative_scale (q.1+q.2.1) b (cons q.1 (cons q.2.1 q.2.2))
      ((rsoc_iff_alternate_embedding _ _ _).mp hq) hb)
  change soc (a*p.1+b*q.1+(a*p.2.1+b*q.2.1))
    (cons (a*p.1+b*q.1) (cons (a*p.2.1+b*q.2.1) (a • p.2.2+b • q.2.2)))
  rw [cons_linear, cons_linear]
  convert h using 1 <;> ring

theorem rsoc_closed (n : ℕ) : IsClosed (rsocSet n) := by
  have heq : rsocSet n = {p : ℝ × ℝ × Tail n | 0 ≤ p.1} ∩
      {p : ℝ × ℝ × Tail n | 0 ≤ p.2.1} ∩
      {p : ℝ × ℝ × Tail n | ‖p.2.2‖^2 ≤ 2*p.1*p.2.1} := by
    ext p
    simp [rsocSet, rsoc, squares_eq_norm_sq, and_assoc]
  rw [heq]
  exact ((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const continuous_snd.fst)).inter
    (isClosed_le (continuous_snd.snd.norm.pow 2)
      ((continuous_const.mul continuous_fst).mul continuous_snd.fst))

theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
theorem sqrt_two_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)

theorem rotation_coordinate (s : ℝ) :
    s/Real.sqrt 2 = (Real.sqrt 2/2)*s := by
  apply (div_eq_iff (ne_of_gt sqrt_two_pos)).mpr
  rw [show (Real.sqrt 2/2*s)*Real.sqrt 2 = ((Real.sqrt 2)^2/2)*s by ring,
    sqrt_two_sq]
  ring

theorem rotation_product (s t : ℝ) :
    2*((s+t)/Real.sqrt 2)*((s-t)/Real.sqrt 2) = s^2-t^2 := by
  have hn := ne_of_gt sqrt_two_pos
  calc
    2*((s+t)/Real.sqrt 2)*((s-t)/Real.sqrt 2) =
        (2*((s+t)*(s-t)))/(Real.sqrt 2)^2 := by field_simp [hn]
    _ = s^2-t^2 := by rw [sqrt_two_sq]; ring

/-- Source rotation: the second rotated coordinate contains the minus sign. -/
theorem source_rotation {n : ℕ} (s t : ℝ) (w : Tail n) :
    soc s (cons t w) ↔
      rsoc ((s+t)/Real.sqrt 2) ((s-t)/Real.sqrt 2) w := by
  rw [soc_iff_squares, squares_cons]
  constructor
  · rintro ⟨hs,hw⟩
    have hp : 0 ≤ s+t := by nlinarith [squares_nonneg w]
    have hm : 0 ≤ s-t := by nlinarith [squares_nonneg w]
    refine ⟨div_nonneg hp sqrt_two_pos.le, div_nonneg hm sqrt_two_pos.le, ?_⟩
    rw [rotation_product]
    linarith
  · rintro ⟨hu,hv,hw⟩
    have hp : 0 ≤ s+t := by
      simpa [div_mul_cancel₀ _ (ne_of_gt sqrt_two_pos)] using
        mul_nonneg hu sqrt_two_pos.le
    have hm : 0 ≤ s-t := by
      simpa [div_mul_cancel₀ _ (ne_of_gt sqrt_two_pos)] using
        mul_nonneg hv sqrt_two_pos.le
    rw [rotation_product] at hw
    exact ⟨by linarith, by linarith⟩

theorem source_rotation_matrix {n : ℕ} (s t : ℝ) (w : Tail n) :
    soc s (cons t w) ↔
      rsoc ((Real.sqrt 2/2)*s+(Real.sqrt 2/2)*t)
        ((Real.sqrt 2/2)*s-(Real.sqrt 2/2)*t) w := by
  have h := source_rotation s t w
  rw [rotation_coordinate,rotation_coordinate] at h
  simpa only [mul_add,mul_sub] using h

theorem rsoc_iff_standard_embedding {n : ℕ} (u v : ℝ) (w : Tail n) :
    rsoc u v w ↔ soc (u+v) (cons (u-v) (Real.sqrt 2 • w)) := by
  rw [soc_iff_squares, squares_cons]
  have hw : squares (Real.sqrt 2 • w) = 2*squares w := by
    simp only [squares, PiLp.smul_apply, smul_eq_mul, mul_pow, sqrt_two_sq,
      Finset.mul_sum]
  rw [hw]
  constructor
  · rintro ⟨hu,hv,hh⟩
    exact ⟨add_nonneg hu hv, by nlinarith⟩
  · rintro ⟨hs,hh⟩
    apply (rsoc_iff_alternate_embedding u v w).mpr
    rw [soc_iff_squares, squares_cons, squares_cons]
    exact ⟨hs,by nlinarith⟩

theorem scalar_rotated_iff (u v x : ℝ) :
    rsoc u v (ofCoords (fun _ : Fin 1 => x)) ↔ Chapter08.Rotated u v x := by
  simp [rsoc, squares, Chapter08.Rotated, Fin.sum_univ_one]

theorem scalar_soc_iff (t x : ℝ) :
    soc t (ofCoords (fun _ : Fin 1 => x)) ↔ |x| ≤ t := by
  rw [soc, norm_eq_sqrt_squares]
  simp [squares, Real.sqrt_sq_eq_abs]

end Chapter08.SecondOrder

#print axioms Chapter08.SecondOrder.squares_eq_norm_sq
#print axioms Chapter08.SecondOrder.soc_convex
#print axioms Chapter08.SecondOrder.soc_closed
#print axioms Chapter08.SecondOrder.rsoc_convex
#print axioms Chapter08.SecondOrder.rsoc_closed
#print axioms Chapter08.SecondOrder.soc_nonnegative_scale
#print axioms Chapter08.SecondOrder.rsoc_nonnegative_scale
#print axioms Chapter08.SecondOrder.source_rotation
#print axioms Chapter08.SecondOrder.source_rotation_matrix
#print axioms Chapter08.SecondOrder.rsoc_iff_alternate_embedding
#print axioms Chapter08.SecondOrder.rsoc_iff_standard_embedding
#print axioms Chapter08.SecondOrder.scalar_rotated_iff
