module

public import Chapter02Model
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! The literal two-free-variable auxiliary program of Westerlund–Pörn 2002,
Eqs. 26–29. All geometry below uses explicit Euclidean sums, not the product
or finite-Pi sup norm used by the ambient Lean type. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

/-- Euclidean dot product over both coordinate blocks of Point n m. -/
def alphaEuclideanDot {n m : ℕ} (a p : Point n m) : ℝ :=
  LinearForm a.1 a.2 p

/-- Both z and zp are freely real; no original-model domain or integer
restriction is carried into this literal auxiliary feasible set. -/
def alphaAuxiliaryRegion {n m : ℕ} (a q : Point n m) (ε : ℝ) :
    Set (Point n m × Point n m) :=
  {zz | alphaEuclideanDot a (zz.1 - q) ≤ 0 ∧
    ε ^ 2 - alphaEuclideanDot (zz.1 - zz.2) (zz.1 - zz.2) ≤ 0 ∧
    alphaEuclideanDot a (zz.2 - q) = 0}

def alphaAuxiliaryObjective {n m : ℕ} (a q : Point n m)
    (zz : Point n m × Point n m) : ℝ :=
  -(alphaEuclideanDot a (zz.1 - q))

private theorem alpha_dot_zero {n m : ℕ} (a : Point n m) :
    alphaEuclideanDot a 0 = 0 := by simp [alphaEuclideanDot, LinearForm]

private theorem alpha_dot_smul_right {n m : ℕ} (a v : Point n m) (c : ℝ) :
    alphaEuclideanDot a (c • v) = c * alphaEuclideanDot a v := by
  simpa only [alphaEuclideanDot, zero_smul, add_zero, zero_mul] using
    linearForm_affine a.1 a.2 v 0 c 0

private theorem alpha_dot_self_smul {n m : ℕ} (v : Point n m) (c : ℝ) :
    alphaEuclideanDot (c • v) (c • v) = c ^ 2 * alphaEuclideanDot v v := by
  simp only [alphaEuclideanDot, LinearForm, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul]
  have hm (x : ℝ) : c * x * (c * x) = c ^ 2 * (x * x) := by ring
  simp only [hm, ← Finset.mul_sum, ← mul_add]

/-- A unit tangent witness gives the actual global minimum zero of the printed
program (26)–(29), strictly below the positive value stated in Eq. 37. This is
about that literal program, not the intended distance-to-plane/projection
program or any complete implementation. The explicit tangent premise excludes
nonzero-normal one-dimensional instances; no dimension existence is asserted. -/
theorem alpha_auxiliary_zero_minimum {n m : ℕ} (a q v : Point n m) (ε : ℝ)
    (hε : 0 < ε) (haa : 0 < alphaEuclideanDot a a)
    (hav : alphaEuclideanDot a v = 0) (hvv : alphaEuclideanDot v v = 1) :
    IsMinimizer (alphaAuxiliaryRegion a q ε) (alphaAuxiliaryObjective a q)
      (q, q + ε • v) ∧
    alphaAuxiliaryObjective a q (q, q + ε • v) = 0 ∧
    0 < ε * Real.sqrt (alphaEuclideanDot a a) := by
  have hobj : alphaAuxiliaryObjective a q (q, q + ε • v) = 0 := by
    simp only [alphaAuxiliaryObjective, sub_self, alpha_dot_zero, neg_zero]
  have hdist : alphaEuclideanDot (q - (q + ε • v)) (q - (q + ε • v)) = ε ^ 2 := by
    rw [sub_add_cancel_left]
    rw [← neg_smul, alpha_dot_self_smul, hvv]
    ring
  have htangent : alphaEuclideanDot a ((q + ε • v) - q) = 0 := by
    rw [add_sub_cancel_left, alpha_dot_smul_right, hav, mul_zero]
  refine ⟨⟨?_, ?_⟩, hobj, mul_pos hε (Real.sqrt_pos.2 haa)⟩
  · change alphaEuclideanDot a (q - q) ≤ 0 ∧
        ε ^ 2 - alphaEuclideanDot (q - (q + ε • v)) (q - (q + ε • v)) ≤ 0 ∧
        alphaEuclideanDot a ((q + ε • v) - q) = 0
    simp only [sub_self, alpha_dot_zero, hdist, le_refl, htangent, and_self]
  · intro zz hzz
    rw [hobj]
    exact neg_nonneg.mpr hzz.1

#print axioms alpha_auxiliary_zero_minimum

end Chapter02
