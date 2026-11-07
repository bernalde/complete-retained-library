module

public import Chapter02PresolveBounds
public import Chapter02BBAdapter
public import Mathlib.Tactic

@[expose] public section

/-! Actual retained affine rows of BBPolyData. Certificates use only the final
retained rows; arbitrary base restrictions, nonlinear rows and integrality stay
in the model. This is a native sufficient deletion criterion, not a theorem
that a presolver discovers every redundancy or that integer-only redundancy
preserves the continuous relaxation. -/
noncomputable section
open scoped BigOperators
namespace Chapter02
namespace BBPolyData
variable {N l r : ℕ}

def retainedPolyhedron (D : BBPolyData N l r) (K : Finset (Fin r)) : Set (RealVector N) :=
  {z | ∀ j ∈ K, ∑ i, D.coefficient j i * z i ≤ D.rhs j}

def retainedContinuous (D : BBPolyData N l r) (B : Set (RealVector N))
    (K : Finset (Fin r)) : Set (RealVector N) :=
  {z | z ∈ B ∧ z ∈ D.retainedPolyhedron K ∧ ∀ j, D.c z j ≤ 0}

def retainedFeasible (D : BBPolyData N l r) (I : Finset (Fin N))
    (B : Set (RealVector N)) (K : Finset (Fin r)) : Set (RealVector N) :=
  {z | z ∈ D.retainedContinuous B K ∧
    ∀ i : {i : Fin N // i ∈ I}, ∃ k : ℤ, (k : ℝ) = z i}

/-- No weight is assigned to an omitted row. Coefficients and right-hand side
are checked explicitly; box information is usable here only as retained rows. -/
structure RetainedRowCertificate (D : BBPolyData N l r) (K : Finset (Fin r))
    (j : Fin r) where
  weight : Fin r → ℝ
  nonneg : ∀ k ∈ K, 0 ≤ weight k
  coefficient_eq : ∀ i, D.coefficient j i = ∑ k ∈ K, weight k * D.coefficient k i
  rhs_le : (∑ k ∈ K, weight k * D.rhs k) ≤ D.rhs j

theorem retained_row_certificate_valid (D : BBPolyData N l r) {K : Finset (Fin r)}
    {j : Fin r} (cert : D.RetainedRowCertificate K j) {z : RealVector N}
    (hz : z ∈ D.retainedPolyhedron K) :
    ∑ i, D.coefficient j i * z i ≤ D.rhs j := by
  calc
    ∑ i, D.coefficient j i * z i =
        ∑ i, ∑ k ∈ K, cert.weight k * (D.coefficient k i * z i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [cert.coefficient_eq i, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k ∈ K, cert.weight k * (∑ i, D.coefficient k i * z i) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ K, cert.weight k * D.rhs k := by
      exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hz k hk) (cert.nonneg k hk)
    _ ≤ D.rhs j := cert.rhs_le

theorem retained_polyhedron_eq_of_certificates (D : BBPolyData N l r)
    (K : Finset (Fin r))
    (cert : ∀ j, j ∉ K → D.RetainedRowCertificate K j) :
    D.retainedPolyhedron K = D.polyhedron := by
  ext z
  constructor
  · intro hz j
    by_cases hj : j ∈ K
    · exact hz j hj
    · exact D.retained_row_certificate_valid (cert j hj) hz
  · exact fun hz j _ => hz j

theorem retained_continuous_eq_of_certificates (D : BBPolyData N l r)
    (B : Set (RealVector N)) (K : Finset (Fin r))
    (cert : ∀ j, j ∉ K → D.RetainedRowCertificate K j) :
    D.retainedContinuous B K = {z | z ∈ B ∧ z ∈ D.polyhedron ∧ ∀ j, D.c z j ≤ 0} := by
  simp only [retainedContinuous, D.retained_polyhedron_eq_of_certificates K cert]

theorem retained_feasible_eq_of_certificates (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B : Set (RealVector N)) (K : Finset (Fin r))
    (cert : ∀ j, j ∉ K → D.RetainedRowCertificate K j) :
    D.retainedFeasible I B K = B ∩ D.feasible I := by
  rw [retainedFeasible, D.retained_continuous_eq_of_certificates B K cert]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, feasible]
  tauto

theorem retained_minimizer_iff_of_certificates (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B : Set (RealVector N)) (K : Finset (Fin r))
    (cert : ∀ j, j ∉ K → D.RetainedRowCertificate K j) (z : RealVector N) :
    IsMinimizer (D.retainedFeasible I B K) D.f z ↔ IsMinimizer (B ∩ D.feasible I) D.f z := by
  rw [D.retained_feasible_eq_of_certificates I B K cert]

/-- This support lemma may use integer feasibility. Its premise must be
discharged by a concrete argument; it gives no continuous-model equality. -/
theorem retained_feasible_eq_of_implication (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B : Set (RealVector N)) (K : Finset (Fin r))
    (hrows : ∀ z ∈ D.retainedFeasible I B K, ∀ j, j ∉ K →
      ∑ i, D.coefficient j i * z i ≤ D.rhs j) :
    D.retainedFeasible I B K = B ∩ D.feasible I := by
  ext z
  constructor
  · intro hz
    refine ⟨hz.1.1, ?_, hz.1.2.2, hz.2⟩
    intro j
    by_cases hj : j ∈ K
    · exact hz.1.2.1 j hj
    · exact hrows z hz j hj
  · intro hz
    exact ⟨⟨hz.1, fun j _ => hz.2.1 j, hz.2.2.1⟩, hz.2.2.2⟩

/-- Original-coordinate OBBT wrapper. R is explicitly a relaxation of the
bounded original mixed model, not a box selected without an enclosure proof. -/
theorem feasible_coordinate_bounds (D : BBPolyData N l r) (I : Finset (Fin N))
    (B R : Set (RealVector N)) (L U : RealVector N)
    (hR : B ∩ D.feasible I ⊆ R)
    (hL : ∀ i, IsLowerBound R (fun z => z i) (L i))
    (hU : ∀ i, IsLowerBound R (fun z => -z i) (-U i)) :
    (B ∩ D.feasible I) ∩ coordinateEnclosure (fun i z => z i) L U = B ∩ D.feasible I := by
  apply Set.inter_eq_left.mpr
  exact coordinateEnclosure_of_relaxation _ _ _ hR hL hU

/-- If R relaxes only the incumbent cutoff, coordinate certificates preserve
actual original minimizers, not every original feasible point. -/
theorem feasible_cutoff_bounds_minimizer_iff (D : BBPolyData N l r)
    (I : Finset (Fin N)) (B R : Set (RealVector N)) (L U : RealVector N) (u : ℝ)
    (hinc : HasUpperBoundWitness (B ∩ D.feasible I) D.f u)
    (hR : cutoffSet (B ∩ D.feasible I) D.f u ⊆ R)
    (hL : ∀ i, IsLowerBound R (fun z => z i) (L i))
    (hU : ∀ i, IsLowerBound R (fun z => -z i) (-U i)) (z : RealVector N) :
    IsMinimizer (B ∩ D.feasible I) D.f z ↔
      IsMinimizer ((B ∩ D.feasible I) ∩ coordinateEnclosure (fun i z => z i) L U) D.f z :=
  cutoff_bounds_preserve_minimizers _ _ _ hinc hR hL hU z

end BBPolyData
end Chapter02

#print axioms Chapter02.BBPolyData.retained_row_certificate_valid
#print axioms Chapter02.BBPolyData.retained_polyhedron_eq_of_certificates
#print axioms Chapter02.BBPolyData.retained_continuous_eq_of_certificates
#print axioms Chapter02.BBPolyData.retained_feasible_eq_of_certificates
#print axioms Chapter02.BBPolyData.retained_minimizer_iff_of_certificates
#print axioms Chapter02.BBPolyData.retained_feasible_eq_of_implication
#print axioms Chapter02.BBPolyData.feasible_coordinate_bounds
#print axioms Chapter02.BBPolyData.feasible_cutoff_bounds_minimizer_iff
