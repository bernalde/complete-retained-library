module

public import Chapter02PSCSource

@[expose] public section

/-! Unaccepted candidate for the optional S018 source-clearance condition 11.
This is the reconstructed feasible-anchor (1)/(A6) comparator in the qualified
QG-(5)/Grossmann-PL separable model. The held report has damaged glyphs; journal
identity is unresolved. This fixed-anchor expression is not a classical
nonlinear dual-value infimum. All accepted definitions are imported unchanged.
-/
noncomputable section
open scoped BigOperators
namespace Chapter02

variable {p q m l s nw nv : ℕ}

/-- Keep the original objective and both complete residual families, including
every coupling constant. Only y changes; w and v stay at this anchor. -/
def pscReconstructedGBDRow (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (y : RealVector m) : ℝ :=
  d.objective e.w e.v y +
    (∑ j, e.lambda j * d.nonlinear j e.w e.v y) +
    ∑ i, e.mu i * d.coupling i e.w e.v y

/-- Algebra alone exposes the exact residual if complementarity is omitted.
No feasibility, sign, derivative, stationarity or minimizer premise is hidden. -/
theorem psc_reconstructed_row_expansion (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (y : RealVector m) :
    pscReconstructedGBDRow d e y = pscGBDRow d e y +
      (∑ j, e.lambda j * d.nonlinear j e.w e.v e.y) +
      ∑ i, e.mu i * d.coupling i e.w e.v e.y := by
  simp only [pscReconstructedGBDRow, pscGBDRow, PSCData.objective,
    PSCData.nonlinear, PSCData.coupling, map_sub, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Complementarity is sufficient for this algebraic bridge. The much stronger
accepted KKT/source premises are required by the separate validity results. -/
theorem psc_reconstructed_row_eq_of_complementarity
    (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (hn : ∀ j, e.lambda j * d.nonlinear j e.w e.v e.y = 0)
    (hc : ∀ i, e.mu i * d.coupling i e.w e.v e.y = 0)
    (y : RealVector m) :
    pscReconstructedGBDRow d e y = pscGBDRow d e y := by
  rw [psc_reconstructed_row_expansion]
  simp only [hn, hc, Finset.sum_const_zero, add_zero]

theorem psc_reconstructed_row_eq_anchored (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) (hk : PSCKKT d e) (y : RealVector m) :
    pscReconstructedGBDRow d e y = pscGBDRow d e y :=
  psc_reconstructed_row_eq_of_complementarity d e
    hk.nonlinear_complementarity hk.coupling_complementarity y

/-- Same selected finite history and same cut-only Y base as pscGBDMaster.
Repeated entries, empty history and zero row counts retain their usual meaning. -/
def pscReconstructedGBDMaster (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) : Set (RealVector m × ℝ) :=
  {z | z.1 ∈ d.Y ∧ ∀ e ∈ H, pscReconstructedGBDRow d e.data z.1 ≤ z.2}

theorem psc_reconstructed_master_eq (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) :
    pscReconstructedGBDMaster d H = pscGBDMaster d H := by
  ext z
  simp only [pscReconstructedGBDMaster, pscGBDMaster, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun e he => ?_⟩
    rw [← psc_reconstructed_row_eq_anchored d e.data e.kkt]
    exact h e he
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun e he => ?_⟩
    rw [psc_reconstructed_row_eq_anchored d e.data e.kkt]
    exact h e he

/-- Transport the accepted source construction: actual fixed-fiber minima,
full anchor derivatives and same-fiber Slater derive the matched entries.
No fixed-anchor expression is silently replaced by an inner infimum. -/
theorem psc_reconstructed_source_comparison (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ d.V d.r) (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (S : List (PSCSourceAnchor d)) :
    let H := pscSourceHistory d hr ht S
    pscProject (pscOAMaster d H) ⊆ pscProject (pscMaster d H) ∧
      pscProject (pscMaster d H) ⊆ pscReconstructedGBDMaster d H ∧
      ∀ w v y, d.feasible w v y →
        (y, d.objective w v y) ∈ pscReconstructedGBDMaster d H := by
  dsimp only
  rw [psc_reconstructed_master_eq]
  exact ⟨psc_projected_oa_subset d _, psc_projected_subset_gbd d _,
    fun w v y hf => psc_original_mem_gbd d _ hr ht w v y hf⟩

/-- Equality preserves actual attained minimizers. No nonempty/compactness or
finite-optimum convention is inferred for empty/unbounded masters. -/
theorem psc_reconstructed_minimizer_iff (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (z : RealVector m × ℝ) :
    IsMinimizer (pscReconstructedGBDMaster d H) Prod.snd z ↔
      IsMinimizer (pscGBDMaster d H) Prod.snd z := by
  rw [psc_reconstructed_master_eq]

#print axioms psc_reconstructed_row_expansion
#print axioms psc_reconstructed_row_eq_of_complementarity
#print axioms psc_reconstructed_row_eq_anchored
#print axioms psc_reconstructed_master_eq
#print axioms psc_reconstructed_source_comparison
#print axioms psc_reconstructed_minimizer_iff

end Chapter02
