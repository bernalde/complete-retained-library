module

public import Chapter02PSCComparator
public import Chapter02PSCExamples

@[expose] public section

/-! Four candidate controls for the optional reconstructed (1)/(A6) bridge.
The accepted E and H data provide actual derivatives, KKT certificates,
relative convexity, fixed-fiber minima and Slater witnesses. Both binary and
continuous Y are retained. The two deliberately wrong definitions below are
mutation controls, not transcriptions attributed to an original source.
No classical dual-value or journal-identity claim is made. -/
noncomputable section
open scoped BigOperators
open Chapter02PSCExamples
namespace Chapter02.PSCComparatorExamples

/-- H has nonzero coupling constants, multiplier and anchor. The reconstructed
rows keep their offsets at every changed y and preserve the attained master
minimum for the same two-entry history. -/
theorem h_reconstructed_full_control (b : Bool) :
    ControlReady (hModel b) (hEntry b true) ∧
    ControlReady (hModel b) (hEntry b false) ∧
    (hModel b).b 0 = 1 ∧ (hAnchor b true).mu 0 = 2 ∧
    (hAnchor b true).y 0 = 1 ∧ (hAnchor b true).v 0 = 1 ∧
    (∀ y, pscReconstructedGBDRow (hModel b) (hAnchor b true) y = 4*signedY y-3 ∧
      pscReconstructedGBDRow (hModel b) (hAnchor b false) y = -4*signedY y-3) ∧
    IsMinimizer (pscReconstructedGBDMaster (hModel b) [hEntry b true,hEntry b false])
      Prod.snd (0,-3) := by
  refine ⟨h_full_model b true,h_full_model b false,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro y
    constructor
    · rw [psc_reconstructed_row_eq_anchored _ _ (h_kkt b true)]
      simpa using h_gbd_row b true y
    · rw [psc_reconstructed_row_eq_anchored _ _ (h_kkt b false)]
      simpa using h_gbd_row b false y
  · exact (psc_reconstructed_minimizer_iff _ _ _).mpr (h_gbd_minimum b)

/-- E exercises the nonlinear multiplier family, absent from H's active cut,
with its actual full analytic model and attained reconstructed-master minimum. -/
theorem e_reconstructed_full_control (b : Bool) :
    ControlReady (eModel b) (eEntry b) ∧ (eAnchor b).lambda 0 = 2 ∧
    (∀ y, pscReconstructedGBDRow (eModel b) (eAnchor b) y = 1-2*y 0) ∧
    IsMinimizer (pscReconstructedGBDMaster (eModel b) [eEntry b])
      Prod.snd (scalar 1,-1) := by
  refine ⟨e_full_model b,rfl,?_,?_⟩
  · intro y
    rw [psc_reconstructed_row_eq_anchored _ _ (e_kkt b)]
    exact e_gbd_row b y
  · exact (psc_reconstructed_minimizer_iff _ _ _).mpr (e_gbd_minimum b)

/-- Deliberately wrong: erase the constants from every coupling residual. -/
def omittedCouplingConstants {p q m l s nw nv : ℕ}
    (d : PSCData p q m l s nw nv) (e : PSCAnchor d) (y : RealVector m) : ℝ :=
  d.objective e.w e.v y + (∑ j, e.lambda j * d.nonlinear j e.w e.v y) +
    ∑ i, e.mu i * (d.E i y + d.F i e.w + d.G i e.v)

/-- Deliberately wrong: retain anchor value but use y in place of y-y_k. -/
def omittedAnchor {p q m l s nw nv : ℕ}
    (d : PSCData p q m l s nw nv) (e : PSCAnchor d) (y : RealVector m) : ℝ :=
  d.objective e.w e.v e.y + d.c y +
    (∑ j, e.lambda j * d.C j y) + ∑ i, e.mu i * d.E i y

def omittedAnchorMaster {p q m l s nw nv : ℕ}
    (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    Set (RealVector m × ℝ) :=
  {z | z.1 ∈ d.Y ∧ ∀ e ∈ H, omittedAnchor d e.data z.1 ≤ z.2}

/-- Full H mutation control at changed y=0: deleting b shifts the row by 2;
deleting the anchor shifts it by 4 and removes an actual original optimum.
The original global lower bound is carried explicitly, not only feasibility. -/
theorem h_missing_terms_control (b : Bool) :
    ControlReady (hModel b) (hEntry b true) ∧
    pscReconstructedGBDRow (hModel b) (hAnchor b true) 0 = -3 ∧
    omittedCouplingConstants (hModel b) (hAnchor b true) 0 = -1 ∧
    omittedAnchor (hModel b) (hAnchor b true) 0 = 1 ∧
    ((hModel b).feasible 0 (scalar 0) 0 ∧
      (hModel b).objective 0 (scalar 0) 0 = 0 ∧
      ∀ w v y, (hModel b).feasible w v y → 0 ≤ (hModel b).objective w v y) ∧
    (0,0) ∉ omittedAnchorMaster (hModel b) [hEntry b true] := by
  have hrow : pscReconstructedGBDRow (hModel b) (hAnchor b true) 0 = -3 := by
    rw [psc_reconstructed_row_eq_anchored _ _ (h_kkt b true),h_gbd_row]
    norm_num [signedY]
  have hc : omittedCouplingConstants (hModel b) (hAnchor b true) 0 = -1 := by
    unfold omittedCouplingConstants
    psc_numeric
  have ha : omittedAnchor (hModel b) (hAnchor b true) 0 = 1 := by
    unfold omittedAnchor
    psc_numeric
  refine ⟨h_full_model b true,hrow,hc,ha,h_original_attained_zero b,?_⟩
  intro hz
  have hbad := hz.2 (hEntry b true) (by simp)
  change omittedAnchor (hModel b) (hAnchor b true) 0 ≤ 0 at hbad
  rw [ha] at hbad
  norm_num at hbad

/-- Empty history preserves the literal cut-only Y base, hence arbitrary
heights and no master minimum, although the accepted original model has an
attained global minimum and its nonempty anchor fiber satisfies full CQ/KKT. -/
theorem h_empty_history_control (b : Bool) :
    ControlReady (hModel b) (hEntry b true) ∧
    ((hModel b).feasible 0 (scalar 0) 0 ∧
      (hModel b).objective 0 (scalar 0) 0 = 0 ∧
      ∀ w v y, (hModel b).feasible w v y → 0 ≤ (hModel b).objective w v y) ∧
    (∀ t : ℝ, (0,t) ∈ pscReconstructedGBDMaster (hModel b) []) ∧
    (∀ z, ¬ IsMinimizer (pscReconstructedGBDMaster (hModel b) []) Prod.snd z) := by
  have hall (t : ℝ) : (0,t) ∈ pscReconstructedGBDMaster (hModel b) [] := by
    change (0 : RealVector 2) ∈ (hModel b).Y ∧ _
    refine ⟨?_,by simp⟩
    psc_numeric
  refine ⟨h_full_model b true,h_original_attained_zero b,hall,?_⟩
  intro z hz
  have hbad := hz.2 (0,z.2-1) (hall (z.2-1))
  change z.2 ≤ z.2-1 at hbad
  linarith

#print axioms h_reconstructed_full_control
#print axioms e_reconstructed_full_control
#print axioms h_missing_terms_control
#print axioms h_empty_history_control

end Chapter02.PSCComparatorExamples
