module

public import Chapter02BBAffine
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-! Generic attainment support for the article-scoped OA availability proof.
The zero sublevel is nonempty and bounded; the domain and all higher sublevels
may initially be unbounded. No restoration minimum or certificate is assumed.
The domain need only be closed and convex with relative continuity of Phi.
The downstream OA adapter, source interpretation and execution are separate. -/

noncomputable section
open Set Metric
namespace Chapter03.OAExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {D : Set E} {Phi : E → ℝ}

/-- A finite continuous convex nonnegative function on a closed domain has
bounded finite sublevels if its zero sublevel is nonempty and bounded.
Convexity includes convexity of the domain. No positive-dimensional assumption
or attainment oracle is required. -/
theorem convex_sublevel_bounded
    (hD : IsClosed D) (hPhi : ContinuousOn Phi D) (hconv : ConvexOn ℝ D Phi)
    (hnonneg : ∀ x ∈ D, 0 ≤ Phi x)
    (hzero : {x ∈ D | Phi x ≤ 0}.Nonempty)
    (hbounded : Bornology.IsBounded {x ∈ D | Phi x ≤ 0}) (a : ℝ) :
    Bornology.IsBounded {x ∈ D | Phi x ≤ a} := by
  classical
  by_cases ha : 0 ≤ a
  · by_contra hunbounded
    obtain ⟨z, hzD, hzPhi⟩ := hzero
    have hz : Phi z = 0 := le_antisymm hzPhi (hnonneg z hzD)
    obtain ⟨v, hv, hray⟩ := Chapter02.bb_unbounded_closed_convex_ray
      (hD.isClosed_le hPhi continuousOn_const) (hconv.convex_le a)
      hunbounded (show z ∈ {x ∈ D | Phi x ≤ a} from ⟨hzD, hzPhi.trans ha⟩)
    have hray_zero (t : ℝ) (ht : 0 ≤ t) :
        z + t • v ∈ {x ∈ D | Phi x ≤ 0} := by
      refine ⟨(hray t ht).1, ?_⟩
      by_contra hnot
      have hb : 0 < Phi (z + t • v) := lt_of_not_ge hnot
      let N : ℝ := 1 + (a + 1) / Phi (z + t • v)
      have hN : 1 < N := by
        dsimp [N]
        have hdiv : 0 < (a + 1) / Phi (z + t • v) :=
          div_pos (by linarith) hb
        linarith
      have hNpos : 0 < N := lt_trans zero_lt_one hN
      have hNi0 : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
      have hNi1 : N⁻¹ ≤ 1 := (inv_le_one₀ hNpos).mpr hN.le
      have hqN := hray (N * t) (mul_nonneg hNpos.le ht)
      have hcombo := hconv.2 hzD hqN.1 (sub_nonneg.mpr hNi1) hNi0
        (sub_add_cancel 1 N⁻¹)
      have hmul : N⁻¹ * (N * t) = t := by
        rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
      have heq : (1 - N⁻¹) • z + N⁻¹ • (z + (N * t) • v) = z + t • v := by
        calc
          _ = ((1 - N⁻¹) + N⁻¹) • z + (N⁻¹ * (N * t)) • v := by module
          _ = _ := by rw [sub_add_cancel, one_smul, hmul]
      have hsmall : Phi (z + t • v) ≤ N⁻¹ * a := by
        calc
          _ ≤ (1 - N⁻¹) * Phi z + N⁻¹ * Phi (z + (N * t) • v) := by
            simpa only [heq, smul_eq_mul] using hcombo
          _ ≤ N⁻¹ * a := by
            rw [hz, mul_zero, zero_add]
            exact mul_le_mul_of_nonneg_left hqN.2 hNi0
      have hlarge : N * Phi (z + t • v) ≤ a := by
        calc
          _ ≤ N * (N⁻¹ * a) := mul_le_mul_of_nonneg_left hsmall hNpos.le
          _ = a := by rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
      have hNvalue : N * Phi (z + t • v) = Phi (z + t • v) + a + 1 := by
        dsimp [N]
        rw [add_mul, one_mul, div_mul_cancel₀ _ hb.ne']
        ring
      linarith
    obtain ⟨R, hR⟩ := hbounded.subset_closedBall z
    let T : ℝ := max R 0 + 1
    have hT : 0 ≤ T := by
      dsimp [T]
      have := le_max_right R 0
      linarith
    have hdist : dist (z + T • v) z = T := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hT,
        hv, mul_one]
    have hTR := hR (hray_zero T hT)
    change dist (z + T • v) z ≤ R at hTR
    rw [hdist] at hTR
    have := le_max_left R 0
    dsimp [T] at hTR
    linarith
  · exact hbounded.subset fun x hx => ⟨hx.1, hx.2.trans (lt_of_not_ge ha).le⟩

/-- The same finite sublevels are compact; continuity is only required on D. -/
theorem convex_sublevel_compact
    (hD : IsClosed D) (hPhi : ContinuousOn Phi D) (hconv : ConvexOn ℝ D Phi)
    (hnonneg : ∀ x ∈ D, 0 ≤ Phi x)
    (hzero : {x ∈ D | Phi x ≤ 0}.Nonempty)
    (hbounded : Bornology.IsBounded {x ∈ D | Phi x ≤ 0}) (a : ℝ) :
    IsCompact {x ∈ D | Phi x ≤ a} :=
  isCompact_iff_isClosed_bounded.mpr ⟨hD.isClosed_le hPhi continuousOn_const,
    convex_sublevel_bounded hD hPhi hconv hnonneg hzero hbounded a⟩

/-- Every nonempty closed subset C of the same D has an attained Phi minimum.
C need not be convex or bounded. Compactness of a reference sublevel is derived,
and its minimum is shown to be global on C before returning the witness. -/
theorem convex_minimizer_on_closed_subset
    (hD : IsClosed D) (hPhi : ContinuousOn Phi D) (hconv : ConvexOn ℝ D Phi)
    (hnonneg : ∀ x ∈ D, 0 ≤ Phi x)
    (hzero : {x ∈ D | Phi x ≤ 0}.Nonempty)
    (hbounded : Bornology.IsBounded {x ∈ D | Phi x ≤ 0})
    {C : Set E} (hC : IsClosed C) (hCD : C ⊆ D) (hne : C.Nonempty) :
    ∃ x, Chapter02.IsMinimizer C Phi x := by
  obtain ⟨q, hq⟩ := hne
  let K : Set E := {x ∈ C | Phi x ≤ Phi q}
  have hCphi : ContinuousOn Phi C := hPhi.mono hCD
  have hKclosed : IsClosed K := hC.isClosed_le hCphi continuousOn_const
  have hKbounded : Bornology.IsBounded K :=
    (convex_sublevel_bounded hD hPhi hconv hnonneg hzero hbounded (Phi q)).subset
      (fun x hx => ⟨hCD hx.1, hx.2⟩)
  have hK : IsCompact K := isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hKbounded⟩
  obtain ⟨x, hx⟩ := Chapter02.compact_feasible_attainment hK
    (show K.Nonempty from ⟨q, hq, le_rfl⟩) (hCphi.mono fun _ hp => hp.1)
  refine ⟨x, hx.1.1, ?_⟩
  intro y hy
  by_cases hyle : Phi y ≤ Phi q
  · exact hx.2 y ⟨hy, hyle⟩
  · exact (hx.2 q ⟨hq, le_rfl⟩).trans (lt_of_not_ge hyle).le

end Chapter03.OAExistence

#check @Chapter03.OAExistence.convex_sublevel_bounded
#check @Chapter03.OAExistence.convex_sublevel_compact
#check @Chapter03.OAExistence.convex_minimizer_on_closed_subset
#print axioms Chapter03.OAExistence.convex_sublevel_bounded
#print axioms Chapter03.OAExistence.convex_sublevel_compact
#print axioms Chapter03.OAExistence.convex_minimizer_on_closed_subset
