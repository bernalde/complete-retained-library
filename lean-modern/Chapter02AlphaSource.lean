module

public import Chapter02AlphaSupport
public import Chapter02ConvexSubgradientSource

@[expose] public section

/-! Full-feasible-set Eq.15 source adapter under a declared ambient-extension
interpretation. The actual derivatives and all-pairs strict law are required
only on the mixed base B0. Scaled maps are cut data, not claimed derivatives.
No Eq.23--25 one-row margin or epsilon-rule validity is asserted. -/

noncomputable section
namespace Chapter02

/-- Original compact domain, affine inequalities, and bounded integer slices. -/
def alphaMixedBase {n m l r : ℕ} (d : ModelData n m l r)
    (K : Set (Point n m)) : Set (Point n m) :=
  K ∩ d.linearRegion ∩ IntegerCylinder d.lo d.hi

/-- The intercept stays unscaled; the stored map is alpha times the actual map.
Its field name is inherited from TangentFamily, with no derivative assertion. -/
def alphaScaledFamily {n m l k : ℕ} (origin : Fin k → Point n m)
    (selected : Fin k → Set (Fin l))
    (G : Fin l → Point n m → Point n m →L[ℝ] ℝ)
    (α : Fin k → Fin l → ℝ) : TangentFamily n m l k where
  origin := origin
  selected := selected
  derivative i j := α i j • G j (origin i)

private theorem alpha_source_eq {n m l r : ℕ} (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) (K : Set (Point n m))
    (hExtension : ∀ j x y, d.g j (x, fun i => (y i : ℝ)) = gMixed j x y) :
    sourceMixedFeasible d gMixed K = d.feasibleOn K := by
  ext p
  constructor
  · rintro ⟨hpK, hpL, y, hy, hcast, hrows⟩
    apply (source_feasible_iff d K p).mpr
    refine ⟨hpK, ?_, hpL, y, hy, hcast⟩
    intro j
    have he : d.g j p = gMixed j p.1 y := by
      simpa only [← hcast] using hExtension j p.1 y
    rw [he]
    exact hrows j
  · intro hp
    obtain ⟨hpK, hrows, hpL, y, hy, hcast⟩ := (source_feasible_iff d K p).mp hp
    refine ⟨hpK, hpL, y, hy, hcast, ?_⟩
    intro j
    have he : d.g j p = gMixed j p.1 y := by
      simpa only [← hcast] using hExtension j p.1 y
    rw [← he]
    exact hrows j

private theorem alpha_base_compact {n m l r : ℕ} (d : ModelData n m l r)
    (K : Set (Point n m)) (hK : IsCompact K) : IsCompact (alphaMixedBase d K) := by
  have hL : IsClosed d.linearRegion := by
    have heq : d.linearRegion = ⋂ row,
        {p | LinearForm (d.A row) (d.B row) p ≤ d.rhs row} := by
      ext p
      simp [ModelData.linearRegion]
    rw [heq]
    exact isClosed_iInter fun row =>
      isClosed_le (linearForm_continuous _ _) continuous_const
  have hY : IsClosed (IntegerCylinder (n := n) d.lo d.hi) := by
    have hfin := (integerBox_finite d.lo d.hi).image
      (fun y : IntVector m => fun i => (y i : ℝ))
    have heq : IntegerCylinder (n := n) d.lo d.hi =
        Prod.snd ⁻¹' ((fun y : IntVector m => fun i => (y i : ℝ)) ''
          IntegerBox d.lo d.hi) := by
      ext p
      simp [IntegerCylinder, eq_comm]
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  exact (hK.inter_right hL).inter_right hY

/-- Static full-S alpha family: attained margins, exact all-real scale criterion,
source alpha>=max(1,g/h) sufficiency, and nonempty-selection origin exclusion.
The declared ambient extension is required to agree on every integer slice;
no convexity or differentiability of the scaled cut maps is asserted. -/
theorem source_alpha_cut_family {n m l r k : ℕ} (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) (K : Set (Point n m))
    (G : Fin l → Point n m → Point n m →L[ℝ] ℝ)
    (origin : Fin k → Point n m) (selected : Fin k → Set (Fin l))
    (hExtension : ∀ j x y, d.g j (x, fun i => (y i : ℝ)) = gMixed j x y)
    (hK : IsCompact K) (hne : (sourceMixedFeasible d gMixed K).Nonempty)
    (hderiv : ∀ j x, x ∈ alphaMixedBase d K → HasFDerivAt (d.g j) (G j x) x)
    (hpseudo : ∀ j x, x ∈ alphaMixedBase d K → ∀ y, y ∈ alphaMixedBase d K →
      d.g j y < d.g j x → G j x (y - x) < 0)
    (horigin : ∀ i, origin i ∈ alphaMixedBase d K)
    (hviol : ∀ i j, j ∈ selected i → 0 < d.g j (origin i)) :
    sourceMixedFeasible d gMixed K = d.feasibleOn K ∧
    IsCompact (alphaMixedBase d K) ∧ IsCompact (sourceMixedFeasible d gMixed K) ∧
    ∃ h : Fin k → Fin l → ℝ,
      (∀ i j, j ∈ selected i → ∃ pstar ∈ sourceMixedFeasible d gMixed K,
        0 < h i j ∧ h i j = -(G j (origin i) (pstar - origin i)) ∧
        (∀ p ∈ sourceMixedFeasible d gMixed K, G j (origin i) (p - origin i) ≤ -h i j) ∧
        G j (origin i) ≠ 0) ∧
      (∀ α : Fin k → Fin l → ℝ,
        (sourceMixedFeasible d gMixed K ⊆ d.masterOn (alphaScaledFamily origin selected G α) K) ↔
          ∀ i j, j ∈ selected i → d.g j (origin i) / h i j ≤ α i j) ∧
      (∀ α : Fin k → Fin l → ℝ,
        (∀ i j, j ∈ selected i → max 1 (d.g j (origin i) / h i j) ≤ α i j) →
          sourceMixedFeasible d gMixed K ⊆ d.masterOn (alphaScaledFamily origin selected G α) K) ∧
      (∀ (α : Fin k → Fin l → ℝ) i, (selected i).Nonempty →
        origin i ∉ (alphaScaledFamily origin selected G α).cutRegion d) := by
  classical
  have hsource := alpha_source_eq d gMixed K hExtension
  have hB := alpha_base_compact d K hK
  have hcont (j : Fin l) : ContinuousOn (d.g j) (alphaMixedBase d K) :=
    fun x hx => (hderiv j x hx).continuousAt.continuousWithinAt
  have hclosed : IsClosed (⋂ j, alphaMixedBase d K ∩ (d.g j) ⁻¹' Set.Iic 0) :=
    isClosed_iInter fun j => (hcont j).preimage_isClosed_of_isClosed hB.isClosed isClosed_Iic
  have hset : sourceMixedFeasible d gMixed K =
      alphaMixedBase d K ∩ ⋂ j, alphaMixedBase d K ∩ (d.g j) ⁻¹' Set.Iic 0 := by
    rw [hsource]
    ext p
    constructor
    · rintro ⟨⟨⟨hpK, hpg⟩, hpL⟩, hpY⟩
      have hpB : p ∈ alphaMixedBase d K := ⟨⟨hpK, hpL⟩, hpY⟩
      exact ⟨hpB, Set.mem_iInter.mpr fun j => ⟨hpB, hpg j⟩⟩
    · rintro ⟨hpB, hrows⟩
      exact ⟨⟨⟨hpB.1.1, fun j => (Set.mem_iInter.mp hrows j).2⟩,
        hpB.1.2⟩, hpB.2⟩
  have hS : IsCompact (sourceMixedFeasible d gMixed K) := by
    rw [hset]
    exact hB.inter_right hclosed
  have hSB : sourceMixedFeasible d gMixed K ⊆ alphaMixedBase d K := by
    rw [hset]
    exact Set.inter_subset_left
  have hgS (j : Fin l) (p : Point n m) (hp : p ∈ sourceMixedFeasible d gMixed K) :
      d.g j p ≤ 0 := by
    rw [hsource] at hp
    exact hp.1.1.2 j
  have hpairs : ∀ i j, ∃ h : ℝ, j ∈ selected i →
      ∃ pstar ∈ sourceMixedFeasible d gMixed K,
        0 < h ∧ h = -(G j (origin i) (pstar - origin i)) ∧
        (∀ p ∈ sourceMixedFeasible d gMixed K, G j (origin i) (p - origin i) ≤ -h) ∧
        G j (origin i) ≠ 0 ∧
        (∀ α : ℝ, (∀ p ∈ sourceMixedFeasible d gMixed K,
          d.g j (origin i) + α * G j (origin i) (p - origin i) ≤ 0) ↔
            d.g j (origin i) / h ≤ α) := by
    intro i j
    by_cases hij : j ∈ selected i
    · obtain ⟨pstar, hpstar, h, hh, heq, hbound, hnonzero, hiff, _⟩ :=
        alpha_compact_support (alphaMixedBase d K) (sourceMixedFeasible d gMixed K)
          (d.g j) (G j) (origin i) (hderiv j) (hpseudo j) hS hne hSB (hgS j)
          (horigin i) (hviol i j hij)
      exact ⟨h, fun _ => ⟨pstar, hpstar, hh, heq, hbound, hnonzero, hiff⟩⟩
    · exact ⟨0, fun hij' => False.elim (hij hij')⟩
  choose h hh using hpairs
  have hiff (α : Fin k → Fin l → ℝ) :
      (sourceMixedFeasible d gMixed K ⊆ d.masterOn (alphaScaledFamily origin selected G α) K) ↔
        ∀ i j, j ∈ selected i → d.g j (origin i) / h i j ≤ α i j := by
    constructor
    · intro hcontain i j hij
      obtain ⟨_, _, _, _, _, _, hlocal⟩ := hh i j hij
      apply (hlocal (α i j)).mp
      intro p hp
      have hcut := (hcontain hp).1.1.2 i j hij
      simpa only [alphaScaledFamily, ContinuousLinearMap.smul_apply, smul_eq_mul] using hcut
    · intro hscale p hp
      have hpF := hsource ▸ hp
      refine ⟨⟨⟨hpF.1.1.1, ?_⟩, hpF.1.2⟩, hpF.2⟩
      intro i j hij
      obtain ⟨_, _, _, _, _, _, hlocal⟩ := hh i j hij
      have hcut := (hlocal (α i j)).mpr (hscale i j hij) p hp
      simpa only [alphaScaledFamily, ContinuousLinearMap.smul_apply, smul_eq_mul] using hcut
  refine ⟨hsource, hB, hS, h, ?_, hiff, ?_, ?_⟩
  · intro i j hij
    obtain ⟨p, hp, hpos, heq, hbound, hnonzero, _⟩ := hh i j hij
    exact ⟨p, hp, hpos, heq, hbound, hnonzero⟩
  · intro α hα
    exact (hiff α).mpr fun i j hij => (le_max_right _ _).trans (hα i j hij)
  · intro α i hselected hcut
    obtain ⟨j, hj⟩ := hselected
    have h := hcut i j hj
    simp only [alphaScaledFamily, sub_self, map_zero, add_zero] at h
    exact (not_le_of_gt (hviol i j hj)) h

end Chapter02

#print axioms Chapter02.source_alpha_cut_family
