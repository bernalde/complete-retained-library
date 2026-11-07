module

public import Chapter02ExteriorTangent
public import Chapter02CPDomainSource

@[expose] public section

/-! Literal compact-domain source adapter for exact exterior tangents. The
strict reference belongs only to K. The unchanged ModelData affine rows and
integer cylinder are retained in feasibleOn/masterOn. No root finder, solver,
iteration, or convergence claim is asserted. -/

noncomputable section
namespace Chapter02

/-- The complete exterior tangent at the selected segment point, as an actual
singleton TangentFamily with one selected nonlinear row. -/
def exteriorTangentFamily {n m l : ℕ} (a q : Point n m) (t : ℝ) (j : Fin l)
    (D : Fin l → Point n m → Point n m →L[ℝ] ℝ) : TangentFamily n m l 1 :=
  cpDomainTangentFamily (fun _ => AffineMap.lineMap a q t) (fun _ => {j}) D

/-- Compact K gives the accepted F1 finite field bound. Compact B and the
positive violation threshold give a uniform separation for every admissible
exterior cut. The full original mixed feasible set survives each such cut;
the separation conclusion also applies to arbitrary ambient cut-feasible w. -/
theorem source_exterior_compact_cut {n m l r : ℕ} (d : ModelData n m l r)
    (K B : Set (Point n m)) (D : Fin l → Point n m → Point n m →L[ℝ] ℝ)
    (hKcompact : IsCompact K) (hK : Convex ℝ K)
    (hB : IsCompact B) (hBK : B ⊆ K)
    (hg : ∀ j, ConvexOn ℝ K (d.g j))
    (hd : ∀ j z, z ∈ K → HasFDerivWithinAt (d.g j) (D j z) K z)
    (hD : ∀ j, ContinuousOn (D j) K)
    (a : Point n m) (haK : a ∈ K) (ha : ∀ j, d.g j a < 0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ j z, z ∈ K → ‖D j z‖ ≤ M) ∧
      ∃ delta > 0, ∀ j q t, (q,t) ∈ exteriorData B d.g a eps j →
        d.feasibleOn K ⊆ d.masterOn (exteriorTangentFamily a q t j D) K ∧
        q ∉ (exteriorTangentFamily a q t j D).cutRegion d ∧
        ∀ w ∈ (exteriorTangentFamily a q t j D).cutRegion d, delta ≤ dist q w := by
  obtain ⟨_, M, hM, hbound, houter⟩ := source_cp_compact_domain d K D hKcompact hg hd hD
  obtain ⟨delta, hdelta, hsep⟩ := exterior_uniform_separation hB hK hBK hg hd hD haK ha heps
  refine ⟨M, hM, hbound, delta, hdelta, ?_⟩
  intro j q t hp
  have hpt := exterior_pointwise hK hBK haK hg hd ha heps hp
  refine ⟨houter 1 (fun _ => AffineMap.lineMap a q t) (fun _ => {j})
    (fun _ => hpt.1), ?_, ?_⟩
  · intro hq
    have hc := hq (0 : Fin 1) j (by simp [exteriorTangentFamily, cpDomainTangentFamily])
    exact (not_le_of_gt hpt.2.2.2.2) hc
  · intro w hw
    exact hsep j q t hp w
      (hw (0 : Fin 1) j (by simp [exteriorTangentFamily, cpDomainTangentFamily]))

end Chapter02

#print axioms Chapter02.source_exterior_compact_cut
