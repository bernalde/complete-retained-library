module

public import Chapter02AlphaObjective
public import Chapter02AlphaSource

@[expose] public section

/-! Literal mixed nonlinear-objective transport for the same-level reduced
subproblem. The continuous height is separate from the original integer block;
the nonlinear objective is separate from the ModelData linear objective.
Ambient extensions and a safe height floor are declared source qualifications.
The arbitrary compact K scope specializes to the printed product domain only
when that domain is chosen or an exact domain identity is supplied. -/

noncomputable section
namespace Chapter02

/-- Original mixed rows and objective values, original K and affine rows, a
bounded integer witness, real height bounds and every same-level objective cut.
The nonlinear reduction is fMixed<=v, not an epigraph inequality fMixed<=mu. -/
def sourceAlphaObjectiveHeightSet {n m l r : ℕ} {I : Type*}
    (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ)
    (fMixed : RealVector n → IntVector m → ℝ) (K : Set (Point n m))
    (G : Point n m → Point n m →L[ℝ] ℝ) (a : I → Point n m) (b v : ℝ) :
    Set (Point n m × ℝ) :=
  {z | z.1 ∈ K ∧ z.1 ∈ d.linearRegion ∧
    ∃ y : IntVector m, y ∈ IntegerBox d.lo d.hi ∧
      z.1.2 = (fun i => (y i : ℝ)) ∧ (∀ j, gMixed j z.1.1 y ≤ 0) ∧
      fMixed z.1.1 y ≤ v ∧ b ≤ z.2 ∧ z.2 ≤ v ∧
      ∀ i, v + G (a i) (z.1 - a i) ≤ z.2}

private theorem sourceObjective_source_eq {n m l r : ℕ} (d : ModelData n m l r)
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

private theorem sourceObjective_subset_base {n m l r : ℕ}
    (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) (K : Set (Point n m)) :
    sourceMixedFeasible d gMixed K ⊆ alphaMixedBase d K := by
  rintro p ⟨hpK, hpL, y, hy, hcast, _⟩
  exact ⟨⟨hpK, hpL⟩, y, hy, hcast⟩

private theorem sourceObjective_value {n m : ℕ}
    (f : Point n m → ℝ) (fMixed : RealVector n → IntVector m → ℝ)
    (hExtension : ∀ x y, f (x, fun i => (y i : ℝ)) = fMixed x y)
    (p : Point n m) (y : IntVector m) (hcast : p.2 = fun i => (y i : ℝ)) :
    f p = fMixed p.1 y := by
  simpa only [← hcast] using hExtension p.1 y

private theorem sourceObjective_pair_eq {n m l r : ℕ} {I : Type*}
    (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ)
    (fMixed : RealVector n → IntVector m → ℝ) (K : Set (Point n m))
    (f : Point n m → ℝ) (G : Point n m → Point n m →L[ℝ] ℝ)
    (a : I → Point n m) (b v : ℝ)
    (hExtension : ∀ x y, f (x, fun i => (y i : ℝ)) = fMixed x y) :
    sourceAlphaObjectiveHeightSet d gMixed fMixed K G a b v =
      alphaObjectiveHeightSet (sourceMixedFeasible d gMixed K) f G a b v := by
  ext z
  constructor
  · rintro ⟨hzK, hzL, y, hy, hcast, hrows, hcutoff, hfloor, hcap, hcuts⟩
    refine ⟨⟨hzK, hzL, y, hy, hcast, hrows⟩, ?_, hfloor, hcap, hcuts⟩
    rw [sourceObjective_value f fMixed hExtension z.1 y hcast]
    exact hcutoff
  · rintro ⟨⟨hzK, hzL, y, hy, hcast, hrows⟩, hcutoff, hfloor, hcap, hcuts⟩
    refine ⟨hzK, hzL, y, hy, hcast, hrows, ?_, hfloor, hcap, hcuts⟩
    rw [← sourceObjective_value f fMixed hExtension z.1 y hcast]
    exact hcutoff

/-- The compact-domain/source-feasible-anchor specialization of the exact
same-level theorem, plus literal returned integer and original objective
transport. Compactness does not replace the actual attained global minimum;
no solver status, constraint pseudoconvexity or algorithm is asserted. -/
theorem source_alpha_objective_equal_height_optimal {n m l r : ℕ} {I : Type*}
    [Fintype I] [Nonempty I] (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ)
    (fMixed : RealVector n → IntVector m → ℝ) (K : Set (Point n m))
    (f : Point n m → ℝ) (G : Point n m → Point n m →L[ℝ] ℝ)
    (a : I → Point n m) (b v : ℝ) (q : Point n m)
    (hgExtension : ∀ j x y, d.g j (x, fun i => (y i : ℝ)) = gMixed j x y)
    (hfExtension : ∀ x y, f (x, fun i => (y i : ℝ)) = fMixed x y)
    (_hK : IsCompact K)
    (hderiv : ∀ x ∈ alphaMixedBase d K, HasFDerivAt f (G x) x)
    (hpseudo : ∀ x ∈ alphaMixedBase d K, ∀ y ∈ alphaMixedBase d K,
      f y < f x → G x (y - x) < 0)
    (ha : ∀ i, a i ∈ sourceMixedFeasible d gMixed K)
    (hlevel : ∀ i, f (a i) = v)
    (hfloor : ∀ p ∈ sourceMixedFeasible d gMixed K, b ≤ f p)
    (hmin : IsMinimizer (sourceAlphaObjectiveHeightSet d gMixed fMixed K G a b v)
      Prod.snd (q, v)) :
    sourceMixedFeasible d gMixed K = d.feasibleOn K ∧
    sourceAlphaObjectiveHeightSet d gMixed fMixed K G a b v =
      alphaObjectiveHeightSet (sourceMixedFeasible d gMixed K) f G a b v ∧
    f q = v ∧ IsMinimizer (sourceMixedFeasible d gMixed K) f q ∧
    IsMinimizer (d.feasibleOn K) f q ∧
    ∃ y : IntVector m, y ∈ IntegerBox d.lo d.hi ∧
      q.2 = (fun i => (y i : ℝ)) ∧ (∀ j, gMixed j q.1 y ≤ 0) ∧
      fMixed q.1 y = v ∧
      ∀ (x : RealVector n) (z : IntVector m),
        (x, fun i => (z i : ℝ)) ∈ K →
        (x, fun i => (z i : ℝ)) ∈ d.linearRegion →
        z ∈ IntegerBox d.lo d.hi → (∀ j, gMixed j x z ≤ 0) →
        fMixed q.1 y ≤ fMixed x z := by
  have hsource := sourceObjective_source_eq d gMixed K hgExtension
  have hpairs := sourceObjective_pair_eq d gMixed fMixed K f G a b v hfExtension
  have hSB := sourceObjective_subset_base d gMixed K
  have hgeneric : IsMinimizer
      (alphaObjectiveHeightSet (sourceMixedFeasible d gMixed K) f G a b v)
      Prod.snd (q, v) := by
    rw [← hpairs]
    exact hmin
  have hexact := alpha_objective_equal_height_optimal
    (alphaMixedBase d K) (sourceMixedFeasible d gMixed K) f G a b v q
    hSB (fun i => hSB (ha i)) hderiv hpseudo hlevel hfloor hgeneric
  have hmodel : IsMinimizer (d.feasibleOn K) f q := by
    rw [← hsource]
    exact hexact.2
  obtain ⟨hqK, hqL, y, hy, hcast, hrows⟩ := hexact.2.1
  have hvalue := sourceObjective_value f fMixed hfExtension q y hcast
  refine ⟨hsource, hpairs, hexact.1, hexact.2, hmodel,
    y, hy, hcast, hrows, hvalue.symm.trans hexact.1, ?_⟩
  intro x z hxK hxL hz hgz
  have hcomp : (x, fun i => (z i : ℝ)) ∈ sourceMixedFeasible d gMixed K :=
    ⟨hxK, hxL, z, hz, rfl, hgz⟩
  have hcompare := hexact.2.2 (x, fun i => (z i : ℝ)) hcomp
  rw [hvalue, hfExtension x z] at hcompare
  exact hcompare

end Chapter02

#print axioms Chapter02.source_alpha_objective_equal_height_optimal
