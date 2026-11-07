module

public import Chapter02ConvexSubgradient
public import Chapter02Model

@[expose] public section

/-! Static full-maximum subgradient cuts for the literal mixed source model.
A supplied globally convex real extension agrees on every integer vector. This
is a declared stronger interpretation of the source's mixed-domain notation,
not an existence theorem for extensions of integer-slice data. The legacy
TangentFamily field named derivative is only a continuous-linear data carrier:
no differentiability, smooth CP driver, numerical normal, or convergence claim
is asserted. Every affine/objective/integer-bound field is copied literally. -/

noncomputable section
namespace Chapter02

/-- Original mixed-source rows with all domain, affine and bounded integer
restrictions explicit. Extension agreement is a separate substantive premise. -/
def sourceMixedFeasible {n m l r : ℕ} (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ)
    (K : Set (Point n m)) : Set (Point n m) :=
  {p | p ∈ K ∧ p ∈ d.linearRegion ∧
    ∃ y : IntVector m, y ∈ IntegerBox d.lo d.hi ∧
      p.2 = (fun i => (y i : ℝ)) ∧ ∀ j, gMixed j p.1 y ≤ 0}

/-- Replace only the nonlinear family by its full signed nonempty maximum. -/
def maximumRowModel {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) : ModelData n m 1 r where
  g := fun _ p => eshMaximum d.g p
  A := d.A
  B := d.B
  rhs := d.rhs
  c1 := d.c1
  c2 := d.c2
  lo := d.lo
  hi := d.hi

/-- Every full-maximum row is selected. The derivative field of this existing
data carrier stores the supplied normal; it asserts no HasFDerivAt fact. -/
def maximumNormalFamily {n m k : ℕ}
    (origin : Fin k → Point n m)
    (normal : Fin k → Point n m →L[ℝ] ℝ) : TangentFamily n m 1 k where
  origin := origin
  selected := fun _ => Set.univ
  derivative := fun i _ => normal i

/-- Genuine ambient support directly derives finite static master validity and
positive-origin cut exclusion. Compactness bounds all ambient normals, without
requiring a continuous choice. The origin-in-K premise retains the intended
source generation scope; ambient support itself also works outside K. -/
theorem source_convex_maximum_cuts {n m l r k : ℕ}
    [Nonempty (Fin l)] (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ)
    (K : Set (Point n m))
    (origin : Fin k → Point n m)
    (normal : Fin k → Point n m →L[ℝ] ℝ)
    (hExtension : ∀ j x y,
      d.g j (x, fun i => (y i : ℝ)) = gMixed j x y)
    (hK : IsCompact K)
    (hg : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (_ha : ∀ i, origin i ∈ K)
    (hn : ∀ i, normal i ∈ ambientConvexSubdiff (eshMaximum d.g) (origin i)) :
    sourceMixedFeasible d gMixed K = d.feasibleOn K ∧
      d.feasibleOn K = (maximumRowModel d).feasibleOn K ∧
      sourceMixedFeasible d gMixed K ⊆
        (maximumRowModel d).masterOn (maximumNormalFamily origin normal) K ∧
      (∀ i, 0 < eshMaximum d.g (origin i) →
        origin i ∉ (maximumNormalFamily origin normal).cutRegion (maximumRowModel d)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K,
        ∀ D ∈ ambientConvexSubdiff (eshMaximum d.g) x, ‖D‖ ≤ M := by
  have hsource : sourceMixedFeasible d gMixed K = d.feasibleOn K := by
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
  have hmaximum : d.feasibleOn K = (maximumRowModel d).feasibleOn K := by
    ext p
    simp only [source_feasible_iff, maximumRowModel, Fin.forall_fin_one,
      eshMaximum_le_iff]
  refine ⟨hsource, hmaximum, ?_, ?_,
    ambient_convex_subgradients_bounded (eshMaximum_convexOn_univ hg) hK⟩
  · intro p hp
    rw [hsource] at hp
    obtain ⟨⟨⟨hpK, hpg⟩, hpL⟩, hpY⟩ := hp
    refine ⟨⟨⟨hpK, ?_⟩, hpL⟩, hpY⟩
    intro i j _
    change eshMaximum d.g (origin i) + normal i (p - origin i) ≤ 0
    exact (hn i p).trans ((eshMaximum_le_iff d.g p 0).mpr hpg)
  · intro i hi hcut
    have hh := hcut i (0 : Fin 1) (Set.mem_univ _)
    change eshMaximum d.g (origin i) + normal i (origin i - origin i) ≤ 0 at hh
    simp only [sub_self, map_zero, add_zero] at hh
    exact (not_le_of_gt hi) hh

end Chapter02

#print axioms Chapter02.source_convex_maximum_cuts
