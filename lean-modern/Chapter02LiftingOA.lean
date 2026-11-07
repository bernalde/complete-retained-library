module

public import Chapter02Lifting
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Tactic

@[expose] public section

/-! Matched actual-derivative outer approximations, one shared auxiliary vector.
Full-space monotonicity derives the derivative's positivity by right difference
quotients. Restricted-domain support positivity remains an explicit condition. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Chapter02

theorem lifting_monotone_derivative_nonneg {p : ℕ} {h : RealVector p → ℝ}
    {a : RealVector p} {L : RealVector p →L[ℝ] ℝ}
    (hm : Monotone h) (hd : HasFDerivAt h L a)
    (v : RealVector p) (hv : 0 ≤ v) : 0 ≤ L v := by
  apply ge_of_tendsto (hd.hasLineDerivAt v).tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have harg : a ≤ a + t • v := by
    intro j
    change a j ≤ a j + t * v j
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt ht) (hv j))
  exact smul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (sub_nonneg.mpr (hm harg))

theorem lifting_monotone_derivative_coefficients {p : ℕ} {h : RealVector p → ℝ}
    {a : RealVector p} {L : RealVector p →L[ℝ] ℝ}
    (hm : Monotone h) (hd : HasFDerivAt h L a) (j : Fin p) :
    0 ≤ L (Pi.single j 1) := by
  apply lifting_monotone_derivative_nonneg hm hd
  intro i
  by_cases hij : i = j <;> simp [Pi.single_apply,hij]

theorem lifting_monotone_derivative {p : ℕ} {h : RealVector p → ℝ}
    {a : RealVector p} {L : RealVector p →L[ℝ] ℝ}
    (hm : Monotone h) (hd : HasFDerivAt h L a) : Monotone L := by
  intro u v huv
  have hp := lifting_monotone_derivative_nonneg hm hd (v-u) (sub_nonneg.mpr huv)
  rw [map_sub] at hp
  exact sub_nonneg.mp hp

section OA
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {p k : ℕ}

def liftingComponentRow (g : X → RealVector p) (a : X)
    (Dg : X →L[ℝ] RealVector p) (x : X) : RealVector p := g a + Dg (x-a)

def liftingOuterRow (g : X → RealVector p) (h : RealVector p → ℝ)
    (a : X) (Dh : RealVector p →L[ℝ] ℝ) (y : RealVector p) : ℝ :=
  h (g a) + Dh (y-g a)

def liftingDirectRow (g : X → RealVector p) (h : RealVector p → ℝ)
    (a : X) (Dg : X →L[ℝ] RealVector p) (Dh : RealVector p →L[ℝ] ℝ)
    (x : X) : ℝ := h (g a) + (Dh.comp Dg) (x-a)

def liftingDirectOA (D : Set X) (g : X → RealVector p) (h : RealVector p → ℝ)
    (a : Fin k → X) (Dg : Fin k → X →L[ℝ] RealVector p)
    (Dh : Fin k → RealVector p →L[ℝ] ℝ) (b : ℝ) : Set X :=
  {x | x ∈ D ∧ ∀ i, liftingDirectRow g h (a i) (Dg i) (Dh i) x ≤ b}

def liftingSharedOA (D : Set X) (E : Set (RealVector p))
    (g : X → RealVector p) (h : RealVector p → ℝ)
    (a : Fin k → X) (Dg : Fin k → X →L[ℝ] RealVector p)
    (Dh : Fin k → RealVector p →L[ℝ] ℝ) (b : ℝ) : Set (X × RealVector p) :=
  {z | z.1 ∈ D ∧ z.2 ∈ E ∧ ∀ i,
    liftingComponentRow g (a i) (Dg i) z.1 ≤ z.2 ∧
    liftingOuterRow g h (a i) (Dh i) z.2 ≤ b}

theorem lifting_chain_rule (g : X → RealVector p) (h : RealVector p → ℝ)
    (a : X) (Dg : X →L[ℝ] RealVector p) (Dh : RealVector p →L[ℝ] ℝ)
    (hg : HasFDerivAt g Dg a) (hh : HasFDerivAt h Dh (g a)) :
    HasFDerivAt (h ∘ g) (Dh.comp Dg) a := hh.comp a hg

theorem lifting_component_support (D : Set X) (g : X → RealVector p)
    (a x : X) (Dg : X →L[ℝ] RealVector p)
    (hc : ∀ j, ConvexOn ℝ D (fun z => g z j)) (ha : a ∈ D) (hx : x ∈ D)
    (hd : HasFDerivAt g Dg a) : liftingComponentRow g a Dg x ≤ g x := by
  intro j
  exact tangent_underestimator_on (hc j) ha hx ((hasFDerivAt_pi'.mp hd) j)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem lifting_outer_support (E : Set (RealVector p)) (g : X → RealVector p)
    (h : RealVector p → ℝ) (a : X) (Dh : RealVector p →L[ℝ] ℝ)
    (y : RealVector p) (hc : ConvexOn ℝ E h) (ha : g a ∈ E) (hy : y ∈ E)
    (hd : HasFDerivAt h Dh (g a)) : liftingOuterRow g h a Dh y ≤ h y :=
  tangent_underestimator_on hc ha hy hd

theorem lifting_direct_outer_identity (g : X → RealVector p) (h : RealVector p → ℝ)
    (a : X) (Dg : X →L[ℝ] RealVector p) (Dh : RealVector p →L[ℝ] ℝ) (x : X) :
    liftingOuterRow g h a Dh (liftingComponentRow g a Dg x) =
      liftingDirectRow g h a Dg Dh x := by
  simp [liftingOuterRow,liftingComponentRow,liftingDirectRow]

theorem lifting_shared_subset_direct (D : Set X) (E : Set (RealVector p))
    (g : X → RealVector p) (h : RealVector p → ℝ) (a : Fin k → X)
    (Dg : Fin k → X →L[ℝ] RealVector p) (Dh : Fin k → RealVector p →L[ℝ] ℝ)
    (b : ℝ) (hm : ∀ i, Monotone (Dh i)) :
    Prod.fst '' liftingSharedOA D E g h a Dg Dh b ⊆ liftingDirectOA D g h a Dg Dh b := by
  rintro x ⟨z,hz,rfl⟩
  refine ⟨hz.1,fun i => ?_⟩
  rw [← lifting_direct_outer_identity]
  exact (add_le_add_right (hm i (sub_le_sub_right (hz.2.2 i).1 _)) _).trans (hz.2.2 i).2

theorem lifting_fullspace_shared_subset_direct (D : Set X) (E : Set (RealVector p))
    (g : X → RealVector p) (h : RealVector p → ℝ) (a : Fin k → X)
    (Dg : Fin k → X →L[ℝ] RealVector p) (Dh : Fin k → RealVector p →L[ℝ] ℝ)
    (b : ℝ) (hm : Monotone h) (hh : ∀ i, HasFDerivAt h (Dh i) (g (a i))) :
    Prod.fst '' liftingSharedOA D E g h a Dg Dh b ⊆ liftingDirectOA D g h a Dg Dh b :=
  lifting_shared_subset_direct D E g h a Dg Dh b (fun i => lifting_monotone_derivative hm (hh i))

theorem lifting_exact_subset_shared (D : Set X) (E : Set (RealVector p))
    (g : X → RealVector p) (h : RealVector p → ℝ) (a : Fin k → X)
    (Dg : Fin k → X →L[ℝ] RealVector p) (Dh : Fin k → RealVector p →L[ℝ] ℝ)
    (b : ℝ) (hdom : Set.MapsTo g D E)
    (hc : ∀ j, ConvexOn ℝ D (fun z => g z j)) (hhc : ConvexOn ℝ E h)
    (ha : ∀ i, a i ∈ D) (hg : ∀ i, HasFDerivAt g (Dg i) (a i))
    (hh : ∀ i, HasFDerivAt h (Dh i) (g (a i))) :
    liftingSet D E g h b ⊆ liftingSharedOA D E g h a Dg Dh b := by
  intro z hz
  refine ⟨hz.1,hz.2.1,fun i => ⟨?_,?_⟩⟩
  · exact (lifting_component_support D g (a i) z.1 (Dg i) hc (ha i) hz.1 (hg i)).trans hz.2.2.1
  · exact (lifting_outer_support E g h (a i) (Dh i) z.2 hhc (hdom (ha i)) hz.2.1 (hh i)).trans hz.2.2.2

theorem lifting_original_subset_projected_oa (D : Set X) (E : Set (RealVector p))
    (g : X → RealVector p) (h : RealVector p → ℝ) (a : Fin k → X)
    (Dg : Fin k → X →L[ℝ] RealVector p) (Dh : Fin k → RealVector p →L[ℝ] ℝ)
    (b : ℝ) (hdom : Set.MapsTo g D E)
    (hc : ∀ j, ConvexOn ℝ D (fun z => g z j)) (hhc : ConvexOn ℝ E h)
    (ha : ∀ i, a i ∈ D) (hg : ∀ i, HasFDerivAt g (Dg i) (a i))
    (hh : ∀ i, HasFDerivAt h (Dh i) (g (a i))) :
    liftingOriginal D g h b ⊆ Prod.fst '' liftingSharedOA D E g h a Dg Dh b := by
  intro x hx
  exact ⟨(x,g x),lifting_exact_subset_shared D E g h a Dg Dh b hdom hc hhc ha hg hh
    (lifting_graph_mem D E g h b hdom hx),rfl⟩

/-- Independent free heights reproduce only the same-anchor direct rows. No
outer-domain restrictions are silently eliminated by this theorem. -/
theorem lifting_independent_outer_projection (g : X → RealVector p)
    (h : RealVector p → ℝ) (a : Fin k → X)
    (Dg : Fin k → X →L[ℝ] RealVector p) (Dh : Fin k → RealVector p →L[ℝ] ℝ)
    (b : ℝ) (hm : ∀ i, Monotone (Dh i)) (x : X) :
    (∃ y : Fin k → RealVector p, ∀ i,
      liftingComponentRow g (a i) (Dg i) x ≤ y i ∧
      liftingOuterRow g h (a i) (Dh i) (y i) ≤ b) ↔
      ∀ i, liftingDirectRow g h (a i) (Dg i) (Dh i) x ≤ b := by
  constructor
  · rintro ⟨y,hy⟩ i
    rw [← lifting_direct_outer_identity]
    exact (add_le_add_right (hm i (sub_le_sub_right (hy i).1 _)) _).trans (hy i).2
  · intro hx
    refine ⟨fun i => liftingComponentRow g (a i) (Dg i) x,fun i => ⟨le_rfl,?_⟩⟩
    simpa only [lifting_direct_outer_identity] using hx i

theorem lifting_oa_minimum_comparison (D : Set X) (E : Set (RealVector p))
    (g : X → RealVector p) (h : RealVector p → ℝ) (a : Fin k → X)
    (Dg : Fin k → X →L[ℝ] RealVector p) (Dh : Fin k → RealVector p →L[ℝ] ℝ)
    (b : ℝ) (hm : ∀ i, Monotone (Dh i)) (f : X → ℝ) (u v : X)
    (hu : IsMinimizer (liftingDirectOA D g h a Dg Dh b) f u)
    (hv : IsMinimizer (Prod.fst '' liftingSharedOA D E g h a Dg Dh b) f v) :
    f u ≤ f v := nested_minima_monotone
      (lifting_shared_subset_direct D E g h a Dg Dh b hm) hu hv

/-- The full-space smooth source endpoint binds all analytic premises and both
containments to the same anchors and actual chain-rule derivative. -/
theorem lifting_fullspace_analytic_comparison (D : Set X)
    (g : X → RealVector p) (h : RealVector p → ℝ) (a : Fin k → X)
    (Dg : Fin k → X →L[ℝ] RealVector p) (Dh : Fin k → RealVector p →L[ℝ] ℝ)
    (b : ℝ) (hm : Monotone h)
    (hc : ∀ j, ConvexOn ℝ D (fun z => g z j)) (hhc : ConvexOn ℝ Set.univ h)
    (ha : ∀ i, a i ∈ D) (hg : ∀ i, HasFDerivAt g (Dg i) (a i))
    (hh : ∀ i, HasFDerivAt h (Dh i) (g (a i))) :
    (∀ i, HasFDerivAt (h ∘ g) ((Dh i).comp (Dg i)) (a i)) ∧
    liftingOriginal D g h b ⊆ Prod.fst '' liftingSharedOA D Set.univ g h a Dg Dh b ∧
    Prod.fst '' liftingSharedOA D Set.univ g h a Dg Dh b ⊆ liftingDirectOA D g h a Dg Dh b := by
  exact ⟨fun i => lifting_chain_rule g h (a i) (Dg i) (Dh i) (hg i) (hh i),
    lifting_original_subset_projected_oa D Set.univ g h a Dg Dh b
      (fun _ _ => Set.mem_univ _) hc hhc ha hg hh,
    lifting_fullspace_shared_subset_direct D Set.univ g h a Dg Dh b hm hh⟩

end OA
end Chapter02

#print axioms Chapter02.lifting_monotone_derivative_nonneg
#print axioms Chapter02.lifting_monotone_derivative_coefficients
#print axioms Chapter02.lifting_monotone_derivative
#print axioms Chapter02.lifting_chain_rule
#print axioms Chapter02.lifting_component_support
#print axioms Chapter02.lifting_outer_support
#print axioms Chapter02.lifting_direct_outer_identity
#print axioms Chapter02.lifting_shared_subset_direct
#print axioms Chapter02.lifting_fullspace_shared_subset_direct
#print axioms Chapter02.lifting_exact_subset_shared
#print axioms Chapter02.lifting_original_subset_projected_oa
#print axioms Chapter02.lifting_independent_outer_projection
#print axioms Chapter02.lifting_oa_minimum_comparison
#print axioms Chapter02.lifting_fullspace_analytic_comparison
