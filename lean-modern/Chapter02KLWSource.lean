module

public import Chapter02LiftingOA
public import Chapter02LiftingEnvelope
public import Mathlib.Tactic

@[expose] public section

/-! KLW2018 Eqs. (4)--(7), with explicit coordinate subsets and one common
nonempty history. A block is exactly the range of an injective coordinate
enumeration: no duplicate coordinate occurs within a block, while different
blocks may overlap. The distinct dimensions d,m are a declared enlargement;
the literal source count is m=d. Ambient component derivatives are actual
HasFDerivAt hypotheses. The strict theorem is a sufficient repair, not the
printed Proposition 2. No strict fixed-level or optimum-value improvement is
asserted. Existing finite-envelope/projection infrastructure is reused. -/

noncomputable section
open scoped BigOperators
namespace Chapter02

structure KLWData (d m : ℕ) where
  size : Fin m → ℕ
  coordinate : (i : Fin m) → Fin (size i) ↪ Fin d
  proper : ∀ i, Set.range (coordinate i) ≠ Set.univ
  component : (i : Fin m) → RealVector (size i) → ℝ
  domain : (i : Fin m) → Set (RealVector (size i))

variable {d m : ℕ} {J : Type*}

def klwBlock (S : KLWData d m) (i : Fin m) : Set (Fin d) :=
  Set.range (S.coordinate i)

def klwProjection (S : KLWData d m) (i : Fin m) :
    RealVector d →L[ℝ] RealVector (S.size i) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (S.coordinate i k)

@[simp] theorem klw_projection_apply (S : KLWData d m) (i : Fin m)
    (x : RealVector d) (k : Fin (S.size i)) :
    klwProjection S i x k = x (S.coordinate i k) := rfl

theorem klw_block_mem_iff (S : KLWData d m) (i : Fin m) (r : Fin d) :
    r ∈ klwBlock S i ↔ ∃ k, S.coordinate i k = r := Iff.rfl

theorem klw_block_proper (S : KLWData d m) (i : Fin m) :
    klwBlock S i ≠ Set.univ := S.proper i

def klwSharedCoordinatesAgree (S : KLWData d m) (u v : RealVector d) : Prop :=
  ∀ i k, i ≠ k → ∀ r, r ∈ klwBlock S i → r ∈ klwBlock S k → u r = v r

def klwDomain (S : KLWData d m) : Set (RealVector d) :=
  {x | ∀ i, klwProjection S i x ∈ S.domain i}

def klwFunction (S : KLWData d m) (x : RealVector d) : ℝ :=
  ∑ i, S.component i (klwProjection S i x)

def klwRow (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (i : Fin m) (j : J) (x : RealVector d) : ℝ :=
  S.component i (klwProjection S i (a j)) +
    L i j (klwProjection S i x - klwProjection S i (a j))

def klwWholeDerivative (S : KLWData d m)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (j : J) : RealVector d →L[ℝ] ℝ :=
  ∑ i, (L i j).comp (klwProjection S i)

def klwWholeRow (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (j : J) (x : RealVector d) : ℝ :=
  klwFunction S (a j) + klwWholeDerivative S L j (x - a j)

def klwDirectEnvelope (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (first : J) (tail : List J) : RealVector d → ℝ :=
  pscEnvelope (klwWholeRow S a L) first tail

def klwComponentEnvelope (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (first : J) (tail : List J) (x : RealVector d) : ℝ :=
  ∑ i, pscEnvelope (klwRow S a L i) first tail x

def klwSharedHeightSet (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (K : Set (RealVector d)) (first : J) (tail : List J) (b : ℝ) :
    Set (RealVector d × RealVector m) :=
  liftingSupportSet K (klwRow S a L) (fun _ => first :: tail) b

def klwEpigraph (K : Set (RealVector d)) (f : RealVector d → ℝ) :
    Set (RealVector d × ℝ) := {p | p.1 ∈ K ∧ f p.1 ≤ p.2}

theorem klw_whole_derivative (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ) (j : J)
    (hd : ∀ i, HasFDerivAt (S.component i) (L i j) (klwProjection S i (a j))) :
    HasFDerivAt (klwFunction S) (klwWholeDerivative S L j) (a j) := by
  unfold klwFunction klwWholeDerivative
  simpa only [Function.comp_def] using
    (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (hd i).comp (a j) (klwProjection S i).hasFDerivAt)

theorem klw_whole_row_eq_sum (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (j : J) (x : RealVector d) :
    klwWholeRow S a L j x = ∑ i, klwRow S a L i j x := by
  simp only [klwWholeRow, klwWholeDerivative, klwFunction, klwRow,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem klw_direct_le_component (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (first : J) (tail : List J) (x : RealVector d) :
    klwDirectEnvelope S a L first tail x ≤ klwComponentEnvelope S a L first tail x := by
  apply (psc_envelope_le_iff (klwWholeRow S a L) first tail x _).mpr
  intro j hj
  rw [klw_whole_row_eq_sum]
  exact Finset.sum_le_sum fun i _ =>
    (psc_envelope_le_iff (klwRow S a L i) first tail x _).mp le_rfl j hj

theorem klw_row_support (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (i : Fin m) (j : J) (x : RealVector d)
    (hc : ConvexOn ℝ (S.domain i) (S.component i))
    (ha : a j ∈ klwDomain S) (hx : x ∈ klwDomain S)
    (hd : HasFDerivAt (S.component i) (L i j) (klwProjection S i (a j))) :
    klwRow S a L i j x ≤ S.component i (klwProjection S i x) :=
  tangent_underestimator_on hc (ha i) (hx i) hd

theorem klw_component_le_function (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (first : J) (tail : List J)
    (ha : ∀ j ∈ first :: tail, a j ∈ klwDomain S)
    (hc : ∀ i, ConvexOn ℝ (S.domain i) (S.component i))
    (hd : ∀ i j, j ∈ first :: tail →
      HasFDerivAt (S.component i) (L i j) (klwProjection S i (a j)))
    (x : RealVector d) (hx : x ∈ klwDomain S) :
    klwComponentEnvelope S a L first tail x ≤ klwFunction S x := by
  apply Finset.sum_le_sum
  intro i _
  apply (psc_envelope_le_iff (klwRow S a L i) first tail x _).mpr
  intro j hj
  exact klw_row_support S a L i j x (hc i) (ha j hj) hx (hd i j hj)

/-- Source adapter W: actual calculus, source row identity, weak envelope order,
free shared-height projection and same-threshold weak sublevel containment. -/
theorem klw_source_envelope_comparison (S : KLWData d m) (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (first : J) (tail : List J)
    (ha : ∀ j ∈ first :: tail, a j ∈ klwDomain S)
    (hc : ∀ i, ConvexOn ℝ (S.domain i) (S.component i))
    (hd : ∀ i j, j ∈ first :: tail →
      HasFDerivAt (S.component i) (L i j) (klwProjection S i (a j)))
    (K : Set (RealVector d)) (hK : K ⊆ klwDomain S) :
    (∀ j ∈ first :: tail,
      HasFDerivAt (klwFunction S) (klwWholeDerivative S L j) (a j)) ∧
    (∀ j x, klwWholeRow S a L j x = ∑ i, klwRow S a L i j x) ∧
    (∀ x ∈ klwDomain S,
      klwDirectEnvelope S a L first tail x ≤ klwComponentEnvelope S a L first tail x ∧
      klwComponentEnvelope S a L first tail x ≤ klwFunction S x) ∧
    (∀ b x, (∃ μ, (x, μ) ∈ klwSharedHeightSet S a L K first tail b) ↔
      x ∈ K ∧ klwComponentEnvelope S a L first tail x ≤ b) ∧
    (∀ b,
      ({x ∈ K | klwFunction S x ≤ b} ⊆
        {x ∈ K | klwComponentEnvelope S a L first tail x ≤ b}) ∧
      ({x ∈ K | klwComponentEnvelope S a L first tail x ≤ b} ⊆
        {x ∈ K | klwDirectEnvelope S a L first tail x ≤ b})) := by
  refine ⟨?_, klw_whole_row_eq_sum S a L, ?_, ?_, ?_⟩
  · intro j hj
    exact klw_whole_derivative S a L j (fun i => hd i j hj)
  · intro x hx
    exact ⟨klw_direct_le_component S a L first tail x,
      klw_component_le_function S a L first tail ha hc hd x hx⟩
  · intro b x
    exact lifting_support_projection K (klwRow S a L) (fun _ => first) (fun _ => tail) b x
  · intro b
    constructor
    · intro x hx
      exact ⟨hx.1, (klw_component_le_function S a L first tail ha hc hd x (hK hx.1)).trans hx.2⟩
    · intro x hx
      exact ⟨hx.1, (klw_direct_le_component S a L first tail x).trans hx.2⟩

/-- Strict support is derived using a midpoint and the actual derivative.
It is not an assumed separating-row oracle. -/
theorem klw_strict_tangent_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} {D : Set E} {u v : E} {L : E →L[ℝ] ℝ}
    (hc : StrictConvexOn ℝ D h) (hu : u ∈ D) (hv : v ∈ D) (hne : u ≠ v)
    (hd : HasFDerivAt h L u) : h u + L (v - u) < h v := by
  let w := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v
  have hw : w ∈ D := hc.1 hu hv (by norm_num) (by norm_num) (by norm_num)
  have hs : h w < (1 / 2 : ℝ) * h u + (1 / 2 : ℝ) * h v :=
    hc.2 hu hv hne (by norm_num) (by norm_num) (by norm_num)
  have ht := tangent_underestimator_on hc.convexOn hu hw hd
  have he : w - u = (1 / 2 : ℝ) • (v - u) := by
    dsimp [w]
    module
  rw [he, map_smul, smul_eq_mul] at ht
  change h w < (1 / 2 : ℝ) * h u + (1 / 2 : ℝ) * h v at hs
  linarith

/-- Sufficient repair R. Coverage and separation concern projected coordinates,
including every anchor, and contain no pre-supplied envelope or tangent gap.
The epigraph witness uses a free height, not a prescribed constraint level. -/
theorem klw_strictness_of_covered_separated_point (S : KLWData d m)
    (a : J → RealVector d)
    (L : (i : Fin m) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (first : J) (tail : List J)
    (ha : ∀ j ∈ first :: tail, a j ∈ klwDomain S)
    (hc : ∀ i, StrictConvexOn ℝ (S.domain i) (S.component i))
    (hd : ∀ i j, j ∈ first :: tail →
      HasFDerivAt (S.component i) (L i j) (klwProjection S i (a j)))
    (K : Set (RealVector d)) (hK : K ⊆ klwDomain S)
    (z : RealVector d) (hz : z ∈ K)
    (hcover : ∀ i, ∃ j ∈ first :: tail,
      klwProjection S i z = klwProjection S i (a j))
    (hsep : ∀ j ∈ first :: tail, ∃ i,
      klwProjection S i z ≠ klwProjection S i (a j)) :
    klwDirectEnvelope S a L first tail z < klwComponentEnvelope S a L first tail z ∧
    klwComponentEnvelope S a L first tail z = klwFunction S z ∧
    (∀ x ∈ klwDomain S,
      klwDirectEnvelope S a L first tail x ≤ klwComponentEnvelope S a L first tail x ∧
      klwComponentEnvelope S a L first tail x ≤ klwFunction S x) ∧
    (∃ r, (z, r) ∈ klwEpigraph K (klwDirectEnvelope S a L first tail) ∧
      (z, r) ∉ klwEpigraph K (klwComponentEnvelope S a L first tail)) := by
  have hzD := hK hz
  have hweak := klw_source_envelope_comparison S a L first tail ha
    (fun i => (hc i).convexOn) hd K hK
  have hvalue : klwComponentEnvelope S a L first tail z = klwFunction S z := by
    apply le_antisymm (hweak.2.2.1 z hzD).2
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨j, hj, he⟩ := hcover i
    have ht : klwRow S a L i j z = S.component i (klwProjection S i z) := by
      simp [klwRow, ← he]
    rw [← ht]
    exact (psc_envelope_le_iff (klwRow S a L i) first tail z _).mp le_rfl j hj
  have hrow : ∀ j ∈ first :: tail, klwWholeRow S a L j z < klwFunction S z := by
    intro j hj
    rw [klw_whole_row_eq_sum]
    obtain ⟨i, hi⟩ := hsep j hj
    apply Finset.sum_lt_sum
    · intro k _
      exact klw_row_support S a L k j z (hc k).convexOn (ha j hj) hzD (hd k j hj)
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      exact klw_strict_tangent_support (hc i) (ha j hj i) (hzD i) hi.symm (hd i j hj)
  have hgap : klwDirectEnvelope S a L first tail z < klwComponentEnvelope S a L first tail z := by
    rw [hvalue]
    obtain ⟨j, hj, he⟩ := lifting_envelope_attained (klwWholeRow S a L) first tail z
    change pscEnvelope (klwWholeRow S a L) first tail z < klwFunction S z
    rw [he]
    exact hrow j hj
  refine ⟨hgap, hvalue, hweak.2.2.1, ?_⟩
  refine ⟨(klwDirectEnvelope S a L first tail z + klwComponentEnvelope S a L first tail z) / 2,
    ⟨hz, by dsimp; linarith⟩, ?_⟩
  intro hp
  have hh := hp.2
  linarith

end Chapter02

#print axioms Chapter02.klw_source_envelope_comparison
#print axioms Chapter02.klw_strictness_of_covered_separated_point
