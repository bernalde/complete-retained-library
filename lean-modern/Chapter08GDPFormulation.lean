module

public import Chapter08GDPLogic

@[expose] public section

/-! Fixed-selector conic GDP correspondence. The original global box is retained
even for an empty outer family. Dependent row dimensions and branch types are
literal. No convexity, attainment or global convex-hull claim is needed here. -/
noncomputable section
open scoped BigOperators
open Set
namespace Chapter08.GDP

def nonnegativeOrthant (m : ℕ) : Set (Vec m) := {r | ∀ j, 0 ≤ r j}

theorem orthant_zero (m : ℕ) : (0 : Vec m) ∈ nonnegativeOrthant m := by
  intro j
  exact le_rfl

theorem orthant_convex (m : ℕ) : Convex ℝ (nonnegativeOrthant m) := by
  intro x hx z hz a b ha hb _ j
  exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hz j))

theorem orthant_closed (m : ℕ) : IsClosed (nonnegativeOrthant m) := by
  unfold nonnegativeOrthant
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)

theorem orthant_scale {m : ℕ} (r : Vec m) (hr : r ∈ nonnegativeOrthant m)
    (a : ℝ) (ha : 0 ≤ a) : a • r ∈ nonnegativeOrthant m := by
  intro j
  exact mul_nonneg ha (hr j)

/-- The source affine inequality uses the negated residual, not Ax-b. -/
theorem affine_orthant_row {n m : ℕ} (A : Vec n →ₗ[ℝ] Vec m)
    (b : Vec m) (x : Vec n) :
    (∀ j, A x j ≤ b j) ↔ b - A x ∈ nonnegativeOrthant m := by
  simp only [nonnegativeOrthant, Set.mem_setOf_eq, Pi.sub_apply, sub_nonneg]

theorem affine_orthant_homogeneous_row {n m : ℕ} (A : Vec n →ₗ[ℝ] Vec m)
    (b : Vec m) (v : Vec n) (y : ℝ) :
    (∀ j, A v j ≤ y*b j) ↔ y • b - A v ∈ nonnegativeOrthant m := by
  simp only [nonnegativeOrthant, Set.mem_setOf_eq, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, sub_nonneg]

def FixedHull {ι : Type*} [Fintype ι] {n : ℕ} (m : ι → ℕ)
    (A : (i : ι) → Vec n →ₗ[ℝ] Vec (m i)) (b : (i : ι) → Vec (m i))
    (K : (i : ι) → Set (Vec (m i))) (lo hi x : Vec n) (y : ι → ℝ) : Prop :=
  (∑ i, y i) = 1 ∧ ∃ v : ι → Vec n, x = ∑ i, v i ∧
    (∀ i, A i (v i) - y i • b i ∈ K i) ∧
    (∀ i j, lo j * y i ≤ v i j ∧ v i j ≤ hi j * y i)

theorem fixed_binary_hull_exact {ι : Type*} [Fintype ι] {n : ℕ}
    (m : ι → ℕ) (A : (i : ι) → Vec n →ₗ[ℝ] Vec (m i))
    (b : (i : ι) → Vec (m i)) (K : (i : ι) → Set (Vec (m i)))
    (lo hi x : Vec n) (y : ι → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hK : ∀ i, 0 ∈ K i) :
    FixedHull m A b K lo hi x y ↔
      (∑ i, y i) = 1 ∧ InBox lo hi x ∧ ∀ i, y i = 1 → A i x - b i ∈ K i := by
  classical
  constructor
  · rintro ⟨hs, v, hx, hc, hv⟩
    obtain ⟨i, hi1, hz⟩ := binary_sum_one_hot y hy hs
    have hv0 : ∀ j, j ≠ i → v j = 0 := fun j hj =>
      zero_weight_box_forces_zero lo hi (v j) (y j) (hz j hj) (hv j)
    have hsum : (∑ j, v j) = v i := Finset.sum_eq_single i
      (by intro j _ hj; exact hv0 j hj)
      (by intro h; exact False.elim (h (Finset.mem_univ i)))
    have hxi := hx.trans hsum
    refine ⟨hs, ?_, ?_⟩
    · intro j
      simpa [hxi, hi1] using hv i j
    · intro j hj
      have hji : j = i := by
        by_contra h
        have hzero := hz j h
        rw [hj] at hzero
        norm_num at hzero
      subst j
      simpa [hxi, hi1] using hc i
  · rintro ⟨hs, hbox, hc⟩
    refine ⟨hs, (fun i => y i • x), ?_, ?_, ?_⟩
    · rw [← Finset.sum_smul, hs, one_smul]
    · intro i
      rcases hy i with h | h
      · simpa [h] using hK i
      · simpa [h] using hc i h
    · intro i j
      rcases hy i with h | h
      · simp [h]
      · simpa [h] using hbox j

structure ConicData (κ : Type*) (I : κ → Type*) (n : ℕ) where
  dim : (k : κ) → I k → ℕ
  map : (k : κ) → (i : I k) → Vec n →ₗ[ℝ] Vec (dim k i)
  offset : (k : κ) → (i : I k) → Vec (dim k i)
  cone : (k : κ) → (i : I k) → Set (Vec (dim k i))
  lower : Vec n
  upper : Vec n
  global : Set (Vec n)

variable {κ : Type*} {I : κ → Type*} [∀ k, Fintype (I k)] {n : ℕ}
  {δ : Type*}

def Source (D : ConicData κ I n) (clauses : δ → Clause (Sigma I))
    (x : Vec n) (Y : Sigma I → Bool) : Prop :=
  x ∈ D.global ∧ InBox D.lower D.upper x ∧ CNF clauses Y ∧
    (∀ k, OneHot (fun i : I k => Y ⟨k,i⟩)) ∧
    ∀ k i, Y ⟨k,i⟩ = true → D.map k i x - D.offset k i ∈ D.cone k i

def Hull (D : ConicData κ I n) (clauses : δ → Clause (Sigma I))
    (x : Vec n) (y : Sigma I → ℝ) : Prop :=
  x ∈ D.global ∧ InBox D.lower D.upper x ∧
    (∀ j, y j = 0 ∨ y j = 1) ∧ LinearCNF clauses y ∧
    ∀ k, FixedHull (D.dim k) (D.map k) (D.offset k) (D.cone k)
      D.lower D.upper x (fun i : I k => y ⟨k,i⟩)

theorem source_hull_fixed_selector (D : ConicData κ I n)
    (clauses : δ → Clause (Sigma I)) (hK : ∀ k i, 0 ∈ D.cone k i)
    (x : Vec n) (Y : Sigma I → Bool) :
    Source D clauses x Y ↔ Hull D clauses x (fun j => bit (Y j)) := by
  constructor
  · rintro ⟨hg, hb, hc, ho, hr⟩
    refine ⟨hg, hb, (fun j => bit_binary (Y j)), (cnf_encoding clauses Y).mp hc, ?_⟩
    intro k
    apply (fixed_binary_hull_exact (D.dim k) (D.map k) (D.offset k) (D.cone k)
      D.lower D.upper x _ (fun i => bit_binary (Y ⟨k,i⟩)) (hK k)).mpr
    exact ⟨(one_hot_encoding _).mp (ho k), hb,
      fun i hi => hr k i ((bit_eq_one_iff _).mp hi)⟩
  · rintro ⟨hg, hb, _, hc, hh⟩
    have hrows := fun k => (fixed_binary_hull_exact (D.dim k) (D.map k)
      (D.offset k) (D.cone k) D.lower D.upper x _
      (fun i => bit_binary (Y ⟨k,i⟩)) (hK k)).mp (hh k)
    exact ⟨hg, hb, (cnf_encoding clauses Y).mpr hc,
      fun k => (one_hot_encoding _).mpr (hrows k).1,
      fun k i hi => (hrows k).2.2 i ((bit_eq_one_iff _).mpr hi)⟩

theorem source_hull_decoded_selector (D : ConicData κ I n)
    (clauses : δ → Clause (Sigma I)) (hK : ∀ k i, 0 ∈ D.cone k i)
    (x : Vec n) (y : Sigma I → ℝ) (hy : ∀ j, y j = 0 ∨ y j = 1) :
    Source D clauses x (fun j => decode (y j)) ↔ Hull D clauses x y := by
  rw [source_hull_fixed_selector D clauses hK]
  have heq : (fun j => bit (decode (y j))) = y := by
    funext j
    exact bit_decode (y j) (hy j)
  rw [heq]

theorem source_hull_projection (D : ConicData κ I n)
    (clauses : δ → Clause (Sigma I)) (hK : ∀ k i, 0 ∈ D.cone k i) (x : Vec n) :
    (∃ Y, Source D clauses x Y) ↔ ∃ y, Hull D clauses x y := by
  constructor
  · rintro ⟨Y, hY⟩
    exact ⟨_, (source_hull_fixed_selector D clauses hK x Y).mp hY⟩
  · rintro ⟨y, hy⟩
    exact ⟨_, (source_hull_decoded_selector D clauses hK x y hy.2.2.1).mpr hy⟩

/-- Validity is checked on an independently given domain, before any inactive
row restriction. It may contain points from every other branch. -/
def ValidOffsets (D : ConicData κ I n)
    (M : (k : κ) → (i : I k) → Vec (D.dim k i)) : Prop :=
  ∀ x ∈ D.global, InBox D.lower D.upper x →
    ∀ k i, D.map k i x - D.offset k i - M k i ∈ D.cone k i

def BigM (D : ConicData κ I n) (clauses : δ → Clause (Sigma I))
    (M : (k : κ) → (i : I k) → Vec (D.dim k i))
    (x : Vec n) (y : Sigma I → ℝ) : Prop :=
  x ∈ D.global ∧ InBox D.lower D.upper x ∧
    (∀ j, y j = 0 ∨ y j = 1) ∧ LinearCNF clauses y ∧
    (∀ k, (∑ i : I k, y ⟨k,i⟩) = 1) ∧
    ∀ k i, D.map k i x - D.offset k i - (1-y ⟨k,i⟩) • M k i ∈ D.cone k i

theorem source_bigM_fixed_selector (D : ConicData κ I n)
    (clauses : δ → Clause (Sigma I))
    (M : (k : κ) → (i : I k) → Vec (D.dim k i)) (hM : ValidOffsets D M)
    (x : Vec n) (Y : Sigma I → Bool) :
    Source D clauses x Y ↔ BigM D clauses M x (fun j => bit (Y j)) := by
  constructor
  · rintro ⟨hg, hb, hc, ho, hr⟩
    refine ⟨hg, hb, (fun j => bit_binary (Y j)), (cnf_encoding clauses Y).mp hc,
      (fun k => (one_hot_encoding _).mp (ho k)), ?_⟩
    intro k i
    cases h : Y ⟨k,i⟩ with
    | true => simpa [h, bit] using hr k i h
    | false => simpa [h, bit] using hM x hg hb k i
  · rintro ⟨hg, hb, _, hc, ho, hr⟩
    refine ⟨hg, hb, (cnf_encoding clauses Y).mpr hc,
      (fun k => (one_hot_encoding _).mpr (ho k)), ?_⟩
    intro k i hi
    simpa [hi, bit] using hr k i

theorem source_bigM_decoded_selector (D : ConicData κ I n)
    (clauses : δ → Clause (Sigma I))
    (M : (k : κ) → (i : I k) → Vec (D.dim k i)) (hM : ValidOffsets D M)
    (x : Vec n) (y : Sigma I → ℝ) (hy : ∀ j, y j = 0 ∨ y j = 1) :
    Source D clauses x (fun j => decode (y j)) ↔ BigM D clauses M x y := by
  rw [source_bigM_fixed_selector D clauses M hM]
  have heq : (fun j => bit (decode (y j))) = y := by
    funext j
    exact bit_decode (y j) (hy j)
  rw [heq]

/-- Projection equivalence transports minimizers together with membership.
This proves no new attainment theorem. -/
theorem projection_minimizer_iff {X Z : Type*} (S : Set X) (T : Set Z)
    (p : Z → X) (hproject : ∀ x, x ∈ S ↔ ∃ z ∈ T, p z = x)
    (f : X → ℝ) (z : Z) :
    Chapter02.IsMinimizer T (f ∘ p) z ↔
      z ∈ T ∧ Chapter02.IsMinimizer S f (p z) := by
  constructor
  · rintro ⟨hz, hmin⟩
    refine ⟨hz, (hproject _).mpr ⟨z,hz,rfl⟩, ?_⟩
    intro x hx
    obtain ⟨w, hw, hp⟩ := (hproject x).mp hx
    simpa [Function.comp_def, hp] using hmin w hw
  · rintro ⟨hz, _, hmin⟩
    exact ⟨hz, fun w hw => hmin _ ((hproject _).mpr ⟨w,hw,rfl⟩)⟩

theorem hull_minimizer_iff (D : ConicData κ I n)
    (clauses : δ → Clause (Sigma I)) (hK : ∀ k i, 0 ∈ D.cone k i)
    (f : Vec n → ℝ) (p : Vec n × (Sigma I → ℝ)) :
    Chapter02.IsMinimizer {q | Hull D clauses q.1 q.2} (fun q => f q.1) p ↔
      Hull D clauses p.1 p.2 ∧
      Chapter02.IsMinimizer {x | ∃ Y, Source D clauses x Y} f p.1 := by
  apply projection_minimizer_iff _ _ Prod.fst _ f p
  intro x
  change (∃ Y, Source D clauses x Y) ↔
    ∃ z : Vec n × (Sigma I → ℝ), Hull D clauses z.1 z.2 ∧ z.1 = x
  rw [source_hull_projection D clauses hK x]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(x,y),hy,rfl⟩
  · rintro ⟨⟨u,y⟩,hy,hx⟩
    subst x
    exact ⟨y,hy⟩

theorem bigM_minimizer_iff (D : ConicData κ I n)
    (clauses : δ → Clause (Sigma I))
    (M : (k : κ) → (i : I k) → Vec (D.dim k i)) (hM : ValidOffsets D M)
    (f : Vec n → ℝ) (p : Vec n × (Sigma I → ℝ)) :
    Chapter02.IsMinimizer {q | BigM D clauses M q.1 q.2} (fun q => f q.1) p ↔
      BigM D clauses M p.1 p.2 ∧
      Chapter02.IsMinimizer {x | ∃ Y, Source D clauses x Y} f p.1 := by
  apply projection_minimizer_iff _ _ Prod.fst _ f p
  intro x
  constructor
  · rintro ⟨Y, hY⟩
    exact ⟨(x,fun j => bit (Y j)), (source_bigM_fixed_selector D clauses M hM x Y).mp hY, rfl⟩
  · rintro ⟨⟨u,y⟩,hy,hx⟩
    subst x
    exact ⟨_, (source_bigM_decoded_selector D clauses M hM u y hy.2.2.1).mpr hy⟩

#print axioms orthant_zero
#print axioms orthant_convex
#print axioms orthant_closed
#print axioms orthant_scale
#print axioms affine_orthant_row
#print axioms affine_orthant_homogeneous_row
#print axioms fixed_binary_hull_exact
#print axioms source_hull_fixed_selector
#print axioms source_hull_decoded_selector
#print axioms source_hull_projection
#print axioms source_bigM_fixed_selector
#print axioms source_bigM_decoded_selector
#print axioms projection_minimizer_iff
#print axioms hull_minimizer_iff
#print axioms bigM_minimizer_iff
end Chapter08.GDP
