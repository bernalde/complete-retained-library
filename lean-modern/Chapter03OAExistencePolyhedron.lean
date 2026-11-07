module

public import Chapter02FiniteCone
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-! Finite polyhedral linear images in one real coordinate are closed.
The polyhedron itself need not be bounded. Empty row and coordinate families
are allowed. These are author implementations pending independent review. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter03.OAExistence

variable {E F I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fintype I] [Fintype J]

/-- The sum of a finite-dimensional linear image and a finitely generated cone
is itself an exact finite cone, using both signs of each basis image. -/
theorem linear_image_add_finiteCone_closed (L : E →L[ℝ] F) (a : J → F) :
    IsClosed {z : F | ∃ x : E, ∃ w : J → ℝ,
      (∀ j, 0 ≤ w j) ∧ z = L x + ∑ j, w j • a j} := by
  classical
  let B := Module.finBasis ℝ E
  let gen : (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E)) ⊕ J → F :=
    Sum.elim (Sum.elim (fun i => L (B i)) (fun i => -L (B i))) a
  have heq : {z : F | ∃ x : E, ∃ w : J → ℝ,
      (∀ j, 0 ≤ w j) ∧ z = L x + ∑ j, w j • a j} = finiteCone gen := by
    ext z
    constructor
    · rintro ⟨x, w, hw, rfl⟩
      let u := fun i => max (B.repr x i) 0
      let v := fun i => max (-(B.repr x i)) 0
      have huv (i) : u i - v i = B.repr x i := by
        dsimp [u, v]
        rcases le_total 0 (B.repr x i) with h | h
        · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
        · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
      refine ⟨Sum.elim (Sum.elim u v) w, ?_, ?_⟩
      · intro j
        rcases j with (i | i) | j
        · exact le_max_right _ _
        · exact le_max_right _ _
        · exact hw j
      · simp only [gen, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
        have hsum : (∑ i, u i • L (B i)) + (∑ i, v i • -L (B i)) = L x := by
          calc
            _ = ∑ i, (u i - v i) • L (B i) := by
              simp only [sub_smul, Finset.sum_sub_distrib, smul_neg,
                Finset.sum_neg_distrib]
              abel
            _ = L (∑ i, B.repr x i • B i) := by
              rw [map_sum]
              simp only [huv,map_smul]
            _ = L x := by rw [B.sum_repr]
        rw [hsum]
    · rintro ⟨w, hw, rfl⟩
      let u := fun i => w (Sum.inl (Sum.inl i))
      let v := fun i => w (Sum.inl (Sum.inr i))
      refine ⟨∑ i, (u i - v i) • B i, fun j => w (Sum.inr j),
        fun j => hw (Sum.inr j), ?_⟩
      simp only [gen, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        map_sum, map_smul, sub_smul, Finset.sum_sub_distrib, smul_neg,
        Finset.sum_neg_distrib]
      simp [u, v, sub_eq_add_neg]
  rw [heq]
  exact finiteCone_isClosed gen

/-- Exact scalar objective values of a finite weak affine system are closed,
including empty polyhedra and unbounded objective images. -/
theorem finite_polyhedron_value_closed
    (a : J → E →L[ℝ] ℝ) (b : J → ℝ) (c : E →L[ℝ] ℝ) :
    IsClosed (c '' {x : E | ∀ j, a j x ≤ b j}) := by
  classical
  let L : E →L[ℝ] ((J → ℝ) × ℝ) := (ContinuousLinearMap.pi a).prod c
  let slack : J → (J → ℝ) × ℝ := fun j => (Pi.single j 1, 0)
  have hs (w : J → ℝ) : (∑ j, w j • slack j) = (w, 0) := by
    ext k
    · simp [slack, Finset.sum_apply, Prod.fst_sum, Pi.single_apply, Pi.smul_apply]
    · simp [slack, Prod.snd_sum]
  have heq : c '' {x : E | ∀ j, a j x ≤ b j} =
      (fun t : ℝ => (b, t)) ⁻¹'
        {z | ∃ x : E, ∃ w : J → ℝ, (∀ j, 0 ≤ w j) ∧
          z = L x + ∑ j, w j • slack j} := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, fun j => b j - a j x, fun j => sub_nonneg.mpr (hx j), ?_⟩
      rw [hs]
      ext j
      · simp [L]
      · simp [L]
    · rintro ⟨x, w, hw, he⟩
      rw [hs] at he
      have hfst := congrArg Prod.fst he
      have hsnd := congrArg Prod.snd he
      refine ⟨x, ?_, ?_⟩
      · intro j
        have hj := congrFun hfst j
        change b j = a j x + w j at hj
        linarith [hw j]
      · simpa [L] using hsnd.symm
  rw [heq]
  exact (linear_image_add_finiteCone_closed L slack).preimage
    (continuous_const.prodMk continuous_id)

/-- Nonemptiness and bounded-below values suffice for actual LP attainment;
no bounded-polyhedron or supplied-optimizer premise occurs. -/
theorem finite_polyhedron_linear_attained
    (a : J → E →L[ℝ] ℝ) (b : J → ℝ) (c : E →L[ℝ] ℝ)
    (hne : ({x : E | ∀ j, a j x ≤ b j} : Set E).Nonempty)
    (hbb : BddBelow (c '' {x : E | ∀ j, a j x ≤ b j})) :
    ∃ x, IsMinimizer {x : E | ∀ j, a j x ≤ b j} c x := by
  have hleast := (finite_polyhedron_value_closed a b c).isLeast_csInf
    (hne.image c) hbb
  obtain ⟨x, hx, he⟩ := hleast.1
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [he]
  exact hleast.2 ⟨y, hy, rfl⟩

end Chapter03.OAExistence

#print axioms Chapter03.OAExistence.linear_image_add_finiteCone_closed
#print axioms Chapter03.OAExistence.finite_polyhedron_value_closed
#print axioms Chapter03.OAExistence.finite_polyhedron_linear_attained
