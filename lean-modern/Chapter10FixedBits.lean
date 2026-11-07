module

public import Chapter10IntegerPenalty

@[expose] public section

/-! Explicit free/fixed coordinate partition. An arbitrary finite coordinate
type is transported by its partition equivalence; quadratic_reindex preserves
the full ordered matrix. A consistent binary fixed assignment is explicit. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Algebra

def extend {U F : Type*} (a : F → ℝ) (z : U → ℝ) : U ⊕ F → ℝ := Sum.elim z a

def restrict {U F : Type*} (x : U ⊕ F → ℝ) : U → ℝ := fun u => x (Sum.inl u)

def fixedDomain {U F : Type*} (a : F → ℝ) : Set (U ⊕ F → ℝ) :=
  {x | Binary x ∧ ∀ f, x (Sum.inr f) = a f}

theorem extend_mem_fixedDomain {U F : Type*} (a : F → ℝ) (ha : Binary a)
    (z : U → ℝ) (hz : Binary z) : extend a z ∈ fixedDomain a := by
  refine ⟨?_, fun _ => rfl⟩
  intro i
  cases i with
  | inl u => exact hz u
  | inr f => exact ha f

theorem restrict_binary {U F : Type*} (a : F → ℝ) (x : U ⊕ F → ℝ)
    (hx : x ∈ fixedDomain a) : Binary (restrict x) := fun u => hx.1 (Sum.inl u)

theorem restrict_extend {U F : Type*} (a : F → ℝ) (z : U → ℝ) :
    restrict (extend a z) = z := rfl

theorem extend_restrict {U F : Type*} (a : F → ℝ) (x : U ⊕ F → ℝ)
    (hx : x ∈ fixedDomain a) : extend a (restrict x) = x := by
  funext i
  cases i with
  | inl u => rfl
  | inr f => exact (hx.2 f).symm

def fixedEquiv {U F : Type*} (a : F → ℝ) (ha : Binary a) :
    {z : U → ℝ // Binary z} ≃ {x : U ⊕ F → ℝ // x ∈ fixedDomain a} where
  toFun z := ⟨extend a z.1, extend_mem_fixedDomain a ha z.1 z.2⟩
  invFun x := ⟨restrict x.1, restrict_binary a x.1 x.2⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; exact extend_restrict a x.1 x.2

theorem fixed_min_transport {U F : Type*} (a : F → ℝ) (ha : Binary a)
    (f : (U ⊕ F → ℝ) → ℝ) (z : U → ℝ) :
    IsMinOn (fixedDomain a) f (extend a z) ↔
      IsMinOn {z | Binary z} (fun z => f (extend a z)) z := by
  constructor
  · rintro ⟨hz, hm⟩
    refine ⟨restrict_binary a (extend a z) hz, ?_⟩
    intro y hy
    exact hm (extend a y) (extend_mem_fixedDomain a ha y hy)
  · rintro ⟨hz, hm⟩
    refine ⟨extend_mem_fixedDomain a ha z hz, ?_⟩
    intro y hy
    have h := hm (restrict y) (restrict_binary a y hy)
    simpa only [extend_restrict a y hy] using h

theorem fixed_feasible_exists_iff {U F : Type*} (a : F → ℝ) (ha : Binary a)
    (P : (U ⊕ F → ℝ) → Prop) :
    (∃ x ∈ fixedDomain a, P x) ↔ ∃ z, Binary z ∧ P (extend a z) := by
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨restrict x, restrict_binary a x hx, by simpa only [extend_restrict a x hx] using hp⟩
  · rintro ⟨z, hz, hp⟩
    exact ⟨extend a z, extend_mem_fixedDomain a ha z hz, hp⟩

def fixedLinear {U F : Type*} [Fintype F] (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) : U → ℝ :=
  fun u => ∑ f, (M (Sum.inl u) (Sum.inr f) + M (Sum.inr f) (Sum.inl u)) * a f

def fixedMatrix {U F : Type*} [Fintype F] [DecidableEq U]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) : U → U → ℝ :=
  fun u v => M (Sum.inl u) (Sum.inl v) + diagonal (fixedLinear M a) u v

def fixedOffset {U F : Type*} [Fintype F]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (κ : ℝ) : ℝ :=
  κ + quadratic (fun f g => M (Sum.inr f) (Sum.inr g)) a

theorem fixed_quadratic_expansion {U F : Type*} [Fintype U] [Fintype F]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (z : U → ℝ) :
    quadratic M (extend a z) =
      quadratic (fun u v => M (Sum.inl u) (Sum.inl v)) z +
      linearCost (fixedLinear M a) z + quadratic (fun f g => M (Sum.inr f) (Sum.inr g)) a := by
  have cross :
      (∑ u, ∑ f, M (Sum.inl u) (Sum.inr f) * z u * a f) +
      (∑ f, ∑ u, M (Sum.inr f) (Sum.inl u) * a f * z u) =
      linearCost (fixedLinear M a) z := by
    rw [Finset.sum_comm (f := fun f u => M (Sum.inr f) (Sum.inl u) * a f * z u)]
    unfold linearCost fixedLinear
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f _
    ring
  simp only [quadratic, Fintype.sum_sum_type, extend, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib]
  rw [← cross]
  ring

theorem fixed_qubo_identity {U F : Type*} [Fintype U] [Fintype F] [DecidableEq U]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (z : U → ℝ) (κ : ℝ) (hz : Binary z) :
    quadratic M (extend a z) + κ = quadratic (fixedMatrix M a) z + fixedOffset M a κ := by
  rw [fixed_quadratic_expansion]
  unfold fixedMatrix fixedOffset
  rw [quadratic_add, quadratic_diagonal _ _ hz]
  ring

theorem fixed_qubo_min_transport {U F : Type*} [Fintype U] [Fintype F] [DecidableEq U]
    (M : U ⊕ F → U ⊕ F → ℝ) (a : F → ℝ) (ha : Binary a) (z : U → ℝ) (κ : ℝ) :
    IsMinOn (fixedDomain a) (fun x => quadratic M x + κ) (extend a z) ↔
      IsMinOn {z | Binary z} (fun z => quadratic (fixedMatrix M a) z + fixedOffset M a κ) z := by
  rw [fixed_min_transport a ha]
  constructor <;> rintro ⟨hz, hm⟩ <;> refine ⟨hz, ?_⟩ <;> intro y hy
  · simpa only [fixed_qubo_identity M a z κ hz, fixed_qubo_identity M a y κ hy] using hm y hy
  · simpa only [fixed_qubo_identity M a z κ hz, fixed_qubo_identity M a y κ hy] using hm y hy

theorem conflicting_fixed_bits_empty {ι : Type*} (D : Set (ι → ℝ)) (i : ι)
    (hzero : ∀ x ∈ D, x i = 0) (hone : ∀ x ∈ D, x i = 1) : D = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h0 := hzero x hx
  have h1 := hone x hx
  linarith

end Chapter10.Algebra

#print axioms Chapter10.Algebra.fixedEquiv
#print axioms Chapter10.Algebra.fixed_qubo_identity
#print axioms Chapter10.Algebra.fixed_qubo_min_transport
