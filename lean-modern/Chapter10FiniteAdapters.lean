module

public import Chapter10QUBOAlgebra

@[expose] public section

/-! Explicit finite enumeration/real-binary adapters for accepted Chapter10
interfaces. These preserve every source coordinate and sum. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Algebra

theorem binary_bit {ι : Type*} (x : ι → Bool) : Binary (fun i => Chapter10.bit (x i)) := by
  intro i
  cases h : x i <;> simp [Chapter10.bit, h]

theorem encode_bit {ι : Type*} (x : ι → Bool) : encode (fun i => Chapter10.bit (x i)) = x := by
  funext i
  cases h : x i <;> simp [encode, Chapter10.bit, h]

def realBinaryEquivBits (ι : Type*) : {x : ι → ℝ // Binary x} ≃ (ι → Bool) where
  toFun x := encode x.1
  invFun x := ⟨fun i => Chapter10.bit (x i), binary_bit x⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact bit_encode x.2 i
  right_inv x := encode_bit x

theorem linearCost_fin_encoding {ι : Type*} [Fintype ι] (c x : ι → ℝ)
    (hx : Binary x) :
    Chapter10.cost (fun k => c ((Fintype.equivFin ι).symm k))
      (fun k => encode x ((Fintype.equivFin ι).symm k)) = linearCost c x := by
  unfold Chapter10.cost linearCost
  simp_rw [bit_encode hx]
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => c i * x i)

theorem finite_binary_cost_range_from_accepted {ι : Type*} [Fintype ι]
    (c x y : ι → ℝ) (hx : Binary x) (hy : Binary y) :
    linearCost c x - linearCost c y ≤ ∑ i, |c i| := by
  have h := Chapter10.cost_range_bound
    (fun k => c ((Fintype.equivFin ι).symm k))
    (fun k => encode x ((Fintype.equivFin ι).symm k))
    (fun k => encode y ((Fintype.equivFin ι).symm k))
  rw [linearCost_fin_encoding c x hx, linearCost_fin_encoding c y hy] at h
  simpa only [(Fintype.equivFin ι).symm.sum_comp (fun i => |c i|)] using h

theorem quadratic_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : κ → κ → ℝ) (x : κ → ℝ) :
    quadratic (fun i j => M (e i) (e j)) (fun i => x (e i)) = quadratic M x := by
  unfold quadratic
  calc
    _ = ∑ i : ι, ∑ j : κ, M (e i) j * x (e i) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_comp (fun j => M (e i) j * x (e i) * x j)
    _ = _ := e.sum_comp (fun i => ∑ j, M i j * x i * x j)

theorem binary_reindex_iff {ι κ : Type*} (e : ι ≃ κ) (x : κ → ℝ) :
    Binary (fun i => x (e i)) ↔ Binary x := by
  constructor
  · intro h j
    simpa using h (e.symm j)
  · intro h i
    exact h (e i)

end Chapter10.Algebra

#print axioms Chapter10.Algebra.finite_binary_cost_range_from_accepted
