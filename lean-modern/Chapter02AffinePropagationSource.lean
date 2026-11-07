module

public import Chapter02AffinePropagation
public import Chapter02BBAdapter

@[expose] public section

/-! Literal original-coordinate MINLP adapter. BBPolyData has no built-in
variable enclosure: every endpoint here explicitly intersects the initial box.
Each one-sided row's finite lower endpoint is derived from that box's image. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

def affineSourceRow {n l r : ℕ} (D : BBPolyData n l r) (X0 : AffineBox n)
    (i : Fin r) : AffineIntervalRow n where
  coefficient := D.coefficient i
  offset := 0
  lower := match X0 with
    | .empty => 0 -- no represented point in this branch
    | .interval a b _ => ∑ j, affineProductLo (D.coefficient i j) (a j) (b j)
  upper := D.rhs i

theorem affine_source_row_holds {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (i : Fin r) (x : RealVector n)
    (hf : x ∈ D.feasible I) (hx : x ∈ X0.members) :
    (affineSourceRow D X0 i).Holds x := by
  cases X0 with
  | empty => exact False.elim hx
  | interval a b ho =>
    constructor
    · have hb := (affine_image_bounds (affineSourceRow D (.interval a b ho) i)
        a b x hx).1
      simpa [affineSourceRow, AffineIntervalRow.imageLo] using hb
    · simpa [affineSourceRow, AffineIntervalRow.value] using hf.1 i

def affineSourcePropagate {n l r : ℕ} (D : BBPolyData n l r)
    (X0 : AffineBox n) (visits : List (Fin r)) : AffineBox n :=
  affinePropagate (visits.map (affineSourceRow D X0)) X0

/-- All original affine/nonlinear rows and designated integrality remain in D;
visits may omit or repeat rows, but no processed row is removed from the base. -/
theorem affine_source_preservation {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r)) :
    D.feasible I ∩ (affineSourcePropagate D X0 visits).members =
      D.feasible I ∩ X0.members := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, affine_propagate_contracts _ X0 hx.2⟩
  · intro hx
    refine ⟨hx.1, affine_propagate_preserves _ X0 x hx.2 ?_⟩
    intro row hrow
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    exact affine_source_row_holds D I X0 i x hx.1 hx.2

theorem affine_source_empty_certificate {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r))
    (he : affineSourcePropagate D X0 visits = .empty) :
    D.feasible I ∩ X0.members = ∅ := by
  rw [← affine_source_preservation D I X0 visits, he]
  exact Set.inter_empty _

theorem affine_source_minimizer_iff {n l r : ℕ} (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X0 : AffineBox n) (visits : List (Fin r))
    (x : RealVector n) :
    IsMinimizer (D.feasible I ∩ (affineSourcePropagate D X0 visits).members) D.f x ↔
      IsMinimizer (D.feasible I ∩ X0.members) D.f x := by
  rw [affine_source_preservation]

#print axioms affine_source_row_holds
#print axioms affine_source_preservation
#print axioms affine_source_empty_certificate
#print axioms affine_source_minimizer_iff

end Chapter02
