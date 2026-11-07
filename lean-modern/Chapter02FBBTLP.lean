module

public import Chapter02FBBTPreservation

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter02FBBT

 theorem upward_fixed_iff {n m} (A : Matrix n m) (q : JointBounds n m) :
    upward A q = q ↔ ∀ i, imageLo A q i ≤ q.1 (.inr i) ∧ q.2 (.inr i) ≤ imageHi A q i := by
  constructor
  · intro h i
    have hl := congrArg (fun p : JointBounds n m => p.1 (.inr i)) h
    have hu := congrArg (fun p : JointBounds n m => p.2 (.inr i)) h
    change max (q.1 (.inr i)) (imageLo A q i) = q.1 (.inr i) at hl
    change min (q.2 (.inr i)) (imageHi A q i) = q.2 (.inr i) at hu
    exact ⟨(le_max_right _ _).trans_eq hl, hu.symm.trans_le (min_le_right _ _)⟩
  · intro h; apply Prod.ext <;> funext s <;> cases s with
    | inl j => rfl
    | inr i => first | exact max_eq_left (h i).1 | exact min_eq_left (h i).2

 theorem downward_fixed_iff {n m} (A : Matrix n m) (q : JointBounds n m) :
    downward A q = q ↔ ∀ i j, inverseLo A q i j ≤ q.1 (.inl j) ∧
      q.2 (.inl j) ≤ inverseHi A q i j := by
  constructor
  · intro h i j
    have hl := congrArg (fun p : JointBounds n m => p.1 (.inl j)) h
    have hu := congrArg (fun p : JointBounds n m => p.2 (.inl j)) h
    change seededMax (q.1 (.inl j)) (fun i => inverseLo A q i j) = q.1 (.inl j) at hl
    change seededMin (q.2 (.inl j)) (fun i => inverseHi A q i j) = q.2 (.inl j) at hu
    exact ⟨(value_le_max _ _ i).trans_eq hl, hu.symm.trans_le (min_le_value _ _ i)⟩
  · intro h; apply Prod.ext <;> funext s <;> cases s with
    | inr i => rfl
    | inl j =>
      first
      | exact le_antisymm ((seededMax_le _ _ _).2 ⟨le_rfl,fun i => (h i j).1⟩) (seed_le_max _ _)
      | exact le_antisymm (min_le_seed _ _) ((le_seededMin _ _ _).2 ⟨le_rfl,fun i => (h i j).2⟩)

 theorem canonical_feasible_iff {n m} (A : Matrix n m) (q0 q : JointBounds n m) :
    LPFeasible A q0 (canonicalAssignment A q) ↔ Ordered q ∧ rawF A q0 q = q := by
  rw [rawF_fixed_iff, upward_fixed_iff, downward_fixed_iff]
  constructor
  · rintro ⟨ho,hq,_,_,hu,hp,hn⟩
    refine ⟨ho,hq,hu,?_⟩
    intro i j
    by_cases hz : A i j = 0
    · simp [inverseLo,inverseHi,hz]
    by_cases hs : 0 < A i j
    · simpa only [inverseLo,inverseHi,if_neg hz,if_pos hs,restLo,restHi,
        canonicalAssignment] using hp i j hs
    · have ht : A i j < 0 := lt_of_le_of_ne (le_of_not_gt hs) hz
      simpa only [inverseLo,inverseHi,if_neg hz,if_neg hs,restLo,restHi,
        canonicalAssignment] using hn i j ht
  · rintro ⟨ho,hq,hu,hd⟩
    refine ⟨ho,hq,(fun _ _ => rfl),(fun _ _ => rfl),hu,?_,?_⟩
    · intro i j hp
      simpa only [inverseLo,inverseHi,if_neg (ne_of_gt hp),if_pos hp,restLo,restHi,
        canonicalAssignment] using hd i j
    · intro i j hn
      simpa only [inverseLo,inverseHi,if_neg (ne_of_lt hn),if_neg (not_lt_of_gt hn),restLo,restHi,
        canonicalAssignment] using hd i j

 theorem assignment_unique {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (p : LPAssignment n m) (h : LPFeasible A q0 p) : p = canonicalAssignment A p.bounds := by
  cases p with | mk q l u =>
    have hl : l = productLo A q := funext fun i => funext fun j => h.2.2.1 i j
    have hu : u = productHi A q := funext fun i => funext fun j => h.2.2.2.1 i j
    cases hl; cases hu; rfl

 theorem lp_fixed_equivalence {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (p : LPAssignment n m) : LPFeasible A q0 p ↔
    Ordered p.bounds ∧ rawF A q0 p.bounds = p.bounds ∧ p = canonicalAssignment A p.bounds := by
  constructor
  · intro h
    have he := assignment_unique A q0 p h
    have hf := (canonical_feasible_iff A q0 p.bounds).1 (he ▸ h)
    exact ⟨hf.1,hf.2,he⟩
  · rintro ⟨ho,hf,he⟩
    rw [he]
    exact (canonical_feasible_iff A q0 p.bounds).2 ⟨ho,hf⟩

 theorem graph_singleton_lp {n m} (A : Matrix n m) (q0 : JointBounds n m) (x)
    (h : graph A x ∈ members q0) :
    LPFeasible A q0 (canonicalAssignment A (graph A x, graph A x)) :=
  (canonical_feasible_iff _ _ _).2 ⟨fun _ => le_rfl, graph_singleton_fixed _ _ _ h⟩

 theorem lp_infeasible_no_graph {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (h : ¬ ∃ p, LPFeasible A q0 p) : ¬ ∃ x, graph A x ∈ members q0 := by
  rintro ⟨x,hx⟩
  exact h ⟨_,graph_singleton_lp A q0 x hx⟩

 theorem objective_both_widths {n m} (p : LPAssignment n m) :
    LPObjective p = (∑ j, (p.bounds.2 (.inl j) - p.bounds.1 (.inl j))) +
      (∑ i, (p.bounds.2 (.inr i) - p.bounds.1 (.inr i))) := by
  simp only [LPObjective, width, Fintype.sum_sum_type]

 theorem zero_product_equalities {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (p : LPAssignment n m) (h : LPFeasible A q0 p) (i j) (hz : A i j = 0) :
    p.zLo i j = 0 ∧ p.zHi i j = 0 := by
  rw [h.2.2.1 i j, h.2.2.2.1 i j]
  simp [productLo,productHi,Chapter02.affineProductLo,Chapter02.affineProductHi,hz]

end Chapter02FBBT
