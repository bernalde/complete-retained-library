module

public import Chapter02Model

@[expose] public section

/-! Literal real bounds for exact NLP branch and bound. Empty boxes are allowed.
The rank and child-weight decrease are derived from floor/ceiling arithmetic;
there is no progress field or integer normalization of the root. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

structure BBNode (m : ℕ) where
  lower : RealVector m
  upper : RealVector m

def BBFractional (v : ℝ) : Prop := ¬ ∃ z : ℤ, (z : ℝ) = v

def BBNode.box {m n : ℕ} (N : BBNode m) : Set (Point n m) :=
  {p | ∀ i, N.lower i ≤ p.2 i ∧ p.2 i ≤ N.upper i}

def BBNode.Refines {m : ℕ} (child parent : BBNode m) : Prop :=
  ∀ i, parent.lower i ≤ child.lower i ∧ child.upper i ≤ parent.upper i

def BBNode.left {m : ℕ} (N : BBNode m) (i : Fin m) (v : ℝ) : BBNode m :=
  ⟨N.lower, Function.update N.upper i (Int.floor v : ℝ)⟩

def BBNode.right {m : ℕ} (N : BBNode m) (i : Fin m) (v : ℝ) : BBNode m :=
  ⟨Function.update N.lower i (Int.ceil v : ℝ), N.upper⟩

def BBNode.span {m : ℕ} (N : BBNode m) (i : Fin m) : ℕ :=
  Int.toNat (Int.ceil (N.upper i) - Int.floor (N.lower i))

def BBNode.rank {m : ℕ} (N : BBNode m) : ℕ := ∑ i, N.span i

def BBNode.weight {m : ℕ} (N : BBNode m) : ℕ := 2 ^ (N.rank + 1) - 1

theorem bb_refines_refl {m : ℕ} (N : BBNode m) : N.Refines N :=
  fun _ => ⟨le_rfl, le_rfl⟩

theorem bb_refines_trans {m : ℕ} {A B C : BBNode m}
    (hAB : A.Refines B) (hBC : B.Refines C) : A.Refines C :=
  fun i => ⟨(hBC i).1.trans (hAB i).1, (hAB i).2.trans (hBC i).2⟩

theorem bb_box_subset_of_refines {m n : ℕ} {A B : BBNode m}
    (h : A.Refines B) : A.box (n := n) ⊆ B.box := by
  intro p hp i
  exact ⟨(h i).1.trans (hp i).1, (hp i).2.trans (h i).2⟩

theorem bb_fractional_floor_lt {v : ℝ} (h : BBFractional v) : (Int.floor v : ℝ) < v := by
  refine lt_of_le_of_ne (Int.floor_le v) ?_
  intro heq
  exact h ⟨Int.floor v, heq⟩

theorem bb_fractional_lt_ceil {v : ℝ} (h : BBFractional v) : v < (Int.ceil v : ℝ) := by
  refine lt_of_le_of_ne (Int.le_ceil v) ?_
  intro heq
  exact h ⟨Int.ceil v, heq.symm⟩

theorem bb_fractional_ceil_eq {v : ℝ} (h : BBFractional v) :
    Int.ceil v = Int.floor v + 1 :=
  (Int.ceil_eq_floor_add_one_iff_notMem v).2 h

theorem bb_left_refines {m n : ℕ} (N : BBNode m) (i : Fin m) (q : Point n m)
    (hq : q ∈ N.box) : (N.left i (q.2 i)).Refines N := by
  intro j
  refine ⟨le_rfl, ?_⟩
  by_cases hji : j = i
  · subst j
    simpa [BBNode.left] using (Int.floor_le (q.2 i)).trans (hq i).2
  · simp [BBNode.left, Function.update_of_ne hji]

theorem bb_right_refines {m n : ℕ} (N : BBNode m) (i : Fin m) (q : Point n m)
    (hq : q ∈ N.box) : (N.right i (q.2 i)).Refines N := by
  intro j
  refine ⟨?_, le_rfl⟩
  by_cases hji : j = i
  · subst j
    simpa [BBNode.right] using (hq i).1.trans (Int.le_ceil (q.2 i))
  · simp [BBNode.right, Function.update_of_ne hji]

theorem bb_mem_left_iff {m n : ℕ} (N : BBNode m) (i : Fin m)
    (q p : Point n m) (hq : q ∈ N.box) :
    p ∈ (N.left i (q.2 i)).box ↔ p ∈ N.box ∧ p.2 i ≤ (Int.floor (q.2 i) : ℝ) := by
  constructor
  · intro hp
    exact ⟨bb_box_subset_of_refines (bb_left_refines N i q hq) hp,
      by simpa [BBNode.left] using (hp i).2⟩
  · rintro ⟨hp, hpi⟩ j
    refine ⟨(hp j).1, ?_⟩
    by_cases hji : j = i
    · subst j; simpa [BBNode.left] using hpi
    · simpa [BBNode.left, Function.update_of_ne hji] using (hp j).2

theorem bb_mem_right_iff {m n : ℕ} (N : BBNode m) (i : Fin m)
    (q p : Point n m) (hq : q ∈ N.box) :
    p ∈ (N.right i (q.2 i)).box ↔ p ∈ N.box ∧ (Int.ceil (q.2 i) : ℝ) ≤ p.2 i := by
  constructor
  · intro hp
    exact ⟨bb_box_subset_of_refines (bb_right_refines N i q hq) hp,
      by simpa [BBNode.right] using (hp i).1⟩
  · rintro ⟨hp, hpi⟩ j
    refine ⟨?_, (hp j).2⟩
    by_cases hji : j = i
    · subst j; simpa [BBNode.right] using hpi
    · simpa [BBNode.right, Function.update_of_ne hji] using (hp j).1

theorem bb_children_integer_cover {m n : ℕ} (N : BBNode m) (i : Fin m)
    (q p : Point n m) (hq : q ∈ N.box) (hp : p ∈ N.box)
    (hi : ∃ z : ℤ, (z : ℝ) = p.2 i) :
    p ∈ (N.left i (q.2 i)).box ∨ p ∈ (N.right i (q.2 i)).box := by
  obtain ⟨z, hz⟩ := hi
  have hd : z ≤ Int.floor (q.2 i) ∨ Int.ceil (q.2 i) ≤ z := by
    have hc := Int.ceil_le_floor_add_one (q.2 i)
    omega
  rcases hd with hl | hr
  · left
    apply (bb_mem_left_iff N i q p hq).2
    exact ⟨hp, by rw [← hz]; exact_mod_cast hl⟩
  · right
    apply (bb_mem_right_iff N i q p hq).2
    exact ⟨hp, by rw [← hz]; exact_mod_cast hr⟩

theorem bb_children_disjoint {m n : ℕ} (N : BBNode m) (i : Fin m)
    (q : Point n m) (hf : BBFractional (q.2 i)) :
    Disjoint ((N.left i (q.2 i)).box (n := n)) ((N.right i (q.2 i)).box) := by
  apply Set.disjoint_left.2
  intro p hl hr
  have hl' : p.2 i ≤ (Int.floor (q.2 i) : ℝ) := by
    simpa [BBNode.left] using (hl i).2
  have hr' : (Int.ceil (q.2 i) : ℝ) ≤ p.2 i := by
    simpa [BBNode.right] using (hr i).1
  have h1 := bb_fractional_floor_lt hf
  have h2 := bb_fractional_lt_ceil hf
  linarith

theorem bb_children_exclude_trial {m n : ℕ} (N : BBNode m) (i : Fin m)
    (q : Point n m) (hf : BBFractional (q.2 i)) :
    q ∉ (N.left i (q.2 i)).box ∧ q ∉ (N.right i (q.2 i)).box := by
  constructor
  · intro h
    have hh : q.2 i ≤ (Int.floor (q.2 i) : ℝ) := by
      simpa [BBNode.left] using (h i).2
    exact not_le_of_gt (bb_fractional_floor_lt hf) hh
  · intro h
    have hh : (Int.ceil (q.2 i) : ℝ) ≤ q.2 i := by
      simpa [BBNode.right] using (h i).1
    exact not_le_of_gt (bb_fractional_lt_ceil hf) hh

theorem bb_left_span_of_ne {m : ℕ} (N : BBNode m) (i j : Fin m) (v : ℝ)
    (hji : j ≠ i) : (N.left i v).span j = N.span j := by
  simp [BBNode.span, BBNode.left, Function.update_of_ne hji]

theorem bb_right_span_of_ne {m : ℕ} (N : BBNode m) (i j : Fin m) (v : ℝ)
    (hji : j ≠ i) : (N.right i v).span j = N.span j := by
  simp [BBNode.span, BBNode.right, Function.update_of_ne hji]

theorem bb_left_span_lt {m n : ℕ} (N : BBNode m) (i : Fin m) (q : Point n m)
    (hq : q ∈ N.box) (hf : BBFractional (q.2 i)) :
    (N.left i (q.2 i)).span i < N.span i := by
  have ha := Int.floor_mono (hq i).1
  have hb := Int.ceil_mono (hq i).2
  have hc := bb_fractional_ceil_eq hf
  simp only [BBNode.span, BBNode.left, Function.update_self, Int.ceil_intCast]
  omega

theorem bb_right_span_lt {m n : ℕ} (N : BBNode m) (i : Fin m) (q : Point n m)
    (hq : q ∈ N.box) (hf : BBFractional (q.2 i)) :
    (N.right i (q.2 i)).span i < N.span i := by
  have ha := Int.floor_mono (hq i).1
  have hb := Int.ceil_mono (hq i).2
  have hc := bb_fractional_ceil_eq hf
  simp only [BBNode.span, BBNode.right, Function.update_self, Int.floor_intCast]
  omega

theorem bb_left_rank_lt {m n : ℕ} (N : BBNode m) (i : Fin m) (q : Point n m)
    (hq : q ∈ N.box) (hf : BBFractional (q.2 i)) :
    (N.left i (q.2 i)).rank < N.rank := by
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hji : j = i
    · subst j; exact (bb_left_span_lt N i q hq hf).le
    · exact (bb_left_span_of_ne N i j (q.2 i) hji).le
  · exact ⟨i, Finset.mem_univ _, bb_left_span_lt N i q hq hf⟩

theorem bb_right_rank_lt {m n : ℕ} (N : BBNode m) (i : Fin m) (q : Point n m)
    (hq : q ∈ N.box) (hf : BBFractional (q.2 i)) :
    (N.right i (q.2 i)).rank < N.rank := by
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hji : j = i
    · subst j; exact (bb_right_span_lt N i q hq hf).le
    · exact (bb_right_span_of_ne N i j (q.2 i) hji).le
  · exact ⟨i, Finset.mem_univ _, bb_right_span_lt N i q hq hf⟩

theorem bb_weight_pos {m : ℕ} (N : BBNode m) : 0 < N.weight := by
  have h := Nat.one_lt_two_pow' N.rank
  unfold BBNode.weight
  omega

theorem bb_children_weight_drop {m n : ℕ} (N : BBNode m) (i : Fin m)
    (q : Point n m) (hq : q ∈ N.box) (hf : BBFractional (q.2 i)) :
    (N.left i (q.2 i)).weight + (N.right i (q.2 i)).weight + 1 ≤ N.weight := by
  have hl := bb_left_rank_lt N i q hq hf
  have hr := bb_right_rank_lt N i q hq hf
  have hpl := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.succ_le_iff.mpr hl)
  have hpr := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.succ_le_iff.mpr hr)
  have hp : 0 < 2 ^ N.rank := pow_pos (by decide) _
  have hplpos : 0 < 2 ^ ((N.left i (q.2 i)).rank + 1) := pow_pos (by decide) _
  have hprpos : 0 < 2 ^ ((N.right i (q.2 i)).rank + 1) := pow_pos (by decide) _
  simp only [BBNode.weight, Nat.two_pow_succ]
  simp only [Nat.succ_eq_add_one] at hpl hpr
  omega

end Chapter02

#print axioms Chapter02.bb_refines_refl
#print axioms Chapter02.bb_refines_trans
#print axioms Chapter02.bb_box_subset_of_refines
#print axioms Chapter02.bb_fractional_floor_lt
#print axioms Chapter02.bb_fractional_lt_ceil
#print axioms Chapter02.bb_fractional_ceil_eq
#print axioms Chapter02.bb_left_refines
#print axioms Chapter02.bb_right_refines
#print axioms Chapter02.bb_mem_left_iff
#print axioms Chapter02.bb_mem_right_iff
#print axioms Chapter02.bb_children_integer_cover
#print axioms Chapter02.bb_children_disjoint
#print axioms Chapter02.bb_children_exclude_trial
#print axioms Chapter02.bb_left_span_of_ne
#print axioms Chapter02.bb_right_span_of_ne
#print axioms Chapter02.bb_left_span_lt
#print axioms Chapter02.bb_right_span_lt
#print axioms Chapter02.bb_left_rank_lt
#print axioms Chapter02.bb_right_rank_lt
#print axioms Chapter02.bb_weight_pos
#print axioms Chapter02.bb_children_weight_drop
