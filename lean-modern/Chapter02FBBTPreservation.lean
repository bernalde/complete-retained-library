module

public import Chapter02FBBTOrder

@[expose] public section

noncomputable section
open Classical
open scoped BigOperators
namespace Chapter02FBBT

 theorem members_nonempty_iff {ι} (q : Bounds ι) : (members q).Nonempty ↔ Ordered q :=
  ⟨fun ⟨_, hx⟩ i => (hx i).1.trans (hx i).2, fun h => ⟨q.1, fun i => ⟨le_rfl, h i⟩⟩⟩
 theorem members_clip_iff {ι} (p q : Bounds ι) (x) :
    x ∈ members (clip p q) ↔ x ∈ members p ∧ x ∈ members q := by
  simp only [members, clip, Set.mem_setOf_eq, max_le_iff, le_min_iff]
  constructor
  · intro h; exact ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩,
      fun i => ⟨(h i).1.2, (h i).2.2⟩⟩
  · rintro ⟨h,k⟩; exact fun i => ⟨⟨(h i).1,(k i).1⟩,⟨(h i).2,(k i).2⟩⟩

 theorem graph_upward {n m} (A : Matrix n m) (q : JointBounds n m) (x)
    (h : graph A x ∈ members q) : graph A x ∈ members (upward A q) := by
  intro s; cases s with
  | inl j => exact h (.inl j)
  | inr i =>
    have hb := Chapter02.affine_image_bounds
      (⟨A i, 0, q.1 (.inr i), q.2 (.inr i)⟩ : Chapter02.AffineIntervalRow n)
      (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)) x (fun j => h (.inl j))
    simp only [Chapter02.AffineIntervalRow.imageLo, Chapter02.AffineIntervalRow.imageHi,
      Chapter02.AffineIntervalRow.value, zero_add] at hb
    exact ⟨max_le (h (.inr i)).1 hb.1, le_min (h (.inr i)).2 hb.2⟩

 theorem graph_inverses {n m} (A : Matrix n m) (q : JointBounds n m) (x)
    (h : graph A x ∈ members q) (i j) :
    inverseLo A q i j ≤ x j ∧ x j ≤ inverseHi A q i j := by
  have hb := Chapter02.affine_inverse_bounds
    (⟨A i, 0, q.1 (.inr i), q.2 (.inr i)⟩ : Chapter02.AffineIntervalRow n)
    (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)) x
    (q.1 (.inr i)) (q.2 (.inr i)) (fun j => h (.inl j))
    (by simpa [Chapter02.AffineIntervalRow.value, graph] using h (.inr i)) j
  simpa [inverseLo, inverseHi, restLo, restHi, productLo, productHi,
    Chapter02.AffineIntervalRow.impliedLo, Chapter02.AffineIntervalRow.impliedHi,
    Chapter02.AffineIntervalRow.restLo, Chapter02.AffineIntervalRow.restHi] using hb

 theorem graph_downward {n m} (A : Matrix n m) (q : JointBounds n m) (x)
    (h : graph A x ∈ members q) : graph A x ∈ members (downward A q) := by
  intro s; cases s with
  | inr i => exact h (.inr i)
  | inl j => exact ⟨(seededMax_le _ _ _).2 ⟨(h (.inl j)).1,
      fun i => (graph_inverses A q x h i j).1⟩,
      (le_seededMin _ _ _).2 ⟨(h (.inl j)).2, fun i => (graph_inverses A q x h i j).2⟩⟩
 theorem graph_rawF {n m} (A : Matrix n m) (q0 q : JointBounds n m) (x)
    (h : graph A x ∈ members q) (h0 : graph A x ∈ members q0) :
    graph A x ∈ members (rawF A q0 q) :=
  graph_downward _ _ _ (graph_upward _ _ _ ((members_clip_iff _ _ _).2 ⟨h,h0⟩))
 theorem graph_rawRun {n m} (A : Matrix n m) (q0 : JointBounds n m) (x)
    (h : graph A x ∈ members q0) (k) : graph A x ∈ members (rawRun A q0 k) := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [rawRun, Function.iterate_succ_apply'] using graph_rawF A q0 _ x ih h

 theorem rawRun_within_initial {n m} (A : Matrix n m) (q0 : JointBounds n m) (k) :
    Within (rawRun A q0 k) q0 := by
  cases k with
  | zero => exact within_refl _
  | succ k => simpa only [rawRun, Function.iterate_succ_apply'] using rawF_within_initial A q0 (rawRun A q0 k)

/-- Any invalid intermediate intersection persists to the final raw output. -/
 theorem rawF_invalid_persists {n m} (A : Matrix n m) (q0 q : JointBounds n m) :
    (¬ Ordered q ∨ ¬ Ordered (clip q q0) ∨ ¬ Ordered (upward A (clip q q0))) →
      ¬ Ordered (rawF A q0 q) := by
  intro h hf
  rcases h with h | h | h
  · exact h (ordered_of_within hf (rawF_contract _ _ _))
  · exact h (ordered_of_within hf (within_trans (downward_contract _ _) (upward_contract _ _)))
  · exact h (ordered_of_within hf (downward_contract _ _))

 theorem public_members_ofBounds {ι} (q : Bounds ι) :
    (publicOfBounds q).members = members q := by
  unfold publicOfBounds
  split_ifs with h
  · rfl
  · apply Set.ext; intro x
    simp only [PublicState.members, Set.mem_empty_iff_false, false_iff]
    exact fun hx => h (fun i => (hx i).1.trans (hx i).2)
 theorem public_empty_iff {ι} (q : Bounds ι) : publicOfBounds q = .empty ↔ ¬ Ordered q := by
  unfold publicOfBounds
  split_ifs <;> simp_all
 theorem publicF_ofBounds {n m} (A : Matrix n m) (q0 q : JointBounds n m) :
    publicF A q0 (publicOfBounds q) = publicOfBounds (rawF A q0 q) := by
  by_cases h : Ordered q
  · simp only [publicOfBounds, dif_pos h, publicF]
  · have hf : ¬ Ordered (rawF A q0 q) := fun hf => h (ordered_of_within hf (rawF_contract _ _ _))
    simp only [publicOfBounds, dif_neg h, publicF, dif_neg hf]
 theorem public_raw_agreement {n m} (A : Matrix n m) (q0 : JointBounds n m) (k) :
    publicRun A q0 k = publicOfBounds (rawRun A q0 k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [publicRun, rawRun, Function.iterate_succ_apply']
    change publicF A q0 (publicRun A q0 k) = publicOfBounds (rawF A q0 (rawRun A q0 k))
    rw [ih, publicF_ofBounds]
 theorem public_run_nonempty_iff {n m} (A : Matrix n m) (q0 : JointBounds n m) :
    (∀ k, (publicRun A q0 k).members.Nonempty) ↔ ∀ k, Ordered (rawRun A q0 k) := by
  simp only [public_raw_agreement, public_members_ofBounds, members_nonempty_iff]

/-- A graph singleton is an actual fixed state, independently of any run premise. -/
 theorem graph_singleton_fixed {n m} (A : Matrix n m) (q0 : JointBounds n m) (x)
    (h : graph A x ∈ members q0) :
    rawF A q0 (graph A x, graph A x) = (graph A x, graph A x) := by
  have hs : graph A x ∈ members (graph A x, graph A x) := fun _ => ⟨le_rfl, le_rfl⟩
  have hp := graph_rawF A q0 _ x hs h
  apply within_antisymm (rawF_contract _ _ _)
  exact hp

end Chapter02FBBT
