module

public import Chapter02BBAdapter
public import Chapter02BBNodes

@[expose] public section

/-! Literal original-coordinate Algorithm 1/2 semantics for the held Belotti
manuscript. The heap is a list of occurrences, interpreting the pseudocode's
heap/set notation. This relation is defined independently of the finite engine.
The upper value U is represented exactly by the optional incumbent: infinity
when absent, its objective when present. There is no independent inconsistent U.
Only solved-value strict pruning is included here; the prose/weak and stored-
bound variants are separate. The printed epsilon does not occur in a test. -/
noncomputable section
namespace Chapter02
variable {N l r : ℕ} {I : Finset (Fin N)}

abbrev BBExternalNode (I : Finset (Fin N)) := BBExtendedNode {i : Fin N // i ∈ I}

structure BBExternalState (I : Finset (Fin N)) where
  live : List (BBExternalNode I)
  incumbent : Option (RealVector N)

def bbExternalUpper (f : RealVector N → ℝ) : Option (RealVector N) → WithTop ℝ
  | none => ⊤
  | some z => (f z : WithTop ℝ)

def bbExternalInteger (I : Finset (Fin N)) (z : RealVector N) : Prop :=
  ∀ i : {i : Fin N // i ∈ I}, ∃ k : ℤ, (k : ℝ) = z i

def bbExternalInitial (I : Finset (Fin N)) : BBExternalState I :=
  ⟨[BBExtendedNode.root], none⟩

/-- Checks follow Algorithm 1: empty, strict worse, integral (replace on ties),
otherwise branch. Every mathematical solve witness is specific to this node. -/
inductive BBExternalProcess (D : BBPolyData N l r) (I : Finset (Fin N)) :
    BBExternalState I → BBExternalState I → Prop
  | empty {pre post : List (BBExternalNode I)} {B : BBExternalNode I} {inc}
      (he : D.relaxation B = ∅) :
      BBExternalProcess D I ⟨pre ++ B :: post, inc⟩ ⟨pre ++ post, inc⟩
  | prune {pre post : List (BBExternalNode I)} {B : BBExternalNode I} {inc z}
      (hz : IsMinimizer (D.relaxation B) D.f z)
      (hp : bbExternalUpper D.f inc < (D.f z : WithTop ℝ)) :
      BBExternalProcess D I ⟨pre ++ B :: post, inc⟩ ⟨pre ++ post, inc⟩
  | integral {pre post : List (BBExternalNode I)} {B : BBExternalNode I} {inc z}
      (hz : IsMinimizer (D.relaxation B) D.f z)
      (hk : ¬ bbExternalUpper D.f inc < (D.f z : WithTop ℝ))
      (hi : bbExternalInteger I z) :
      BBExternalProcess D I ⟨pre ++ B :: post, inc⟩ ⟨pre ++ post, some z⟩
  | branch {pre post : List (BBExternalNode I)} {B : BBExternalNode I} {inc z}
      (i : {i : Fin N // i ∈ I}) (hz : IsMinimizer (D.relaxation B) D.f z)
      (hk : ¬ bbExternalUpper D.f inc < (D.f z : WithTop ℝ))
      (hi : BBFractional (z i)) :
      BBExternalProcess D I ⟨pre ++ B :: post, inc⟩
        ⟨pre ++ [B.left i (z i), B.right i (z i)] ++ post, inc⟩

inductive BBExternalTrace (D : BBPolyData N l r) (I : Finset (Fin N)) :
    BBExternalState I → ℕ → BBExternalState I → Prop
  | refl (s) : BBExternalTrace D I s 0 s
  | step {s t u k} (h : BBExternalTrace D I s k t) (hstep : BBExternalProcess D I t u) :
      BBExternalTrace D I s (k + 1) u

def BBExternalReachable (D : BBPolyData N l r) (I : Finset (Fin N))
    (s : BBExternalState I) : Prop := ∃ k, BBExternalTrace D I (bbExternalInitial I) k s

theorem bb_external_fractional_exists {z : RealVector N}
    (h : ¬ bbExternalInteger I z) : ∃ i : {i : Fin N // i ∈ I}, BBFractional (z i) := by
  classical
  by_contra hn
  apply h
  intro i
  by_contra hi
  exact hn ⟨i, hi⟩

theorem bb_external_nonblocking_at (D : BBPolyData N l r)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : ContinuousOn D.f D.polyhedron)
    (pre post : List (BBExternalNode I)) (B : BBExternalNode I)
    (inc : Option (RealVector N)) :
    ∃ t, BBExternalProcess D I ⟨pre ++ B :: post, inc⟩ t := by
  classical
  rcases D.relaxation_empty_or_minimum B hX hc hf with he | ⟨z, hz⟩
  · exact ⟨_, .empty he⟩
  · by_cases hp : bbExternalUpper D.f inc < (D.f z : WithTop ℝ)
    · exact ⟨_, .prune hz hp⟩
    · by_cases hi : bbExternalInteger I z
      · exact ⟨_, .integral hz hp hi⟩
      · obtain ⟨i, hi⟩ := bb_external_fractional_exists hi
        exact ⟨_, .branch i hz hp hi⟩

theorem bb_external_nonblocking (D : BBPolyData N l r)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : ContinuousOn D.f D.polyhedron) (s : BBExternalState I) (hne : s.live ≠ []) :
    ∃ t, BBExternalProcess D I s t := by
  rcases s with ⟨live, inc⟩
  cases live with
  | nil => exact (hne rfl).elim
  | cons B post => exact bb_external_nonblocking_at D hX hc hf [] post B inc

theorem bb_external_process_live_nonempty (D : BBPolyData N l r)
    {s t : BBExternalState I} (h : BBExternalProcess D I s t) : s.live ≠ [] := by
  cases h <;> simp

theorem bb_external_no_step_iff (D : BBPolyData N l r)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : ContinuousOn D.f D.polyhedron) (s : BBExternalState I) :
    (¬ ∃ t, BBExternalProcess D I s t) ↔ s.live = [] := by
  constructor
  · intro h
    by_contra hn
    exact h (bb_external_nonblocking D hX hc hf s hn)
  · rintro he ⟨t, ht⟩
    exact bb_external_process_live_nonempty D ht he

theorem bb_external_root_empty_implies_infeasible (D : BBPolyData N l r)
    (he : D.relaxation (BBExtendedNode.root : BBExternalNode I) = ∅) :
    D.feasible I = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨hx, hc, _⟩
  have hr : z ∈ D.relaxation (BBExtendedNode.root : BBExternalNode I) :=
    ⟨hx, hc, BBExtendedNode.holds_root _⟩
  simp only [he, Set.mem_empty_iff_false] at hr

theorem bb_external_integral_root_optimal (D : BBPolyData N l r)
    {z : RealVector N}
    (hz : IsMinimizer (D.relaxation (BBExtendedNode.root : BBExternalNode I)) D.f z)
    (hi : bbExternalInteger I z) : IsMinimizer (D.feasible I) D.f z := by
  refine ⟨⟨hz.1.1, hz.1.2.1, hi⟩, ?_⟩
  rintro w ⟨hx, hc, _⟩
  exact hz.2 w ⟨hx, hc, BBExtendedNode.holds_root _⟩

theorem bb_external_left_subset (D : BBPolyData N l r) (B : BBExternalNode I)
    (q : RealVector N) (hq : q ∈ D.relaxation B) (i : {i : Fin N // i ∈ I}) :
    D.relaxation (B.left i (q i)) ⊆ D.relaxation B := by
  classical
  rintro z ⟨hx, hc, hb⟩
  refine ⟨hx, hc, ?_⟩
  intro j
  by_cases hj : j = i
  · subst j
    refine ⟨(hb i).1, ?_⟩
    have hz : z i ≤ (Int.floor (q i) : ℝ) := by
      simpa only [BBExtendedNode.left, Function.update_self, WithTop.coe_le_coe] using (hb i).2
    exact (show (z i : WithTop ℝ) ≤ (q i : WithTop ℝ) by
      exact WithTop.coe_le_coe.mpr (hz.trans (Int.floor_le _))).trans (hq.2.2 i).2
  · simpa [BBExtendedNode.left, Function.update, hj] using hb j

theorem bb_external_right_subset (D : BBPolyData N l r) (B : BBExternalNode I)
    (q : RealVector N) (hq : q ∈ D.relaxation B) (i : {i : Fin N // i ∈ I}) :
    D.relaxation (B.right i (q i)) ⊆ D.relaxation B := by
  classical
  rintro z ⟨hx, hc, hb⟩
  refine ⟨hx, hc, ?_⟩
  intro j
  by_cases hj : j = i
  · subst j
    refine ⟨?_, (hb i).2⟩
    have hz : (Int.ceil (q i) : ℝ) ≤ z i := by
      simpa only [BBExtendedNode.right, Function.update_self, WithBot.coe_le_coe] using (hb i).1
    exact (hq.2.2 i).1.trans (show (q i : WithBot ℝ) ≤ (z i : WithBot ℝ) by
      exact WithBot.coe_le_coe.mpr ((Int.le_ceil _).trans hz))
  · simpa [BBExtendedNode.right, Function.update, hj] using hb j

/-- Literal generation of a child from a feasible relaxation trial. Membership
suffices for containment; a global-minimum premise is unnecessary here. -/
inductive BBExternalChild (D : BBPolyData N l r) : BBExternalNode I → BBExternalNode I → Prop
  | left (B) (q : RealVector N) (hq : q ∈ D.relaxation B) (i : {i : Fin N // i ∈ I})
      (hi : BBFractional (q i)) : BBExternalChild D B (B.left i (q i))
  | right (B) (q : RealVector N) (hq : q ∈ D.relaxation B) (i : {i : Fin N // i ∈ I})
      (hi : BBFractional (q i)) : BBExternalChild D B (B.right i (q i))

theorem bb_external_child_subset (D : BBPolyData N l r)
    {B C : BBExternalNode I} (h : BBExternalChild D B C) :
    D.relaxation C ⊆ D.relaxation B := by
  cases h with
  | left q hq i _ => exact bb_external_left_subset D _ q hq i
  | right q hq i _ => exact bb_external_right_subset D _ q hq i

theorem bb_external_subtree_subset (D : BBPolyData N l r)
    {B C : BBExternalNode I} (h : Relation.ReflTransGen (BBExternalChild D) B C) :
    D.relaxation C ⊆ D.relaxation B := by
  induction h with
  | refl => exact Set.Subset.refl _
  | tail _ hchild ih => exact (bb_external_child_subset D hchild).trans ih

theorem bb_external_infeasible_subtree (D : BBPolyData N l r)
    {B C : BBExternalNode I} (h : Relation.ReflTransGen (BBExternalChild D) B C)
    (he : D.relaxation B = ∅) : D.relaxation C = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hb := bb_external_subtree_subset D h hz
  simp only [he, Set.mem_empty_iff_false] at hb

/-- Arbitrary additional restrictions, including restrictions never generated
because an ancestor was already empty. This avoids making the source subtree
claim vacuous through a feasible-trial requirement. -/
def BBExtendedNode.Refines {ι : Type*} (C B : BBExtendedNode ι) : Prop :=
  ∀ i, B.lower i ≤ C.lower i ∧ C.upper i ≤ B.upper i

theorem bb_external_refined_subset (D : BBPolyData N l r)
    {B C : BBExternalNode I} (h : C.Refines B) :
    D.relaxation C ⊆ D.relaxation B := by
  rintro z ⟨hx, hc, hb⟩
  exact ⟨hx, hc, fun i => ⟨(h i).1.trans (hb i).1, (hb i).2.trans (h i).2⟩⟩

theorem bb_external_infeasible_refinement (D : BBPolyData N l r)
    {B C : BBExternalNode I} (h : C.Refines B) (he : D.relaxation B = ∅) :
    D.relaxation C = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hb := bb_external_refined_subset D h hz
  simp only [he, Set.mem_empty_iff_false] at hb

end Chapter02

#print axioms Chapter02.bb_external_fractional_exists
#print axioms Chapter02.bb_external_nonblocking_at
#print axioms Chapter02.bb_external_nonblocking
#print axioms Chapter02.bb_external_process_live_nonempty
#print axioms Chapter02.bb_external_no_step_iff
#print axioms Chapter02.bb_external_root_empty_implies_infeasible
#print axioms Chapter02.bb_external_integral_root_optimal
#print axioms Chapter02.bb_external_left_subset
#print axioms Chapter02.bb_external_right_subset
#print axioms Chapter02.bb_external_child_subset
#print axioms Chapter02.bb_external_subtree_subset
#print axioms Chapter02.bb_external_infeasible_subtree
#print axioms Chapter02.bb_external_refined_subset
#print axioms Chapter02.bb_external_infeasible_refinement
