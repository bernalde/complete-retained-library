module

public import Chapter02BBAffine
public import Chapter02BBBounds
public import Mathlib.Analysis.Convex.Extrema

@[expose] public section

/-! Exact node semantics for finite-real-bound NLP branch and bound.
Classification is classical mathematical existence, not a numerical solver.
Bad-status deletion is sound only under the separately stated compact mixed
base premise and refinement derived by the actual process. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

def bbRootNode {n m l r : ℕ} (d : ModelData n m l r) : BBNode m := ⟨d.lo, d.hi⟩

def BBNode.region {n m l r : ℕ} (N : BBNode m) (d : ModelData n m l r) :=
  bbNodeRelaxation d N.lower N.upper

def BBNode.feasible {n m l r : ℕ} (N : BBNode m) (d : ModelData n m l r) :=
  MixedFeasible d.nonlinearRegion d.linearRegion N.lower N.upper

def BBIntegerPoint {n m : ℕ} (q : Point n m) : Prop :=
  ∃ y : IntVector m, q.2 = fun i => (y i : ℝ)

theorem bb_root_region {n m l r : ℕ} (d : ModelData n m l r) :
    (bbRootNode d).region d = d.relaxationOn Set.univ := by
  ext p
  simp [bbRootNode, BBNode.region, bbNodeRelaxation, ModelData.relaxationOn]

theorem bb_root_feasible {n m l r : ℕ} (d : ModelData n m l r) :
    (bbRootNode d).feasible d = d.feasibleOn Set.univ := by
  simp [bbRootNode, BBNode.feasible, ModelData.feasibleOn]

theorem bb_region_mem_iff {n m l r : ℕ} (d : ModelData n m l r)
    (N : BBNode m) (p : Point n m) :
    p ∈ N.region d ↔ p ∈ d.nonlinearRegion ∧ p ∈ d.linearRegion ∧ p ∈ N.box := Iff.rfl

theorem bb_feasible_mem_iff {n m l r : ℕ} (d : ModelData n m l r)
    (N : BBNode m) (p : Point n m) :
    p ∈ N.feasible d ↔ p ∈ N.region d ∧ BBIntegerPoint p := by
  constructor
  · intro hp
    exact ⟨mixed_subset_relaxation _ _ _ _ hp, hp.2.choose, hp.2.choose_spec.2⟩
  · rintro ⟨hp, y, hy⟩
    refine ⟨⟨hp.1, hp.2.1⟩, y, ?_, hy⟩
    simpa only [IntegerBox, Set.mem_setOf_eq, hy] using hp.2.2

theorem bb_feasible_subset_region {n m l r : ℕ} (d : ModelData n m l r)
    (N : BBNode m) : N.feasible d ⊆ N.region d :=
  fun p hp => ((bb_feasible_mem_iff d N p).mp hp).1

theorem bb_region_subset_of_refines {n m l r : ℕ} (d : ModelData n m l r)
    {A B : BBNode m} (h : A.Refines B) : A.region d ⊆ B.region d := by
  intro p hp
  exact ⟨hp.1, hp.2.1, bb_box_subset_of_refines h hp.2.2⟩

theorem bb_feasible_subset_of_refines {n m l r : ℕ} (d : ModelData n m l r)
    {A B : BBNode m} (h : A.Refines B) : A.feasible d ⊆ B.feasible d := by
  intro p hp
  rw [bb_feasible_mem_iff] at hp ⊢
  exact ⟨bb_region_subset_of_refines d h hp.1, hp.2⟩

theorem bb_feasible_subset_root {n m l r : ℕ} (d : ModelData n m l r)
    {N : BBNode m} (h : N.Refines (bbRootNode d)) :
    N.feasible d ⊆ d.feasibleOn Set.univ := by
  rw [← bb_root_feasible]
  exact bb_feasible_subset_of_refines d h

theorem bb_integer_coordinate {n m : ℕ} {p : Point n m}
    (hp : BBIntegerPoint p) (i : Fin m) : ∃ z : ℤ, (z : ℝ) = p.2 i := by
  obtain ⟨y, hy⟩ := hp
  exact ⟨y i, by rw [hy]⟩

theorem bb_fractional_coordinate {n m : ℕ} {p : Point n m}
    (hp : ¬ BBIntegerPoint p) : ∃ i, BBFractional (p.2 i) := by
  classical
  by_contra h
  have hh : ∀ i, ∃ z : ℤ, (z : ℝ) = p.2 i := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  choose y hy using hh
  exact hp ⟨y, funext (fun i => (hy i).symm)⟩

theorem bb_child_feasible_cover {n m l r : ℕ} (d : ModelData n m l r)
    (N : BBNode m) (i : Fin m) (q : Point n m) (hq : q ∈ N.region d) :
    N.feasible d = (N.left i (q.2 i)).feasible d ∪
      (N.right i (q.2 i)).feasible d := by
  ext p
  constructor
  · intro hp
    obtain ⟨hr, hi⟩ := (bb_feasible_mem_iff d N p).mp hp
    have hh := bb_children_integer_cover N i q p hq.2.2 hr.2.2
      (bb_integer_coordinate hi i)
    rcases hh with hl | hr'
    · exact Or.inl ((bb_feasible_mem_iff d _ p).mpr ⟨⟨hr.1, hr.2.1, hl⟩, hi⟩)
    · exact Or.inr ((bb_feasible_mem_iff d _ p).mpr ⟨⟨hr.1, hr.2.1, hr'⟩, hi⟩)
  · rintro (hp | hp)
    · exact bb_feasible_subset_of_refines d (bb_left_refines N i q hq.2.2) hp
    · exact bb_feasible_subset_of_refines d (bb_right_refines N i q hq.2.2) hp

theorem bb_child_feasible_disjoint {n m l r : ℕ} (d : ModelData n m l r)
    (N : BBNode m) (i : Fin m) (q : Point n m) (hf : BBFractional (q.2 i)) :
    Disjoint ((N.left i (q.2 i)).feasible d) ((N.right i (q.2 i)).feasible d) := by
  apply Set.disjoint_left.mpr
  intro p hl hr
  exact Set.disjoint_left.mp (bb_children_disjoint N i q hf)
    (bb_feasible_subset_region d _ hl).2.2 (bb_feasible_subset_region d _ hr).2.2

theorem bb_affine_subset_of_refines {n m l r : ℕ} (d : ModelData n m l r)
    {A B : BBNode m} (h : A.Refines B) :
    bbAffineRelaxation d A.lower A.upper ⊆ bbAffineRelaxation d B.lower B.upper := by
  intro p hp
  exact ⟨hp.1, hp.2.1, bb_box_subset_of_refines h hp.2.2⟩

theorem bb_descendant_base_compact {n m l r : ℕ} (d : ModelData n m l r)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) {N : BBNode m}
    (href : N.Refines (bbRootNode d)) : IsCompact (bbMixedBase d N.lower N.upper) :=
  bb_mixed_base_compact_of_refines d N.lower N.upper hbase
    (fun i => (href i).1) (fun i => (href i).2)

theorem bb_bad_no_minimum_empty {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi))
    {N : BBNode m} (href : N.Refines (bbRootNode d))
    (hne : (N.region d).Nonempty) (hbad : ¬ ∃ p, IsMinimizer (N.region d) f p) :
    N.feasible d = ∅ := by
  apply bb_mixed_feasible_empty_of_base_empty
  exact bb_node_no_minimum_implies_mixed_base_empty d N.lower N.upper f
    (bb_descendant_base_compact d hbase href) hg
    (hf.mono (bb_affine_subset_of_refines d href)) hne hbad

theorem bb_bad_unbounded_empty {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi))
    {N : BBNode m} (href : N.Refines (bbRootNode d))
    (hbad : ∀ B : ℝ, ∃ p ∈ N.region d, f p < B) : N.feasible d = ∅ := by
  obtain ⟨q, hq, _⟩ := hbad 0
  apply bb_bad_no_minimum_empty d f hbase hg hf href ⟨q, hq⟩
  rintro ⟨p, hp, hmin⟩
  obtain ⟨q, hq, hlt⟩ := hbad (f p)
  exact (not_lt_of_ge (hmin q hq)) hlt

theorem bb_bad_unattained_empty {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j))
    (hf : ContinuousOn f (bbAffineRelaxation d d.lo d.hi))
    {N : BBNode m} (href : N.Refines (bbRootNode d))
    (hne : (N.region d).Nonempty) (_hbelow : BddBelow (f '' N.region d))
    (hbad : ¬ ∃ p, IsMinimizer (N.region d) f p) : N.feasible d = ∅ :=
  bb_bad_no_minimum_empty d f hbase hg hf href hne hbad

/-- An exact status at one node; no existence oracle or mixed-emptiness field. -/
inductive BBReply {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (N : BBNode m) : Type
  | empty (h : N.region d = ∅)
  | minimum (q : Point n m) (h : IsMinimizer (N.region d) f q)
  | unbounded (h : ∀ B : ℝ, ∃ q ∈ N.region d, f q < B)
  | unattained (hne : (N.region d).Nonempty) (hbelow : BddBelow (f '' N.region d))
      (hbad : ¬ ∃ q, IsMinimizer (N.region d) f q)

/-- Classical classification does not use compactness or promise numerical runtime. -/
theorem bb_reply_exists {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (N : BBNode m) : Nonempty (BBReply d f N) := by
  classical
  by_cases he : N.region d = ∅
  · exact ⟨.empty he⟩
  by_cases hm : ∃ q, IsMinimizer (N.region d) f q
  · obtain ⟨q, hq⟩ := hm
    exact ⟨.minimum q hq⟩
  by_cases hb : BddBelow (f '' N.region d)
  · exact ⟨.unattained (Set.nonempty_iff_ne_empty.mpr he) hb hm⟩
  · refine ⟨.unbounded ?_⟩
    intro B
    by_contra hn
    apply hb
    refine ⟨B, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact le_of_not_gt (fun hlt => hn ⟨q, hq, hlt⟩)

theorem bb_root_integral_optimal {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) {q : Point n m}
    (hq : IsMinimizer ((bbRootNode d).region d) f q) (hi : BBIntegerPoint q) :
    IsMinimizer (d.feasibleOn Set.univ) f q := by
  rw [← bb_root_feasible]
  exact minimizer_of_relaxation_feasible (bb_feasible_subset_region d _) hq
    ((bb_feasible_mem_iff d _ q).mpr ⟨hq.1, hi⟩)

theorem bb_integral_node_upper_bound {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) {N : BBNode m} (href : N.Refines (bbRootNode d))
    {q : Point n m} (hq : q ∈ N.region d) (hi : BBIntegerPoint q) :
    HasUpperBoundWitness (d.feasibleOn Set.univ) f (f q) :=
  ⟨q, bb_feasible_subset_root d href ((bb_feasible_mem_iff d N q).mpr ⟨hq, hi⟩), le_rfl⟩

theorem bb_node_minimum_lower_bound {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) {N : BBNode m} {q : Point n m}
    (hq : IsMinimizer (N.region d) f q) : IsLowerBound (N.feasible d) f (f q) :=
  lowerBound_of_relaxation (bb_feasible_subset_region d N) hq.2

theorem bb_empty_node_feasible {n m l r : ℕ} (d : ModelData n m l r)
    {N : BBNode m} (h : N.region d = ∅) : N.feasible d = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hh := bb_feasible_subset_region d N hp
  simp only [h, Set.mem_empty_iff_false] at hh

theorem bb_strict_prune_excludes_optimum {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) {N : BBNode m} {q inc p : Point n m}
    (hq : IsMinimizer (N.region d) f q) (hi : inc ∈ d.feasibleOn Set.univ)
    (hp : IsMinimizer (d.feasibleOn Set.univ) f p) (hstrict : f inc < f q) :
    p ∉ N.feasible d := by
  intro hnode
  have hlow := bb_node_minimum_lower_bound d f hq p hnode
  have hu := hp.2 inc hi
  exact (not_lt_of_ge (hlow.trans hu)) hstrict

/-- Any valid bound supports the comparison. Using a stored bound before a
solve is a separate algorithm variant, not silently an Algorithm 1 step. -/
theorem bb_valid_bound_strict_prune {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) {N : BBNode m} {v : ℝ} {inc p : Point n m}
    (hv : IsLowerBound (N.feasible d) f v) (hi : inc ∈ d.feasibleOn Set.univ)
    (hp : IsMinimizer (d.feasibleOn Set.univ) f p) (hstrict : f inc < v) :
    p ∉ N.feasible d := by
  intro hnode
  exact (not_lt_of_ge ((hv p hnode).trans (hp.2 inc hi))) hstrict

/-- Weak pruning preserves a point at least as good as every discarded point;
it may discard a tied optimizer. -/
theorem bb_valid_bound_weak_prune {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) {N : BBNode m} {v : ℝ} {inc : Point n m}
    (hv : IsLowerBound (N.feasible d) f v) (hweak : f inc ≤ v) :
    ∀ p ∈ N.feasible d, f inc ≤ f p :=
  fun p hp => hweak.trans (hv p hp)

theorem bb_node_convex {n m l r : ℕ} (d : ModelData n m l r) (N : BBNode m)
    (hg : ∀ j, ConvexOn ℝ Set.univ (d.g j)) : Convex ℝ (N.region d) := by
  apply continuousRelaxation_convex N.lower N.upper
  · simpa using source_nonlinearRegion_convex_on d Set.univ convex_univ hg
  · exact source_linearRegion_convex d

/-- An exact constrained local minimum, not a KKT point or a solver exit flag. -/
theorem bb_exact_local_minimum_global {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (N : BBNode m) (hg : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hf : ConvexOn ℝ Set.univ f) {q : Point n m} (hq : q ∈ N.region d)
    (hlocal : IsLocalMinOn f (N.region d) q) : IsMinimizer (N.region d) f q := by
  exact ⟨hq, fun _ hp => IsMinOn.of_isLocalMinOn_of_convexOn hq hlocal
    (hf.subset (Set.subset_univ _) (bb_node_convex d N hg)) hp⟩

end Chapter02

#print axioms Chapter02.bb_root_region
#print axioms Chapter02.bb_root_feasible
#print axioms Chapter02.bb_region_mem_iff
#print axioms Chapter02.bb_feasible_mem_iff
#print axioms Chapter02.bb_feasible_subset_region
#print axioms Chapter02.bb_region_subset_of_refines
#print axioms Chapter02.bb_feasible_subset_of_refines
#print axioms Chapter02.bb_feasible_subset_root
#print axioms Chapter02.bb_integer_coordinate
#print axioms Chapter02.bb_fractional_coordinate
#print axioms Chapter02.bb_child_feasible_cover
#print axioms Chapter02.bb_child_feasible_disjoint
#print axioms Chapter02.bb_affine_subset_of_refines
#print axioms Chapter02.bb_descendant_base_compact
#print axioms Chapter02.bb_bad_no_minimum_empty
#print axioms Chapter02.bb_bad_unbounded_empty
#print axioms Chapter02.bb_bad_unattained_empty
#print axioms Chapter02.bb_reply_exists
#print axioms Chapter02.bb_root_integral_optimal
#print axioms Chapter02.bb_integral_node_upper_bound
#print axioms Chapter02.bb_node_minimum_lower_bound
#print axioms Chapter02.bb_empty_node_feasible
#print axioms Chapter02.bb_strict_prune_excludes_optimum
#print axioms Chapter02.bb_valid_bound_strict_prune
#print axioms Chapter02.bb_valid_bound_weak_prune
#print axioms Chapter02.bb_node_convex
#print axioms Chapter02.bb_exact_local_minimum_global
