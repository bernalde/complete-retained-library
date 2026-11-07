module

public import Chapter02OAHistory
public import Chapter02BBNodes

@[expose] public section

/-! Changing-cut LP geometry for the separately qualified single-tree repair.
Real seed origins are distinct from solved integer-fiber batches. The LP has
only affine rows; original nonlinear feasibility is never inserted into it.
Exact status classification is not a numerical solver contract. -/
noncomputable section
open scoped BigOperators
namespace Chapter02
variable {n m l r : ℕ}

structure STSeed (n m l : ℕ) where
  origin : Point n m
  selected : Set (Fin l)

def stSeedCuts (d : ModelData n m l r) (a : STSeed n m l) (q : Point n m) : Prop :=
  ∀ j ∈ a.selected, d.g j a.origin + (fderiv ℝ (d.g j) a.origin) (q-a.origin) ≤ 0

def stSeedRegion (d : ModelData n m l r) (seeds : List (STSeed n m l)) :
    Set (Point n m) := {q | ∀ a ∈ seeds, stSeedCuts d a q}

def stSeedFamily (d : ModelData n m l r) (seeds : List (STSeed n m l)) :
    TangentFamily n m l seeds.length where
  origin i := (seeds.get i).origin
  selected i := (seeds.get i).selected
  derivative i j := fderiv ℝ (d.g j) (seeds.get i).origin

theorem st_seed_region_eq (d : ModelData n m l r) (seeds : List (STSeed n m l)) :
    stSeedRegion d seeds = (stSeedFamily d seeds).cutRegion d := by
  ext q
  constructor
  · intro h i j hj
    exact h (seeds.get i) (List.get_mem seeds i) j hj
  · intro h a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact h i

theorem st_seed_region_closed (d : ModelData n m l r) (seeds : List (STSeed n m l)) :
    IsClosed (stSeedRegion d seeds) := by
  rw [st_seed_region_eq]
  exact selected_cutRegion_closed d _

theorem st_seed_region_convex (d : ModelData n m l r) (seeds : List (STSeed n m l)) :
    Convex ℝ (stSeedRegion d seeds) := by
  rw [st_seed_region_eq]
  exact selected_cutRegion_convex d _

theorem st_seed_cuts_valid (d : ModelData n m l r) (a : STSeed n m l)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {q : Point n m}
    (hq : q ∈ d.nonlinearRegion) : stSeedCuts d a q := by
  intro j _
  exact tangent_cut_valid (hconv j) (hdiff j a.origin).hasFDerivAt (hq j)

theorem st_seed_region_valid (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    d.nonlinearRegion ⊆ stSeedRegion d seeds :=
  fun _ hq a _ => st_seed_cuts_valid d a hconv hdiff hq

def stLP (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) : Set (Point n m) :=
  {q | q ∈ d.linearRegion ∧ q ∈ N.box ∧ q ∈ stSeedRegion d seeds ∧
    ∀ b ∈ H, oaBatchCuts d b q}

theorem st_lp_mem_iff (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) (q : Point n m) :
    q ∈ stLP d seeds H N ↔ q ∈ d.linearRegion ∧ q ∈ N.box ∧
      q ∈ stSeedRegion d seeds ∧ ∀ b ∈ H, oaBatchCuts d b q := Iff.rfl

theorem st_lp_intersection (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) :
    stLP d seeds H N = bbAffineRelaxation d N.lower N.upper ∩
      (stSeedRegion d seeds ∩ (oaHistoryFamily d H).cutRegion d) := by
  ext q
  simp only [st_lp_mem_iff, Set.mem_inter_iff, oa_history_cutRegion_iff,
    bbAffineRelaxation, ContinuousRelaxation, Set.mem_univ, true_and,
    BBNode.box, Set.mem_setOf_eq]
  tauto

theorem st_lp_closed (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) : IsClosed (stLP d seeds H N) := by
  rw [st_lp_intersection]
  exact (bb_affine_relaxation_closed d N.lower N.upper).inter
    ((st_seed_region_closed d seeds).inter (selected_cutRegion_closed d _))

theorem st_lp_convex (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) : Convex ℝ (stLP d seeds H N) := by
  rw [st_lp_intersection]
  exact (continuousRelaxation_convex N.lower N.upper convex_univ
    (source_linearRegion_convex d)).inter
      ((st_seed_region_convex d seeds).inter (selected_cutRegion_convex d _))

theorem st_lp_subset_affine (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) :
    stLP d seeds H N ⊆ bbAffineRelaxation d N.lower N.upper :=
  fun _ hq => ⟨Set.mem_univ _, hq.1, hq.2.1⟩

theorem st_lp_subset_of_refines (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m))
    {A B : BBNode m} (h : A.Refines B) : stLP d seeds H A ⊆ stLP d seeds H B :=
  fun _ hp => ⟨hp.1, bb_box_subset_of_refines h hp.2.1, hp.2.2⟩

theorem st_lp_append_batch (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (b : OABatch n m) (N : BBNode m) :
    stLP d seeds (H ++ [b]) N = stLP d seeds H N ∩ {q | oaBatchCuts d b q} := by
  ext q
  simp [st_lp_mem_iff, and_assoc, or_imp, forall_and]

theorem st_lp_append_seed (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (a : STSeed n m l) (N : BBNode m) :
    stLP d (seeds ++ [a]) H N = stLP d seeds H N ∩ {q | stSeedCuts d a q} := by
  ext q
  simp [st_lp_mem_iff, stSeedRegion, and_assoc, and_comm, and_left_comm,
    or_imp, forall_and]

theorem st_feasible_subset_lp (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) : N.feasible d ⊆ stLP d seeds H N := by
  intro q hq
  have hr := bb_feasible_subset_region d N hq
  refine ⟨hr.2.1, hr.2.2, st_seed_region_valid d seeds hconv hdiff hr.1, ?_⟩
  intro b _ j hj
  exact tangent_cut_valid (hconv j) (hdiff j b.anchor).hasFDerivAt (hr.1 j)

theorem st_lp_minimum_lower_bound (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {q : Point n m}
    (hq : IsMinimizer (stLP d seeds H N) d.objective q) :
    IsLowerBound (N.feasible d) d.objective (d.objective q) :=
  lowerBound_of_relaxation (st_feasible_subset_lp d seeds H N hconv hdiff) hq.2

theorem st_lp_empty_feasible (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (he : stLP d seeds H N = ∅) : N.feasible d = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := st_feasible_subset_lp d seeds H N hconv hdiff hq
  rw [he] at h
  exact h

theorem st_lp_compact_of_mixed_base_nonempty (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (hM : IsCompact (bbMixedBase d N.lower N.upper))
    (hne : (bbMixedBase d N.lower N.upper).Nonempty) :
    IsCompact (stLP d seeds H N) :=
  (bb_affine_relaxation_compact d N.lower N.upper hM hne).of_isClosed_subset
    (st_lp_closed d seeds H N) (st_lp_subset_affine d seeds H N)

/-- Exact bad-status deletion is a derived repair, silent in the source prose. -/
theorem st_lp_bad_no_minimum_empty (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (href : N.Refines (bbRootNode d))
    (hne : (stLP d seeds H N).Nonempty)
    (hbad : ¬ ∃ q, IsMinimizer (stLP d seeds H N) d.objective q) : N.feasible d = ∅ := by
  apply bb_mixed_feasible_empty_of_base_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hc := st_lp_compact_of_mixed_base_nonempty d seeds H N
    (bb_descendant_base_compact d hbase href) ⟨p,hp⟩
  exact hbad (compact_feasible_attainment hc hne
    (linearForm_continuous d.c1 d.c2).continuousOn)

theorem st_lp_bad_unbounded_empty (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (href : N.Refines (bbRootNode d))
    (hbad : ∀ B : ℝ, ∃ q ∈ stLP d seeds H N, d.objective q < B) : N.feasible d = ∅ := by
  obtain ⟨q,hq,_⟩ := hbad 0
  apply st_lp_bad_no_minimum_empty d seeds H N hbase href ⟨q,hq⟩
  rintro ⟨p,hp,hmin⟩
  obtain ⟨q,hq,hlt⟩ := hbad (d.objective p)
  exact (not_lt_of_ge (hmin q hq)) hlt

theorem st_lp_bad_unattained_empty (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi)) (href : N.Refines (bbRootNode d))
    (hne : (stLP d seeds H N).Nonempty)
    (_hbelow : BddBelow (d.objective '' stLP d seeds H N))
    (hbad : ¬ ∃ q, IsMinimizer (stLP d seeds H N) d.objective q) : N.feasible d = ∅ :=
  st_lp_bad_no_minimum_empty d seeds H N hbase href hne hbad

theorem st_lp_integer_master (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (href : N.Refines (bbRootNode d)) {q : Point n m}
    (hq : q ∈ stLP d seeds H N) (hi : BBIntegerPoint q) : q ∈ oaMaster d H := by
  obtain ⟨y,hy⟩ := hi
  apply (oa_master_mem_iff d H q).mpr
  refine ⟨hq.1, ⟨y, ?_, hy⟩, hq.2.2.2⟩
  have hb := bb_box_subset_of_refines href hq.2.1
  intro i
  simpa only [hy, bbRootNode] using hb i

theorem st_lp_fiber_reply (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (hbase : IsCompact (bbMixedBase d d.lo d.hi))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (href : N.Refines (bbRootNode d))
    {q : Point n m} (hq : q ∈ stLP d seeds H N) (hi : BBIntegerPoint q) :
    ∃ b : OABatch n m, oaBatchValid d b ∧ q.2 = oaIntCast b.integer := by
  have hm := st_lp_integer_master d seeds H N href hq hi
  obtain ⟨y,hy,hqy,_⟩ := oa_master_integer_witness d H q hm
  obtain ⟨b,hb,hby⟩ := oa_fiber_reply_exists d y hy hbase ⟨q,hq.1,hqy⟩ hdiff
  exact ⟨b,hb,by simpa only [hby] using hqy⟩

theorem st_callback_anchor_node (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    {q : Point n m} (hq : q ∈ stLP d seeds H N) {b : OABatch n m}
    (hb : oaBatchValid d b) (hy : q.2 = oaIntCast b.integer)
    (hn : b.restoration = none) : b.anchor ∈ N.feasible d := by
  have ha := oaBatch_feasible_original d b hb hn
  have hr := bb_feasible_subset_region d (bbRootNode d) (by simpa [bb_root_feasible] using ha)
  apply (bb_feasible_mem_iff d N b.anchor).mpr
  refine ⟨⟨hr.1,hr.2.1,?_⟩, b.integer,hb.2.1⟩
  intro i
  have heq : b.anchor.2 = q.2 := hb.2.1.trans hy.symm
  simpa only [heq] using hq.2.1 i

inductive STLPReply (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) : Type
  | empty (h : stLP d seeds H N = ∅)
  | minimum (q : Point n m) (h : IsMinimizer (stLP d seeds H N) d.objective q)
  | unbounded (h : ∀ B : ℝ, ∃ q ∈ stLP d seeds H N, d.objective q < B)
  | unattained (hne : (stLP d seeds H N).Nonempty)
      (hbelow : BddBelow (d.objective '' stLP d seeds H N))
      (hbad : ¬ ∃ q, IsMinimizer (stLP d seeds H N) d.objective q)

theorem st_lp_reply_exists (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) : Nonempty (STLPReply d seeds H N) := by
  classical
  by_cases he : stLP d seeds H N = ∅
  · exact ⟨.empty he⟩
  by_cases hm : ∃ q, IsMinimizer (stLP d seeds H N) d.objective q
  · obtain ⟨q,hq⟩ := hm
    exact ⟨.minimum q hq⟩
  by_cases hb : BddBelow (d.objective '' stLP d seeds H N)
  · exact ⟨.unattained (Set.nonempty_iff_ne_empty.mpr he) hb hm⟩
  · refine ⟨.unbounded ?_⟩
    intro B
    by_contra hn
    apply hb
    refine ⟨B, ?_⟩
    rintro _ ⟨q,hq,rfl⟩
    exact le_of_not_gt (fun hlt => hn ⟨q,hq,hlt⟩)

abbrev STLPRow (m l r s h : ℕ) :=
  Fin r ⊕ (Fin m ⊕ (Fin m ⊕ ((Fin s × Fin l) ⊕ (Fin h × Fin l))))

def stYProjection (n m : ℕ) (i : Fin m) : Point n m →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (RealVector n) (RealVector m))

@[simp] theorem st_y_projection_apply (i : Fin m) (q : Point n m) :
    stYProjection n m i q = q.2 i := rfl

theorem st_tangent_as_linear (f : Point n m → ℝ) (a q : Point n m) :
    f a + (fderiv ℝ f a) (q-a) ≤ 0 ↔
      (fderiv ℝ f a) q ≤ (fderiv ℝ f a) a - f a := by
  rw [map_sub]
  constructor <;> intro h <;> linarith

/-- Nonselected slots are the harmless row 0≤0. All row slots are finite. -/
def stLPRowData (d : ModelData n m l r) (seeds : List (STSeed n m l))
    (H : List (OABatch n m)) (N : BBNode m) :
    STLPRow m l r seeds.length H.length → (Point n m →L[ℝ] ℝ) × ℝ := by
  classical
  exact fun row => match row with
    | .inl i => (linearFormCLM (d.A i) (d.B i), d.rhs i)
    | .inr (.inl i) => (-stYProjection n m i, -N.lower i)
    | .inr (.inr (.inl i)) => (stYProjection n m i, N.upper i)
    | .inr (.inr (.inr (.inl (i,j)))) =>
        if j ∈ (seeds.get i).selected then
          (fderiv ℝ (d.g j) (seeds.get i).origin,
            (fderiv ℝ (d.g j) (seeds.get i).origin) (seeds.get i).origin -
              d.g j (seeds.get i).origin)
        else (0,0)
    | .inr (.inr (.inr (.inr (i,j)))) =>
        if j ∈ oaBatchRows d (H.get i) then
          (fderiv ℝ (d.g j) (H.get i).anchor,
            (fderiv ℝ (d.g j) (H.get i).anchor) (H.get i).anchor - d.g j (H.get i).anchor)
        else (0,0)

theorem st_lp_finite_affine_iff (d : ModelData n m l r)
    (seeds : List (STSeed n m l)) (H : List (OABatch n m)) (N : BBNode m)
    (q : Point n m) : q ∈ stLP d seeds H N ↔
    ∀ row, (stLPRowData d seeds H N row).1 q ≤ (stLPRowData d seeds H N row).2 := by
  classical
  constructor
  · intro hq row
    rcases row with i | (i | (i | (⟨i,j⟩ | ⟨i,j⟩)))
    · exact hq.1 i
    · simpa only [stLPRowData, ContinuousLinearMap.neg_apply, st_y_projection_apply,
        neg_le_neg_iff] using (hq.2.1 i).1
    · exact (hq.2.1 i).2
    · by_cases hj : j ∈ (seeds.get i).selected
      · simpa only [stLPRowData, if_pos hj] using
          (st_tangent_as_linear (d.g j) _ q).mp
            (hq.2.2.1 (seeds.get i) (List.get_mem seeds i) j hj)
      · simp only [stLPRowData,if_neg hj,ContinuousLinearMap.zero_apply,le_refl]
    · by_cases hj : j ∈ oaBatchRows d (H.get i)
      · simpa only [stLPRowData, if_pos hj] using
          (st_tangent_as_linear (d.g j) _ q).mp
            (hq.2.2.2 (H.get i) (List.get_mem H i) j hj)
      · simp only [stLPRowData,if_neg hj,ContinuousLinearMap.zero_apply,le_refl]
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · intro i
      exact h (.inl i)
    · intro i
      refine ⟨?_,h (.inr (.inr (.inl i)))⟩
      simpa only [stLPRowData, ContinuousLinearMap.neg_apply, st_y_projection_apply,
        neg_le_neg_iff] using h (.inr (.inl i))
    · intro a ha j hj
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
      apply (st_tangent_as_linear (d.g j) _ q).mpr
      simpa only [stLPRowData, if_pos hj] using h (.inr (.inr (.inr (.inl (i,j)))))
    · intro b hb j hj
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hb
      apply (st_tangent_as_linear (d.g j) _ q).mpr
      simpa only [stLPRowData, if_pos hj] using h (.inr (.inr (.inr (.inr (i,j)))))

end Chapter02

#print axioms Chapter02.st_seed_region_eq
#print axioms Chapter02.st_seed_region_closed
#print axioms Chapter02.st_seed_region_convex
#print axioms Chapter02.st_seed_cuts_valid
#print axioms Chapter02.st_seed_region_valid
#print axioms Chapter02.st_lp_mem_iff
#print axioms Chapter02.st_lp_intersection
#print axioms Chapter02.st_lp_closed
#print axioms Chapter02.st_lp_convex
#print axioms Chapter02.st_lp_subset_affine
#print axioms Chapter02.st_lp_subset_of_refines
#print axioms Chapter02.st_lp_append_batch
#print axioms Chapter02.st_lp_append_seed
#print axioms Chapter02.st_feasible_subset_lp
#print axioms Chapter02.st_lp_minimum_lower_bound
#print axioms Chapter02.st_lp_empty_feasible
#print axioms Chapter02.st_lp_compact_of_mixed_base_nonempty
#print axioms Chapter02.st_lp_bad_no_minimum_empty
#print axioms Chapter02.st_lp_bad_unbounded_empty
#print axioms Chapter02.st_lp_bad_unattained_empty
#print axioms Chapter02.st_lp_integer_master
#print axioms Chapter02.st_lp_fiber_reply
#print axioms Chapter02.st_callback_anchor_node
#print axioms Chapter02.st_lp_reply_exists
#print axioms Chapter02.st_y_projection_apply
#print axioms Chapter02.st_tangent_as_linear
#print axioms Chapter02.st_lp_finite_affine_iff
