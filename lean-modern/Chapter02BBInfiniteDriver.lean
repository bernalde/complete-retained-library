module

public import Chapter02BBExternal
public import Chapter02BBInfinite

@[expose] public section

/-! Literal Algorithm 1 on the unbounded half-integer line. The mixed feasible
set is empty (hence compact), yet every finite execution has a successor and
no reachable state is terminal. This uses the same external process as the
bounded-polyhedron adapter and has no assumed progress/nonblocking field. -/
noncomputable section
namespace Chapter02

def bbHalfData : BBPolyData 2 0 2 where
  coefficient := ![![1, -1], ![-1, 1]]
  rhs := ![1 / 2, -(1 / 2)]
  c := fun _ _ => 0
  f := fun _ => 0

abbrev BBHalfIndex := {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))}
abbrev BBHalfState := BBExternalState (Finset.univ : Finset (Fin 2))
abbrev BBHalfNode := BBExtendedNode BBHalfIndex

theorem bb_half_polyhedron : bbHalfData.polyhedron = bbHalfLine := by
  ext z
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    norm_num [bbHalfData, Fin.sum_univ_two] at h0 h1
    change z 0 - z 1 = 1 / 2
    linarith
  · intro h j
    change z 0 - z 1 = 1 / 2 at h
    fin_cases j <;> norm_num [bbHalfData, Fin.sum_univ_two] <;> linarith

theorem bb_half_relaxation_iff (B : BBHalfNode) (z : RealVector 2) :
    z ∈ bbHalfData.relaxation B ↔ z ∈ bbHalfLine ∧ B.Holds (fun i => z i) := by
  simp [BBPolyData.relaxation, bb_half_polyhedron]

theorem bb_half_external_integer_iff (z : RealVector 2) :
    bbExternalInteger Finset.univ z ↔ bbAllInteger z := by
  constructor
  · intro h i
    exact h ⟨i, Finset.mem_univ _⟩
  · intro h i
    exact h i

theorem bb_half_external_feasible_empty : bbHalfData.feasible Finset.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨hz, _, hi⟩
  apply bb_half_no_integer (by simpa [bb_half_polyhedron] using hz)
  exact (bb_half_external_integer_iff z).mp hi

theorem bb_half_external_mixed_base_compact :
    IsCompact (bbHalfData.polyhedron ∩ {z | bbExternalInteger Finset.univ z}) := by
  have he : bbHalfData.polyhedron ∩ {z | bbExternalInteger Finset.univ z} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hi⟩
    exact bb_half_no_integer (by simpa [bb_half_polyhedron] using hz)
      ((bb_half_external_integer_iff z).mp hi)
  rw [he]
  exact isCompact_empty

def BBHalfTail (B : BBHalfNode) : Prop :=
  ∃ T : ℝ, ∀ t, T ≤ t → bbHalfPoint t ∈ bbHalfData.relaxation B

theorem bb_half_point_coordinate_ge (t : ℝ) (i : Fin 2) : t ≤ bbHalfPoint t i := by
  fin_cases i <;> dsimp [bbHalfPoint] <;> linarith

theorem bb_half_root_tail : BBHalfTail (BBExtendedNode.root : BBHalfNode) := by
  refine ⟨0, fun t _ => (bb_half_relaxation_iff _ _).mpr ?_⟩
  exact ⟨bb_half_point_mem t, BBExtendedNode.holds_root _⟩

theorem bb_half_tail_nonempty {B : BBHalfNode} (h : BBHalfTail B) :
    (bbHalfData.relaxation B).Nonempty := by
  obtain ⟨T, hT⟩ := h
  exact ⟨bbHalfPoint T, hT T le_rfl⟩

theorem bb_half_tail_right {B : BBHalfNode} (h : BBHalfTail B)
    (i : BBHalfIndex) (v : ℝ) : BBHalfTail (B.right i v) := by
  classical
  obtain ⟨T, hT⟩ := h
  refine ⟨max T (Int.ceil v : ℝ), ?_⟩
  intro t ht
  have hTt : T ≤ t := (le_max_left _ _).trans ht
  have hvt : (Int.ceil v : ℝ) ≤ t := (le_max_right _ _).trans ht
  obtain ⟨hl, hb⟩ := (bb_half_relaxation_iff B _).mp (hT t hTt)
  apply (bb_half_relaxation_iff _ _).mpr
  refine ⟨hl, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    refine ⟨?_, (hb i).2⟩
    simp only [BBExtendedNode.right, Function.update_self, WithBot.coe_le_coe]
    exact hvt.trans (bb_half_point_coordinate_ge t i)
  · simpa [BBExtendedNode.right, Function.update, hji] using hb j

def BBHalfInvariant (s : BBHalfState) : Prop :=
  s.incumbent = none ∧ ∃ B ∈ s.live, BBHalfTail B

theorem bb_half_initial_invariant : BBHalfInvariant (bbExternalInitial Finset.univ) :=
  ⟨rfl, BBExtendedNode.root, by simp [bbExternalInitial], bb_half_root_tail⟩

theorem bb_half_process_preserves {s t : BBHalfState}
    (hstep : BBExternalProcess bbHalfData Finset.univ s t)
    (hinv : BBHalfInvariant s) : BBHalfInvariant t := by
  rcases hinv with ⟨hinc, B, hmem, htail⟩
  cases hstep with
  | @empty pre post C inc he =>
    refine ⟨hinc, B, ?_, htail⟩
    simp only [List.mem_append, List.mem_cons] at hmem ⊢
    rcases hmem with hp | heq | hp
    · exact Or.inl hp
    · subst B
      have hh := bb_half_tail_nonempty htail
      simp [he] at hh
    · exact Or.inr hp
  | @prune pre post C inc z hz hp =>
    change inc = none at hinc
    subst inc
    simp [bbExternalUpper] at hp
  | @integral pre post C inc z hz hk hi =>
    exact (bb_half_no_integer ((bb_half_relaxation_iff C z).mp hz.1).1
      ((bb_half_external_integer_iff z).mp hi)).elim
  | @branch pre post C inc z i hz hk hi =>
    refine ⟨hinc, ?_⟩
    simp only [List.mem_append, List.mem_cons] at hmem
    rcases hmem with hp | heq | hp
    · exact ⟨B, by simp only [List.mem_append]; exact Or.inl (Or.inl hp), htail⟩
    · subst B
      exact ⟨C.right i (z i), by simp, bb_half_tail_right htail i (z i)⟩
    · exact ⟨B, by simp only [List.mem_append]; exact Or.inr hp, htail⟩

theorem bb_half_trace_invariant {s : BBHalfState} {k : ℕ}
    (h : BBExternalTrace bbHalfData Finset.univ (bbExternalInitial Finset.univ) k s) :
    BBHalfInvariant s := by
  induction h with
  | refl => exact bb_half_initial_invariant
  | step h hs ih => exact bb_half_process_preserves hs ih

theorem bb_half_reachable_invariant {s : BBHalfState}
    (h : BBExternalReachable bbHalfData Finset.univ s) : BBHalfInvariant s := by
  obtain ⟨k, hk⟩ := h
  exact bb_half_trace_invariant hk

theorem bb_half_nonblocking_at (pre post : List BBHalfNode) (B : BBHalfNode)
    (inc : Option (RealVector 2)) :
    ∃ t, BBExternalProcess bbHalfData Finset.univ ⟨pre ++ B :: post, inc⟩ t := by
  classical
  rcases (bbHalfData.relaxation B).eq_empty_or_nonempty with he | ⟨z, hz⟩
  · exact ⟨_, .empty he⟩
  · have hm : IsMinimizer (bbHalfData.relaxation B) bbHalfData.f z :=
      ⟨hz, fun _ _ => le_rfl⟩
    have hk : ¬ bbExternalUpper bbHalfData.f inc < (bbHalfData.f z : WithTop ℝ) := by
      cases inc <;> simp [bbExternalUpper, bbHalfData]
    obtain ⟨i, hi⟩ := bb_half_fractional ((bb_half_relaxation_iff B z).mp hz).1
    exact ⟨_, .branch ⟨i, Finset.mem_univ _⟩ hm hk hi⟩

theorem bb_half_invariant_has_step {s : BBHalfState} (h : BBHalfInvariant s) :
    ∃ t, BBExternalProcess bbHalfData Finset.univ s t := by
  rcases s with ⟨live, inc⟩
  cases live with
  | nil =>
    obtain ⟨_, B, hb, _⟩ := h
    exact (List.not_mem_nil hb).elim
  | cons B bs => exact bb_half_nonblocking_at [] bs B inc

/-- Every finite execution, for all node, minimizer and fractional-coordinate
choices, can be extended. Thus no finite maximal execution or returned answer
exists on this instance. -/
theorem bb_half_every_finite_trace_extends {s : BBHalfState} {k : ℕ}
    (h : BBExternalTrace bbHalfData Finset.univ (bbExternalInitial Finset.univ) k s) :
    ∃ t, BBExternalProcess bbHalfData Finset.univ s t ∧
      BBExternalTrace bbHalfData Finset.univ (bbExternalInitial Finset.univ) (k + 1) t := by
  obtain ⟨t, ht⟩ := bb_half_invariant_has_step (bb_half_trace_invariant h)
  exact ⟨t, ht, .step h ht⟩

theorem bb_half_no_reachable_terminal {s : BBHalfState}
    (h : BBExternalReachable bbHalfData Finset.univ s) : s.live ≠ [] := by
  obtain ⟨_, B, hb, _⟩ := bb_half_reachable_invariant h
  intro he
  simp [he] at hb

def bbHalfChooseNext (s : BBHalfState) : BBHalfState := by
  classical
  exact if h : ∃ t, BBExternalProcess bbHalfData Finset.univ s t then h.choose else s

theorem bb_half_choose_next_step {s : BBHalfState} (h : BBHalfInvariant s) :
    BBExternalProcess bbHalfData Finset.univ s (bbHalfChooseNext s) := by
  have he := bb_half_invariant_has_step h
  simpa only [bbHalfChooseNext, dif_pos he] using he.choose_spec

def bbHalfExecution : ℕ → BBHalfState
  | 0 => bbExternalInitial Finset.univ
  | k + 1 => bbHalfChooseNext (bbHalfExecution k)

theorem bb_half_execution_invariant (k : ℕ) : BBHalfInvariant (bbHalfExecution k) := by
  induction k with
  | zero => exact bb_half_initial_invariant
  | succ k ih => exact bb_half_process_preserves (bb_half_choose_next_step ih) ih

theorem bb_half_infinite_execution_exists :
    ∃ run : ℕ → BBHalfState, run 0 = bbExternalInitial Finset.univ ∧
      ∀ k, BBExternalProcess bbHalfData Finset.univ (run k) (run (k + 1)) :=
  ⟨bbHalfExecution, rfl, fun k => bb_half_choose_next_step (bb_half_execution_invariant k)⟩

theorem bb_half_source_smooth : ContDiff ℝ 2 bbHalfData.f ∧ ContDiff ℝ 2 bbHalfData.c :=
  ⟨contDiff_const, contDiff_const⟩

theorem bb_half_source_convex : ConvexOn ℝ Set.univ bbHalfData.f ∧
    ∀ j, ConvexOn ℝ Set.univ (fun z => bbHalfData.c z j) :=
  ⟨convexOn_const 0 convex_univ, fun _ => convexOn_const 0 convex_univ⟩

def bbIrrationalData : BBPolyData 2 0 2 where
  coefficient := ![![1, -Real.sqrt 2], ![-1, Real.sqrt 2]]
  rhs := ![0, 0]
  c := fun _ _ => 0
  f := fun z => -z 1

theorem bb_irrational_polyhedron : bbIrrationalData.polyhedron = bbIrrationalLine := by
  ext z
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    norm_num [bbIrrationalData, Fin.sum_univ_two] at h0 h1
    change z 0 = Real.sqrt 2 * z 1
    nlinarith
  · intro h j
    change z 0 = Real.sqrt 2 * z 1 at h
    fin_cases j <;> norm_num [bbIrrationalData, Fin.sum_univ_two] <;> nlinarith

theorem bb_irrational_external_root :
    bbIrrationalData.relaxation (BBExtendedNode.root : BBHalfNode) = bbIrrationalLine := by
  ext z
  simp [BBPolyData.relaxation, bb_irrational_polyhedron, BBExtendedNode.Holds,
    BBExtendedNode.root]

theorem bb_irrational_external_feasible :
    bbIrrationalData.feasible Finset.univ = {0} := by
  have he : bbIrrationalData.feasible Finset.univ =
      bbIrrationalLine ∩ {z | bbAllInteger z} := by
    ext z
    simp [BBPolyData.feasible, bb_irrational_polyhedron,
      ← bb_half_external_integer_iff, bbExternalInteger, and_assoc, and_left_comm, and_comm]
  rw [he, bb_irrational_mixed_singleton]

theorem bb_irrational_external_base :
    bbIrrationalData.polyhedron ∩ {z | bbExternalInteger Finset.univ z} = {0} := by
  have he : bbIrrationalData.polyhedron ∩ {z | bbExternalInteger Finset.univ z} =
      bbIrrationalLine ∩ {z | bbAllInteger z} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, bb_irrational_polyhedron,
      bb_half_external_integer_iff]
  rw [he, bb_irrational_mixed_singleton]

theorem bb_irrational_external_bad_reply :
    ∀ B : ℝ, ∃ z ∈ bbIrrationalData.relaxation (BBExtendedNode.root : BBHalfNode),
      bbIrrationalData.f z < B := by
  rw [bb_irrational_external_root]
  simpa only [bbIrrationalData] using bb_irrational_relaxation_unbounded

theorem bb_irrational_external_no_minimum :
    ¬ ∃ z, IsMinimizer (bbIrrationalData.relaxation (BBExtendedNode.root : BBHalfNode))
      bbIrrationalData.f z := by
  rintro ⟨z, hz⟩
  obtain ⟨w, hw, hlt⟩ := bb_irrational_external_bad_reply (bbIrrationalData.f z)
  exact (not_lt_of_ge (hz.2 w hw)) hlt

theorem bb_irrational_external_bad_discharge_fails :
    IsCompact (bbIrrationalData.polyhedron ∩ {z | bbExternalInteger Finset.univ z}) ∧
      (bbIrrationalData.feasible Finset.univ).Nonempty ∧
      (∀ B : ℝ, ∃ z ∈ bbIrrationalData.relaxation (BBExtendedNode.root : BBHalfNode),
        bbIrrationalData.f z < B) := by
  refine ⟨?_, ?_, bb_irrational_external_bad_reply⟩
  · rw [bb_irrational_external_base]
    exact isCompact_singleton
  · rw [bb_irrational_external_feasible]
    exact Set.singleton_nonempty _

theorem bb_irrational_source_smooth :
    ContDiff ℝ 2 bbIrrationalData.f ∧ ContDiff ℝ 2 bbIrrationalData.c := by
  constructor
  · change ContDiff ℝ 2 (fun z : RealVector 2 => -z 1)
    exact (contDiff_apply ℝ (fun _ => ℝ) (1 : Fin 2)).neg
  · exact contDiff_const

theorem bb_irrational_source_convex : ConvexOn ℝ Set.univ bbIrrationalData.f ∧
    ∀ j, ConvexOn ℝ Set.univ (fun z => bbIrrationalData.c z j) := by
  refine ⟨⟨convex_univ, ?_⟩, fun _ => convexOn_const 0 convex_univ⟩
  intro x _ y _ a b _ _ _
  change -(a * x 1 + b * y 1) ≤ a * (-x 1) + b * (-y 1)
  linarith

end Chapter02

#print axioms Chapter02.bb_half_polyhedron
#print axioms Chapter02.bb_half_relaxation_iff
#print axioms Chapter02.bb_half_external_integer_iff
#print axioms Chapter02.bb_half_external_feasible_empty
#print axioms Chapter02.bb_half_external_mixed_base_compact
#print axioms Chapter02.bb_half_point_coordinate_ge
#print axioms Chapter02.bb_half_root_tail
#print axioms Chapter02.bb_half_tail_nonempty
#print axioms Chapter02.bb_half_tail_right
#print axioms Chapter02.bb_half_initial_invariant
#print axioms Chapter02.bb_half_process_preserves
#print axioms Chapter02.bb_half_trace_invariant
#print axioms Chapter02.bb_half_reachable_invariant
#print axioms Chapter02.bb_half_nonblocking_at
#print axioms Chapter02.bb_half_invariant_has_step
#print axioms Chapter02.bb_half_every_finite_trace_extends
#print axioms Chapter02.bb_half_no_reachable_terminal
#print axioms Chapter02.bb_half_choose_next_step
#print axioms Chapter02.bb_half_execution_invariant
#print axioms Chapter02.bb_half_infinite_execution_exists
#print axioms Chapter02.bb_half_source_smooth
#print axioms Chapter02.bb_half_source_convex
#print axioms Chapter02.bb_irrational_polyhedron
#print axioms Chapter02.bb_irrational_external_root
#print axioms Chapter02.bb_irrational_external_feasible
#print axioms Chapter02.bb_irrational_external_base
#print axioms Chapter02.bb_irrational_external_bad_reply
#print axioms Chapter02.bb_irrational_external_no_minimum
#print axioms Chapter02.bb_irrational_external_bad_discharge_fails
#print axioms Chapter02.bb_irrational_source_smooth
#print axioms Chapter02.bb_irrational_source_convex
