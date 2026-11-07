module

public import Chapter03OAExistenceMaster

@[expose] public section

/-! Boundary controls for the structural LP bridge. These are not claims that
the artificial data below satisfy the article's analytic or LICQ package. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT Chapter03.OAExec
namespace Chapter03.OAExistence.LPControls

/-- This feasible polyhedron is unbounded, while its identity objective attains. -/
theorem halfline_unbounded : ¬ BddAbove {x : ℝ | 0 ≤ x} := by
  rintro ⟨b, hb⟩
  have hh : max (0 : ℝ) (b + 1) ≤ b := hb (by
    change (0 : ℝ) ≤ max 0 (b + 1)
    exact le_max_left _ _)
  have := le_max_right (0 : ℝ) (b + 1)
  linarith

theorem halfline_attained : ∃ x : ℝ, IsMinimizer {x : ℝ | 0 ≤ x} id x := by
  have hh := finite_polyhedron_linear_attained
    (fun _ : Fin 1 => -(ContinuousLinearMap.id ℝ ℝ)) (fun _ => (0 : ℝ))
    (ContinuousLinearMap.id ℝ ℝ)
    (show ({x : ℝ | ∀ _ : Fin 1, -(ContinuousLinearMap.id ℝ ℝ) x ≤ 0}).Nonempty
      from ⟨0, by simp⟩)
    (show BddBelow ((ContinuousLinearMap.id ℝ ℝ) ''
      {x : ℝ | ∀ _ : Fin 1, -(ContinuousLinearMap.id ℝ ℝ) x ≤ 0}) from by
      refine ⟨0, ?_⟩
      rintro t ⟨x, hx, rfl⟩
      simpa using hx 0)
  simpa using hh

theorem no_rows_zero_attained :
    ∃ x : ℝ, IsMinimizer Set.univ (fun _ : ℝ => (0 : ℝ)) x := by
  have hh := finite_polyhedron_linear_attained
    (fun _ : Fin 0 => (0 : ℝ →L[ℝ] ℝ)) (fun _ => (0 : ℝ)) (0 : ℝ →L[ℝ] ℝ)
    (show ({x : ℝ | ∀ i : Fin 0, (0 : ℝ →L[ℝ] ℝ) x ≤ 0}).Nonempty
      from ⟨0, by simp⟩)
    (show BddBelow ((0 : ℝ →L[ℝ] ℝ) ''
      {x : ℝ | ∀ i : Fin 0, (0 : ℝ →L[ℝ] ℝ) x ≤ 0}) from by
      refine ⟨0, ?_⟩
      rintro t ⟨x, _, rfl⟩
      simp)
  rcases hh with ⟨x,hx⟩
  refine ⟨x,?_⟩
  simpa [IsMinimizer] using hx

/-- Empty row sets do not force a lower bound for a nonzero linear objective. -/
theorem no_rows_nonzero_unbounded :
    ¬ BddBelow ((ContinuousLinearMap.id ℝ ℝ) ''
      {x : ℝ | ∀ _ : Fin 0, (0 : ℝ →L[ℝ] ℝ) x ≤ 0}) := by
  simp

/-- Zero continuous dimension is allowed even with a nonempty zero-row family. -/
theorem zero_dimension_attained : ∃ x : RealVector 0,
    IsMinimizer {x : RealVector 0 | ∀ _ : Fin 1, (0 : RealVector 0 →L[ℝ] ℝ) x ≤ 0}
      (0 : RealVector 0 →L[ℝ] ℝ) x := by
  apply finite_polyhedron_linear_attained
  · exact ⟨0, by simp⟩
  · refine ⟨0, ?_⟩
    rintro t ⟨x, _, rfl⟩
    simp

/-- An inconsistent zero row gives the empty image, not a default-infimum answer. -/
theorem inconsistent_values_empty_closed :
    (ContinuousLinearMap.id ℝ ℝ) ''
      {x : ℝ | ∀ _ : Fin 1, (0 : ℝ →L[ℝ] ℝ) x ≤ -1} = ∅ ∧
    IsClosed ((ContinuousLinearMap.id ℝ ℝ) ''
      {x : ℝ | ∀ _ : Fin 1, (0 : ℝ →L[ℝ] ℝ) x ≤ -1}) := by
  refine ⟨by norm_num, ?_⟩
  exact finite_polyhedron_value_closed (fun _ : Fin 1 => (0 : ℝ →L[ℝ] ℝ))
    (fun _ => -1) (ContinuousLinearMap.id ℝ ℝ)

def dependentRows : Fin 3 → ℝ →L[ℝ] ℝ :=
  ![ContinuousLinearMap.id ℝ ℝ, -(ContinuousLinearMap.id ℝ ℝ), 0]

theorem dependent_opposing_zero_attained : ∃ x : ℝ,
    IsMinimizer {x : ℝ | ∀ i, dependentRows i x ≤ 0}
      (ContinuousLinearMap.id ℝ ℝ) x := by
  apply finite_polyhedron_linear_attained dependentRows (fun _ => 0)
  · exact ⟨0, by simp⟩
  · refine ⟨0, ?_⟩
    rintro t ⟨x, hx, rfl⟩
    simpa [dependentRows] using hx 1

/-- Deliberately empty support domain: the master is still its exact domain-free set. -/
def zeroData : Data 0 0 0 0 where
  model := {
    g := fun _ _ => 0
    A := fun _ _ => 0
    B := fun _ _ => 0
    rhs := fun _ => 0
    c1 := 0
    c2 := 0
    lo := 0
    hi := 0 }
  f := fun _ => 0
  Df := fun _ => 0
  Dg := fun _ _ => 0
  domain := ∅

def invalidDeletion : Event zeroData where
  target := 0
  target_mem := by intro i; exact Fin.elim0 i
  x := 0
  restoration := some 0

theorem zero_master_mem (z : Point 0 0 × ℝ) :
    z ∈ master zeroData (0,0) [] ↔ 0 ≤ z.2 := by
  rw [master_mem_iff]
  have hy : z.1 ∈ IntegerCylinder (n := 0) zeroData.model.lo zeroData.model.hi :=
    ⟨0, by intro i; exact Fin.elim0 i, Subsingleton.elim _ _⟩
  simp only [hy, true_and]
  simp [zeroData, ModelData.linearRegion, noGoods]
  intro _
  constructor <;> intro e he <;> cases he

theorem zero_master_height_values :
    Prod.snd '' master zeroData (0,0) [] = Set.Ici (0 : ℝ) := by
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (zero_master_mem z).mp hz
  · intro ht
    exact ⟨((0,0),t), (zero_master_mem _).mpr ht, rfl⟩

/-- No continuous or integer coordinates, no soft/hard rows, empty history:
the seed objective still supplies the lower height bound and attainment. -/
theorem zero_master_attained_with_empty_domain : zeroData.domain = ∅ ∧
    ∃ z, IsMinimizer (master zeroData (0,0) []) Prod.snd z := by
  refine ⟨rfl, master_attained_of_bddBelow zeroData (0,0) [] ?_ ?_⟩
  · exact ⟨((0,0),0), (zero_master_mem _).mpr le_rfl⟩
  · rw [zero_master_height_values]
    exact bddBelow_Ici

/-- Structural closure also covers an invalid repeated history whose no-good
deletes the unique zero-dimensional integer assignment. -/
theorem invalid_repeated_deletion_empty :
    ¬ EventValid zeroData invalidDeletion ∧
    master zeroData (0,0) [invalidDeletion, invalidDeletion] = ∅ ∧
    IsClosed (Prod.snd '' master zeroData (0,0) [invalidDeletion, invalidDeletion]) := by
  refine ⟨fun h => h.1, ?_, master_height_values_closed _ _ _⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact hz.2 invalidDeletion (by simp) (by simp [invalidDeletion]) (Subsingleton.elim _ _)

end Chapter03.OAExistence.LPControls

#print axioms Chapter03.OAExistence.LPControls.halfline_attained
#print axioms Chapter03.OAExistence.LPControls.zero_dimension_attained
#print axioms Chapter03.OAExistence.LPControls.no_rows_nonzero_unbounded
#print axioms Chapter03.OAExistence.LPControls.zero_master_attained_with_empty_domain
#print axioms Chapter03.OAExistence.LPControls.invalid_repeated_deletion_empty
