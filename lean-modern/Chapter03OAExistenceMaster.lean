module

public import Chapter03OAExistencePolyhedron
public import Chapter03OAExecHistory

@[expose] public section

/-! Exact finite polyhedral representation of the accepted domain-free master.
The statement permits arbitrary finite histories, including invalid or repeated
events. No support-domain, analytic, KKT or bounded-master premise is added. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT Chapter03.OAExistence
namespace Chapter03.OAExec
variable {n m l r : ℕ}

/-- The selected rows include the unchanged all-row seed slot. -/
abbrev MasterSelected (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :=
  {ij : Fin (H.length + 1) × Fin l // ij.2 ∈ (family d seed H).selected ij.1}

abbrev MasterRowIndex (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :=
  (Fin r ⊕ Fin (H.length + 1)) ⊕ MasterSelected d seed H

/-- Linear parts of hard, objective-height and selected nonlinear inequalities. -/
def masterRow (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :
    MasterRowIndex d seed H → (Point n m × ℝ) →L[ℝ] ℝ :=
  Sum.elim (Sum.elim
    (fun i => (linearFormCLM (d.model.A i) (d.model.B i)).comp
      (ContinuousLinearMap.fst ℝ (Point n m) ℝ))
    (fun i => (familyDf d seed H i).comp
      (ContinuousLinearMap.fst ℝ (Point n m) ℝ) -
      ContinuousLinearMap.snd ℝ (Point n m) ℝ))
    (fun ij => ((family d seed H).derivative ij.val.1 ij.val.2).comp
      (ContinuousLinearMap.fst ℝ (Point n m) ℝ))

def masterRowBound (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :
    MasterRowIndex d seed H → ℝ :=
  Sum.elim (Sum.elim d.model.rhs
    (fun i => familyDf d seed H i ((family d seed H).origin i) -
      d.f ((family d seed H).origin i)))
    (fun ij => (family d seed H).derivative ij.val.1 ij.val.2
      ((family d seed H).origin ij.val.1) -
      d.model.g ij.val.2 ((family d seed H).origin ij.val.1))

/-- Both directions refer to the original epigraph master, not a new algorithm. -/
theorem master_rows_iff (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (z : Point n m × ℝ) :
    z ∈ master d seed H ↔
      (∀ i, masterRow d seed H i z ≤ masterRowBound d seed H i) ∧
      z.1 ∈ IntegerCylinder (n := n) d.model.lo d.model.hi ∧ noGoods H z.1 := by
  constructor
  · rintro ⟨⟨⟨⟨⟨_, hg⟩, hl⟩, hy⟩, hf⟩, hn⟩
    refine ⟨?_, hy, hn⟩
    intro i
    rcases i with (i | i) | ij
    · exact hl i
    · have hh := hf i
      change familyDf d seed H i z.1 - z.2 ≤
        familyDf d seed H i ((family d seed H).origin i) -
          d.f ((family d seed H).origin i)
      rw [map_sub] at hh
      linarith
    · have hh := hg ij.val.1 ij.val.2 ij.property
      change d.model.g ij.val.2 ((family d seed H).origin ij.val.1) +
        (family d seed H).derivative ij.val.1 ij.val.2
          (z.1 - (family d seed H).origin ij.val.1) ≤ 0 at hh
      change (family d seed H).derivative ij.val.1 ij.val.2 z.1 ≤
        (family d seed H).derivative ij.val.1 ij.val.2
          ((family d seed H).origin ij.val.1) -
        d.model.g ij.val.2 ((family d seed H).origin ij.val.1)
      rw [map_sub] at hh
      linarith
  · rintro ⟨hr, hy, hn⟩
    refine ⟨⟨⟨⟨⟨Set.mem_univ _, ?_⟩, ?_⟩, hy⟩, ?_⟩, hn⟩
    · intro i j hj
      have hh := hr (Sum.inr ⟨(i,j), hj⟩)
      change (family d seed H).derivative i j z.1 ≤
        (family d seed H).derivative i j ((family d seed H).origin i) -
          d.model.g j ((family d seed H).origin i) at hh
      change d.model.g j ((family d seed H).origin i) +
        (family d seed H).derivative i j (z.1 - (family d seed H).origin i) ≤ 0
      rw [map_sub]
      linarith
    · intro i
      exact hr (Sum.inl (Sum.inl i))
    · intro i
      have hh := hr (Sum.inl (Sum.inr i))
      change familyDf d seed H i z.1 - z.2 ≤
        familyDf d seed H i ((family d seed H).origin i) -
          d.f ((family d seed H).origin i) at hh
      rw [map_sub]
      linarith

/-- Continuous coordinates and height vary; the integer coordinates are zero. -/
def masterFiberEmbedding (n m : ℕ) :
    (RealVector n × ℝ) →L[ℝ] (Point n m × ℝ) :=
  ((ContinuousLinearMap.inl ℝ (RealVector n) (RealVector m)).comp
    (ContinuousLinearMap.fst ℝ (RealVector n) ℝ)).prod
    (ContinuousLinearMap.snd ℝ (RealVector n) ℝ)

def masterFiberLift (y : IntVector m) (v : RealVector n × ℝ) : Point n m × ℝ :=
  ((v.1, intCast y), v.2)

def masterFiberPolyhedron (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (y : IntVector m) : Set (RealVector n × ℝ) :=
  {v | ∀ i, ((masterRow d seed H i).comp (masterFiberEmbedding n m)) v ≤
    masterRowBound d seed H i - masterRow d seed H i ((0, intCast y), 0)}

def masterAllowed (d : Data n m l r) (H : List (Event d)) : Finset (IntVector m) := by
  classical
  exact d.box.filter (fun y => noGoods H (0, intCast y))

theorem masterFiber_row_identity (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (y : IntVector m) (v : RealVector n × ℝ)
    (i : MasterRowIndex d seed H) :
    masterRow d seed H i (masterFiberLift y v) =
      ((masterRow d seed H i).comp (masterFiberEmbedding n m)) v +
        masterRow d seed H i ((0, intCast y), 0) := by
  rw [ContinuousLinearMap.comp_apply, ← map_add]
  congr 1
  ext <;> simp [masterFiberLift, masterFiberEmbedding]

theorem masterFiber_mem_iff (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (y : IntVector m) (hy : y ∈ masterAllowed d H)
    (v : RealVector n × ℝ) :
    masterFiberLift y v ∈ master d seed H ↔ v ∈ masterFiberPolyhedron d seed H y := by
  classical
  obtain ⟨hybox, hyng⟩ := Finset.mem_filter.mp hy
  have hc : (masterFiberLift y v).1 ∈ IntegerCylinder (n := n) d.model.lo d.model.hi :=
    ⟨y, by simpa [Data.box] using hybox, rfl⟩
  have hn : noGoods H (masterFiberLift y v).1 := hyng
  rw [master_rows_iff]
  constructor
  · intro hh i
    have hi := hh.1 i
    rw [masterFiber_row_identity] at hi
    exact le_sub_iff_add_le.mpr hi
  · intro hh
    refine ⟨?_, hc, hn⟩
    intro i
    rw [masterFiber_row_identity]
    exact le_sub_iff_add_le.mp (hh i)

/-- No-goods filter complete integer fibers; they are not strict continuous rows. -/
theorem master_finite_fiber_union (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) :
    master d seed H = ⋃ y ∈ masterAllowed d H,
      masterFiberLift y '' masterFiberPolyhedron d seed H y := by
  classical
  ext z
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · intro hz
    obtain ⟨y, hy, hey⟩ := master_integer hz
    have ha : y ∈ masterAllowed d H := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [Data.box] using hy, ?_⟩
      intro e he hn
      simpa only [← hey] using hz.2 e he hn
    have hzlift : masterFiberLift y (z.1.1,z.2) = z := by
      apply Prod.ext
      · exact Prod.ext rfl hey.symm
      · rfl
    refine ⟨y, ha, (z.1.1,z.2), ?_, hzlift⟩
    apply (masterFiber_mem_iff d seed H y ha _).mp
    rwa [hzlift]
  · rintro ⟨y, hy, v, hv, rfl⟩
    exact (masterFiber_mem_iff d seed H y hy v).mpr hv

theorem master_height_finite_union (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) :
    Prod.snd '' master d seed H = ⋃ y ∈ masterAllowed d H,
      Prod.snd '' masterFiberPolyhedron d seed H y := by
  rw [master_finite_fiber_union]
  simp only [Set.image_iUnion, Set.image_image]
  rfl

/-- The accepted master has closed height values for every finite history.
No analyticity, valid-history or support-domain condition is required. -/
theorem master_height_values_closed (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) : IsClosed (Prod.snd '' master d seed H) := by
  classical
  rw [master_height_finite_union]
  apply isClosed_biUnion_finset
  intro y _
  exact finite_polyhedron_value_closed
    (fun i => (masterRow d seed H i).comp (masterFiberEmbedding n m))
    (fun i => masterRowBound d seed H i - masterRow d seed H i ((0, intCast y), 0))
    (ContinuousLinearMap.snd ℝ (RealVector n) ℝ)

/-- Actual bounded-below master minima exist even when the continuous master
is unbounded. This directly supplies LocalAvailability.master_attainment. -/
theorem master_attained_of_bddBelow (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (hne : (master d seed H).Nonempty)
    (hbb : BddBelow (Prod.snd '' master d seed H)) :
    ∃ z, IsMinimizer (master d seed H) Prod.snd z := by
  have hleast := (master_height_values_closed d seed H).isLeast_csInf
    (hne.image Prod.snd) hbb
  obtain ⟨z, hz, he⟩ := hleast.1
  refine ⟨z, hz, ?_⟩
  intro w hw
  rw [he]
  exact hleast.2 ⟨w, hw, rfl⟩

end Chapter03.OAExec

#print axioms Chapter03.OAExec.master_rows_iff
#print axioms Chapter03.OAExec.masterFiber_mem_iff
#print axioms Chapter03.OAExec.master_finite_fiber_union
#print axioms Chapter03.OAExec.master_height_finite_union
#print axioms Chapter03.OAExec.master_height_values_closed
#print axioms Chapter03.OAExec.master_attained_of_bddBelow
