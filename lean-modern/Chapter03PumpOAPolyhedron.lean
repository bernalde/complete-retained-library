module

public import Chapter03PumpOARows

@[expose] public section

/-! Exact finite integer-fiber representation and height attainment for the
retained combined master. No compact master, valid prefix, optimizer or progress
premise is used. Both exclusion families are preserved as whole-fiber filters. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExistence
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

def masterFiberPolyhedron (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (y : IntVector m) : Set (RealVector n × ℝ) :=
  {v | ∀ i, ((masterRow d delta P H i).comp (OAExec.masterFiberEmbedding n m)) v ≤
    masterRowBound d delta P H i - masterRow d delta P H i ((0,intCast y),0)}

def masterAllowed (d : OAExec.Data n m l r) (P : FP.State n m)
    (H : List (OAExec.Event d)) : Finset (IntVector m) := by
  classical
  exact d.box.filter (fun y => noGoods P H (0,intCast y))

theorem masterFiber_row_identity (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) (H : List (OAExec.Event d)) (y : IntVector m)
    (v : RealVector n × ℝ) (i : MasterRowIndex d delta P H) :
    masterRow d delta P H i (OAExec.masterFiberLift y v) =
      ((masterRow d delta P H i).comp (OAExec.masterFiberEmbedding n m)) v +
        masterRow d delta P H i ((0,intCast y),0) := by
  rw [ContinuousLinearMap.comp_apply, ← map_add]
  congr 1
  ext <;> simp [OAExec.masterFiberLift, OAExec.masterFiberEmbedding]

/-- Equivalence, not merely enclosure, for each permitted integer assignment. -/
theorem masterFiber_mem_iff (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) (H : List (OAExec.Event d)) (y : IntVector m)
    (hy : y ∈ masterAllowed d P H) (v : RealVector n × ℝ) :
    OAExec.masterFiberLift y v ∈ master d delta P H ↔
      v ∈ masterFiberPolyhedron d delta P H y := by
  classical
  obtain ⟨hybox,hyng⟩ := Finset.mem_filter.mp hy
  have hc : (OAExec.masterFiberLift y v).1 ∈
      IntegerCylinder (n := n) d.model.lo d.model.hi :=
    ⟨y,by simpa [OAExec.Data.box] using hybox,rfl⟩
  have hn : noGoods P H (OAExec.masterFiberLift y v).1 := hyng
  rw [master_rows_iff]
  constructor
  · intro hh i
    have hi := hh.1 i
    rw [masterFiber_row_identity] at hi
    exact le_sub_iff_add_le.mpr hi
  · intro hh
    refine ⟨?_,hc,hn⟩
    intro i
    rw [masterFiber_row_identity]
    exact le_sub_iff_add_le.mp (hh i)

/-- The original combined master is exactly a finite union of affine lifts of
finite weak polyhedra. No success, empty-fiber or projection row is omitted. -/
theorem master_finite_fiber_union (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) (H : List (OAExec.Event d)) :
    master d delta P H = ⋃ y ∈ masterAllowed d P H,
      OAExec.masterFiberLift y '' masterFiberPolyhedron d delta P H y := by
  classical
  ext z
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · intro hz
    obtain ⟨y,hy,hey⟩ := OAExec.master_integer hz.2
    have hng := ((master_rows_iff d delta P H z).mp hz).2.2
    have ha : y ∈ masterAllowed d P H := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [OAExec.Data.box] using hy,?_,?_⟩
      · intro e he hn
        simpa only [← hey] using hng.1 e he hn
      · intro e he hn
        simpa only [← hey] using hng.2 e he hn
    have hzlift : OAExec.masterFiberLift y (z.1.1,z.2) = z := by
      apply Prod.ext
      · exact Prod.ext rfl hey.symm
      · rfl
    refine ⟨y,ha,(z.1.1,z.2),?_,hzlift⟩
    apply (masterFiber_mem_iff d delta P H y ha _).mp
    rwa [hzlift]
  · rintro ⟨y,hy,v,hv,rfl⟩
    exact (masterFiber_mem_iff d delta P H y hy v).mpr hv

theorem master_height_finite_union (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) (H : List (OAExec.Event d)) :
    Prod.snd '' master d delta P H = ⋃ y ∈ masterAllowed d P H,
      Prod.snd '' masterFiberPolyhedron d delta P H y := by
  rw [master_finite_fiber_union]
  simp only [Set.image_iUnion, Set.image_image]
  rfl

theorem master_height_values_closed (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) (H : List (OAExec.Event d)) :
    IsClosed (Prod.snd '' master d delta P H) := by
  classical
  letI : Fintype (MasterRowIndex d delta P H) := Fintype.ofFinite _
  rw [master_height_finite_union]
  apply isClosed_biUnion_finset
  intro y _
  exact finite_polyhedron_value_closed
    (fun i => (masterRow d delta P H i).comp (OAExec.masterFiberEmbedding n m))
    (fun i => masterRowBound d delta P H i-masterRow d delta P H i ((0,intCast y),0))
    (ContinuousLinearMap.snd ℝ (RealVector n) ℝ)

/-- A nonempty combined master with bounded-below height attains its minimum,
even for arbitrary finite prefix/suffix data and unbounded continuous masters. -/
theorem master_attained_of_bddBelow (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) (H : List (OAExec.Event d))
    (hne : (master d delta P H).Nonempty)
    (hbb : BddBelow (Prod.snd '' master d delta P H)) :
    ∃ z, IsMinimizer (master d delta P H) Prod.snd z := by
  have hleast := (master_height_values_closed d delta P H).isLeast_csInf
    (hne.image Prod.snd) hbb
  obtain ⟨z,hz,he⟩ := hleast.1
  refine ⟨z,hz,?_⟩
  intro w hw
  rw [he]
  exact hleast.2 ⟨w,hw,rfl⟩

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.masterFiber_mem_iff
#print axioms Chapter03.PumpOA.master_finite_fiber_union
#print axioms Chapter03.PumpOA.master_height_values_closed
#print axioms Chapter03.PumpOA.master_attained_of_bddBelow
