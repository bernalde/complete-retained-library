module

public import Chapter03OAExistenceAnalytic

@[expose] public section

/-! Exact positive-part objective and hard-slice identities for the source
individual-slack restoration. All original g rows remain in the sum. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

def violation (d : Data n m l r) : Point n m → ℝ :=
  weightedPositive (fun _ : Fin l => 1) d.model.g

theorem violation_nonneg (d : Data n m l r) (p : Point n m) :
    0 ≤ violation d p :=
  weightedPositive_nonneg _ _ (fun _ => zero_le_one) p

theorem violation_eq_zero_iff (d : Data n m l r) (p : Point n m) :
    violation d p = 0 ↔ ∀ j, d.model.g j p ≤ 0 :=
  weightedPositive_eq_zero_iff _ _ (fun _ => zero_lt_one) p

theorem violation_le_zero_iff (d : Data n m l r) (p : Point n m) :
    violation d p ≤ 0 ↔ ∀ j, d.model.g j p ≤ 0 := by
  rw [← violation_eq_zero_iff]
  exact ⟨fun h => le_antisymm h (violation_nonneg d p),fun h => h.le⟩

theorem violation_continuousOn (d : Data n m l r) (a : Analytic d) :
    ContinuousOn (violation d) d.domain := by
  change ContinuousOn (fun p => ∑ j, (1 : ℝ) * max (d.model.g j p) 0) d.domain
  apply continuousOn_finset_sum
  intro j _
  apply continuousOn_const.mul
  have hg : ContinuousOn (d.model.g j) d.domain :=
    fun p hp => (a.derivative_g p hp j).continuousAt.continuousWithinAt
  exact hg.sup continuousOn_const

theorem violation_convex (d : Data n m l r) (a : Analytic d) :
    ConvexOn ℝ d.domain (violation d) := by
  have h (S : Finset (Fin l)) :
      ConvexOn ℝ d.domain (fun p => ∑ j ∈ S, max (d.model.g j p) 0) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using convexOn_const (0 : ℝ) a.convex_f.1
    | @insert j S hj ih =>
      simpa [Finset.sum_insert hj,Pi.add_def] using
        ((a.convex_g j).sup (convexOn_const (0 : ℝ) a.convex_f.1)).add ih
  change ConvexOn ℝ d.domain (fun p => ∑ j, (1 : ℝ) * max (d.model.g j p) 0)
  simpa only [one_mul] using h Finset.univ

theorem violation_zero_sublevel (d : Data n m l r) :
    {p ∈ (asFP d).base | violation d p ≤ 0} = d.relaxation := by
  ext p
  rw [Set.mem_setOf_eq,violation_le_zero_iff,asFP_base_iff,relaxation_mem_iff]
  tauto

def hardSlice (d : Data n m l r) (y : IntVector m) : Set (Point n m) :=
  {p ∈ (asFP d).base | p.2 = intCast y}

theorem hardSlice_closed (d : Data n m l r) (y : IntVector m) :
    IsClosed (hardSlice d y) :=
  (Chapter03.FP.base_closed (asFP d)).inter (isClosed_eq continuous_snd continuous_const)

theorem hardSlice_subset_domain (d : Data n m l r)
    (hdom : d.domain = (asFP d).base) (y : IntVector m) :
    hardSlice d y ⊆ d.domain :=
  fun _ hp => hdom.symm ▸ hp.1

theorem hardSlice_insert_iff (d : Data n m l r) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi) (x : RealVector n) :
    (x,intCast y) ∈ hardSlice d y ↔
      x ∈ weightedHardRegion Set.univ (hard d.model (intCast y)) := by
  constructor
  · intro hx
    refine ⟨Set.mem_univ _,?_⟩
    intro i
    exact sub_nonpos.mpr (hx.1.1 i)
  · rintro ⟨_,hh⟩
    refine ⟨⟨?_,hy⟩,rfl⟩
    intro i
    exact sub_nonpos.mp (hh i)

@[simp] theorem violation_fiber (d : Data n m l r) (x : RealVector n)
    (y : RealVector m) :
    violation d (x,y) = weightedPositive (fun _ : Fin l => 1) (soft d.model y) x := rfl

theorem hardSlice_minimum_gives_restoration (d : Data n m l r)
    (y : IntVector m) (hy : y ∈ IntegerBox d.model.lo d.model.hi) (x : RealVector n)
    (hmin : IsMinimizer (hardSlice d y) (violation d) (x,intCast y)) :
    IsMinimizer (restSet d.model (intCast y)) restCost
      (weightedInsert x (fun j => max (d.model.g j (x,intCast y)) 0)) := by
  apply (rest_minimizer_iff d.model (intCast y) x _).mpr
  refine ⟨⟨(hardSlice_insert_iff d y hy x).mp hmin.1,?_⟩,fun _ => rfl⟩
  intro z hz
  exact hmin.2 (z,intCast y) ((hardSlice_insert_iff d y hy z).mpr hz)

end Chapter03.OAExec

#print axioms Chapter03.OAExec.violation_convex
#print axioms Chapter03.OAExec.violation_zero_sublevel
#print axioms Chapter03.OAExec.hardSlice_minimum_gives_restoration
