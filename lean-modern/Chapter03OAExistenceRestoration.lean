module

public import Chapter03OAExistenceViolation
public import Chapter03OAExistenceSublevels

@[expose] public section

/-! Attainment of the actual sum of individual nonnegative slacks on each
requested hard fiber. Bounded nonlinear relaxation supplies compact sublevels;
neither bounded X nor a restoration optimizer/KKT premise is assumed. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

theorem restoration_minimum_exists (d : Data n m l r) (a : Analytic d)
    (hdom : d.domain = (asFP d).base) (hbounded : Bornology.IsBounded d.relaxation)
    (hne : d.relaxation.Nonempty) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi) (hslice : (hardSlice d y).Nonempty) :
    ∃ x : RealVector n, ∃ s : RealVector l,
      IsMinimizer (restSet d.model (intCast y)) restCost (weightedInsert x s) := by
  have hcont : ContinuousOn (violation d) ((asFP d).base) := by
    rw [← hdom]
    exact violation_continuousOn d a
  have hconv : ConvexOn ℝ ((asFP d).base) (violation d) := by
    rw [← hdom]
    exact violation_convex d a
  have hzero : {p ∈ (asFP d).base | violation d p ≤ 0}.Nonempty := by
    rw [violation_zero_sublevel]
    exact hne
  have hzeroBounded : Bornology.IsBounded {p ∈ (asFP d).base | violation d p ≤ 0} := by
    rw [violation_zero_sublevel]
    exact hbounded
  obtain ⟨⟨x,w⟩,hm⟩ := Chapter03.OAExistence.convex_minimizer_on_closed_subset
    (Chapter03.FP.base_closed (asFP d)) hcont hconv
    (fun p _ => violation_nonneg d p) hzero hzeroBounded
    (hardSlice_closed d y) (fun _ hp => hp.1) hslice
  have hw : w = intCast y := hm.1.2
  subst w
  exact ⟨x,fun j => max (d.model.g j (x,intCast y)) 0,
    hardSlice_minimum_gives_restoration d y hy x hm⟩

theorem master_point_base (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) {z : Point n m × ℝ} (hz : z ∈ master d seed H) :
    z.1 ∈ (asFP d).base := by
  obtain ⟨hl,⟨y,hy,hcast⟩,_⟩ := (master_mem_iff d seed H z).mp hz
  refine ⟨hl,?_⟩
  rw [hcast]
  exact hy

theorem master_hardSlice_nonempty (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) {z : Point n m × ℝ} (hz : z ∈ master d seed H)
    (y : IntVector m) (hsame : z.1.2 = intCast y) : (hardSlice d y).Nonempty :=
  ⟨z.1,master_point_base d seed H hz,hsame⟩

theorem requested_restoration_minimum_exists (d : Data n m l r) (a : Analytic d)
    (hdom : d.domain = (asFP d).base) (hbounded : Bornology.IsBounded d.relaxation)
    (seed : Point n m) (hseed : SeedValid d seed) (H : List (Event d))
    {z : Point n m × ℝ} (hz : z ∈ master d seed H)
    (y : IntVector m) (hy : y ∈ IntegerBox d.model.lo d.model.hi)
    (hsame : z.1.2 = intCast y) :
    ∃ x : RealVector n, ∃ s : RealVector l,
      IsMinimizer (restSet d.model (intCast y)) restCost (weightedInsert x s) :=
  restoration_minimum_exists d a hdom hbounded ⟨seed,hseed.1.1⟩ y hy
    (master_hardSlice_nonempty d seed H hz y hsame)

end Chapter03.OAExec

#print axioms Chapter03.OAExec.restoration_minimum_exists
#print axioms Chapter03.OAExec.requested_restoration_minimum_exists
