module

public import Chapter03FPAnalytic
public import Chapter03OAExecInitialization

@[expose] public section

/-! Author-stage exact adapters for OA availability. The bounded-set reading
of A3 and ambient derivatives on the hard domain are explicit sufficient
interpretations. This module derives initializer and feasible-fiber attainment;
it neither assumes an optimizer nor changes the accepted execution. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

/-- The same model/objective/derivatives, with the FP derivative argument order.
The unused pump cutoff parameter is zero. This does not execute a pump. -/
def asFP (d : Data n m l r) : Chapter03.FP.Data n m l r where
  model := d.model
  f := d.f
  Df := d.Df
  Dg j p := d.Dg p j
  nonlinear := d.nonlinear
  delta := 0

@[simp] theorem asFP_relaxation (d : Data n m l r) :
    (asFP d).relaxation = d.relaxation := rfl

@[simp] theorem asFP_original (d : Data n m l r) :
    (asFP d).original = d.original := rfl

theorem asFP_base_iff (d : Data n m l r) (p : Point n m) :
    p ∈ (asFP d).base ↔ p ∈ d.model.linearRegion ∧
      ∀ j, d.model.lo j ≤ p.2 j ∧ p.2 j ≤ d.model.hi j := Iff.rfl

theorem asFP_analytic (d : Data n m l r) (a : Analytic d)
    (hdom : d.domain = (asFP d).base)
    (hbounded : Bornology.IsBounded d.relaxation) : Chapter03.FP.Analytic (asFP d) where
  convex_f := by
    change ConvexOn ℝ (asFP d).base d.f
    rw [← hdom]
    exact a.convex_f
  convex_g := by
    intro j
    change ConvexOn ℝ (asFP d).base (d.model.g j)
    rw [← hdom]
    exact a.convex_g j
  derivative_f := by
    intro p hp
    change HasFDerivAt d.f (d.Df p) p
    exact a.derivative_f p (hdom.symm ▸ hp)
  derivative_g := by
    intro j p hp
    exact a.derivative_g p (hdom.symm ▸ hp) j
  bounded_relaxation := hbounded
  delta_nonnegative := le_rfl

theorem relaxation_subset_domain_of_base (d : Data n m l r)
    (hdom : d.domain = (asFP d).base) : d.relaxation ⊆ d.domain := by
  rw [hdom]
  exact Chapter03.FP.relaxation_subset_base (asFP d)

/-- Every exact initializer answer has domain membership, not just a chosen
attainment witness. -/
theorem relaxation_minimum_domain (d : Data n m l r)
    (hdom : d.domain = (asFP d).base) {seed : Point n m}
    (hmin : IsMinimizer d.relaxation d.f seed) : seed ∈ d.domain :=
  relaxation_subset_domain_of_base d hdom hmin.1

def exact_initialization (d : Data n m l r)
    (hdom : d.domain = (asFP d).base) (seed : Point n m)
    (hmin : IsMinimizer d.relaxation d.f seed) : Initialization d :=
  .minimum seed hmin (relaxation_minimum_domain d hdom hmin)

theorem initial_availability_of_bounded_relaxation (d : Data n m l r)
    (a : Analytic d) (hdom : d.domain = (asFP d).base)
    (hbounded : Bornology.IsBounded d.relaxation) : InitialAvailability d := by
  classical
  by_cases hne : d.relaxation.Nonempty
  · obtain ⟨p,hp⟩ := Chapter03.FP.relaxation_attained (asFP d)
      (asFP_analytic d a hdom hbounded) hne
    exact Or.inr ⟨p,hp,relaxation_subset_domain_of_base d hdom hp.1⟩
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

theorem initialization_nonempty_of_bounded_relaxation (d : Data n m l r)
    (a : Analytic d) (hdom : d.domain = (asFP d).base)
    (hbounded : Bornology.IsBounded d.relaxation) : Nonempty (Initialization d) :=
  initialization_inhabited (initial_availability_of_bounded_relaxation d a hdom hbounded)

theorem asFP_fiber_insert_iff (d : Data n m l r) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi) (x : RealVector n) :
    (x,intCast y) ∈ (asFP d).fiber y ↔ x ∈ fiber d.model (intCast y) := by
  change ((x,intCast y) ∈ d.relaxation ∧ intCast y = Chapter03.FP.intCast y) ↔ _
  rw [relaxation_mem_iff]
  constructor
  · rintro ⟨⟨hg,hl,_⟩,_⟩
    exact ⟨hl,hg⟩
  · rintro ⟨hl,hg⟩
    exact ⟨⟨hg,hl,hy⟩,rfl⟩

theorem asFP_fiber_iff (d : Data n m l r) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi) (p : Point n m) :
    p ∈ (asFP d).fiber y ↔ p.2 = intCast y ∧ p.1 ∈ fiber d.model (intCast y) := by
  rcases p with ⟨x,w⟩
  constructor
  · intro hp
    have hw : w = intCast y := hp.2
    subst w
    exact ⟨rfl,(asFP_fiber_insert_iff d y hy x).mp hp⟩
  · rintro ⟨hw,hx⟩
    change w = intCast y at hw
    subst w
    exact (asFP_fiber_insert_iff d y hy x).mpr hx

theorem asFP_fiber_minimizer_iff (d : Data n m l r) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi) (x : RealVector n) :
    IsMinimizer ((asFP d).fiber y) d.f (x,intCast y) ↔
      IsMinimizer (fiber d.model (intCast y)) (fiberObjective d.f (intCast y)) x := by
  constructor
  · rintro ⟨hx,hm⟩
    exact ⟨(asFP_fiber_insert_iff d y hy x).mp hx,
      fun z hz => hm (z,intCast y) ((asFP_fiber_insert_iff d y hy z).mpr hz)⟩
  · rintro ⟨hx,hm⟩
    refine ⟨(asFP_fiber_insert_iff d y hy x).mpr hx,?_⟩
    rintro ⟨z,w⟩ hz
    obtain ⟨hw,hz⟩ := (asFP_fiber_iff d y hy (z,w)).mp hz
    change w = intCast y at hw
    subst w
    exact hm z hz

theorem fixed_minimum_exists (d : Data n m l r) (a : Analytic d)
    (hdom : d.domain = (asFP d).base) (hbounded : Bornology.IsBounded d.relaxation)
    (y : IntVector m) (hy : y ∈ IntegerBox d.model.lo d.model.hi)
    (hne : (fiber d.model (intCast y)).Nonempty) :
    ∃ x, IsMinimizer (fiber d.model (intCast y)) (fiberObjective d.f (intCast y)) x := by
  have hfp : ((asFP d).fiber y).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,intCast y),(asFP_fiber_insert_iff d y hy x).mpr hx⟩
  obtain ⟨⟨x,w⟩,hp⟩ := Chapter03.FP.fiber_attained (asFP d)
    (asFP_analytic d a hdom hbounded) y hfp
  have hw : w = intCast y := hp.1.2
  subst w
  exact ⟨x,(asFP_fiber_minimizer_iff d y hy x).mp hp⟩

/-- Every exact restoration reply is admitted, without a restoration KKT or
tight-slack premise. Its actual primal feasibility supplies domain membership. -/
theorem exact_restoration_event_valid (d : Data n m l r)
    (hdom : d.domain = (asFP d).base) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi) (x : RealVector n) (s : RealVector l)
    (hempty : ¬ (fiber d.model (intCast y)).Nonempty)
    (hmin : IsMinimizer (restSet d.model (intCast y)) restCost (weightedInsert x s)) :
    EventValid d ⟨y,hy,x,some s⟩ := by
  refine ⟨?_,hempty,hmin⟩
  change (x,intCast y) ∈ d.domain
  rw [hdom,asFP_base_iff]
  refine ⟨?_,hy⟩
  have hh := ((restSet_insert_iff d.model (intCast y) x s).mp hmin.1).1
  intro i
  exact sub_nonpos.mp (hh i)

end Chapter03.OAExec

#print axioms Chapter03.OAExec.initial_availability_of_bounded_relaxation
#print axioms Chapter03.OAExec.fixed_minimum_exists
#print axioms Chapter03.OAExec.exact_restoration_event_valid
