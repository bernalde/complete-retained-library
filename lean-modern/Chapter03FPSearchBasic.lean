module

public import Chapter03FPSearchAffineCQ
public import Chapter03FPSearchFinite

@[expose] public section

/-! BASIC first-search normal law derived from the exact joint-domain CQ.
This module adds no normal cut to the master and assumes no progress oracle. -/
noncomputable section
open scoped RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch
variable {n m l r : ℕ}

theorem basic_normal_law (d : Data n m l) (b : BaseRows d r)
    (h : Analytic d) (Q : Finset (IntVector m)) (hcq : ProjectionLICQ d b Q) :
    NormalLaw d .basic Q := by
  intro s hs hQ p hp e he
  exact affine_base_projection_normal d b h e.target e.projection p
    (hs.events e he).projection_min
    (hcq e.target (hQ e he) e.projection (hs.events e he).projection_min)
    hp.1 (fun j hj => master_active_tangent d h hs hp he j hj)

/-- Qualified BASIC first-feasibility endpoint. Every exact initializer and
selector is admitted; uniform joint LICQ over the exact finite affine base
supplies the normal law internally. The result concerns return and call counts,
not distinctness of relaxed projections in the held source Theorem 1. -/
theorem qualified_basic_first_feasibility (d : Data n m l) (b : BaseRows d r)
    (h : Analytic d) (Q : Finset (IntVector m))
    (hb : TargetBound d .basic Q) (hcq : ProjectionLICQ d b Q) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d .basic) ∧
      ∀ (initial : Initialization d) (choose : Selector d .basic),
        ∃ out, procedureWithFuel d .basic initial choose (Q.card+1) = some out ∧
          out.Correct d ∧ out.Counts Q.card := by
  exact ⟨initialization_nonempty d h, selector_nonempty d h .basic,
    fun initial choose => initialized_finite_return d h hb
      (basic_normal_law d b h Q hcq) initial choose⟩

end Chapter03.FPSearch
