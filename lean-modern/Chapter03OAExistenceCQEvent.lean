module

public import Chapter03OAExistenceFixedKKT
public import Chapter03OAExecModel

@[expose] public section

/-! Every exact fixed minimum satisfying the literal active-x LICQ is a valid
existing OA event. This is an admissibility theorem for the supplied minimum,
not merely for a classically selected witness. Restoration KKT is unused. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

theorem fixed_event_valid_of_licq
    (d : Data n m l r) (a : Analytic d)
    (y : IntVector m) (hy : y ∈ IntegerBox d.model.lo d.model.hi)
    (x : RealVector n)
    (hmin : IsMinimizer (fiber d.model (intCast y))
      (fiberObjective d.f (intCast y)) x)
    (hlicq : FixedLICQ d.model x (intCast y) (d.Dg (x,intCast y))) :
    EventValid d ⟨y,hy,x,none⟩ := by
  have hp : (x,intCast y) ∈ d.domain :=
    a.original_domain ((fiber_original_iff d.model y hy x).mp hmin.1)
  refine ⟨hp, hmin, ?_⟩
  exact fixed_kkt_exists_of_licq d.model d.f x (intCast y)
    (d.Df (x,intCast y)) (d.Dg (x,intCast y))
    (a.derivative_f _ hp) (a.derivative_g _ hp) hmin hlicq

end Chapter03.OAExec

#check Chapter03.OAExec.fixed_event_valid_of_licq
#print axioms Chapter03.OAExec.fixed_event_valid_of_licq
