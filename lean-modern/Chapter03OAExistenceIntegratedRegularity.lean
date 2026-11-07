module

public import Chapter03OAExistenceIntegratedExecution

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.OAExec.Integrated

theorem domain_product : domain=bounds.region ×ˢ Set.Icc (scalar 0) (scalar 1) := by
  ext p
  simp only [Set.mem_prod,Set.mem_Icc,bounds_region]
  change (p.1 0≤1/2 ∧ 0≤p.2 0 ∧ p.2 0≤1) ↔
    p.1 0≤1/2 ∧ (∀i,0≤p.2 i) ∧ ∀i,p.2 i≤1
  simp only [Fin.forall_fin_one]

theorem bounds_unbounded : ¬ Bornology.IsBounded bounds.region := by
  intro hX
  apply domain_unbounded
  rw [domain_product]
  exact hX.prod (isCompact_Icc.isBounded)

/-- Uniform LICQ at every actual minimum of every nonempty legal fixed fiber.
The y=0 branch is excluded by original-fiber emptiness. The unique y=1 minimum
has one active hard x-normal, and its original nonlinear row is inactive. -/
theorem all_minima_LICQ (y : IntVector 1) (hy : y∈IntegerBox model.lo model.hi)
    (x : V) (hm : IsMinimizer (fiber model (intCast y))
      (fiberObjective objective (intCast y)) x) :
    LinearIndependent ℝ
      (fun i : {i : Fin 1 ⊕ Fin 1 |
        Sum.elim (fun j => soft model (intCast y) j x)
          (fun k => hard model (intCast y) k x) i=0} =>
        Sum.elim (fun j => restrict (Dg (x,intCast y) j))
          (fun k => fiberLinearRow model k) i.1) := by
  change LinearIndepOn ℝ
    (fun i : Fin 1 ⊕ Fin 1 =>
      Sum.elim (fun j => restrict (Dg (x,intCast y) j))
        (fun k => fiberLinearRow model k) i)
    {i | Sum.elim (fun j => soft model (intCast y) j x)
      (fun k => hard model (intCast y) k x) i=0}
  rcases target_cases y hy with rfl|rfl
  · exact False.elim (zero_fiber_empty ⟨x,by simpa only [cast_target0] using hm.1⟩)
  · rw [cast_target1]
    simp only [cast_target1] at hm
    have hx : x=scalar (1/2) := fixed_unique hm
    subst x
    exact fixed_LICQ

end Chapter03.OAExec.Integrated
