module

public import Chapter03OASoftExecutionSelectors
public import Chapter03OASoftExecutionReturn

@[expose] public section

/-! Derived initialized qualified soft execution. Attainment, fixed KKT,
restoration replies and inhabited selectors are proved from visible assumptions;
no final output or progress callback is supplied. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.OASoftExecutionAvailability
variable {n m l r : ℕ} {d : OAExec.Data n m l r}

theorem initialized_choices_nonempty (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (epsilon : ℝ) :
    Nonempty (OASoftExec.InitializedSelectors d epsilon) :=
  OASoftExec.initialized_selectors_inhabited (fun seed hs => local_available h hard seed hs epsilon)

theorem initial_policy_nonempty (d : OAExec.Data n m l r) : Nonempty (Policy d []) :=
  ⟨⟨fun _ => 0,fun _ => le_rfl,fun i => Fin.elim0 i⟩⟩

/-- One initialized endpoint, universally over actual admitted selector and seed
weight choices. Its existence clauses prevent vacuity of those choice types. -/
theorem qualified_initialized_finite_return (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (OAExec.Initialization d) ∧ Nonempty (Policy d []) ∧
    (∀ seed, SeedValid d seed → OASoftExec.LocalAvailability d seed epsilon) ∧
    Nonempty (OASoftExec.InitializedSelectors d epsilon) ∧
    ∀ (choose : OASoftExec.InitializedSelectors d epsilon) (P0 : Policy d [])
      (initial : OAExec.Initialization d),
      ∃ out, OASoftExec.execute d epsilon choose P0 initial = some out ∧
        OAExec.ReturnCertificate d epsilon out.result ∧
        out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
        out.restorations ≤ d.box.card :=
  ⟨h.initialization_nonempty,initial_policy_nonempty d,
    fun seed hs => local_available h hard seed hs epsilon,
    initialized_choices_nonempty h hard epsilon,
    fun choose P0 initial => OASoftExec.initialized_finite_return h.analytic heps choose P0 initial⟩

theorem qualified_initialized_zero_return (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (choose : OASoftExec.InitializedSelectors d 0)
    (P0 : Policy d []) (initial : OAExec.Initialization d) :
    ∃ out, OASoftExec.execute d 0 choose P0 initial = some out ∧
      (match out.result with
       | .infeasible => ¬ d.original.Nonempty
       | .solution p => IsMinimizer d.original d.f p) ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card := by
  obtain ⟨out,he,hc,hm,hf,hr⟩ :=
    (qualified_initialized_finite_return h hard (le_refl (0 : ℝ))).2.2.2.2 choose P0 initial
  refine ⟨out,he,?_,hm,hf,hr⟩
  cases hv : out.result with
  | infeasible => simpa only [hv,OAExec.ReturnCertificate] using hc
  | solution p => simpa only [hv,OAExec.ReturnCertificate,add_zero,IsMinimizer] using hc

end Chapter03.OASoftExecutionAvailability
