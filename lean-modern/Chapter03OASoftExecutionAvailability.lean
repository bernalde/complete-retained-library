module

public import Chapter03OASoftStoredPolicy
public import Chapter03OAExistenceAvailability

@[expose] public section

/-! S018 author proposal: actual choice existence under explicit regularity and
hard affine entailment. No execution or future coverage is an assumption. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
open Chapter03.OAExec Chapter03.OASoftMaster Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.OASoftExecutionAvailability
variable {n m l r : ℕ} {d : OAExec.Data n m l r}

/-- A certificate-independent sufficient data restriction. This requires all
nonselected affine rows to hold on the actual hard domain, not only supported
rows at one minimum. Moving a soft row to that domain is a separate repair. -/
def HardAffineEntailment (d : OAExec.Data n m l r) : Prop :=
  ∀ j, j ∉ d.nonlinear → ∀ q ∈ d.model.linearRegion,
    q ∈ IntegerCylinder (n := n) d.model.lo d.model.hi → d.model.g j q ≤ 0

/-- Choose a certificate once, then retain that chosen value in generation data.
The KKT witness is obtained from actual EventValid, not postulated coverage. -/
def generationOfValid (hard : HardAffineEntailment d) {e : OAExec.Event d}
    (he : OAExec.EventValid d e) : Generation d e where
  valid := he
  certificate hn := Classical.choice (OAExec.event_fixed_kkt he hn)
  hard := by
    intro hn j hj _ q hq hy
    calc
      _ = d.model.g j q := affine_tangent (d.affine_of_not_nonlinear j hj)
        ((Classical.choice (OAExec.event_fixed_kkt he hn)).derivative_g j) q
      _ ≤ 0 := hard j hj q hq hy

/-- Uniform all-minimizer LICQ supplies actual fixed KKT through the accepted
necessity theorem; the final Generation stores one such actual certificate. -/
theorem fixed_generation_exists (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi)
    (hne : (fiber d.model (intCast y)).Nonempty) :
    ∃ x, Nonempty (Generation d ⟨y,hy,x,none⟩) := by
  obtain ⟨x,hm⟩ := OAExec.fixed_minimum_exists d h.analytic h.domain_base
    h.bounded_relaxation y hy hne
  exact ⟨x,⟨generationOfValid hard (h.every_exact_fixed_event y hy x hm)⟩⟩

/-- The restoration branch has no KKT or LICQ obligation. Its attained slack
minimum and actual empty fixed fiber are the accepted event validity data. -/
theorem restoration_generation_exists (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (hne : d.relaxation.Nonempty)
    (y : IntVector m) (hy : y ∈ IntegerBox d.model.lo d.model.hi)
    (hslice : (OAExec.hardSlice d y).Nonempty)
    (hempty : ¬ (fiber d.model (intCast y)).Nonempty) :
    ∃ x s, Nonempty (Generation d ⟨y,hy,x,some s⟩) := by
  obtain ⟨x,s,hm⟩ := OAExec.restoration_minimum_exists d h.analytic h.domain_base
    h.bounded_relaxation hne y hy hslice
  exact ⟨x,s,⟨generationOfValid hard
    (h.every_exact_restoration_event y hy x s hempty hm)⟩⟩

/-- Every actual soft candidate has an attained valid fixed/restoration reply
with generation data. This does not require hard tangent-master membership. -/
theorem requested_generation_exists (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (hne : d.relaxation.Nonempty)
    (seed : Point n m) (H : List (OAExec.Event d))
    {z : Candidate (OAExec.family d seed H)} (hz : z ∈ historyMaster d seed H) :
    ∃ e : OAExec.Event d, Nonempty (Generation d e) ∧ z.1.2 = intCast e.target := by
  classical
  obtain ⟨y,hy,hsame⟩ := hz.2.1
  by_cases hf : (fiber d.model (intCast y)).Nonempty
  · obtain ⟨x,hx⟩ := fixed_generation_exists h hard y hy hf
    exact ⟨⟨y,hy,x,none⟩,hx,hsame⟩
  · obtain ⟨x,s,hx⟩ := restoration_generation_exists h hard hne y hy
      (soft_master_hardSlice_nonempty d seed H hz y hsame) hf
    exact ⟨⟨y,hy,x,some s⟩,hx,hsame⟩

end Chapter03.OASoftExecutionAvailability
