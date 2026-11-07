module

public import Chapter03PumpOAModel
public import Chapter03FPTraceC2Handoff

@[expose] public section

/-! Exact hard-domain source adapter for the accepted C2 pump trace.
There are no continuous coordinates and no soft or hard rows; the fixed LICQ
family is empty. The objective, bounds, derivatives, cutoff and actual pump
trace are unchanged. This is supporting author evidence, not acceptance. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA.C2
open Chapter03.FPTrace

def spec : OAExec.Data 0 2 0 0 where
  model := C2.model
  f := C2.d.f
  Df := C2.d.Df
  Dg p j := C2.d.Dg j p
  domain := C2.d.base

theorem nonlinear_empty : spec.nonlinear = ∅ := by
  ext j
  exact Fin.elim0 j

theorem adapter_exact : asFPDelta spec (37/81) = C2.d := by
  unfold asFPDelta OAExec.asFP
  simp only [nonlinear_empty]
  rfl

theorem exact_identities : spec.model = C2.d.model ∧ spec.f = C2.d.f ∧
    spec.Df = C2.d.Df ∧ (∀ p j, spec.Dg p j = C2.d.Dg j p) ∧
    spec.domain = C2.d.base ∧ spec.relaxation = C2.d.relaxation ∧
    spec.original = C2.d.original ∧ spec.box = C2.d.box :=
  ⟨rfl,rfl,rfl,fun _ _ => rfl,rfl,rfl,rfl,rfl⟩

theorem analytic : OAExec.Analytic spec where
  convex_f := C2.d_analytic.convex_f
  convex_g := C2.d_analytic.convex_g
  original_domain := fun _ hp => FP.relaxation_subset_base C2.d
    (FP.original_subset_relaxation C2.d hp)
  derivative_f := C2.d_analytic.derivative_f
  derivative_g p hp j := C2.d_analytic.derivative_g j p hp

theorem fixed_licq (y : IntVector 2) (x : RealVector 0) :
    FixedLICQ spec.model x (intCast y) (spec.Dg (x,intCast y)) := by
  exact linearIndependent_empty_type

def bounds : Bounds 0 where
  lower j := Fin.elim0 j
  upper j := Fin.elim0 j

def encoding : HardBoundEncoding bounds spec.model where
  valid j := Fin.elim0 j
  side j := Fin.elim0 j
  injective := by intro i; exact Fin.elim0 i
  lower_cover j := Fin.elim0 j
  upper_cover j := Fin.elim0 j
  row_spec j := Fin.elim0 j

theorem domain_article : spec.domain = OAExec.articleDomain bounds spec := by
  rw [OAExec.articleDomain_eq_base bounds spec encoding]
  rfl

theorem source_package : OAExec.AvailabilityAssumptions spec :=
  OAExec.article_availability_assumptions bounds spec encoding analytic domain_article
    C2.d_analytic.bounded_relaxation (fun y _ x _ => fixed_licq y x)

theorem seed_valid : OAExec.SeedValid spec C2.seed := by
  refine ⟨C2.seed_minimizer 1 0 (37/81) (by norm_num),?_,?_⟩
  · exact FP.relaxation_subset_base C2.d
      (C2.seed_minimizer 1 0 (37/81) (by norm_num)).1
  · intro hi
    obtain ⟨y,hy⟩ := hi
    have he := congrFun hy (0 : Fin 2)
    norm_num [C2.seed,C2.pt,intCast] at he
    have hlo : (0 : ℤ) < y 0 := by exact_mod_cast (show (0 : ℝ) < (y 0 : ℝ) by linarith)
    have hhi : y 0 < (1 : ℤ) := by exact_mod_cast (show (y 0 : ℝ) < 1 by linarith)
    omega

/-- The existing actual cap-two trace, transported by an exact data equality. -/
theorem capTwo_procedure_exact :
    FP.procedure (asFPDelta spec (37/81))
      (adapter_exact.symm ▸ C2.initialization)
      (adapter_exact.symm ▸ C2.chooseCapTwo) = some (.loop C2.capTwoOutput) := by
  have transport : ∀ (data : FP.Data 0 2 0 0) (h : data = C2.d),
      FP.procedure data (h.symm ▸ C2.initialization) (h.symm ▸ C2.chooseCapTwo) =
        some (.loop C2.capTwoOutput) := by
    intro data h
    subst data
    exact C2.capTwo_procedure
  exact transport _ adapter_exact

end Chapter03.PumpOA.C2

#print axioms Chapter03.PumpOA.C2.adapter_exact
#print axioms Chapter03.PumpOA.C2.source_package
#print axioms Chapter03.PumpOA.C2.seed_valid
#print axioms Chapter03.PumpOA.C2.capTwo_procedure_exact
