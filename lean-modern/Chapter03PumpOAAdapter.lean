module

public import Chapter03PumpOAModel

@[expose] public section

/-! Syntactic shared-data identities for the cutoff-parameter adapter. These
do not add analytic hypotheses or identify the qualified hard OA continuation
with the article's soft-rMIP/DICOPT algorithm. Existing Model equalities for
original/relaxation/box are reused unchanged. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

theorem asFPDelta_model (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).model = d.model := rfl

theorem asFPDelta_objective (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).f = d.f := rfl

theorem asFPDelta_Df (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).Df = d.Df := rfl

/-- The same actual derivative family, with the accepted FP argument order. -/
theorem asFPDelta_Dg (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).Dg = fun j p => d.Dg p j := rfl

/-- The exact nonlinear predicate is inherited; no row is deleted or hardened. -/
theorem asFPDelta_nonlinear (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).nonlinear = {j | ¬ AffineRow (d.model.g j)} := rfl

/-- This is the explicit hard base, not an assumed equality to arbitrary
`d.domain`. The latter remains a separate availability qualification. -/
theorem asFPDelta_base (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).base = {p | p ∈ d.model.linearRegion ∧
      ∀ j, d.model.lo j ≤ p.2 j ∧ p.2 j ≤ d.model.hi j} := rfl

/-- All promised shared-data identities, including the three already compiled
Model lemmas. This is bookkeeping, not a new scientific endpoint. -/
theorem asFPDelta_identities (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).model = d.model ∧
    (asFPDelta d delta).f = d.f ∧
    (asFPDelta d delta).Df = d.Df ∧
    (asFPDelta d delta).Dg = (fun j p => d.Dg p j) ∧
    (asFPDelta d delta).nonlinear = d.nonlinear ∧
    (asFPDelta d delta).base = {p | p ∈ d.model.linearRegion ∧
      ∀ j, d.model.lo j ≤ p.2 j ∧ p.2 j ≤ d.model.hi j} ∧
    (asFPDelta d delta).relaxation = d.relaxation ∧
    (asFPDelta d delta).original = d.original ∧
    (asFPDelta d delta).box = d.box :=
  ⟨asFPDelta_model d delta,asFPDelta_objective d delta,asFPDelta_Df d delta,
    asFPDelta_Dg d delta,asFPDelta_nonlinear d delta,asFPDelta_base d delta,
    asFPDelta_relaxation d delta,asFPDelta_original d delta,asFPDelta_box d delta⟩

end Chapter03.PumpOA

#check Chapter03.PumpOA.asFPDelta_model
#print axioms Chapter03.PumpOA.asFPDelta_model
#check Chapter03.PumpOA.asFPDelta_objective
#print axioms Chapter03.PumpOA.asFPDelta_objective
#check Chapter03.PumpOA.asFPDelta_Df
#print axioms Chapter03.PumpOA.asFPDelta_Df
#check Chapter03.PumpOA.asFPDelta_Dg
#print axioms Chapter03.PumpOA.asFPDelta_Dg
#check Chapter03.PumpOA.asFPDelta_nonlinear
#print axioms Chapter03.PumpOA.asFPDelta_nonlinear
#check Chapter03.PumpOA.asFPDelta_base
#print axioms Chapter03.PumpOA.asFPDelta_base
#check Chapter03.PumpOA.asFPDelta_identities
#print axioms Chapter03.PumpOA.asFPDelta_identities
#check Chapter03.PumpOA.asFPDelta_relaxation
#print axioms Chapter03.PumpOA.asFPDelta_relaxation
#check Chapter03.PumpOA.asFPDelta_original
#print axioms Chapter03.PumpOA.asFPDelta_original
#check Chapter03.PumpOA.asFPDelta_box
#print axioms Chapter03.PumpOA.asFPDelta_box
