module

public import Chapter03PumpOAScalarSource

@[expose] public section

/-! Nonempty fractional relaxation y=1/2 and no feasible binary fiber.
The pump actually inspects an empty initial master; no incumbent is invented.
All-minimum fixed LICQ holds because each integer fiber is proved empty. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA.Infeasible
open Symmetric (P pt iv yc seed)

def model : ModelData 0 1 2 0 where
  g := ![fun p => p.2 0-1/2,fun p => 1/2-p.2 0]
  A j := Fin.elim0 j
  B j := Fin.elim0 j
  rhs j := Fin.elim0 j
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

def spec : OAExec.Data 0 1 2 0 where
  model := model
  f := Symmetric.spec.f
  Df := Symmetric.spec.Df
  Dg _ := ![yc,-yc]
  domain := Symmetric.spec.domain

def pump : FP.Data 0 1 2 0 := asFPDelta spec 0
def s0 : FP.State 0 1 := FP.initialState seed

theorem relaxation (p : P) : p∈spec.relaxation ↔ p.2 0=1/2 := by
  constructor
  · intro hp
    have hg := (OAExec.relaxation_mem_iff spec p).mp hp
    have h0 := hg.1 0
    have h1 := hg.1 1
    change p.2 0-1/2≤0 at h0
    change 1/2-p.2 0≤0 at h1
    linarith
  · intro h
    apply (OAExec.relaxation_mem_iff spec p).mpr
    refine ⟨?_,fun j => Fin.elim0 j,?_⟩
    · intro j; fin_cases j <;> norm_num [spec,model,h]
    · intro j; fin_cases j; norm_num [spec,model,h]

theorem domain_base : spec.domain=(OAExec.asFP spec).base := by
  exact Symmetric.domain_base

theorem row_derivative (p : P) (j : Fin 2) :
    HasFDerivAt (model.g j) (spec.Dg p j) p := by
  fin_cases j
  · exact yc.hasFDerivAt.sub_const (1/2)
  · change HasFDerivAt (fun q : P => 1/2-q.2 0) (-yc) p
    simpa only [zero_sub,Symmetric.yc_apply] using (hasFDerivAt_const (1/2 : ℝ) p).fun_sub yc.hasFDerivAt

theorem analytic : OAExec.Analytic spec where
  convex_f := Symmetric.analytic.convex_f
  convex_g j := by
    refine ⟨Symmetric.analytic.convex_f.1,?_⟩
    intro p _ q _ a b _ _ hab
    fin_cases j
    · change a*p.2 0+b*q.2 0-1/2≤a*(p.2 0-1/2)+b*(q.2 0-1/2)
      nlinarith
    · change 1/2-(a*p.2 0+b*q.2 0)≤a*(1/2-p.2 0)+b*(1/2-q.2 0)
      nlinarith
  original_domain := by
    intro p hp
    have h := (relaxation p).mp (OAExec.original_subset_relaxation spec hp)
    change 0≤p.2 0 ∧ p.2 0≤1
    rw [h]; norm_num
  derivative_f := Symmetric.analytic.derivative_f
  derivative_g p _ j := row_derivative p j

theorem bounded_relaxation : Bornology.IsBounded spec.relaxation := by
  apply Symmetric.bounded_relaxation.subset
  intro p hp
  apply (Symmetric.relaxation p).mpr
  rw [(relaxation p).mp hp]
  norm_num

theorem fixed_empty (y : IntVector 1) (hy : y∈IntegerBox model.lo model.hi) :
    ¬ (fiber model (intCast y)).Nonempty := by
  rintro ⟨x,hx⟩
  rcases Symmetric.binary hy with rfl|rfl
  · have h := hx.2 1
    norm_num [model,soft,intCast,iv] at h
  · have h := hx.2 0
    norm_num [model,soft,intCast,iv] at h

def encoding : HardBoundEncoding Symmetric.bounds spec.model where
  valid j := Fin.elim0 j
  side j := Fin.elim0 j
  injective := by intro i; exact Fin.elim0 i
  lower_cover j := Fin.elim0 j
  upper_cover j := Fin.elim0 j
  row_spec j := Fin.elim0 j

theorem source_package : OAExec.AvailabilityAssumptions spec :=
  OAExec.article_availability_assumptions Symmetric.bounds spec encoding analytic
    (domain_base.trans (OAExec.articleDomain_eq_base Symmetric.bounds spec encoding).symm)
    bounded_relaxation (fun y hy x hm => False.elim (fixed_empty y hy ⟨x,hm.1⟩))

theorem pump_analytic : FP.Analytic pump := asFPDelta_analytic source_package (le_refl 0)

theorem seed_minimum : IsMinimizer spec.relaxation spec.f seed := by
  refine ⟨(relaxation seed).mpr rfl,?_⟩
  intro p hp
  have h := (relaxation p).mp hp
  change ((1/2:ℝ)-1/2)^2≤(p.2 0-1/2)^2
  rw [h]

theorem seed_valid : OAExec.SeedValid spec seed :=
  ⟨seed_minimum,Symmetric.seed_valid.2.1,Symmetric.seed_not_integral⟩

theorem original_empty : ¬ spec.original.Nonempty := by
  rintro ⟨p,hp⟩
  obtain ⟨_,hg,hl,y,hy,he⟩ := (source_feasible_iff model Set.univ p).mp hp
  apply fixed_empty y hy
  refine ⟨p.1,?_⟩
  change p.2=intCast y at he
  simpa only [← he] using (show p.1∈fiber model p.2 from ⟨hl,hg⟩)

theorem seed_tangent (p : P) (j : Fin 2) :
    spec.model.g j seed+spec.Dg seed j (p-seed)=spec.model.g j p := by
  fin_cases j <;> norm_num [spec,model,seed,pt,Symmetric.yc_apply]

theorem master_empty : ¬ (FP.master pump s0).Nonempty := by
  rintro ⟨z,hz⟩
  have h := (FPAdapters.master_source_rows_iff pump s0 z).mp hz
  obtain ⟨y,hy,he⟩ := h.2.1
  let i : Fin (FP.anchors pump s0).length := ⟨0,by simp [FP.anchors,s0,FP.initialState]⟩
  have hg0 := h.2.2.1 i 0 (by trivial)
  have hg1 := h.2.2.1 i 1 (by trivial)
  change spec.model.g 0 seed+spec.Dg seed 0 (z.1-seed)≤0 at hg0
  change spec.model.g 1 seed+spec.Dg seed 1 (z.1-seed)≤0 at hg1
  rw [seed_tangent] at hg0 hg1
  rcases Symmetric.binary hy with rfl|rfl
  · have he0 := congrFun he 0
    norm_num [FP.intCast,iv] at he0
    norm_num [spec,model,he0] at hg1
  · have he1 := congrFun he 0
    norm_num [FP.intCast,iv] at he1
    norm_num [spec,model,he1] at hg0

theorem handoff_empty : FP.handoff pump s0=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  apply master_empty
  exact ⟨z,hz.1,by simp [FP.retainedNormals,s0,FP.initialState],hz.2.2,trivial⟩

def choose : FP.Selector pump none := fun s => by
  classical
  exact if h : s=s0 then h.symm ▸ .stop .emptyMaster (.emptyMaster master_empty)
    else Classical.choice (FP.decision_nonempty pump pump_analytic none s)

def output : FP.LoopOutput 0 1 := ⟨s0,.emptyMaster,0,0,1,0⟩
def initialization : FP.Initialization pump := .minimum seed seed_minimum

theorem actual_procedure : FP.procedure pump initialization choose=some (.loop output) := by
  have hn : seed∉pump.original := fun h => original_empty ⟨seed,h⟩
  have hb : pump.box.card=2 := Symmetric.box_card
  simp [FP.procedure,initialization,hn,hb,FP.run,choose,s0,
    FP.terminalOutput,FP.terminalProjectionCount,output]

end Chapter03.PumpOA.Infeasible

#print axioms Chapter03.PumpOA.Infeasible.source_package
#print axioms Chapter03.PumpOA.Infeasible.actual_procedure
#print axioms Chapter03.PumpOA.Infeasible.original_empty
#print axioms Chapter03.PumpOA.Infeasible.handoff_empty
