module

public import Chapter03FPIntegerControls
public import Chapter03FPUnboundedLinearControl
public import Chapter03FP

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPControls

/-- Connect a proved concrete execution to the final general procedure theorem,
without assuming its return claims as control premises. -/
theorem return_of_execution {n m l r : ℕ} (d : Data n m l r) (ha : Analytic d)
    (cap : Option ℕ) (initial : Initialization d) (choose : Selector d cap)
    (out : Outcome n m) (he : procedure d initial choose = some out) :
    ReturnClaims d cap initial out ∧ CountBounds d cap out := by
  obtain ⟨out',he',hr,hc⟩ := (qualified_source_pump d ha cap).2.2.1 initial choose
  have ho : out'=out := Option.some.inj (he'.symm.trans he)
  subst out'
  exact ⟨hr,hc⟩

theorem c1_delta1_qualified_return :
    ReturnClaims (c1 1) none (.minimum seed (seed_minimum 1)) (.loop out1) ∧
    CountBounds (c1 1) none (.loop out1) :=
  return_of_execution (c1 1) (c1_analytic 1 (by norm_num)) none
    (.minimum seed (seed_minimum 1)) choose1 (.loop out1) procedure_delta1

theorem c1_delta0_qualified_return :
    ReturnClaims (c1 0) none (.minimum seed (seed_minimum 0)) (.loop out0) ∧
    CountBounds (c1 0) none (.loop out0) :=
  return_of_execution (c1 0) (c1_analytic 0 (by norm_num)) none
    (.minimum seed (seed_minimum 0)) choose0 (.loop out0) procedure_delta0

theorem general_qualified_return :
    ReturnClaims generalData none (.minimum seed general_seed) (.loop out0) ∧
    CountBounds generalData none (.loop out0) :=
  return_of_execution generalData general_analytic none
    (.minimum seed general_seed) generalSelector (.loop out0) general_procedure

theorem cap0_qualified_return :
    ReturnClaims unboundedData (some 0) (.minimum seed unbounded_seed) (.loop cap0Output) ∧
    CountBounds unboundedData (some 0) (.loop cap0Output) :=
  return_of_execution unboundedData unbounded_analytic (some 0)
    (.minimum seed unbounded_seed) cap0Selector (.loop cap0Output) cap0_procedure

theorem unboundedLinear_qualified_return :
    ReturnClaims unboundedLinearData (some 0) (.minimum seed unboundedLinear_seed) (.loop cap0Output) ∧
    CountBounds unboundedLinearData (some 0) (.loop cap0Output) :=
  return_of_execution unboundedLinearData unboundedLinear_analytic (some 0)
    (.minimum seed unboundedLinear_seed) unboundedLinearSelector (.loop cap0Output)
    unboundedLinear_procedure

theorem empty_qualified_return :
    ReturnClaims emptyData none (.empty empty_relaxation) .initialInfeasible ∧
    CountBounds emptyData none .initialInfeasible :=
  return_of_execution emptyData empty_analytic none (.empty empty_relaxation) emptySelector
    .initialInfeasible empty_initialization

theorem zero_qualified_return :
    ReturnClaims zeroData none (.minimum (0,0) zero_minimum) (.initialOptimal (0,0)) ∧
    CountBounds zeroData none (.initialOptimal (0,0)) :=
  return_of_execution zeroData zero_analytic none (.minimum (0,0) zero_minimum) zeroSelector
    (.initialOptimal (0,0)) zero_initialization

theorem integral_qualified_return {cap : Option ℕ} (choose : Selector unboundedData cap) :
    ReturnClaims unboundedData cap (.minimum (pt 0 0) unbounded_integral_minimum)
      (.initialOptimal (pt 0 0)) ∧ CountBounds unboundedData cap (.initialOptimal (pt 0 0)) :=
  return_of_execution unboundedData unbounded_analytic cap
    (.minimum (pt 0 0) unbounded_integral_minimum) choose
    (.initialOptimal (pt 0 0)) (integral_initialization choose)

/-- Counters refer to the actual final Outcome type: one relaxed initializer,
then body/projection/master/polish counts in that order. -/
theorem actual_counter_values :
    (Outcome.loop out1).counts = ⟨1,1,2,2,1⟩ ∧
    (Outcome.loop out0).counts = ⟨1,2,2,3,2⟩ ∧
    (Outcome.loop cap0Output).counts = ⟨1,0,0,1,0⟩ ∧
    (Outcome.initialInfeasible : Outcome 1 1).counts = ⟨1,0,0,0,0⟩ ∧
    (Outcome.initialOptimal (pt 0 0)).counts = ⟨1,0,0,0,0⟩ ∧
    (Outcome.initialOptimal (0,0) : Outcome 0 0).counts = ⟨1,0,0,0,0⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Chapter03.FPControls
