module

public import Chapter03FPBoundaryControls

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPControls

/-- Separate from the height-unbounded f=-x control: the source objective is
the nonaffine square (y-1/2)^2 and the continuous linear master is unbounded. -/
def unboundedLinearData : Data 1 1 1 2 := data false 0 1 1 0 0

theorem unboundedLinear_analytic : Analytic unboundedLinearData :=
  analytic false 0 1 1 0 (by norm_num) (by norm_num)

theorem unboundedLinear_seed :
    IsMinimizer unboundedLinearData.relaxation unboundedLinearData.f seed :=
  relaxation_seed false 0 1 1 0 (by norm_num) (by norm_num)

theorem unboundedLinear_master_minimum (x : ℝ) :
    IsMinimizer (master unboundedLinearData s0) (masterCost s0) (pt x 0,0) := by
  refine ⟨(master_s0 false 0 1 1 0 _).mpr ?_,?_⟩
  · exact ⟨by simp,⟨0,by norm_num,by norm_num,by norm_num [pt]⟩,by simp⟩
  · intro z hz
    obtain ⟨_,⟨k,h0,h1,he⟩,_⟩ := (master_s0 false 0 1 1 0 z).mp hz
    rcases binary_value h0 h1 with rfl|rfl <;>
      norm_num [masterCost,l1_formula,State.reference,s0,initialState,seed,pt,he]

theorem unboundedLinear_no_coordinate_bound :
    ¬∃ U : ℝ, ∀ z∈master unboundedLinearData s0, z.1.1 0 ≤ U := by
  rintro ⟨U,hU⟩
  have h := hU _ (unboundedLinear_master_minimum (U+1)).1
  change U+1 ≤ U at h
  linarith

def unboundedLinearSelector : Selector unboundedLinearData (some 0) :=
  patch s0 (.stop .handoff (.handoff (unboundedLinear_master_minimum 0) rfl (by simp)))
    (Classical.choice (selector_nonempty unboundedLinearData unboundedLinear_analytic (some 0)))

theorem unboundedLinear_run (fuel : ℕ) :
    run unboundedLinearData unboundedLinearSelector (fuel+1) s0 = some cap0Output := by
  rw [run]
  simp [unboundedLinearSelector,terminalOutput,terminalProjectionCount,cap0Output]

theorem unboundedLinear_procedure :
    procedure unboundedLinearData (.minimum seed unboundedLinear_seed) unboundedLinearSelector =
      some (.loop cap0Output) := by
  rw [procedure_fractional_eq unboundedLinearData seed unboundedLinear_seed unboundedLinearSelector
    (fractional_seed false 0 1 1 0 0)]
  change (run unboundedLinearData unboundedLinearSelector (_+1) s0).map Outcome.loop = _
  rw [unboundedLinear_run]; rfl

end Chapter03.FPControls
