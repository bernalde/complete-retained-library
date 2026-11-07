module

public import Chapter02DICOPTQuarticAdapter
public import Chapter02DICOPTHeuristicControl

@[expose] public section

noncomputable section
namespace Chapter02DICOPTExamples

/-- Two distinct, fully analytic source controls: a static local-anchor
    componentwise-quasiconvex lower-bound control and an executed convex
    heuristic-stop countertrace. Their scopes are retained in both structures. -/
theorem source_countercontrols :
    Chapter02.DICOPTQuarticAdapter.QuarticSourceControl ∧ HeuristicCountercontrol :=
  ⟨Chapter02.DICOPTQuarticAdapter.quartic_source_control,heuristic_full_countertrace⟩

end Chapter02DICOPTExamples
#print axioms Chapter02DICOPTExamples.source_countercontrols
