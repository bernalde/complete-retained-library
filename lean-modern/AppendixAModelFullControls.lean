module

public import AppendixAModelInterfaces
public import AppendixAModelControls

@[expose] public section

noncomputable section
namespace AppendixATheory

theorem reversed_source_graphs_loopfree : LoopFree reversedPhysical ∧ LoopFree twoLogical := by
  unfold LoopFree AppendixA.adjacent reversedPhysical twoLogical
  decide

theorem reversed_full_delta_control : ∃ D, FullDeltaRows reversedPhysical twoLogical reversedAlpha D :=
  (full_delta_projection _ _ 1 _ reversed_rows reversed_source_graphs_loopfree.2).mpr
    reversed_edge_coverage

theorem singleton_and_disconnected_size_flags :
    (∀ j, sizeFlag reversedAlpha j = false) ∧ sizeFlag allOneFiber 0 = true := by
  unfold sizeFlag fiber reversedAlpha allOneFiber
  decide

end AppendixATheory
