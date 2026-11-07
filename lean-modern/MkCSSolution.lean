module

public import MkCSStatement

/-! Bundle wrapper only: every component is an existing accepted theorem.
The completed proof does not import the Challenge placeholder. -/
public section
namespace PalomarMkCS

theorem solution : Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Chapter09.Source.qNonlinear_binary_maximum
  · exact Chapter09.Source.orderedProducts_eq_twice
  · exact Chapter09.Source.qNonlinear_eq_alpha
  · exact Chapter09.Source.nonlinear_optimizer_repair
  · exact Chapter09.Source.nonlinear_optimizer_strict
  · exact Chapter09.Source.qNonlinear_one_color
  · exact Chapter09.Source.nonlinear_one_color_strict
  · exact Chapter09.Source.nonlinear_one_color_repair
  · exact Chapter09.Source.Controls.unit_edge_global_tie
  · exact Chapter09.Source.Controls.half_color_global_tie

end PalomarMkCS
