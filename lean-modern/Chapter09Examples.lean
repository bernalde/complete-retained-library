module

public import Chapter09

@[expose] public section

noncomputable section
namespace Chapter09Examples
open Chapter09

def edge : Finset (Fin 2 × Fin 2) := {(0, 1)}
def both : Finset (Fin 2) := {0, 1}

lemma subsets_two (S : Finset (Fin 2)) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = both := by
  by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
  · right; right; right; ext x; fin_cases x <;> simp [both, h0, h1]
  · right; left; ext x; fin_cases x <;> simp [h0, h1]
  · right; right; left; ext x; fin_cases x <;> simp [h0, h1]
  · left; ext x; fin_cases x <;> simp [h0, h1]

private noncomputable def __migrationExample_Chapter09Examples_L18_N001 : ¬ feasible edge both := by
  simp [feasible, edge, both]

private noncomputable def __migrationExample_Chapter09Examples_L21_N002 : feasible edge ({0} : Finset (Fin 2)) := by
  simp [feasible, edge]

private noncomputable def __migrationExample_Chapter09Examples_L24_N003 : score edge (fun _ => 1) both = 1 := by
  norm_num [score, conflicts, edge, both, Finset.filter_singleton, Finset.filter_insert, Finset.filter_empty]

private noncomputable def __migrationExample_Chapter09Examples_L27_N004 : isScoreMax edge (fun _ => 1) both := by
  intro T
  rcases subsets_two T with rfl | rfl | rfl | rfl <;>
    norm_num [score, conflicts, edge, both, Finset.filter_singleton, Finset.filter_insert, Finset.filter_empty]

private noncomputable def __migrationExample_Chapter09Examples_L32_N005 : repair edge both = ({1} : Finset (Fin 2)) := by
  norm_num [repair, cover, conflicts, edge, both, Finset.filter_singleton, Finset.filter_insert, Finset.filter_empty]
  ext x
  fin_cases x <;> norm_num

private noncomputable def __migrationExample_Chapter09Examples_L37_N006 : isScoreMax edge (fun _ => 2) ({0} : Finset (Fin 2)) := by
  intro T
  rcases subsets_two T with rfl | rfl | rfl | rfl <;>
    norm_num [score, conflicts, edge, both, Finset.filter_singleton, Finset.filter_insert, Finset.filter_empty]

private noncomputable def __migrationExample_Chapter09Examples_L42_N007 : ∀ e ∈ edge, (1 : ℝ) < (fun _ => 2) e := by simp

private noncomputable def __migrationExample_Chapter09Examples_L44_N008 : feasible (∅ : Finset (Fin 2 × Fin 2)) both := by simp [feasible]

private noncomputable def __migrationExample_Chapter09Examples_L46_N009 : orderedColorPenalty 1 (fun (_ : Fin 3) (_ : Fin 1) => (1 : ℝ)) = 0 :=
  one_color_penalty_zero _

end Chapter09Examples
