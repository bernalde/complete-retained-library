module

public import AppendixA

@[expose] public section

noncomputable section
namespace AppendixAExamples
open AppendixA

def pathEdges : Finset (Fin 5 × Fin 5) := {(0,1),(1,2),(2,3),(3,4)}
def badFiber : Finset (Fin 5) := {0,1,3,4}

private noncomputable def __migrationExample_AppendixAExamples_L10_N001 : ∀ a ∈ badFiber, ∃ b ∈ badFiber, adjacent pathEdges a b := by
  unfold badFiber adjacent pathEdges
  decide

private theorem stay_left {b : Fin 5}
    (h : Relation.ReflTransGen (fiberStep pathEdges badFiber) 0 b) : b = 0 ∨ b = 1 := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c hab hbc ih =>
    rcases ih with rfl | rfl <;> fin_cases c <;>
      simp_all [fiberStep, adjacent, pathEdges, badFiber]

private theorem bad_disconnected : ¬ connected pathEdges badFiber := by
  intro h
  have ht := stay_left (h 0 (by decide) 3 (by decide))
  rcases ht with ht | ht
  · exact (by decide : (3 : Fin 5) ≠ 0) ht
  · exact (by decide : (3 : Fin 5) ≠ 1) ht

private noncomputable def __migrationExample_AppendixAExamples_L29_N002 : ¬ connected pathEdges badFiber := bad_disconnected

private theorem zero_reaches (b : Fin 5) :
    Relation.ReflTransGen (fiberStep pathEdges Finset.univ) 0 b := by
  have h01 : fiberStep pathEdges Finset.univ 0 1 := by simp [fiberStep,adjacent,pathEdges]
  have h12 : fiberStep pathEdges Finset.univ 1 2 := by simp [fiberStep,adjacent,pathEdges]
  have h23 : fiberStep pathEdges Finset.univ 2 3 := by simp [fiberStep,adjacent,pathEdges]
  have h34 : fiberStep pathEdges Finset.univ 3 4 := by simp [fiberStep,adjacent,pathEdges]
  have w1 := Relation.ReflTransGen.single h01
  have w2 := w1.tail h12
  have w3 := w2.tail h23
  have w4 := w3.tail h34
  fin_cases b
  · exact Relation.ReflTransGen.refl
  · exact w1
  · exact w2
  · exact w3
  · exact w4

private theorem full_connected : connected pathEdges Finset.univ := by
  have hs : Symmetric (fiberStep pathEdges Finset.univ) := by
    intro a b h
    exact ⟨h.2.1,h.1,adjacent_symmetric pathEdges h.2.2⟩
  letI : Std.Symm (fiberStep pathEdges Finset.univ) := ⟨hs⟩
  intro a _ b _
  exact (Relation.ReflTransGen.stdSymm.symm _ _ (zero_reaches a)).trans (zero_reaches b)

private noncomputable def __migrationExample_AppendixAExamples_L55_N003 : connected pathEdges Finset.univ := full_connected

private noncomputable def __migrationExample_AppendixAExamples_L57_N004 : (1 : ℝ) ≤ (badFiber.card : ℝ) - ((badFiber ∩ Finset.univ).card : ℝ) +
    ((boundary pathEdges badFiber ∩ Finset.univ).card : ℝ) :=
  real_boundary_cut_valid pathEdges badFiber Finset.univ bad_disconnected full_connected

private noncomputable def __migrationExample_AppendixAExamples_L61_N005 : connected (∅ : Finset (Fin 0 × Fin 0)) ∅ := by simp [connected]

private noncomputable def __migrationExample_AppendixAExamples_L63_N006 : ((∀ i ∈ (Finset.univ : Finset (Fin 2)), natbit true ≤ natbit true) ∧
    ((Finset.univ : Finset (Fin 2)).filter (fun _ => true = true)).card + 1 ≤
    (Finset.univ : Finset (Fin 2)).card + natbit true) := by decide

private noncomputable def __migrationExample_AppendixAExamples_L67_N007 : ¬ ((∀ i ∈ (Finset.univ : Finset (Fin 2)), natbit false ≤ natbit true) ∧
    ((Finset.univ : Finset (Fin 2)).filter (fun _ => true = true)).card + 1 ≤
    (Finset.univ : Finset (Fin 2)).card + natbit false) := by decide

end AppendixAExamples
