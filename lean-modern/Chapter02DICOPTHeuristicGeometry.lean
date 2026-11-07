module

public import Chapter02DICOPTHeuristic
public import Chapter02DICOPTControlGeometry

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
open scoped BigOperators
namespace Chapter02DICOPTExamples

/-- Literal active affine/box rows for the fixed binary fiber. Nonlinear row families
    are empty in this convex control. -/
def heuristicLinearized (a : Anchor heuristicData) : Set V := {v |
  (∀ i, heuristicData.affineRow i a.x a.y=0 → dot (heuristicData.D i) v≤0) ∧
  (∀ i, heuristicData.xL i=a.x i → -v i≤0) ∧
  ∀ i, a.x i=heuristicData.xU i → v i≤0}

theorem heuristic_affine_derivative (i : Fin 4) (y : RealVector 3) (x : V) :
    HasFDerivAt (fun z => heuristicData.affineRow i z y)
      ((heuristicData.D i 0) • coord) x := by
  convert ((derivative_coord x).const_mul (heuristicData.D i 0)).add_const
    (dot (heuristicData.C i) y-heuristicData.rhs i) using 1
  ext z
  simp [Data.affineRow,dot,Fin.sum_univ_one]
  ring

theorem heuristic_linearized_zero (a : Anchor heuristicData) :
    heuristicLinearized a={0} := by
  ext v
  constructor
  · intro hv
    have he := ((heuristic_hard _ _).mp a.kkt.feasible.1).2.2
    have h2 : heuristicData.affineRow 2 a.x a.y=0 := by
      norm_num [Data.affineRow,heuristicData,Matrix.cons_val_two]
      linarith
    have h3 : heuristicData.affineRow 3 a.x a.y=0 := by
      norm_num [Data.affineRow,heuristicData,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_three]
      linarith
    have hle := hv.1 2 h2
    have hge := hv.1 3 h3
    norm_num [heuristicData,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_three] at hle hge
    exact scalar_ext (by change v 0=0; linarith)
  · rintro rfl
    simp [heuristicLinearized,dot]

theorem heuristic_actual_abadie (a : Anchor heuristicData) :
    posTangentConeAt (heuristicData.fiber a.y) a.x = heuristicLinearized a ∧
    heuristicLinearized a={0} := by
  rw [heuristic_fiber_singleton,heuristic_linearized_zero]
  exact ⟨DICOPTControlGeometry.singleton_posTangentCone a.x,rfl⟩

end Chapter02DICOPTExamples
