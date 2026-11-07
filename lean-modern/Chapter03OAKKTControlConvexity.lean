module

public import Chapter03OAKKTControlActive

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples
namespace Chapter03.OAKKT.Controls

theorem square_convex : ConvexOn ℝ Set.univ (fun p : P => (p.1 0)^2) := by
  simpa [Function.comp_def] using
    (Chapter02DICOPTExamples.convex_square_on (S:=Set.univ) convex_univ).comp_linearMap
      (LinearMap.fst ℝ V V)

theorem positiveF_convex : ConvexOn ℝ Set.univ positiveF :=
  square_convex.add (cy.toLinearMap.convexOn convex_univ)

theorem positiveG_convex : ConvexOn ℝ Set.univ positiveG :=
  square_convex.sub (cy.toLinearMap.concaveOn convex_univ)

theorem affine_convex (u v c : ℝ) :
    ConvexOn ℝ Set.univ (fun p : P => u*p.1 0+v*p.2 0+c) := by
  simpa only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,cx_apply,cy_apply] using
    ((((u • cx+v • cy).toLinearMap).convexOn convex_univ).add_const c).congr
      (g := fun p : P => (u • cx+v • cy) p+c) (fun _ _ => rfl)

theorem thesis_convex (j : Fin 5) : ConvexOn ℝ Set.univ (thesisModel.g j) := by
  fin_cases j
  · exact positiveG_convex
  · simpa [thesisModel,sub_eq_add_neg,add_comm] using affine_convex (-1) 0 (1/2)
  · simpa [thesisModel,sub_eq_add_neg] using affine_convex 1 0 (-1)
  · simpa [thesisModel,sub_eq_add_neg] using affine_convex 0 (-1) 0
  · simpa [thesisModel,sub_eq_add_neg] using affine_convex 0 1 (-1)

theorem activeF_convex : ConvexOn ℝ Set.univ activeF := by
  change ConvexOn ℝ Set.univ (fun p : P => -p.1 0+p.2 0)
  simpa using affine_convex (-1) 1 0

theorem active_convex (j : Fin 3) : ConvexOn ℝ Set.univ (activeModel.g j) := by
  fin_cases j
  · exact positiveG_convex
  · simpa [activeModel,sub_eq_add_neg] using affine_convex 0 (-1) 0
  · simpa [activeModel,sub_eq_add_neg] using affine_convex 0 1 (-1)

end Chapter03.OAKKT.Controls
