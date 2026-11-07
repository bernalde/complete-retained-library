module

public import Chapter02LiftingValueExamples
public import Mathlib.Tactic

@[expose] public section

/-! Full-model equality controls: stronger-or-equal need not be strict even for
nonlinear components or multiple anchors. Every derivative is the actual map;
free heights retain the same original objective and box. -/
noncomputable section
open Chapter02 Chapter02LiftingValueExamples
namespace Chapter02LiftingEqualityExamples

def singleDirect : Set (RealVector 2) :=
  liftingDirectOA box g h (fun _ : Fin 1 => pt 1 1)
    (fun _ => dg (pt 1 1)) (fun _ => dh) 1
def singleShared : Set (RealVector 2 × RealVector 2) :=
  liftingSharedOA box Set.univ g h (fun _ : Fin 1 => pt 1 1)
    (fun _ => dg (pt 1 1)) (fun _ => dh) 1

theorem single_direct_rows (x : RealVector 2) :
    x ∈ singleDirect ↔ x ∈ box ∧ 2*(x 0+x 1)-2 ≤ 1 := by
  simp only [singleDirect,liftingDirectOA,Set.mem_setOf_eq,Fin.forall_fin_one]
  dsimp [liftingDirectRow,g,h,dg,dh,pt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply, Pi.sub_apply, smul_eq_mul, g, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨hx,hrow⟩ <;> refine ⟨hx,?_⟩ <;> linarith

theorem single_shared_rows (x y : RealVector 2) :
    (x,y) ∈ singleShared ↔ x ∈ box ∧ (∀ j, 2*x j-1 ≤ y j) ∧ y 0+y 1 ≤ 1 := by
  simp only [singleShared,liftingSharedOA,Set.mem_setOf_eq,Set.mem_univ,true_and,
    Pi.le_def,Fin.forall_fin_one,Fin.forall_fin_two]
  dsimp [liftingComponentRow,liftingOuterRow,g,h,dg,dh,pt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply, Pi.sub_apply, smul_eq_mul, g, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨hx,⟨ha,hb⟩,hc⟩ <;> refine ⟨hx,⟨?_,?_⟩,?_⟩ <;> linarith

theorem single_projection (x : RealVector 2) :
    (∃ y, (x,y) ∈ singleShared) ↔ x ∈ singleDirect := by
  rw [single_direct_rows]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hx,hr,hb⟩ := (single_shared_rows x y).mp hy
    exact ⟨hx,by linarith [hr 0,hr 1]⟩
  · rintro ⟨hx,hb⟩
    refine ⟨fun j => 2*x j-1,(single_shared_rows x _).mpr ⟨hx,fun _ => le_rfl,?_⟩⟩
    linarith

theorem single_actual_minima :
    IsMinimizer singleDirect objective (pt 1 (-1)) ∧
    IsMinimizer singleShared (fun z => objective z.1) (pt 1 (-1),pt 1 (-3)) ∧
    objective (pt 1 (-1)) = -2 ∧ pt 0 0 ∈ original 1 := by
  have hb : ∀ x ∈ box, objective (pt 1 (-1)) ≤ objective x := by
    intro x hx; dsimp [objective,pt]; linarith [(hx 0).2,(hx 1).1]
  refine ⟨⟨?_,fun x hx => hb x ((single_direct_rows x).mp hx).1⟩,
    ⟨?_,fun z hz => hb z.1 ((single_shared_rows z.1 z.2).mp hz).1⟩,?_,?_⟩
  · rw [single_direct_rows]; norm_num [box,pt,Fin.forall_fin_two]
  · rw [single_shared_rows]; norm_num [box,pt,Fin.forall_fin_two]
  · norm_num [objective,pt]
  · rw [original_rows]; norm_num [box,pt,Fin.forall_fin_two]

def affineG (x : RealVector 2) : RealVector 2 := x
def affineD : RealVector 2 →L[ℝ] RealVector 2 := ContinuousLinearMap.id ℝ _
def affineDirect : Set (RealVector 2) :=
  liftingDirectOA box affineG h anchor (fun _ => affineD) (fun _ => dh) 1
def affineShared : Set (RealVector 2 × RealVector 2) :=
  liftingSharedOA box Set.univ affineG h anchor (fun _ => affineD) (fun _ => dh) 1

theorem affine_derivative_and_supports (a x : RealVector 2) :
    HasFDerivAt affineG affineD a ∧
    liftingComponentRow affineG a affineD x = x ∧
    liftingDirectRow affineG h a affineD dh x = h x := by
  refine ⟨affineD.hasFDerivAt,?_,?_⟩
  · simp [liftingComponentRow,affineG,affineD]
  · simp [liftingDirectRow,affineG,affineD,h,dh]; ring

theorem affine_original_direct (x : RealVector 2) :
    x ∈ affineDirect ↔ x ∈ liftingOriginal box affineG h 1 := by
  change (x ∈ box ∧ ∀ i, liftingDirectRow affineG h (anchor i) affineD dh x ≤ 1) ↔ _
  simp_rw [(affine_derivative_and_supports _ x).2.2]
  simp [liftingOriginal,affineG]

theorem affine_shared_exact (z : RealVector 2 × RealVector 2) :
    z ∈ affineShared ↔ z ∈ liftingSet box Set.univ affineG h 1 := by
  have hr : ∀ i, liftingOuterRow affineG h (anchor i) dh z.2 = h z.2 := by
    intro i; simp [liftingOuterRow,affineG,h,dh]; ring
  change (z.1 ∈ box ∧ z.2 ∈ Set.univ ∧ ∀ i,
    liftingComponentRow affineG (anchor i) affineD z.1 ≤ z.2 ∧
    liftingOuterRow affineG h (anchor i) dh z.2 ≤ 1) ↔ _
  simp_rw [(affine_derivative_and_supports _ z.1).2.1,hr]
  simp [liftingSet,affineG]

theorem affine_two_anchor_projection (x : RealVector 2) :
    (∃ y, (x,y) ∈ affineShared) ↔ x ∈ affineDirect := by
  simp_rw [affine_shared_exact]
  rw [lifting_exists_iff box Set.univ affineG h 1
    (fun _ _ => Set.mem_univ _) (outer_monotone.monotoneOn Set.univ),affine_original_direct]

theorem affine_nontrivial_minima :
    IsMinimizer affineDirect objective (pt 1 (-1)) ∧
    IsMinimizer affineShared (fun z => objective z.1) (pt 1 (-1),pt 1 (-1)) ∧
    anchor 0 ≠ anchor 1 := by
  have hb : ∀ x ∈ box, objective (pt 1 (-1)) ≤ objective x := by
    intro x hx; dsimp [objective,pt]; linarith [(hx 0).2,(hx 1).1]
  refine ⟨⟨?_,fun x hx => hb x ((affine_original_direct x).mp hx).1⟩,
    ⟨?_,fun z hz => hb z.1 ((affine_shared_exact z).mp hz).1⟩,?_⟩
  · rw [affine_original_direct]; norm_num [liftingOriginal,box,affineG,h,pt,Fin.forall_fin_two]
  · rw [affine_shared_exact]
    norm_num [liftingSet,box,affineG,h,pt,Fin.forall_fin_two]
  · intro he; have hc := congrFun he 0; norm_num [anchor,pt] at hc

theorem repeated_anchor_models :
    liftingDirectOA box g h (fun _ : Fin 2 => pt 1 1)
      (fun _ => dg (pt 1 1)) (fun _ => dh) 1 = singleDirect ∧
    liftingSharedOA box Set.univ g h (fun _ : Fin 2 => pt 1 1)
      (fun _ => dg (pt 1 1)) (fun _ => dh) 1 = singleShared := by
  constructor <;> ext z <;> simp [singleDirect,singleShared,liftingDirectOA,liftingSharedOA]

end Chapter02LiftingEqualityExamples

#print axioms Chapter02LiftingEqualityExamples.single_direct_rows
#print axioms Chapter02LiftingEqualityExamples.single_shared_rows
#print axioms Chapter02LiftingEqualityExamples.single_projection
#print axioms Chapter02LiftingEqualityExamples.single_actual_minima
#print axioms Chapter02LiftingEqualityExamples.affine_derivative_and_supports
#print axioms Chapter02LiftingEqualityExamples.affine_original_direct
#print axioms Chapter02LiftingEqualityExamples.affine_shared_exact
#print axioms Chapter02LiftingEqualityExamples.affine_two_anchor_projection
#print axioms Chapter02LiftingEqualityExamples.affine_nontrivial_minima
#print axioms Chapter02LiftingEqualityExamples.repeated_anchor_models
