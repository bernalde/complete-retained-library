module

public import Chapter02LiftingSource
public import Chapter02LiftingValueExamples
public import Mathlib.Tactic

@[expose] public section

/-! Finite source-model realization of S and the native S-value control.
There are two original continuous coordinates, no integer coordinates, four
literal box rows, and continuous appended heights. The source stores
t_j = y_j - b/2, so component x_j²-b/2 ≤ t_j has the zero aggregate budget.
No additional height bound is imposed, in particular on the OA heights. -/
noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02LiftingValueSource
open Chapter02LiftingValueExamples

def originalPoint (x : RealVector 2) : Point 2 0 := (x, fun i => Fin.elim0 i)

def model (b : ℝ) : ModelData 2 0 1 (2+2) where
  g := fun _ p => (p.1 0)^2 + (p.1 1)^2 - b
  A := Fin.addCases (fun j => Pi.single j (-1)) (fun j => Pi.single j 1)
  B := fun _ i => Fin.elim0 i
  rhs := fun _ => 1
  c1 := ![-1,1]
  c2 := fun i => Fin.elim0 i
  lo := fun i => Fin.elim0 i
  hi := fun i => Fin.elim0 i

def component (b : ℝ) (j : Fin 2) (p : Point 2 0) : ℝ := (p.1 j)^2-b/2
def weight : Fin 1 → RealVector 2 := fun _ _ => 1
def liftedModel (b : ℝ) := (model b).separableLift (component b) weight
def liftedPoint (b : ℝ) (x y : RealVector 2) : Point (2+2) 0 :=
  liftingSourceInsert (originalPoint x) (fun j => y j-b/2)
def rawHeights (b : ℝ) (z : Point (2+2) 0) : RealVector 2 :=
  fun j => liftingSourceHeight z j+b/2

private theorem no_integer_restriction {n : ℕ} (lo hi : RealVector 0) (p : Point n 0) :
    p ∈ IntegerCylinder lo hi := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · funext i; exact Fin.elim0 i

private theorem model_no_integer_iff {n l r : ℕ} (d : ModelData n 0 l r) (p : Point n 0) :
    p ∈ d.feasibleOn Set.univ ↔ (∀ j, d.g j p ≤ 0) ∧ p ∈ d.linearRegion := by
  simp [ModelData.feasibleOn, MixedFeasible, ModelData.nonlinearRegion,
    no_integer_restriction]

theorem original_point_surjective (p : Point 2 0) : originalPoint p.1 = p := by
  apply Prod.ext
  · rfl
  · funext i; exact Fin.elim0 i

theorem source_linear_rows (b : ℝ) (p : Point 2 0) :
    p ∈ (model b).linearRegion ↔ p.1 ∈ box := by
  constructor
  · intro hp j
    have hl := hp (j.castAdd 2)
    have hu := hp (j.natAdd 2)
    simp only [model,Fin.addCases_left,Fin.addCases_right] at hl hu
    simp [LinearForm,Pi.single_apply] at hl hu
    exact ⟨by linarith, hu⟩
  · intro hp row
    refine Fin.addCases (fun j => ?_) (fun j => ?_) row
    · simp only [model,Fin.addCases_left]
      simp [LinearForm,Pi.single_apply]
      linarith [(hp j).1]
    · simp only [model,Fin.addCases_right]
      simpa [LinearForm,Pi.single_apply] using (hp j).2

theorem source_objective (b : ℝ) (p : Point 2 0) :
    (model b).objective p = objective p.1 := by
  simp [model,ModelData.objective,LinearForm,objective,Fin.sum_univ_two]

theorem original_feasible_iff (b : ℝ) (p : Point 2 0) :
    p ∈ (model b).feasibleOn Set.univ ↔ p.1 ∈ original b := by
  rw [model_no_integer_iff,source_linear_rows,original_rows]
  simp only [model,Fin.forall_fin_one,sub_nonpos]
  exact and_comm

theorem component_identity (b : ℝ) (i : Fin 1) (p : Point 2 0) :
    (model b).g i p = ∑ j, weight i j * component b j p := by
  simp [model,component,weight,Fin.sum_univ_two]
  ring

def originalCoordinate (j : Fin 2) : Point 2 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (RealVector 2) (RealVector 0))

theorem source_component_derivative (b : ℝ) (j : Fin 2) (p : Point 2 0) :
    HasFDerivAt (component b j) ((2*p.1 j) • originalCoordinate j) p := by
  have hbase : HasFDerivAt (fun x : Point 2 0 => (x.1 j)^2)
      ((2*p.1 j) • originalCoordinate j) p := by
    simpa [originalCoordinate,Function.comp_def] using
      (hasDerivAt_pow 2 (p.1 j)).comp_hasFDerivAt p (originalCoordinate j).hasFDerivAt
  exact hbase.sub_const (b/2)

theorem source_constraint_derivative (b : ℝ) (i : Fin 1) (p : Point 2 0) :
    HasFDerivAt ((model b).g i)
      ((dh.comp (dg p.1)).comp (ContinuousLinearMap.fst ℝ (RealVector 2) (RealVector 0))) p := by
  simpa [model,h,g,Function.comp_def] using
    ((composite_derivative p.1).comp p
      (ContinuousLinearMap.fst ℝ (RealVector 2) (RealVector 0)).hasFDerivAt).sub_const b

theorem source_lift_projection (b : ℝ) :
    liftingSourceProject '' (liftedModel b).feasibleOn Set.univ =
      (model b).feasibleOn Set.univ := by
  simpa [liftedModel] using lifting_source_mixed_projection (model b) Set.univ
    (component b) weight (by intro i j; norm_num [weight]) (component_identity b)

theorem lifted_point_project (b : ℝ) (x y : RealVector 2) :
    liftingSourceProject (liftedPoint b x y) = originalPoint x := by
  simp [liftedPoint]

theorem lifted_point_heights (b : ℝ) (x y : RealVector 2) :
    rawHeights b (liftedPoint b x y) = y := by
  ext j
  simp [rawHeights,liftedPoint]

theorem lifted_point_surjective (b : ℝ) (z : Point (2+2) 0) :
    liftedPoint b (liftingSourceProject z).1 (rawHeights b z) = z := by
  apply Prod.ext
  · simp [liftedPoint,originalPoint,liftingSourceInsert,liftingSourceProject,
      rawHeights,liftingSourceHeight]
    exact weightedInsert_project z.1
  · funext i; exact Fin.elim0 i

theorem shifted_lifted_feasible_iff (b : ℝ) (z : Point (2+2) 0) :
    z ∈ (liftedModel b).feasibleOn Set.univ ↔
      ((liftingSourceProject z).1, rawHeights b z) ∈ exactLift b := by
  have hr := lifting_source_feasible_rows (model b) Set.univ (component b) weight z
  simp only [Set.preimage_univ] at hr
  rw [show liftedModel b = (model b).separableLift (component b) weight from rfl,hr,
    source_linear_rows,exact_rows]
  simp only [Set.mem_univ,true_and,no_integer_restriction,and_true,
    weight,one_mul,Fin.sum_univ_two,Fin.forall_fin_one,component,rawHeights]
  constructor
  · rintro ⟨hc,hbox,hb⟩
    exact ⟨hbox,fun j => by linarith [hc j],by linarith⟩
  · rintro ⟨hbox,hc,hb⟩
    exact ⟨fun j => by linarith [hc j],hbox,by linarith⟩

theorem lifted_objective (b : ℝ) (z : Point (2+2) 0) :
    (liftedModel b).objective z = objective (liftingSourceProject z).1 := by
  rw [liftedModel,lifting_source_objective,source_objective]

theorem original_minimizer_iff (b : ℝ) (x : RealVector 2) :
    IsMinimizer ((model b).feasibleOn Set.univ) (model b).objective (originalPoint x) ↔
      IsMinimizer (original b) objective x := by
  constructor
  · rintro ⟨hx,hm⟩
    refine ⟨(original_feasible_iff b _).mp hx,?_⟩
    intro y hy
    simpa [source_objective,originalPoint] using hm (originalPoint y)
      ((original_feasible_iff b _).mpr hy)
  · rintro ⟨hx,hm⟩
    refine ⟨(original_feasible_iff b _).mpr hx,?_⟩
    intro p hp
    simpa [source_objective,originalPoint] using hm p.1 ((original_feasible_iff b p).mp hp)

theorem lifted_minimizer_iff (b : ℝ) (x y : RealVector 2) :
    IsMinimizer ((liftedModel b).feasibleOn Set.univ) (liftedModel b).objective (liftedPoint b x y) ↔
      IsMinimizer (exactLift b) (fun p => objective p.1) (x,y) := by
  constructor
  · rintro ⟨hx,hm⟩
    refine ⟨?_,?_⟩
    · simpa [lifted_point_project,lifted_point_heights,originalPoint] using
        (shifted_lifted_feasible_iff b _).mp hx
    · rintro ⟨x',y'⟩ hy
      have hfeas : liftedPoint b x' y' ∈ (liftedModel b).feasibleOn Set.univ := by
        apply (shifted_lifted_feasible_iff b _).mpr
        simpa [lifted_point_project,lifted_point_heights,originalPoint] using hy
      simpa [lifted_objective,lifted_point_project,originalPoint] using hm _ hfeas
  · rintro ⟨hx,hm⟩
    refine ⟨?_,?_⟩
    · apply (shifted_lifted_feasible_iff b _).mpr
      simpa [lifted_point_project,lifted_point_heights,originalPoint] using hx
    · intro z hz
      simpa [lifted_objective,lifted_point_project,originalPoint] using
        hm _ ((shifted_lifted_feasible_iff b z).mp hz)

theorem original_source_minimum :
    IsMinimizer ((model (1/2)).feasibleOn Set.univ) (model (1/2)).objective
      (originalPoint (pt (1/2) (-1/2))) ∧
    (model (1/2)).objective (originalPoint (pt (1/2) (-1/2))) = -1 := by
  exact ⟨(original_minimizer_iff _ _).mpr original_minimum.1,
    by simpa [source_objective,originalPoint] using original_minimum.2⟩

theorem exact_source_minimum :
    IsMinimizer ((liftedModel (1/2)).feasibleOn Set.univ) (liftedModel (1/2)).objective
      (liftedPoint (1/2) (pt (1/2) (-1/2)) (pt (1/4) (1/4))) ∧
    (liftedModel (1/2)).objective
      (liftedPoint (1/2) (pt (1/2) (-1/2)) (pt (1/4) (1/4))) = -1 := by
  exact ⟨(lifted_minimizer_iff _ _ _).mpr exact_minimum.1,
    by simpa [lifted_objective,lifted_point_project,originalPoint] using exact_minimum.2⟩

/-- Literal diagonal tangent LP: four retained box rows and two direct rows. -/
def directModel (b : ℝ) : ModelData 2 0 0 ((2+2)+2) where
  g := fun j => Fin.elim0 j
  A := Fin.addCases (model b).A (fun k _ => if k = 0 then 2 else -2)
  B := fun _ j => Fin.elim0 j
  rhs := Fin.addCases (model b).rhs (fun _ => b+2)
  c1 := (model b).c1
  c2 := (model b).c2
  lo := (model b).lo
  hi := (model b).hi

theorem direct_linear_rows (b : ℝ) (p : Point 2 0) :
    p ∈ (directModel b).linearRegion ↔ p.1 ∈ direct b := by
  rw [direct_rows]
  constructor
  · intro hp
    have hbase : p ∈ (model b).linearRegion := by
      intro j
      simpa only [directModel,model,Fin.addCases_left] using hp (j.castAdd 2)
    have hpos := hp ((0 : Fin 2).natAdd (2+2))
    have hneg := hp ((1 : Fin 2).natAdd (2+2))
    simp only [directModel,Fin.addCases_right] at hpos hneg
    norm_num [LinearForm,Fin.sum_univ_two] at hpos hneg
    exact ⟨(source_linear_rows b p).mp hbase,by linarith,by linarith⟩
  · rintro ⟨hbox,hpos,hneg⟩ row
    refine Fin.addCases (fun j => ?_) (fun k => ?_) row
    · simpa only [directModel,model,Fin.addCases_left] using (source_linear_rows b p).mpr hbox j
    · simp only [directModel,Fin.addCases_right]
      fin_cases k <;> norm_num [LinearForm,Fin.sum_univ_two] <;> linarith

theorem direct_feasible_iff (b : ℝ) (p : Point 2 0) :
    p ∈ (directModel b).feasibleOn Set.univ ↔ p.1 ∈ direct b := by
  rw [model_no_integer_iff]
  constructor
  · exact fun hp => (direct_linear_rows b p).mp hp.2
  · exact fun hp => ⟨fun j => Fin.elim0 j,(direct_linear_rows b p).mpr hp⟩

theorem direct_objective (b : ℝ) (p : Point 2 0) :
    (directModel b).objective p = objective p.1 := source_objective b p

/-- Four box rows, one aggregate budget row, and four component tangent rows.
Stored height variables are continuous and have no additional bounds. -/
def sharedModel (b : ℝ) : ModelData (2+2) 0 0 (((2+2)+1)+(2+2)) where
  g := fun j => Fin.elim0 j
  A := Fin.addCases (liftedModel b).A
    (Fin.addCases
      (fun j => Fin.addCases (Pi.single j 2) (Pi.single j (-1)))
      (fun j => Fin.addCases (Pi.single j (-2)) (Pi.single j (-1))))
  B := fun _ j => Fin.elim0 j
  rhs := Fin.addCases (liftedModel b).rhs (fun _ => 1+b/2)
  c1 := (liftedModel b).c1
  c2 := (liftedModel b).c2
  lo := (liftedModel b).lo
  hi := (liftedModel b).hi

private theorem stored_linear_rows (b : ℝ) (z : Point (2+2) 0) :
    z ∈ (liftedModel b).linearRegion ↔
      (liftingSourceProject z).1 ∈ box ∧
        liftingSourceHeight z 0+liftingSourceHeight z 1 ≤ 0 := by
  rw [liftedModel,lifting_source_affine_rows,source_linear_rows]
  simp [weight,Fin.sum_univ_two,Fin.forall_fin_one]

private theorem component_affine_row (s : ℝ) (j : Fin 2) (z : Point (2+2) 0) :
    LinearForm (Fin.addCases (Pi.single j s) (Pi.single j (-1))) (fun i => Fin.elim0 i) z =
      s*(liftingSourceProject z).1 j-liftingSourceHeight z j := by
  rw [lifting_linearForm_append]
  simp [LinearForm,Pi.single_apply]
  ring

theorem shared_linear_rows (b : ℝ) (z : Point (2+2) 0) :
    z ∈ (sharedModel b).linearRegion ↔
      ((liftingSourceProject z).1,rawHeights b z) ∈ shared b := by
  rw [shared_rows]
  constructor
  · intro hz
    have hbase : z ∈ (liftedModel b).linearRegion := by
      intro i
      simpa only [sharedModel,Fin.addCases_left,LinearForm,Fin.sum_univ_zero,add_zero] using hz (i.castAdd (2+2))
    obtain ⟨hbox,hbudget⟩ := (stored_linear_rows b z).mp hbase
    refine ⟨hbox,?_,?_⟩
    · intro j
      have hp := hz ((j.castAdd 2).natAdd ((2+2)+1))
      have hn := hz ((j.natAdd 2).natAdd ((2+2)+1))
      simp only [sharedModel,Fin.addCases_right,Fin.addCases_left,component_affine_row] at hp hn
      dsimp [rawHeights]
      exact ⟨by linarith,by linarith⟩
    · dsimp [rawHeights]; linarith
  · rintro ⟨hbox,hrows,hbudget⟩ row
    refine Fin.addCases (fun i => ?_) (fun k => ?_) row
    · have hbase : z ∈ (liftedModel b).linearRegion := by
        apply (stored_linear_rows b z).mpr
        refine ⟨hbox,?_⟩
        dsimp [rawHeights] at hbudget
        linarith
      simpa only [sharedModel,Fin.addCases_left,LinearForm,Fin.sum_univ_zero,add_zero] using hbase i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · simp only [sharedModel,Fin.addCases_right,Fin.addCases_left,component_affine_row]
        have hp := (hrows j).1
        dsimp [rawHeights] at hp
        linarith
      · simp only [sharedModel,Fin.addCases_right,component_affine_row]
        have hn := (hrows j).2
        dsimp [rawHeights] at hn
        linarith

theorem shared_feasible_iff (b : ℝ) (z : Point (2+2) 0) :
    z ∈ (sharedModel b).feasibleOn Set.univ ↔
      ((liftingSourceProject z).1,rawHeights b z) ∈ shared b := by
  rw [model_no_integer_iff]
  constructor
  · exact fun hz => (shared_linear_rows b z).mp hz.2
  · exact fun hz => ⟨fun j => Fin.elim0 j,(shared_linear_rows b z).mpr hz⟩

theorem shared_objective (b : ℝ) (z : Point (2+2) 0) :
    (sharedModel b).objective z = objective (liftingSourceProject z).1 := lifted_objective b z

theorem direct_source_minimum :
    IsMinimizer ((directModel (1/2)).feasibleOn Set.univ) (directModel (1/2)).objective
      (originalPoint (pt 1 (-1))) ∧
    (directModel (1/2)).objective (originalPoint (pt 1 (-1))) = -2 := by
  refine ⟨⟨(direct_feasible_iff _ _).mpr direct_minimum.1.1,?_⟩,?_⟩
  · intro p hp
    simpa [direct_objective,originalPoint] using
      direct_minimum.1.2 p.1 ((direct_feasible_iff _ p).mp hp)
  · simpa [direct_objective,originalPoint] using direct_minimum.2

theorem shared_source_minimum :
    IsMinimizer ((sharedModel (1/2)).feasibleOn Set.univ) (sharedModel (1/2)).objective
      (liftedPoint (1/2) (pt 1 (-1/4)) (pt 1 (-1/2))) ∧
    (sharedModel (1/2)).objective (liftedPoint (1/2) (pt 1 (-1/4)) (pt 1 (-1/2))) = -5/4 ∧
    liftingSourceHeight (liftedPoint (1/2) (pt 1 (-1/4)) (pt 1 (-1/2))) 1 = -3/4 := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · apply (shared_feasible_iff _ _).mpr
    simpa [lifted_point_project,lifted_point_heights,originalPoint] using shared_minimum.1.1
  · intro z hz
    simpa [shared_objective,lifted_point_project,originalPoint] using
      shared_minimum.1.2 _ ((shared_feasible_iff _ z).mp hz)
  · simpa [shared_objective,lifted_point_project,originalPoint] using shared_minimum.2
  · norm_num [liftedPoint,pt]

theorem historical_source_strictness :
    originalPoint (pt 1 (-1)) ∈ (directModel 1).feasibleOn Set.univ ∧
    ¬ ∃ z : Point (2+2) 0, z ∈ (sharedModel 1).feasibleOn Set.univ ∧
      (liftingSourceProject z).1 = pt 1 (-1) := by
  refine ⟨(direct_feasible_iff _ _).mpr historical_strictness.1,?_⟩
  rintro ⟨z,hz,hx⟩
  have hs := (shared_feasible_iff 1 z).mp hz
  rw [hx] at hs
  exact historical_strictness.2 ⟨rawHeights 1 z,hs⟩

end Chapter02LiftingValueSource

#print axioms Chapter02LiftingValueSource.source_linear_rows
#print axioms Chapter02LiftingValueSource.original_point_surjective
#print axioms Chapter02LiftingValueSource.source_objective
#print axioms Chapter02LiftingValueSource.original_feasible_iff
#print axioms Chapter02LiftingValueSource.component_identity
#print axioms Chapter02LiftingValueSource.source_component_derivative
#print axioms Chapter02LiftingValueSource.source_constraint_derivative
#print axioms Chapter02LiftingValueSource.source_lift_projection
#print axioms Chapter02LiftingValueSource.lifted_point_project
#print axioms Chapter02LiftingValueSource.lifted_point_heights
#print axioms Chapter02LiftingValueSource.lifted_point_surjective
#print axioms Chapter02LiftingValueSource.shifted_lifted_feasible_iff
#print axioms Chapter02LiftingValueSource.lifted_objective
#print axioms Chapter02LiftingValueSource.original_minimizer_iff
#print axioms Chapter02LiftingValueSource.lifted_minimizer_iff
#print axioms Chapter02LiftingValueSource.original_source_minimum
#print axioms Chapter02LiftingValueSource.exact_source_minimum
#print axioms Chapter02LiftingValueSource.direct_linear_rows
#print axioms Chapter02LiftingValueSource.direct_feasible_iff
#print axioms Chapter02LiftingValueSource.direct_objective
#print axioms Chapter02LiftingValueSource.shared_linear_rows
#print axioms Chapter02LiftingValueSource.shared_feasible_iff
#print axioms Chapter02LiftingValueSource.shared_objective
#print axioms Chapter02LiftingValueSource.direct_source_minimum
#print axioms Chapter02LiftingValueSource.shared_source_minimum
#print axioms Chapter02LiftingValueSource.historical_source_strictness
