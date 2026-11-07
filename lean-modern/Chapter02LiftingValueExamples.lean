module

public import Chapter02LiftingOA
public import Chapter02LiftingEnvelope
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-! S and native S-value whole-model controls. Both coordinates are continuous;
all four original box bounds are retained. The shared OA heights are free except
for actual tangent and aggregate rows. The source's historical budget is 1;
the rational optimum variant uses budget 1/2 and is explicitly a new control. -/
noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02LiftingValueExamples

def pt (u v : ℝ) : RealVector 2 := ![u,v]
def box : Set (RealVector 2) := {x | ∀ j, -1 ≤ x j ∧ x j ≤ 1}
def g (x : RealVector 2) : RealVector 2 := fun j => (x j)^2
def h (y : RealVector 2) : ℝ := y 0 + y 1
def objective (x : RealVector 2) : ℝ := -x 0+x 1
def anchor (i : Fin 2) : RealVector 2 := if i=0 then pt 1 1 else pt (-1) (-1)
def dg (a : RealVector 2) : RealVector 2 →L[ℝ] RealVector 2 :=
  ContinuousLinearMap.pi (fun j => (2*a j) • ContinuousLinearMap.proj j)
def dh : RealVector 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0 : RealVector 2 →L[ℝ] ℝ) +
  (ContinuousLinearMap.proj 1 : RealVector 2 →L[ℝ] ℝ)
def original (b : ℝ) := liftingOriginal box g h b
def exactLift (b : ℝ) := liftingSet box Set.univ g h b
def direct (b : ℝ) := liftingDirectOA box g h anchor (fun i => dg (anchor i)) (fun _ => dh) b
def shared (b : ℝ) := liftingSharedOA box Set.univ g h anchor (fun i => dg (anchor i)) (fun _ => dh) b

theorem component_derivative (a : RealVector 2) : HasFDerivAt g (dg a) a := by
  apply hasFDerivAt_pi'.mpr
  intro j
  have hh := (hasDerivAt_pow 2 (a j)).comp_hasFDerivAt a
    (ContinuousLinearMap.proj j : RealVector 2 →L[ℝ] ℝ).hasFDerivAt
  simpa [g,dg,Function.comp_def] using hh

theorem outer_derivative (y : RealVector 2) : HasFDerivAt h dh y := by
  exact (ContinuousLinearMap.proj 0 : RealVector 2 →L[ℝ] ℝ).hasFDerivAt.add
    (ContinuousLinearMap.proj 1 : RealVector 2 →L[ℝ] ℝ).hasFDerivAt

theorem outer_monotone : Monotone h := by
  intro x y hxy; exact add_le_add (hxy 0) (hxy 1)

theorem analytic_hypotheses :
    (∀ j, ConvexOn ℝ box (fun x => g x j)) ∧ ConvexOn ℝ Set.univ h ∧
    (∀ i, anchor i ∈ box) := by
  have hb : Convex ℝ box := by
    intro x hx y hy a b ha hb hab j
    change -1 ≤ a*x j+b*y j ∧ a*x j+b*y j ≤ 1
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left (hx j).1 ha,mul_le_mul_of_nonneg_left (hy j).1 hb]
    · nlinarith [mul_le_mul_of_nonneg_left (hx j).2 ha,mul_le_mul_of_nonneg_left (hy j).2 hb]
  refine ⟨?_,?_,?_⟩
  · intro j
    have hs : ConvexOn ℝ Set.univ (fun t : ℝ => t^2) := (by decide : Even 2).convexOn_pow
    refine ⟨hb,?_⟩
    intro x hx y hy a b ha hb hab
    exact hs.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  · refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [h]; ring_nf; exact le_rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [anchor,box,pt]

theorem composite_derivative (a : RealVector 2) :
    HasFDerivAt (h ∘ g) (dh.comp (dg a)) a :=
  lifting_chain_rule g h a (dg a) dh (component_derivative a) (outer_derivative (g a))

theorem original_rows (b : ℝ) (x : RealVector 2) :
    x ∈ original b ↔ x ∈ box ∧ (x 0)^2+(x 1)^2 ≤ b := Iff.rfl

theorem exact_rows (b : ℝ) (x y : RealVector 2) :
    (x,y) ∈ exactLift b ↔ x ∈ box ∧ (∀ j, (x j)^2 ≤ y j) ∧ y 0+y 1 ≤ b := by
  simp [exactLift,liftingSet,g,h,Pi.le_def]

theorem direct_rows (b : ℝ) (x : RealVector 2) :
    x ∈ direct b ↔ x ∈ box ∧ 2*(x 0+x 1)-2 ≤ b ∧ -2*(x 0+x 1)-2 ≤ b := by
  simp only [direct,liftingDirectOA,Set.mem_setOf_eq,Fin.forall_fin_two]
  dsimp [liftingDirectRow,anchor,pt,g,h,dg,dh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.pi_apply, Pi.sub_apply, smul_eq_mul, g, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨hx,hp,hn⟩ <;> refine ⟨hx,?_,?_⟩ <;> linarith

theorem shared_rows (b : ℝ) (x y : RealVector 2) :
    (x,y) ∈ shared b ↔ x ∈ box ∧
      (∀ j, 2*x j-1 ≤ y j ∧ -2*x j-1 ≤ y j) ∧ y 0+y 1 ≤ b := by
  simp only [shared,liftingSharedOA,Set.mem_setOf_eq,Set.mem_univ,true_and,
    Pi.le_def,Fin.forall_fin_two]
  dsimp [liftingComponentRow,liftingOuterRow,anchor,pt,g,h,dg,dh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.pi_apply, Pi.sub_apply, smul_eq_mul, g, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨hx,⟨⟨hp0,hp1⟩,hbp⟩,⟨⟨hn0,hn1⟩,hbn⟩⟩
    refine ⟨hx,⟨⟨?_,?_⟩,?_,?_⟩,?_⟩ <;> linarith
  · rintro ⟨hx,⟨⟨hp0,hn0⟩,hp1,hn1⟩,hb⟩
    refine ⟨hx,⟨⟨?_,?_⟩,?_⟩,⟨⟨?_,?_⟩,?_⟩⟩ <;> linarith

theorem direct_description (b : ℝ) (x : RealVector 2) :
    x ∈ direct b ↔ x ∈ box ∧ |x 0+x 1| ≤ (b+2)/2 := by
  rw [direct_rows,abs_le]
  constructor <;> rintro ⟨hx,hp,hn⟩ <;> refine ⟨hx,?_,?_⟩ <;> linarith

theorem shared_projection (b : ℝ) (x : RealVector 2) :
    (∃ y, (x,y) ∈ shared b) ↔ x ∈ box ∧ |x 0|+|x 1| ≤ (b+2)/2 := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hx,hrows,hb⟩ := (shared_rows b x y).mp hy
    have hj : ∀ j, 2*|x j|-1 ≤ y j := by
      intro j; rcases le_total 0 (x j) with hpos|hneg
      · rw [abs_of_nonneg hpos]; exact (hrows j).1
      · rw [abs_of_nonpos hneg]; linarith [(hrows j).2]
    exact ⟨hx,by linarith [hj 0,hj 1]⟩
  · rintro ⟨hx,hb⟩
    refine ⟨fun j => 2*|x j|-1,(shared_rows b x _).mpr ⟨hx,?_,?_⟩⟩
    · intro j; constructor <;> linarith [le_abs_self (x j),neg_le_abs (x j)]
    · linarith

theorem complete_containments (b : ℝ) :
    original b ⊆ Prod.fst '' shared b ∧ Prod.fst '' shared b ⊆ direct b ∧
    Prod.fst '' exactLift b = original b := by
  refine ⟨?_,?_,?_⟩
  · exact lifting_original_subset_projected_oa box Set.univ g h anchor _ _ b
      (fun _ _ => Set.mem_univ _) analytic_hypotheses.1 analytic_hypotheses.2.1
      analytic_hypotheses.2.2 (fun i => component_derivative _) (fun i => outer_derivative _)
  · exact lifting_fullspace_shared_subset_direct box Set.univ g h anchor _ _ b
      outer_monotone (fun i => outer_derivative _)
  · exact lifting_projection box Set.univ g h b (fun _ _ => Set.mem_univ _)
      (outer_monotone.monotoneOn Set.univ)

theorem historical_descriptions (x : RealVector 2) :
    (x ∈ direct 1 ↔ x ∈ box ∧ |x 0+x 1| ≤ 3/2) ∧
    ((∃ y, (x,y) ∈ shared 1) ↔ x ∈ box ∧ |x 0|+|x 1| ≤ 3/2) := by
  constructor
  · convert direct_description 1 x using 1; norm_num
  · convert shared_projection 1 x using 1; norm_num

theorem historical_strictness : pt 1 (-1) ∈ direct 1 ∧
    ¬ ∃ y, (pt 1 (-1),y) ∈ shared 1 := by
  rw [direct_description,shared_projection]
  norm_num [box,pt,Fin.forall_fin_two]

def independentRows (i j : Fin 2) (x : RealVector 2) : ℝ :=
  liftingComponentRow g (anchor i) (dg (anchor i)) x j

theorem independent_equals_direct (b : ℝ) (x : RealVector 2) :
    (∃ y, (x,y) ∈ liftingIndependentSupportSet box independentRows (fun _ => b)) ↔
      x ∈ direct b := by
  rw [lifting_independent_projection,direct_rows]
  simp only [Fin.forall_fin_two,Fin.sum_univ_two]
  dsimp [independentRows,liftingComponentRow,anchor,pt,g,dg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.pi_apply, Pi.sub_apply, smul_eq_mul, g, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨hx,hp,hn⟩ <;> refine ⟨hx,?_,?_⟩ <;> linarith

theorem historical_independent_heights :
    (pt 1 (-1), ![pt 1 (-3),pt (-3) 1]) ∈
      liftingIndependentSupportSet box independentRows (fun _ => 1) ∧
    ¬ ∃ y, (pt 1 (-1),y) ∈ shared 1 := by
  refine ⟨?_,historical_strictness.2⟩
  norm_num [liftingIndependentSupportSet,independentRows,liftingComponentRow,
    box,anchor,pt,g,dg,Fin.forall_fin_two,Fin.sum_univ_two]

theorem direct_minimum : IsMinimizer (direct (1/2)) objective (pt 1 (-1)) ∧
    objective (pt 1 (-1)) = -2 := by
  refine ⟨⟨?_,?_⟩,by norm_num [objective,pt]⟩
  · rw [direct_rows]; norm_num [box,pt,Fin.forall_fin_two]
  · intro x hx
    have hb := ((direct_rows _ x).mp hx).1
    dsimp [objective,pt]; linarith [(hb 0).2,(hb 1).1]

theorem shared_minimum :
    IsMinimizer (shared (1/2)) (fun z => objective z.1) (pt 1 (-1/4),pt 1 (-1/2)) ∧
    objective (pt 1 (-1/4)) = -5/4 := by
  refine ⟨⟨?_,?_⟩,by norm_num [objective,pt]⟩
  · rw [shared_rows]; norm_num [box,pt,Fin.forall_fin_two]
  · rintro ⟨x,y⟩ hz
    obtain ⟨_,hr,hb⟩ := (shared_rows _ x y).mp hz
    dsimp [objective,pt]; linarith [(hr 0).1,(hr 1).2]

theorem original_minimum : IsMinimizer (original (1/2)) objective (pt (1/2) (-1/2)) ∧
    objective (pt (1/2) (-1/2)) = -1 := by
  refine ⟨⟨?_,?_⟩,by norm_num [objective,pt]⟩
  · rw [original_rows]; norm_num [box,pt,Fin.forall_fin_two]
  · intro x hx
    have hb := ((original_rows _ x).mp hx).2
    dsimp [objective,pt]
    nlinarith [sq_nonneg (x 0+x 1),sq_nonneg (x 0-x 1-1)]

theorem exact_minimum :
    IsMinimizer (exactLift (1/2)) (fun z => objective z.1)
      (pt (1/2) (-1/2),pt (1/4) (1/4)) ∧ objective (pt (1/2) (-1/2)) = -1 := by
  refine ⟨?_,original_minimum.2⟩
  apply (lifting_minimizer_iff box Set.univ g h (1/2)
    (fun _ _ => Set.mem_univ _) (outer_monotone.monotoneOn Set.univ) objective _).mpr
  refine ⟨?_,original_minimum.1⟩
  rw [← exactLift,exact_rows]; norm_num [box,pt,Fin.forall_fin_two]

theorem actual_optimum_gaps :
    objective (pt 1 (-1)) < objective (pt 1 (-1/4)) ∧
    objective (pt 1 (-1/4)) < objective (pt (1/2) (-1/2)) := by
  norm_num [objective,pt]

end Chapter02LiftingValueExamples

#print axioms Chapter02LiftingValueExamples.component_derivative
#print axioms Chapter02LiftingValueExamples.outer_derivative
#print axioms Chapter02LiftingValueExamples.outer_monotone
#print axioms Chapter02LiftingValueExamples.analytic_hypotheses
#print axioms Chapter02LiftingValueExamples.composite_derivative
#print axioms Chapter02LiftingValueExamples.original_rows
#print axioms Chapter02LiftingValueExamples.exact_rows
#print axioms Chapter02LiftingValueExamples.direct_rows
#print axioms Chapter02LiftingValueExamples.shared_rows
#print axioms Chapter02LiftingValueExamples.direct_description
#print axioms Chapter02LiftingValueExamples.shared_projection
#print axioms Chapter02LiftingValueExamples.complete_containments
#print axioms Chapter02LiftingValueExamples.historical_descriptions
#print axioms Chapter02LiftingValueExamples.historical_strictness
#print axioms Chapter02LiftingValueExamples.independent_equals_direct
#print axioms Chapter02LiftingValueExamples.historical_independent_heights
#print axioms Chapter02LiftingValueExamples.direct_minimum
#print axioms Chapter02LiftingValueExamples.shared_minimum
#print axioms Chapter02LiftingValueExamples.original_minimum
#print axioms Chapter02LiftingValueExamples.exact_minimum
#print axioms Chapter02LiftingValueExamples.actual_optimum_gaps
