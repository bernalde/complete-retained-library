module

public import Chapter04SlaterBall
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! One full-hypothesis control for the corrected Chapter4 Slater-ball lemma.
The data are x ∈ [0,1], integer y = 0, x² + y² ≤ 4, objective x.
This file makes no assertion that the wrapper's existential center is the
particular optimum, and makes no algorithm-execution claim. -/

noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter04.CenterCut.Control

abbrev P := Point 1 1

def pt (x y : ℝ) : P := (fun _ => x, fun _ => y)

def model : ModelData 1 1 1 2 where
  g _ p := (p.1 0)^2 + (p.2 0)^2 - 4
  A row _ := if row = 0 then -1 else 1
  B _ _ := 0
  rhs row := if row = 0 then 0 else 1
  c1 _ := 1
  c2 _ := 0
  lo _ := 0
  hi _ := 0

theorem pt_eta (p : P) : pt (p.1 0) (p.2 0) = p := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

@[simp] theorem objective_eq (p : P) : model.objective p = p.1 0 := by
  simp [ModelData.objective, LinearForm, model]

theorem linear_iff (p : P) : p ∈ model.linearRegion ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 1 := by
  simp [ModelData.linearRegion, LinearForm, model, Fin.forall_fin_two]

theorem cylinder_iff (p : P) :
    p ∈ IntegerCylinder (n := 1) model.lo model.hi ↔ p.2 0 = 0 := by
  constructor
  · rintro ⟨y, hy, hp⟩
    have hb := hy 0
    change 0 ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 0 at hb
    rw [hp]
    exact le_antisymm hb.2 hb.1
  · intro hp
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i
      norm_num [model]
    · funext i
      fin_cases i
      simpa using hp

theorem compact_base :
    IsCompact (model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi) := by
  have heq : model.linearRegion ∩ IntegerCylinder (n := 1) model.lo model.hi =
      (fun x : ℝ => pt x 0) '' Set.Icc 0 1 := by
    ext p
    simp only [Set.mem_inter_iff, linear_iff, cylinder_iff, Set.mem_image,
      Set.mem_Icc]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨p.1 0, hx, ?_⟩
      simpa [hy] using pt_eta p
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
  rw [heq]
  apply isCompact_Icc.image
  unfold pt
  fun_prop

theorem rows_continuous (j : Fin 1) : Continuous (model.g j) := by
  unfold model
  fun_prop

theorem rows_convex (j : Fin 1) : ConvexOn ℝ Set.univ (model.g j) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  change (a * p.1 0 + b * q.1 0)^2 + (a * p.2 0 + b * q.2 0)^2 - 4 ≤
    a * ((p.1 0)^2 + (p.2 0)^2 - 4) + b * ((q.1 0)^2 + (q.2 0)^2 - 4)
  have hx := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.1 0 - q.1 0))
  have hy := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.2 0 - q.2 0))
  have heq : b = 1 - a := by linarith
  subst b
  nlinarith

/-- A strict midpoint inequality proves the row genuinely violates affine
interpolation; its displayed formula is the nonlinear quadratic used above. -/
theorem nonlinear_row_midpoint :
    model.g 0 ((1 / 2 : ℝ) • pt (-1) 0 + (1 / 2 : ℝ) • pt 1 0) <
      (1 / 2 : ℝ) * model.g 0 (pt (-1) 0) + (1 / 2 : ℝ) * model.g 0 (pt 1 0) := by
  norm_num [model, pt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]

theorem zero_feasible : pt 0 0 ∈ model.feasibleOn Set.univ := by
  apply (source_feasible_iff model Set.univ (pt 0 0)).mpr
  refine ⟨Set.mem_univ _, ?_, ?_, fun _ => 0, ?_, ?_⟩
  · intro j
    norm_num [model, pt]
  · exact (linear_iff _).mpr (by norm_num [pt])
  · intro i
    norm_num [model]
  · simp [pt]

theorem feasible_nonempty : (model.feasibleOn Set.univ).Nonempty :=
  ⟨pt 0 0, zero_feasible⟩

theorem zero_minimizer : IsMinimizer (model.feasibleOn Set.univ)
    model.objective (pt 0 0) := by
  refine ⟨zero_feasible, ?_⟩
  intro p hp
  have hx := (linear_iff p).mp ((source_feasible_iff model Set.univ p).mp hp).2.2.1
  simpa [pt] using hx.1

theorem fiber_slater : OAFiberSlater model := by
  intro y hy _
  have hcast : oaIntCast y = (pt 0 0).2 := by
    funext i
    have hb := hy i
    change 0 ≤ (y i : ℝ) ∧ (y i : ℝ) ≤ 0 at hb
    exact le_antisymm hb.2 hb.1
  refine ⟨pt 0 0, ?_, ?_⟩
  · exact ⟨(linear_iff _).mpr (by norm_num [pt]), hcast.symm⟩
  · intro j
    norm_num [model, pt]

/-- The complete source wrapper is applied to the concrete data. Its chosen
optimizer has the exact value zero. The center meets all original restrictions,
whereas every point of the full Euclidean ball meets the nonlinear row and
epsilon objective cutoff. No affine/integer restriction is imposed on that ball. -/
theorem source_ball_control :
    ∃ pStar, IsMinimizer (model.feasibleOn Set.univ) model.objective pStar ∧
      model.objective pStar = 0 ∧
      ∀ ε : ℝ, 0 < ε → ∃ center : P, ∃ radius : ℝ,
        center ∈ model.feasibleOn Set.univ ∧ 0 < radius ∧
        ∀ q : P, ‖coordinates 1 1 q - coordinates 1 1 center‖ ≤ radius →
          model.objective q ≤ ε ∧ ∀ j, model.g j q ≤ 0 := by
  obtain ⟨pStar, hmin, hball⟩ := source_epsilon_slater_ball model rows_continuous
    rows_convex compact_base feasible_nonempty fiber_slater
  have hvalue : model.objective pStar = 0 := by
    apply le_antisymm
    · simpa [pt] using hmin.2 (pt 0 0) zero_feasible
    · simpa [pt] using zero_minimizer.2 pStar hmin.1
  refine ⟨pStar, hmin, hvalue, ?_⟩
  intro ε hε
  simpa only [hvalue, zero_add] using hball ε hε

end Chapter04.CenterCut.Control

#print axioms Chapter04.CenterCut.Control.compact_base
#print axioms Chapter04.CenterCut.Control.rows_continuous
#print axioms Chapter04.CenterCut.Control.rows_convex
#print axioms Chapter04.CenterCut.Control.nonlinear_row_midpoint
#print axioms Chapter04.CenterCut.Control.zero_minimizer
#print axioms Chapter04.CenterCut.Control.fiber_slater
#print axioms Chapter04.CenterCut.Control.source_ball_control
