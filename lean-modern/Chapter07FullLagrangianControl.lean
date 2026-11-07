module

public import Chapter07FullLagrangian
public import Chapter06LevelControlData

@[expose] public section

/-!
Invented exact affine-normal nonvacuity control. At the actual fixed-y minimum
of x²+x-2y on the unit box, the lower-x normal cancels raw derivative 1.
The soft row is strictly inactive; the hard normals remain in the full KKT.
This is a mathematical example, not a historical numerical experiment.
-/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter06.Level
namespace Chapter07.FullLagrangianControl

abbrev P := Point 1 1

def d : Data 1 1 1 4 where
  f := fun p => (p.1 0)^2 + p.1 0 - 2*p.2 0
  g := fun _ _ => -1
  A := Chapter06.LevelControl.d.A
  B := Chapter06.LevelControl.d.B
  b := fun i => if i.val=1 then 1 else if i.val=3 then 1 else 0

def anchor : P := Chapter06.LevelControl.pt 0 0

theorem objective_eq : d.f = fun p =>
    Chapter06.LevelControl.d.f p + Chapter06.LevelControl.X p := by
  funext p
  simp [d, Chapter06.LevelControl.d]
  ring

theorem hard_iff (p : P) : p ∈ d.hard ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  constructor
  · intro h
    have h0 := h ⟨0, by decide⟩; have h1 := h ⟨1, by decide⟩
    have h2 := h ⟨2, by decide⟩; have h3 := h ⟨3, by decide⟩
    norm_num [d, Chapter06.LevelControl.d, LinearForm] at h0 h1 h2 h3
    exact ⟨by linarith, h1, by linarith, h3⟩
  · rintro ⟨hx0, hx1, hy0, hy1⟩ i
    fin_cases i <;> norm_num [d, Chapter06.LevelControl.d, LinearForm] <;> linarith

theorem hard_eq_unit_box : d.hard = Set.Icc
    (Chapter06.LevelControl.pt 0 0) (Chapter06.LevelControl.pt 1 1) := by
  ext p
  rw [hard_iff]
  simp [Set.mem_Icc, Prod.le_def, Pi.le_def, Chapter06.LevelControl.pt,
    Fin.forall_fin_one, and_assoc, and_left_comm, and_comm]

theorem hard_compact : IsCompact d.hard := by
  rw [hard_eq_unit_box]
  exact isCompact_Icc

theorem objective_C2 : ContDiff ℝ 2 d.f := by
  change ContDiff ℝ 2 (fun p : P => (p.1 0)^2 + p.1 0 - 2*p.2 0)
  fun_prop

theorem soft_C2 (j : Fin 1) : ContDiff ℝ 2 (d.g j) := contDiff_const

theorem objective_convex : ConvexOn ℝ Set.univ d.f := by
  rw [objective_eq]
  exact Chapter06.LevelControl.objective_convex.add
    (Chapter06.LevelControl.X.toLinearMap.convexOn convex_univ)

theorem soft_convex (j : Fin 1) : ConvexOn ℝ Set.univ (d.g j) :=
  convexOn_const (-1) convex_univ

theorem fiber_slater (y : IntVector 1) (hne : (d.feasibleFiber y).Nonempty) :
    ∃ p ∈ d.hardFiber y, ∀ j, d.g j p < 0 := by
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hp.1, fun _ => by norm_num [d]⟩

def regularity : Regularity d where
  hard_compact := hard_compact
  hard_nonempty := ⟨anchor, (hard_iff _).mpr (by norm_num [anchor, Chapter06.LevelControl.pt])⟩
  objective_convex := objective_convex
  objective_C1 := objective_C2.of_le (by norm_num)
  constraint_convex := soft_convex
  constraint_C1 := fun j => (soft_C2 j).of_le (by norm_num)
  fiber_slater := fiber_slater

theorem anchor_feasible : anchor ∈ d.feasibleFiber (Chapter06.LevelControl.iy 0) := by
  refine ⟨⟨(hard_iff _).mpr (by norm_num [anchor, Chapter06.LevelControl.pt]), ?_⟩, ?_⟩
  · funext i
    norm_num [anchor, Chapter06.LevelControl.pt, Chapter06.LevelControl.iy, intCast]
  · intro j
    norm_num [d]

theorem actual_minimum :
    IsMinimizer (d.feasibleFiber (Chapter06.LevelControl.iy 0)) d.f anchor := by
  refine ⟨anchor_feasible, ?_⟩
  intro q hq
  have hx := ((hard_iff q).mp hq.1.1).1
  have hy := congrFun hq.1.2 0
  norm_num [intCast, Chapter06.LevelControl.iy] at hy
  change (0:ℝ)^2 + 0 - 2*0 ≤ (q.1 0)^2 + q.1 0 - 2*q.2 0
  nlinarith [sq_nonneg (q.1 0)]

theorem fderiv_f_apply (a h : P) :
    fderiv ℝ d.f a h = 2*a.1 0*h.1 0 + h.1 0 - 2*h.2 0 := by
  have hd := (((Chapter06.LevelControl.regularity.objective_C1.differentiable
    (by norm_num)) a).hasFDerivAt).fun_add (Chapter06.LevelControl.X.hasFDerivAt (x := a))
  rw [objective_eq, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, Chapter06.LevelControl.fderiv_f_apply,
    Chapter06.LevelControl.X_apply]
  ring

def lambda : Fin 1 → ℝ := fun _ => 0
def mu : Fin 4 → ℝ := fun i => if i.val=0 then 1 else 0

def explicit_KKT : FeasibleKKT d regularity anchor where
  lambda := lambda
  mu := mu
  lambda_nonneg := by intro j; norm_num [lambda]
  mu_nonneg := by intro i; simp [mu]; split_ifs <;> norm_num
  soft_compl := by intro j; norm_num [lambda]
  hard_compl := by
    intro i
    fin_cases i <;> norm_num [mu, linearResidual, boxedModel, d,
      Chapter06.LevelControl.d, LinearForm, anchor, Chapter06.LevelControl.pt]
  stationarity := by
    ext dx
    simp [lambda, mu, Chapter03.OAKKT.restrict_apply, fderiv_f_apply,
      anchor, Chapter06.LevelControl.pt, Fin.sum_univ_succ, fiberLinearRow_apply,
      boxedModel, d, Chapter06.LevelControl.d, LinearForm]
    change fderiv ℝ d.f anchor (dx, 0) + -dx 0 = 0
    rw [fderiv_f_apply]
    simp [anchor, Chapter06.LevelControl.pt]

theorem actual_KKT_exists : Nonempty (FeasibleKKT d regularity anchor) :=
  feasibleKKT_exists d regularity (Chapter06.LevelControl.iy 0) actual_minimum

theorem full_lagrangian_eq : FullLagrangian.lagrangian d lambda mu =
    Chapter06.LevelControl.d.f := by
  funext p
  simp [FullLagrangian.lagrangian, FullLagrangian.hardRow, lambda, mu,
    Fin.sum_univ_succ, d, Chapter06.LevelControl.d, LinearForm]
  ring

theorem full_lagrangian_formula (p : P) :
    FullLagrangian.lagrangian d lambda mu p = (p.1 0)^2 - 2*p.2 0 := by
  rw [full_lagrangian_eq]
  rfl

theorem raw_continuous_derivative_one :
    fderiv ℝ d.f anchor ((fun _ => 1), 0) = 1 := by
  norm_num [fderiv_f_apply, anchor, Chapter06.LevelControl.pt]

theorem full_continuous_derivative_zero (v : RealVector 1) :
    fderiv ℝ (FullLagrangian.lagrangian d lambda mu) anchor (v, 0) = 0 :=
  FullLagrangian.continuous_stationarity d regularity anchor explicit_KKT v

/-- Independent of the displayed multiplier construction, the actual minimum
also invokes the generic source-minimum-to-stationarity existence bridge. -/
theorem derived_polished_stationarity :
    ∃ K : FeasibleKKT d regularity anchor, ∀ v : RealVector 1,
      fderiv ℝ (FullLagrangian.lagrangian d K.lambda K.mu) anchor (v, 0) = 0 :=
  FullLagrangian.polished_stationarity d regularity
    (Chapter06.LevelControl.iy 0) anchor actual_minimum

theorem lower_normal_nonzero :
    mu 0 = 1 ∧ mu 0 * d.A 0 0 = -1 ∧ d.g 0 anchor = -1 := by
  norm_num [mu, d, Chapter06.LevelControl.d]

end Chapter07.FullLagrangianControl

#print axioms Chapter07.FullLagrangianControl.hard_eq_unit_box
#print axioms Chapter07.FullLagrangianControl.hard_compact
#print axioms Chapter07.FullLagrangianControl.objective_C2
#print axioms Chapter07.FullLagrangianControl.soft_C2
#print axioms Chapter07.FullLagrangianControl.objective_convex
#print axioms Chapter07.FullLagrangianControl.soft_convex
#print axioms Chapter07.FullLagrangianControl.fiber_slater
#print axioms Chapter07.FullLagrangianControl.regularity
#print axioms Chapter07.FullLagrangianControl.anchor_feasible
#print axioms Chapter07.FullLagrangianControl.actual_minimum
#print axioms Chapter07.FullLagrangianControl.fderiv_f_apply
#print axioms Chapter07.FullLagrangianControl.explicit_KKT
#print axioms Chapter07.FullLagrangianControl.actual_KKT_exists
#print axioms Chapter07.FullLagrangianControl.full_lagrangian_eq
#print axioms Chapter07.FullLagrangianControl.full_lagrangian_formula
#print axioms Chapter07.FullLagrangianControl.raw_continuous_derivative_one
#print axioms Chapter07.FullLagrangianControl.full_continuous_derivative_zero
#print axioms Chapter07.FullLagrangianControl.derived_polished_stationarity
#print axioms Chapter07.FullLagrangianControl.lower_normal_nonzero
