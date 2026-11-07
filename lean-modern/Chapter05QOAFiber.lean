module

public import Chapter02Slater
public import Chapter03OAKKTSource
public import Chapter05QuadraticAnalytic
public import Chapter05QOAModel

@[expose] public section

/-! Actual fixed-fiber support for the qualified quadratic OA family.
The convex domain is retained in the partial-Lagrangian minimum. Its normal
is derived, not replaced by zero ambient stationarity. -/
noncomputable section
open scoped BigOperators
open Set Chapter02 Chapter03.OAKKT Chapter05.Quadratic
namespace Chapter05.QOA

variable {n p m : ℕ}

theorem convex_restrict_product {f : Point n p → ℝ}
    (hf : ConvexOn ℝ univ f) (y : RealVector p)
    {C : Set (RealVector n)} (hC : Convex ℝ C) :
    ConvexOn ℝ C (fun x => f (x,y)) := by
  refine ⟨hC,?_⟩
  intro x hx z hz s t hs ht hst
  have hy : s • y + t • y = y := by rw [← add_smul,hst,one_smul]
  have hc := hf.2 (mem_univ (x,y)) (mem_univ (z,y)) hs ht hst
  change f (s • x + t • z,s • y + t • y) ≤ s • f (x,y) + t • f (z,y) at hc
  simpa only [hy] using hc

def fiberLagrangianDerivative (f : Point n p → ℝ)
    (g : Fin m → Point n p → ℝ) (y : RealVector p) (a : RealVector n)
    (lambda : Fin m → ℝ) : RealVector n →L[ℝ] ℝ :=
  restrict (fderiv ℝ f (a,y)) +
    ∑ j, lambda j • restrict (fderiv ℝ (g j) (a,y))

/-- Actual Slater multipliers and the retained-domain normal inequality. -/
theorem fiber_lagrangian_certificate (C : Set (RealVector n))
    (f : Point n p → ℝ) (g : Fin m → Point n p → ℝ)
    (y : RealVector p) (a : RealVector n)
    (hC : Convex ℝ C) (hf : ConvexOn ℝ univ f)
    (hg : ∀ j, ConvexOn ℝ univ (g j))
    (hf2 : ContDiff ℝ 2 f) (hg2 : ∀ j, ContDiff ℝ 2 (g j))
    (hmin : IsMinimizer {x ∈ C | ∀ j, g j (x,y) ≤ 0} (fun x => f (x,y)) a)
    (hslater : ∃ x ∈ C, ∀ j, g j (x,y) < 0) :
    ∃ lambda : Fin m → ℝ,
      (∀ j, 0 ≤ lambda j) ∧
      (∀ j, lambda j * g j (a,y) = 0) ∧
      IsMinimizer C (fun x => f (x,y) + ∑ j, lambda j * g j (x,y)) a ∧
      ∀ q ∈ C, (-fiberLagrangianDerivative f g y a lambda) (q-a) ≤ 0 := by
  obtain ⟨lambda,hl,hcompl,hL⟩ := convex_slater_partialLagrangian_minimum C
    (fun x => f (x,y)) (fun j x => g j (x,y)) a hC
    (convex_restrict_product hf y hC)
    (fun j => convex_restrict_product (hg j) y hC) hmin hslater
  have hdf : HasFDerivAt (fun x => f (x,y)) (restrict (fderiv ℝ f (a,y))) a :=
    fiber_derivative ((hf2.differentiable (by norm_num)) (a,y)).hasFDerivAt
  have hdg (j : Fin m) : HasFDerivAt (fun x => g j (x,y))
      (restrict (fderiv ℝ (g j) (a,y))) a :=
    fiber_derivative (((hg2 j).differentiable (by norm_num)) (a,y)).hasFDerivAt
  have hdL : HasFDerivAt (fun x => f (x,y) + ∑ j, lambda j * g j (x,y))
      (fiberLagrangianDerivative f g y a lambda) a :=
    hdf.fun_add (HasFDerivAt.fun_sum fun j _ => (hdg j).const_mul (lambda j))
  refine ⟨lambda,hl,hcompl,hL,?_⟩
  intro q hq
  simpa only [ContinuousLinearMap.neg_apply,neg_nonpos] using
    convex_minimum_derivative_nonneg hC hL hdL hq

/-- Same-fiber linear support, proved from the actual nonlinear minimum and CQ. -/
theorem feasible_fiber_tangent_lower (C : Set (RealVector n))
    (f : Point n p → ℝ) (g : Fin m → Point n p → ℝ)
    (y : RealVector p) (a q : RealVector n)
    (hC : Convex ℝ C) (hf : ConvexOn ℝ univ f)
    (hg : ∀ j, ConvexOn ℝ univ (g j))
    (hf2 : ContDiff ℝ 2 f) (hg2 : ∀ j, ContDiff ℝ 2 (g j))
    (hmin : IsMinimizer {x ∈ C | ∀ j, g j (x,y) ≤ 0} (fun x => f (x,y)) a)
    (hslater : ∃ x ∈ C, ∀ j, g j (x,y) < 0)
    (hq : q ∈ C) (hrows : ∀ j, tangent (g j) (a,y) (q,y) ≤ 0) :
    f (a,y) ≤ tangent f (a,y) (q,y) := by
  obtain ⟨lambda,hl,hcompl,_,hnormal⟩ :=
    fiber_lagrangian_certificate C f g y a hC hf hg hf2 hg2 hmin hslater
  have hnon : 0 ≤ fiberLagrangianDerivative f g y a lambda (q-a) := by
    simpa only [ContinuousLinearMap.neg_apply,neg_nonpos] using hnormal q hq
  have hsum : (∑ j, lambda j * restrict (fderiv ℝ (g j) (a,y)) (q-a)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    have hrow := hrows j
    rw [tangent,derivative_fiber_action] at hrow
    have hm := mul_nonpos_of_nonneg_of_nonpos (hl j) hrow
    rw [mul_add,hcompl j,zero_add] at hm
    exact hm
  simp only [fiberLagrangianDerivative,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul] at hnon
  rw [tangent,derivative_fiber_action]
  linarith

/-- Individual positive-part restoration excludes the entire hard fiber. -/
theorem restoration_fiber_tangent_excludes (C : Set (RealVector n))
    (g : Fin m → Point n p → ℝ) (y : RealVector p) (a : RealVector n)
    (hC : Convex ℝ C) (hg : ∀ j, ConvexOn ℝ univ (g j))
    (hg2 : ∀ j, ContDiff ℝ 2 (g j))
    (hmin : IsMinimizer C (weightedPositive (fun _ : Fin m => (1 : ℝ))
      (fun j x => g j (x,y))) a)
    (hempty : ¬ ∃ x ∈ C, ∀ j, g j (x,y) ≤ 0) :
    ¬ ∃ q ∈ C, ∀ j, tangent (g j) (a,y) (q,y) ≤ 0 := by
  have hex := weighted_empty_hard_actual_minimum_excludes C
    (fun j x => g j (x,y)) (fun _ => 1) a
    (fun j => restrict (fderiv ℝ (g j) (a,y))) hC (fun _ => by norm_num)
    (fun j => convex_restrict_product (hg j) y convex_univ)
    (fun j => fiber_derivative
      (((hg2 j).differentiable (by norm_num)) (a,y)).hasFDerivAt) hmin hempty
  rintro ⟨q,hq,hrows⟩
  apply hex
  refine ⟨q,hq,fun j => ?_⟩
  simpa only [tangent,derivative_fiber_action] using hrows j

/-- Nonnegative actual quadratic additions preserve the same-fiber support. -/
theorem feasible_fiber_quadratic_lower (C : Set (RealVector n))
    (f : Point n p → ℝ) (g : Fin m → Point n p → ℝ)
    (y : RealVector p) (a q : RealVector n) (alpha eta : ℝ) (beta : Fin m → ℝ)
    (hC : Convex ℝ C) (hf : ConvexOn ℝ univ f)
    (hg : ∀ j, ConvexOn ℝ univ (g j))
    (hf2 : ContDiff ℝ 2 f) (hg2 : ∀ j, ContDiff ℝ 2 (g j))
    (hmin : IsMinimizer {x ∈ C | ∀ j, g j (x,y) ≤ 0} (fun x => f (x,y)) a)
    (hslater : ∃ x ∈ C, ∀ j, g j (x,y) < 0)
    (hq : q ∈ C) (halpha : 0 ≤ alpha) (hbeta : ∀ j, 0 ≤ beta j)
    (hobj : cut f (a,y) alpha (q,y) ≤ eta)
    (hrows : ∀ j, cut (g j) (a,y) (beta j) (q,y) ≤ 0) :
    f (a,y) ≤ eta :=
  (feasible_fiber_tangent_lower C f g y a q hC hf hg hf2 hg2 hmin hslater hq
    (fun j => (tangent_le_cut (hg j) (hg2 j) (a,y) (hbeta j) (q,y)).trans
      (hrows j))).trans ((tangent_le_cut hf hf2 (a,y) halpha (q,y)).trans hobj)

theorem restoration_fiber_quadratic_excludes (C : Set (RealVector n))
    (g : Fin m → Point n p → ℝ) (y : RealVector p) (a : RealVector n)
    (beta : Fin m → ℝ) (hC : Convex ℝ C)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) (hg2 : ∀ j, ContDiff ℝ 2 (g j))
    (hmin : IsMinimizer C (weightedPositive (fun _ : Fin m => (1 : ℝ))
      (fun j x => g j (x,y))) a)
    (hempty : ¬ ∃ x ∈ C, ∀ j, g j (x,y) ≤ 0)
    (hbeta : ∀ j, 0 ≤ beta j) :
    ¬ ∃ q ∈ C, ∀ j, cut (g j) (a,y) (beta j) (q,y) ≤ 0 := by
  rintro ⟨q,hq,hrows⟩
  apply restoration_fiber_tangent_excludes C g y a hC hg hg2 hmin hempty
  exact ⟨q,hq,fun j => (tangent_le_cut (hg j) (hg2 j) (a,y) (hbeta j) (q,y)).trans
    (hrows j)⟩

variable {r : ℕ} {d : Data n p m r}

/-- Projection of the literal individual nonnegative slack-sum minimum. -/
theorem event_restoration_positive_minimum {e : Event d}
    (he : EventValid d e) {s : RealVector m} (hs : e.restoration = some s) :
    IsMinimizer (d.hardFiber e.target)
      (weightedPositive (fun _ : Fin m => (1 : ℝ)) (d.soft e.target)) e.x := by
  have hm := he.2
  rw [hs] at hm
  have hp := weighted_lift_project_minimizer (d.hardFiber e.target)
    (Fin.elim0 : Fin 0 → RealVector n → ℝ) (d.soft e.target)
    (fun _ => 1) (fun _ => by norm_num) hm.2
  simpa only [empty_hard_region,weightedX_insert] using hp

theorem event_feasible_master_lower (hr : Regularity d)
    {e : Event d} (he : EventValid d e) (hn : e.restoration = none)
    {H : List (Token n p m)} (het : e.token ∈ H)
    {q : Point n p × ℝ} (hq : q ∈ master d H)
    (hy : q.1.2 = intCast e.target) : d.f e.anchor ≤ q.2 := by
  have hm := he.2
  rw [hn] at hm
  have hq' := (master_mem_iff d H q).mp hq
  have hpoint : q.1 = (q.1.1,intCast e.target) := Prod.ext rfl hy
  apply feasible_fiber_quadratic_lower (d.hardFiber e.target) d.f d.g
    (intCast e.target) e.x q.1.1 e.objectiveScale q.2 e.constraintScale
    (hardFiber_convex hr.X_convex e.target) hr.objective_convex
    hr.constraint_convex hr.objective_C2 hr.constraint_C2 hm
    (hr.fiber_slater e.target e.target_mem ⟨e.x,hm.1⟩)
    (base_hard hq'.1 hy) he.1.1.1 (fun j => (he.1.2 j).1)
  · have hh := hq'.2.1 e.token het
    change cut d.f (e.x,intCast e.target) e.objectiveScale q.1 ≤ q.2 at hh
    rw [hpoint] at hh
    exact hh
  · intro j
    have hh := hq'.2.2 e.token het j
    change cut (d.g j) (e.x,intCast e.target) (e.constraintScale j) q.1 ≤ 0 at hh
    rw [hpoint] at hh
    exact hh

theorem event_restoration_master_excludes (hr : Regularity d)
    {e : Event d} (he : EventValid d e) {s : RealVector m}
    (hs : e.restoration = some s) {H : List (Token n p m)} (het : e.token ∈ H) :
    ¬ ∃ q ∈ master d H, q.1.2 = intCast e.target := by
  have hm := he.2
  rw [hs] at hm
  have hempty : ¬ ∃ x ∈ d.hardFiber e.target, ∀ j, d.g j (x,intCast e.target) ≤ 0 := by
    simpa only [Data.feasibleFiber,Data.soft,Set.nonempty_def,Set.mem_setOf_eq] using hm.1
  have hex := restoration_fiber_quadratic_excludes (d.hardFiber e.target) d.g
    (intCast e.target) e.x e.constraintScale (hardFiber_convex hr.X_convex e.target)
    hr.constraint_convex hr.constraint_C2 (event_restoration_positive_minimum he hs)
    hempty (fun j => (he.1.2 j).1)
  rintro ⟨q,hq,hy⟩
  have hq' := (master_mem_iff d H q).mp hq
  have hpoint : q.1 = (q.1.1,intCast e.target) := Prod.ext rfl hy
  apply hex
  refine ⟨q.1.1,base_hard hq'.1 hy,fun j => ?_⟩
  have hh := hq'.2.2 e.token het j
  change cut (d.g j) (e.x,intCast e.target) (e.constraintScale j) q.1 ≤ 0 at hh
  rw [hpoint] at hh
  exact hh

/-- Every retained processed fiber meeting the master is feasible and supports
the actual stored NLP value. This is the geometric input to finite progress. -/
theorem event_master_same_fiber (hr : Regularity d)
    {e : Event d} (he : EventValid d e) {H : List (Token n p m)} (het : e.token ∈ H)
    {q : Point n p × ℝ} (hq : q ∈ master d H) (hy : q.1.2 = intCast e.target) :
    e.restoration = none ∧ d.f e.anchor ≤ q.2 := by
  cases hs : e.restoration with
  | none => exact ⟨rfl,event_feasible_master_lower hr he hs het hq hy⟩
  | some s => exact (event_restoration_master_excludes hr he hs het ⟨q,hq,hy⟩).elim

end Chapter05.QOA
