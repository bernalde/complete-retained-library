module

public import Chapter02LiftingSource
public import Chapter02LiftingOA
public import Chapter02LiftingEnvelope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! Full-set hypothesis and boundary controls for the cleared lifting scope.
These are mathematical examples, not measurements or source theorem promotion. -/
noncomputable section
open scoped BigOperators
namespace Chapter02.LiftingExamples

theorem square_convex : ConvexOn ℝ Set.univ (fun x : ℝ => x^2) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ s t hs ht hst
  have hp := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x-y))
  have hteq : t = 1-s := by linarith
  simp only [smul_eq_mul]
  rw [hteq] at hp ⊢
  nlinarith

theorem square_derivative (x : ℝ) :
    HasFDerivAt (fun z : ℝ => z^2) ((2*x) • (1 : ℝ →L[ℝ] ℝ)) x := by
  convert (hasDerivAt_pow 2 x).hasFDerivAt using 1
  ext
  simp [mul_comm]

def mOriginal := liftingOriginal (Set.Icc (-1:ℝ) 1) (fun x => x^2) (fun y => 1-y) 0
def mLift := liftingSet (Set.Icc (-1:ℝ) 1) Set.univ (fun x => x^2) (fun y => 1-y) 0

theorem m_original_iff (x : ℝ) : x ∈ mOriginal ↔ x = -1 ∨ x = 1 := by
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hf⟩
    change 1-x^2 ≤ 0 at hf
    have hs : x^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (sub_nonneg.mpr hlo)]
    have hz : (x-1)*(x+1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h <;> [right;left] <;> linarith
  · rintro (rfl | rfl) <;> norm_num [mOriginal,liftingOriginal]

theorem m_full_control :
    ConvexOn ℝ Set.univ (fun x : ℝ => x^2) ∧
    ConvexOn ℝ Set.univ (fun y : ℝ => 1-y) ∧
    (∀ x : ℝ, HasFDerivAt (fun z : ℝ => z^2) ((2*x) • (1 : ℝ →L[ℝ] ℝ)) x) ∧
    (∀ y : ℝ, HasDerivAt (fun z : ℝ => 1-z) (-1) y) ∧
    ¬ Monotone (fun y : ℝ => 1-y) ∧
    (0,1) ∈ mLift ∧ 0 ∉ mOriginal := by
  refine ⟨square_convex,?_,square_derivative,?_,?_,?_,?_⟩
  · refine ⟨convex_univ,?_⟩
    intro x _ y _ s t _ _ hst
    simp only [smul_eq_mul]
    nlinarith
  · intro y; simpa using (hasDerivAt_const y (1:ℝ)).fun_sub (hasDerivAt_id y)
  · intro h; have hh := h (show (0:ℝ) ≤ 1 by norm_num); norm_num at hh
  · norm_num [mLift,liftingSet]
  · norm_num [m_original_iff]

def dOriginal := liftingOriginal (Set.Icc (-1:ℝ) 1) (fun x => x^2) id 1
def dLift := liftingSet (Set.Icc (-1:ℝ) 1) Set.univ (fun x => x^2) id 1
def dUnsafe : Set (ℝ × ℝ) := {z | z ∈ dLift ∧ z.2 ≤ 1/4}

theorem d_original_minimum : IsMinimizer dOriginal (fun x => -x) 1 := by
  refine ⟨by norm_num [dOriginal,liftingOriginal],?_⟩
  intro x hx
  exact neg_le_neg hx.1.2

theorem d_unsafe_minimum : IsMinimizer dUnsafe (fun z => -z.1) (1/2,1/4) := by
  refine ⟨by norm_num [dUnsafe,dLift,liftingSet],?_⟩
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  have hs : x^2 ≤ y := hx.2.2.1
  change -(1/2:ℝ) ≤ -x
  nlinarith [sq_nonneg (x-1/2)]

theorem d_safe_projection :
    Prod.fst '' liftingSet (Set.Icc (-1:ℝ) 1) (Set.Icc 0 1) (fun x => x^2) id 1 = dOriginal := by
  apply lifting_projection
  · intro x hx
    refine ⟨sq_nonneg x,?_⟩
    change x^2 ≤ 1
    have hlo := hx.1
    have hhi := hx.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (sub_nonneg.mpr hlo)]
  · intro x _ y _ hxy; exact hxy

theorem d_bound_deletion_control : (1,1) ∈ dLift ∧
    (¬ ∃ y, (1,y) ∈ dUnsafe) ∧
    IsMinimizer dOriginal (fun x => -x) 1 ∧
    IsMinimizer dUnsafe (fun z => -z.1) (1/2,1/4) := by
  refine ⟨by norm_num [dLift,liftingSet],?_,d_original_minimum,d_unsafe_minimum⟩
  rintro ⟨y,hy⟩
  have hs : (1:ℝ)^2 ≤ y := hy.1.2.2.1
  have hb := hy.2
  norm_num at hs hb
  linarith

def hG (x : ℝ) : RealVector 1 := fun _ => x^2
def hDg (x : ℝ) : ℝ →L[ℝ] RealVector 1 :=
  ContinuousLinearMap.pi (fun _ => (2*x) • (1 : ℝ →L[ℝ] ℝ))
def hOuter : RealVector 1 → ℝ := fun y => y 0
def hDh : RealVector 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0

theorem h_component_derivative (x : ℝ) : HasFDerivAt hG (hDg x) x :=
  hasFDerivAt_pi.mpr (fun _ => square_derivative x)

theorem h_mismatched_histories :
    (2,fun _ => 0) ∈ liftingSharedOA (Set.Icc (-2:ℝ) 2) Set.univ hG hOuter
      (fun _ : Fin 1 => 0) (fun _ => hDg 0) (fun _ => hDh) 1 ∧
    (2:ℝ) ∉ liftingDirectOA (Set.Icc (-2:ℝ) 2) hG hOuter
      (fun _ : Fin 1 => 2) (fun _ => hDg 2) (fun _ => hDh) 1 := by
  constructor
  · norm_num [liftingSharedOA,liftingComponentRow,liftingOuterRow,hG,hDg,hOuter,hDh,Pi.le_def]
  · norm_num [liftingDirectOA,liftingDirectRow,hG,hDg,hOuter,hDh]

theorem h_both_valid_outer :
    liftingOriginal (Set.Icc (-2:ℝ) 2) hG hOuter 1 ⊆
      Prod.fst '' liftingSharedOA (Set.Icc (-2:ℝ) 2) Set.univ hG hOuter
        (fun _ : Fin 1 => 0) (fun _ => hDg 0) (fun _ => hDh) 1 ∧
    liftingOriginal (Set.Icc (-2:ℝ) 2) hG hOuter 1 ⊆
      liftingDirectOA (Set.Icc (-2:ℝ) 2) hG hOuter
        (fun _ : Fin 1 => 2) (fun _ => hDg 2) (fun _ => hDh) 1 := by
  constructor
  · intro x hx
    refine ⟨(x,fun _ => x^2),?_,rfl⟩
    refine ⟨hx.1,Set.mem_univ _,fun _ => ⟨?_,?_⟩⟩
    · intro j; simpa [liftingComponentRow,hG,hDg] using sq_nonneg x
    · simpa [liftingOuterRow,hG,hOuter,hDh] using hx.2
  · intro x hx
    refine ⟨hx.1,fun _ => ?_⟩
    have hb : x^2 ≤ 1 := hx.2
    simp [liftingDirectRow,hG,hDg,hOuter,hDh]
    nlinarith [sq_nonneg (x-2)]

theorem empty_domain_control :
    liftingSet (∅ : Set ℝ) Set.univ (fun x => x^2) id 1 = ∅ := by
  ext z; simp [liftingSet]

theorem nonsmooth_epigraph_control (x t : ℝ) :
    (x,t) ∈ EpigraphLift Set.univ (fun z : ℝ => |z|) ↔
      ∃ y ∈ Set.Ici (0:ℝ), |x| ≤ y ∧ y ≤ t := by
  constructor
  · rintro ⟨_,h⟩; exact ⟨|x|,abs_nonneg x,le_rfl,h⟩
  · rintro ⟨y,_,hxy,hyt⟩; exact ⟨Set.mem_univ _,hxy.trans hyt⟩

theorem nonsmooth_zero_witness :
    (0,0) ∈ EpigraphLift Set.univ (fun z : ℝ => |z|) ∧
    (0,0) ∈ liftingSet Set.univ (Set.Ici (0:ℝ)) abs id 0 := by
  norm_num [EpigraphLift,liftingSet]

def expOuter (y : RealVector 2) : ℝ := y 0 + Real.exp (y 1)
def expOuterDerivative (y : RealVector 2) : RealVector 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0) + Real.exp (y 1) • (ContinuousLinearMap.proj 1)

theorem exp_outer_derivative (y : RealVector 2) :
    HasFDerivAt expOuter (expOuterDerivative y) y := by
  exact (ContinuousLinearMap.proj (0:Fin 2) : RealVector 2 →L[ℝ] ℝ).hasFDerivAt.add
    (ContinuousLinearMap.proj (1:Fin 2) : RealVector 2 →L[ℝ] ℝ).hasFDerivAt.exp

theorem exp_outer_monotone : Monotone expOuter := by
  intro x y hxy
  exact add_le_add (hxy 0) (Real.exp_le_exp.mpr (hxy 1))

theorem exp_outer_convex : ConvexOn ℝ Set.univ expOuter := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ s t hs ht hst
  have hh := convexOn_exp.2 (Set.mem_univ (x 1)) (Set.mem_univ (y 1)) hs ht hst
  simp only [expOuter,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at *
  nlinarith

def expAnchor : RealVector 2 := ![-Real.exp 1,1]

theorem exp_fullspace_control :
    HasFDerivAt expOuter (expOuterDerivative expAnchor) expAnchor ∧
    Monotone (expOuterDerivative expAnchor) ∧
    expOuterDerivative expAnchor (Pi.single 0 1) = 1 ∧
    1 < expOuterDerivative expAnchor (Pi.single 1 1) ∧
    (expAnchor,expAnchor) ∈ liftingSet Set.univ Set.univ id expOuter 0 := by
  refine ⟨exp_outer_derivative _,lifting_monotone_derivative exp_outer_monotone
    (exp_outer_derivative _),?_,?_,?_⟩
  · norm_num [expOuterDerivative,Pi.single_apply]
  · simp [expOuterDerivative,Pi.single_apply,expAnchor,Real.one_lt_exp_iff]
  · simp [liftingSet,expOuter,expAnchor]

theorem exp_matched_oa_nonvacuity :
    (expAnchor,expAnchor) ∈ liftingSharedOA Set.univ Set.univ id expOuter
      (fun _ : Fin 1 => expAnchor) (fun _ => 1) (fun _ => expOuterDerivative expAnchor) 0 ∧
    Prod.fst '' liftingSharedOA Set.univ Set.univ id expOuter
      (fun _ : Fin 1 => expAnchor) (fun _ => 1) (fun _ => expOuterDerivative expAnchor) 0 ⊆
      liftingDirectOA Set.univ id expOuter (fun _ : Fin 1 => expAnchor)
        (fun _ => 1) (fun _ => expOuterDerivative expAnchor) 0 ∧
    HasFDerivAt (expOuter ∘ id)
      ((expOuterDerivative expAnchor).comp (1 : RealVector 2 →L[ℝ] RealVector 2)) expAnchor := by
  have hc : ∀ j : Fin 2, ConvexOn ℝ Set.univ (fun x : RealVector 2 => x j) := by
    intro j
    refine ⟨convex_univ,?_⟩
    intro x _ y _ s t _ _ _
    simp
  refine ⟨?_,lifting_fullspace_shared_subset_direct Set.univ Set.univ id expOuter
    (fun _ : Fin 1 => expAnchor) (fun _ => 1) (fun _ => expOuterDerivative expAnchor) 0
    exp_outer_monotone (fun _ => exp_outer_derivative _),?_⟩
  · apply lifting_exact_subset_shared Set.univ Set.univ id expOuter
      (fun _ : Fin 1 => expAnchor) (fun _ => 1) (fun _ => expOuterDerivative expAnchor) 0
      (fun _ _ => Set.mem_univ _) hc exp_outer_convex (fun _ => Set.mem_univ _)
      (fun _ => hasFDerivAt_id _) (fun _ => exp_outer_derivative _)
    exact exp_fullspace_control.2.2.2.2
  · exact lifting_chain_rule id expOuter expAnchor 1 (expOuterDerivative expAnchor)
      (hasFDerivAt_id _) (exp_outer_derivative _)

theorem empty_support_finite_objective_minimum :
    IsMinimizer
      (liftingSupportSet (Set.Icc (-1:ℝ) 1) (fun (_ : Fin 1) (_ : Unit) (_ : ℝ) => 0)
        (fun _ => []) (-5)) (fun z => -z.1) (1,fun _ => -5) := by
  refine ⟨?_,?_⟩
  · norm_num [liftingSupportSet,pscEnvelopeRows,Fin.sum_univ_one]
  · intro z hz
    exact neg_le_neg hz.1.2

theorem zero_component_budget_control :
    (∃ y, (0,y) ∈ liftingSupportSet (Set.Icc (-1:ℝ) 1)
      (fun (_ : Fin 0) (_ : Unit) (_ : ℝ) => 0) (fun _ => []) 0) ∧
    ¬ ∃ y, (0,y) ∈ liftingSupportSet (Set.Icc (-1:ℝ) 1)
      (fun (_ : Fin 0) (_ : Unit) (_ : ℝ) => 0) (fun _ => []) (-1) := by
  norm_num [liftingSupportSet]

end Chapter02.LiftingExamples

#print axioms Chapter02.LiftingExamples.square_convex
#print axioms Chapter02.LiftingExamples.square_derivative
#print axioms Chapter02.LiftingExamples.m_original_iff
#print axioms Chapter02.LiftingExamples.m_full_control
#print axioms Chapter02.LiftingExamples.d_original_minimum
#print axioms Chapter02.LiftingExamples.d_unsafe_minimum
#print axioms Chapter02.LiftingExamples.d_safe_projection
#print axioms Chapter02.LiftingExamples.d_bound_deletion_control
#print axioms Chapter02.LiftingExamples.h_component_derivative
#print axioms Chapter02.LiftingExamples.h_mismatched_histories
#print axioms Chapter02.LiftingExamples.h_both_valid_outer
#print axioms Chapter02.LiftingExamples.empty_domain_control
#print axioms Chapter02.LiftingExamples.nonsmooth_epigraph_control
#print axioms Chapter02.LiftingExamples.nonsmooth_zero_witness
#print axioms Chapter02.LiftingExamples.exp_outer_derivative
#print axioms Chapter02.LiftingExamples.exp_outer_monotone
#print axioms Chapter02.LiftingExamples.exp_outer_convex
#print axioms Chapter02.LiftingExamples.exp_fullspace_control
#print axioms Chapter02.LiftingExamples.exp_matched_oa_nonvacuity
#print axioms Chapter02.LiftingExamples.empty_support_finite_objective_minimum
#print axioms Chapter02.LiftingExamples.zero_component_budget_control
