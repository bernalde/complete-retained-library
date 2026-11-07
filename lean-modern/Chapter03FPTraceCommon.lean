module

public import Chapter03FPProcedureModel
public import Chapter03FPAdapters

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPTrace

variable {n : ℕ}

def y0 : Point n 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 2)).comp (ContinuousLinearMap.snd ℝ (RealVector n) (RealVector 2))
def y1 : Point n 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (1 : Fin 2)).comp (ContinuousLinearMap.snd ℝ (RealVector n) (RealVector 2))
def x0 : Point 1 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector 2))

@[simp] theorem y0_apply (p : Point n 2) : y0 p = p.2 0 := rfl
@[simp] theorem y1_apply (p : Point n 2) : y1 p = p.2 1 := rfl
@[simp] theorem x0_apply (p : Point 1 2) : x0 p = p.1 0 := rfl

/-- Generic finite-dimensional helper, independently reproved for these controls.
The scalar-control lane uses the same elementary derivative/Jensen pattern. -/
theorem square_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (c : ℝ) (p : E) :
    HasFDerivAt (fun q => (L q-c)^2) ((2*(L p-c)) • L) p := by
  have h := ((L.hasFDerivAt (x := p)).sub_const c).fun_mul ((L.hasFDerivAt (x := p)).sub_const c)
  simpa only [pow_two] using h.congr_fderiv (show
    (L p-c) • L+(L p-c) • L=(2*(L p-c)) • L by
      apply ContinuousLinearMap.ext
      intro q
      simp
      ring)

theorem square_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (L : E →L[ℝ] ℝ) (c : ℝ) :
    ConvexOn ℝ S (fun p => (L p-c)^2) := by
  refine ⟨hS,?_⟩
  intro p hp q hq a b ha hb hab
  simp only [map_add,map_smul,smul_eq_mul]
  have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (L p-L q))
  have he : b=1-a := by linarith
  subst b
  nlinarith

theorem linear_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (L : E →L[ℝ] ℝ) : ConvexOn ℝ S L := by
  refine ⟨hS,?_⟩
  intro p hp q hq a b ha hb hab
  simp only [map_add,map_smul,smul_eq_mul,le_refl]

theorem distance_two (y : IntVector 2) (p : Point n 2) :
    distance y p=((y 0:ℝ)-p.2 0)^2+((y 1:ℝ)-p.2 1)^2 := by
  rw [distance,EuclideanSpace.real_norm_sq_eq]
  simp [Chapter03.yMap,intY,intCast,Fin.sum_univ_two]

theorem normal_two (e : Event n 2) (p : Point n 2) :
    e.normal p=(e.projection.2 0-(e.target 0:ℝ))*(p.2 0-e.projection.2 0)+
      (e.projection.2 1-(e.target 1:ℝ))*(p.2 1-e.projection.2 1) := by
  simp [Event.normal,Chapter03.yMap,intY,intCast,PiLp.inner_apply,
    Fin.sum_univ_two,real_inner_eq_re_inner]
  ring

theorem l1_two (a p : Point n 2) :
    l1 a p=|p.2 0-a.2 0|+|p.2 1-a.2 1| := by simp [l1,Fin.sum_univ_two]

def corner (a b : ℤ) : IntVector 2 := ![a,b]

theorem integer_corner_cases (y : IntVector 2)
    (h : ∀ j, (0:ℝ) ≤ (y j:ℝ) ∧ (y j:ℝ) ≤ 1) :
    y=corner 0 0 ∨ y=corner 0 1 ∨ y=corner 1 0 ∨ y=corner 1 1 := by
  have h0 : 0 ≤ y 0 ∧ y 0 ≤ 1 := by exact_mod_cast h 0
  have h1 : 0 ≤ y 1 ∧ y 1 ≤ 1 := by exact_mod_cast h 1
  have hy0 : y 0=0 ∨ y 0=1 := by omega
  have hy1 : y 1=0 ∨ y 1=1 := by omega
  have extc : ∀ a b, y 0=a → y 1=b → y=corner a b := by
    intro a b ha hb
    funext j
    fin_cases j <;> simp [corner,ha,hb]
  rcases hy0 with ha|ha <;> rcases hy1 with hb|hb
  · exact Or.inl (extc _ _ ha hb)
  · exact Or.inr (Or.inl (extc _ _ ha hb))
  · exact Or.inr (Or.inr (Or.inl (extc _ _ ha hb)))
  · exact Or.inr (Or.inr (Or.inr (extc _ _ ha hb)))

end Chapter03.FPTrace
