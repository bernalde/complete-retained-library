module

public import Chapter03FPProcedureModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPControls

abbrev P := Point 1 1
def pt (x y : ℝ) : P := (fun _ => x, fun _ => y)
def iv (y : ℤ) : IntVector 1 := fun _ => y
def xc : P →L[ℝ] ℝ := (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ _ _)
def yc : P →L[ℝ] ℝ := (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem xc_apply (p : P) : xc p = p.1 0 := rfl
@[simp] theorem yc_apply (p : P) : yc p = p.2 0 := rfl
@[simp] theorem pt_fst (x y : ℝ) (j : Fin 1) : (pt x y).1 j = x := rfl
@[simp] theorem pt_snd (x y : ℝ) (j : Fin 1) : (pt x y).2 j = y := rfl
@[simp] theorem iv_apply (y : ℤ) (j : Fin 1) : iv y j = y := rfl
theorem pt_eta (p : P) : pt (p.1 0) (p.2 0) = p := by
  apply Prod.ext <;> funext j <;> fin_cases j <;> rfl

def model (bounded : Bool) (upper shift : ℝ) : ModelData 1 1 1 2 where
  g _ p := (p.1 0)^2 + shift
  A i _ := if bounded then if i = 0 then 1 else -1 else 0
  B _ _ := 0
  rhs _ := 1
  c1 _ := 0
  c2 _ := 0
  lo _ := 0
  hi _ := upper

def data (bounded : Bool) (a b upper delta shift : ℝ) : Data 1 1 1 2 where
  model := model bounded upper shift
  f p := -a * p.1 0 + b * (p.2 0 - 1/2)^2
  Df p := (-a) • xc + (2*b*(p.2 0-1/2)) • yc
  Dg _ p := (2*p.1 0) • xc
  nonlinear := Set.univ
  delta := delta

theorem linear_mem (bounded : Bool) (upper shift : ℝ) (p : P) :
    p ∈ (model bounded upper shift).linearRegion ↔
      (bounded = true → -1 ≤ p.1 0 ∧ p.1 0 ≤ 1) := by
  cases bounded
  · simp [model, ModelData.linearRegion, LinearForm, Fin.forall_fin_two, Fin.sum_univ_one]
  · simp only [model, ModelData.linearRegion, Set.mem_setOf_eq, Fin.forall_fin_two,
      LinearForm, Fin.sum_univ_one]
    norm_num
    constructor <;> intro h <;> constructor <;> linarith

theorem base_mem (bounded : Bool) (a b upper delta shift : ℝ) (p : P) :
    p ∈ (data bounded a b upper delta shift).base ↔
      (bounded = true → -1 ≤ p.1 0 ∧ p.1 0 ≤ 1) ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ upper := by
  change (p ∈ (model bounded upper shift).linearRegion ∧
    ∀ j, 0 ≤ p.2 j ∧ p.2 j ≤ upper) ↔ _
  rw [linear_mem]
  simp only [Fin.forall_fin_one]

theorem relaxation_iff (bounded : Bool) (a b upper delta : ℝ) (p : P) :
    p ∈ (data bounded a b upper delta 0).relaxation ↔
      p.1 0 = 0 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ upper := by
  rw [relaxation_mem_iff, base_mem]
  simp only [data, model, add_zero, Fin.forall_fin_one]
  constructor
  · rintro ⟨⟨_,hy⟩,hx⟩; exact ⟨by nlinarith [sq_nonneg (p.1 0)],hy⟩
  · rintro ⟨hx,hy⟩; exact ⟨⟨by intro _; rw [hx]; norm_num,hy⟩,by rw [hx]; norm_num⟩

theorem square_deriv (L : P →L[ℝ] ℝ) (c : ℝ) (p : P) :
    HasFDerivAt (fun q => (L q-c)^2) ((2*(L p-c)) • L) p := by
  have hd := ((L.hasFDerivAt (x := p)).sub_const c).fun_mul ((L.hasFDerivAt (x := p)).sub_const c)
  simpa only [pow_two] using hd.congr_fderiv (show
    (L p-c) • L + (L p-c) • L = (2*(L p-c)) • L by
      apply ContinuousLinearMap.ext; intro q; simp; ring)

theorem f_deriv (bounded : Bool) (a b upper delta shift : ℝ) (p : P) :
    HasFDerivAt (data bounded a b upper delta shift).f
      ((data bounded a b upper delta shift).Df p) p := by
  exact ((xc.hasFDerivAt.const_mul (-a)).add ((square_deriv yc (1/2) p).const_mul b)).congr_fderiv
    (by apply ContinuousLinearMap.ext; intro q; simp [data]; ring)

theorem g_deriv (bounded : Bool) (a b upper delta shift : ℝ) (j : Fin 1) (p : P) :
    HasFDerivAt ((data bounded a b upper delta shift).model.g j)
      ((data bounded a b upper delta shift).Dg j p) p := by
  simpa [data, model] using (square_deriv xc 0 p).add_const shift

theorem square_convex {S : Set P} (hS : Convex ℝ S) (L : P →L[ℝ] ℝ) (c : ℝ) :
    ConvexOn ℝ S (fun q => (L q-c)^2) := by
  refine ⟨hS, ?_⟩
  intro p hp q hq u v hu hv huv
  simp only [map_add, map_smul, smul_eq_mul]
  have h := mul_nonneg (mul_nonneg hu hv) (sq_nonneg (L p-L q))
  have he : v = 1-u := by linarith
  subst v
  nlinarith

theorem affine_convex {S : Set P} (hS : Convex ℝ S) (L : P →L[ℝ] ℝ) (a : ℝ) :
    ConvexOn ℝ S (fun q => a*L q) := by
  refine ⟨hS, ?_⟩
  intro p hp q hq u v hu hv huv
  simp only [map_add,map_smul,smul_eq_mul]
  exact le_of_eq (by ring)

theorem analytic (bounded : Bool) (a b upper delta : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ delta) :
    Analytic (data bounded a b upper delta 0) := by
  let d := data bounded a b upper delta 0
  have hbound : Bornology.IsBounded d.relaxation := by
    apply (isCompact_Icc : IsCompact (Set.Icc (pt 0 0) (pt 0 upper))).isBounded.subset
    intro p hp
    obtain ⟨hx,hy,hU⟩ := (relaxation_iff bounded a b upper delta p).mp hp
    constructor <;> constructor <;> intro j <;> fin_cases j <;> simp [pt,hx,hy,hU]
  refine ⟨?_, ?_, ?_, ?_, hbound, hd⟩
  · exact (affine_convex (base_convex d) xc (-a)).add
      ((square_convex (base_convex d) yc (1/2)).smul hb)
  · intro j
    simpa [d,data,model] using (square_convex (base_convex d) xc 0)
  · intro p _; exact f_deriv bounded a b upper delta 0 p
  · intro j p _; exact g_deriv bounded a b upper delta 0 j p

theorem distance_formula (y : IntVector 1) (p : P) : distance y p = ((y 0 : ℝ)-p.2 0)^2 := by
  simp [distance, intY, intCast, Chapter03.yMap, PiLp.norm_sq_eq_of_L2,
    Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]

theorem l1_formula (p q : P) : l1 p q = |q.2 0-p.2 0| := by
  simp [l1, Fin.sum_univ_one]

theorem relaxation_seed (bounded : Bool) (a b upper delta : ℝ)
    (hb : 0 ≤ b) (hu : (1/2:ℝ) ≤ upper) :
    IsMinimizer (data bounded a b upper delta 0).relaxation
      (data bounded a b upper delta 0).f (pt 0 (1/2)) := by
  refine ⟨(relaxation_iff _ _ _ _ _ _).mpr ⟨rfl,by norm_num,hu⟩, ?_⟩
  intro p hp
  have hx := ((relaxation_iff _ _ _ _ _ _).mp hp).1
  simp only [data,pt_fst,pt_snd,hx,mul_zero,neg_mul,neg_zero,zero_add,sub_self]
  norm_num only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,mul_zero]
  exact mul_nonneg hb (sq_nonneg _)

theorem fiber_singleton (bounded : Bool) (a b upper delta : ℝ) (k : ℤ) :
    (data bounded a b upper delta 0).fiber (iv k) ⊆ {pt 0 k} := by
  intro p hp
  have hx := ((relaxation_iff _ _ _ _ _ _).mp hp.1).1
  have hy : p.2 0 = (k:ℝ) := congrFun hp.2 0
  rw [Set.mem_singleton_iff,← pt_eta p,hx,hy]

theorem fiber_minimum (bounded : Bool) (a b upper delta : ℝ) (k : ℤ)
    (hk : 0 ≤ (k:ℝ)) (hu : (k:ℝ) ≤ upper) :
    IsMinimizer ((data bounded a b upper delta 0).fiber (iv k))
      (data bounded a b upper delta 0).f (pt 0 k) := by
  refine ⟨⟨(relaxation_iff _ _ _ _ _ _).mpr ⟨rfl,hk,hu⟩,rfl⟩, ?_⟩
  intro p hp
  have he := fiber_singleton bounded a b upper delta k hp
  rw [show p = pt 0 k from he]

end Chapter03.FPControls
