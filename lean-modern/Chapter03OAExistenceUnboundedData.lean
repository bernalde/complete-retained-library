module

public import Chapter03OAExistenceAvailability

@[expose] public section

/-! Two tangent balls on an unbounded continuous domain. Their joint nonlinear
relaxation is one fractional point; every integer fiber is empty. This control
therefore discloses vacuous fixed-fiber LICQ and exercises genuine unbounded
master replies, rather than a feasible-fiber multiplier example. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec.UnboundedControl

abbrev P := Point 2 1
def pt (a b y : ℝ) : P := (![a,b],fun _ => y)
def cx : P →L[ℝ] ℝ := (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ _ _)
def cz : P →L[ℝ] ℝ := (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.fst ℝ _ _)
def cy : P →L[ℝ] ℝ := (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
def sign (j : Fin 2) : ℝ := if j = 0 then -2 else 2
def row (j : Fin 2) (p : P) : ℝ :=
  (p.1 0)^2 + (p.1 1)^2 + sign j * p.1 0 + (p.2 0-1/2)^2
def rowD (p : P) (j : Fin 2) : P →L[ℝ] ℝ :=
  (2*p.1 0+sign j) • cx + (2*p.1 1) • cz + (2*(p.2 0-1/2)) • cy
def model : ModelData 2 1 2 0 where
  g := row
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := ![0,1]
  c2 := 0
  lo := 0
  hi := 1
def spec : Data 2 1 2 0 where
  model := model
  f := cz
  Df _ := cz
  Dg := rowD
  domain := cy ⁻¹' Set.Icc 0 1
def seed : P := pt 0 0 (1/2)
def bounds : Bounds 2 := ⟨fun _ => .negInfinity,fun _ => .posInfinity⟩
def target (b : Fin 2) : IntVector 1 := fun _ => (b.val : ℤ)

@[simp] theorem cx_apply (p : P) : cx p = p.1 0 := rfl
@[simp] theorem cz_apply (p : P) : cz p = p.1 1 := rfl
@[simp] theorem cy_apply (p : P) : cy p = p.2 0 := rfl

theorem square_derivative (L : P →L[ℝ] ℝ) (a : ℝ) (p : P) :
    HasFDerivAt (fun q => (L q-a)^2) ((2*(L p-a)) • L) p := by
  have h := L.hasFDerivAt.sub_const a (x := p)
  convert h.mul h using 1
  · ext q
    exact pow_two (L q-a)
  · apply ContinuousLinearMap.ext
    intro v
    simp [two_mul,add_mul]

theorem row_derivative (j : Fin 2) (p : P) : HasFDerivAt (row j) (rowD p j) p := by
  have h := ((square_derivative cx 0 p).add (square_derivative cz 0 p)).add
    (cx.hasFDerivAt.const_mul (sign j) (x := p))
  convert h.add (square_derivative cy (1/2) p) using 1
  · ext q
    simp [row]
  · apply ContinuousLinearMap.ext
    intro v
    simp [rowD,add_mul]
    ring

theorem objective_C1 : ContDiff ℝ 1 spec.f := cz.contDiff
theorem rows_C1 (j : Fin 2) : ContDiff ℝ 1 (model.g j) := by
  change ContDiff ℝ 1 (row j)
  unfold row
  fun_prop

theorem square_convex (L : P →L[ℝ] ℝ) (a : ℝ) :
    ConvexOn ℝ Set.univ (fun p => (L p-a)^2) := by
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  simp only [map_add,map_smul,smul_eq_mul]
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (L p-L q))
  have he : t = 1-s := by linarith
  rw [he] at h ⊢
  nlinarith only [h]

theorem row_convex (j : Fin 2) : ConvexOn ℝ Set.univ (row j) := by
  have h := ((square_convex cx 0).add (square_convex cz 0)).add
    ((sign j • cx).toLinearMap.convexOn convex_univ)
  convert h.add (square_convex cy (1/2)) using 1
  ext p
  simp [row]

theorem domain_convex : Convex ℝ spec.domain :=
  (convex_Icc (0 : ℝ) 1).linear_preimage cy.toLinearMap

theorem relaxation_iff (p : P) : p ∈ spec.relaxation ↔ p = seed := by
  rw [relaxation_mem_iff]
  constructor
  · rintro ⟨hg,_,_⟩
    have h0 := hg 0
    have h1 := hg 1
    norm_num [spec,model,row,sign] at h0 h1
    have ha : p.1 0 = 0 := by nlinarith [sq_nonneg (p.1 1),sq_nonneg (p.2 0-1/2),sq_nonneg (p.1 0)]
    have hb : p.1 1 = 0 := by nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.2 0-1/2),sq_nonneg (p.1 1)]
    have hy : p.2 0 = 1/2 := by nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.1 1),sq_nonneg (p.2 0-1/2)]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [seed,pt,ha,hb]
    · ext i
      fin_cases i
      simpa [seed,pt] using hy
  · rintro rfl
    refine ⟨?_,?_,?_⟩
    · intro j
      fin_cases j <;> norm_num [spec,model,row,seed,pt,sign]
    · intro i; exact Fin.elim0 i
    · intro j
      norm_num [spec,model,seed,pt]

theorem relaxation_singleton : spec.relaxation = {seed} := by
  ext p
  exact relaxation_iff p

theorem seed_domain : seed ∈ spec.domain := by norm_num [spec,seed,pt]
theorem seed_minimum : IsMinimizer spec.relaxation spec.f seed := by
  refine ⟨(relaxation_iff seed).mpr rfl,?_⟩
  intro p hp
  rw [(relaxation_iff p).mp hp]

theorem target_mem (b : Fin 2) : target b ∈ IntegerBox model.lo model.hi := by
  fin_cases b <;> norm_num [IntegerBox,model,target]

theorem target_cases (y : IntVector 1) (hy : y ∈ IntegerBox model.lo model.hi) :
    y = target 0 ∨ y = target 1 := by
  have hh := hy 0
  change (0 : ℝ) ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 1 at hh
  have hi : y 0 = 0 ∨ y 0 = 1 := by exact_mod_cast (show (y 0 : ℝ) = 0 ∨ (y 0 : ℝ) = 1 by
    have h0 : (0 : ℤ) ≤ y 0 := by exact_mod_cast hh.1
    have h1 : y 0 ≤ (1 : ℤ) := by exact_mod_cast hh.2
    rcases (show y 0 = 0 ∨ y 0 = 1 by omega) with h | h <;> simp [h])
  rcases hi with h | h
  · left; ext i; fin_cases i; simpa [target] using h
  · right; ext i; fin_cases i; simpa [target] using h

theorem seed_fractional : ¬ integral seed := by
  rintro ⟨y,hy⟩
  have h := congrFun hy 0
  change (1/2 : ℝ) = (y 0 : ℝ) at h
  have hlo : (0 : ℤ) < y 0 := by exact_mod_cast (show (0 : ℝ) < (y 0 : ℝ) by linarith)
  have hhi : y 0 < (1 : ℤ) := by exact_mod_cast (show (y 0 : ℝ) < 1 by linarith)
  omega

theorem original_empty : ¬ spec.original.Nonempty := by
  rintro ⟨p,hp⟩
  have he := (relaxation_iff p).mp (original_subset_relaxation spec hp)
  have hi := ((source_feasible_iff model Set.univ p).mp hp).2.2.2
  exact seed_fractional (he ▸ ⟨hi.choose,hi.choose_spec.2⟩)

theorem analytic : Analytic spec where
  convex_f := cz.toLinearMap.convexOn domain_convex
  convex_g j := (row_convex j).subset (Set.subset_univ _) domain_convex
  original_domain p hp := False.elim (original_empty ⟨p,hp⟩)
  derivative_f _ _ := cz.hasFDerivAt
  derivative_g p _ j := row_derivative j p

theorem seed_valid : SeedValid spec seed := ⟨seed_minimum,seed_domain,seed_fractional⟩

def bounds_encoding : HardBoundEncoding bounds model where
  valid := by intro i; simp [Bounds.Valid,bounds]
  side := Fin.elim0
  injective := Function.injective_of_subsingleton _
  lower_cover := by intro i a h; cases h
  upper_cover := by intro i a h; cases h
  row_spec := by intro j; exact Fin.elim0 j

theorem domain_article : spec.domain = articleDomain bounds spec := by
  ext p
  simp [spec,articleDomain,bounds,Bounds.region,ExtendedBound.lowerHolds,
    ExtendedBound.upperHolds,model,Fin.forall_fin_one]

theorem bounded_relaxation : Bornology.IsBounded spec.relaxation := by
  rw [relaxation_singleton]
  exact Bornology.isBounded_singleton

theorem fibers_empty (y : IntVector 1) (hy : y ∈ IntegerBox model.lo model.hi) :
    ¬ (fiber model (intCast y)).Nonempty := by
  rintro ⟨x,hx⟩
  exact original_empty ⟨(x,intCast y),(fiber_original_iff model y hy x).mp hx⟩

/-- This example has no nonempty integer fiber; uniform fixed LICQ is vacuous. -/
theorem fixed_licq (y : IntVector 1) (hy : y ∈ IntegerBox model.lo model.hi)
    (x : RealVector 2)
    (hm : IsMinimizer (fiber model (intCast y)) (fiberObjective spec.f (intCast y)) x) :
    FixedLICQ model x (intCast y) (spec.Dg (x,intCast y)) :=
  False.elim (fibers_empty y hy ⟨x,hm.1⟩)

theorem assumptions : AvailabilityAssumptions spec :=
  article_availability_assumptions bounds spec bounds_encoding analytic domain_article
    bounded_relaxation fixed_licq

end Chapter03.OAExec.UnboundedControl

#print axioms Chapter03.OAExec.UnboundedControl.assumptions
