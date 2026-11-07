module

public import Chapter03OAExistenceAvailability
public import Chapter03OAExecArticleReturns

@[expose] public section

/-! Explicit source-domain adapters for previously accepted article controls.
The old Data values use Set.univ as their support domain. Restriction below
changes that field explicitly; it does not change the model, functions, stored
derivatives or feasible sets. Old execution traces are not silently retyped. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article.Source

def onHardDomain {n m l r : ℕ} (d : Data n m l r) : Data n m l r :=
  { d with domain := (asFP d).base }

theorem onHardDomain_data {n m l r : ℕ} (d : Data n m l r) :
    (onHardDomain d).model = d.model ∧ (onHardDomain d).f = d.f ∧
    (onHardDomain d).Df = d.Df ∧ (onHardDomain d).Dg = d.Dg ∧
    (onHardDomain d).original = d.original ∧
    (onHardDomain d).relaxation = d.relaxation ∧
    (onHardDomain d).box = d.box ∧ (onHardDomain d).nonlinear = d.nonlinear ∧
    (onHardDomain d).selected = d.selected ∧ asFP (onHardDomain d) = asFP d := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem onHardDomain_base {n m l r : ℕ} (d : Data n m l r) :
    (onHardDomain d).domain = (asFP (onHardDomain d)).base := rfl

theorem onHardDomain_analytic {n m l r : ℕ} (d : Data n m l r)
    (a : Analytic d) (hdom : d.domain = Set.univ) : Analytic (onHardDomain d) where
  convex_f := by
    have hf : ConvexOn ℝ Set.univ d.f := hdom ▸ a.convex_f
    exact hf.subset (Set.subset_univ _) (Chapter03.FP.base_convex (asFP d))
  convex_g j := by
    have hg : ConvexOn ℝ Set.univ (d.model.g j) := hdom ▸ a.convex_g j
    exact hg.subset (Set.subset_univ _) (Chapter03.FP.base_convex (asFP d))
  original_domain p hp := Chapter03.FP.relaxation_subset_base (asFP d)
    (original_subset_relaxation d hp)
  derivative_f p _ := a.derivative_f p (by rw [hdom]; trivial)
  derivative_g p _ j := a.derivative_g p (by rw [hdom]; trivial) j

def interval (a b : ℝ) : Bounds 1 where
  lower := fun _ => .finite a
  upper := fun _ => .finite b

def boxEncoding (a b : ℝ) (g : P → ℝ) :
    HardBoundEncoding (interval a b) (boxModel a b g) where
  valid := by intro i; simp [interval]
  side := ![Sum.inl 0, Sum.inr 0]
  injective := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  lower_cover := by intro i c h; fin_cases i; exact ⟨0,rfl⟩
  upper_cover := by intro i c h; fin_cases i; exact ⟨1,rfl⟩
  row_spec := by
    intro i; fin_cases i
    · refine ⟨a,rfl,?_⟩
      intro p
      simp [linearResidual,boxModel,LinearForm,scalar,Fin.sum_univ_one]
      ring
    · refine ⟨b,rfl,?_⟩
      intro p
      simp [linearResidual,boxModel,LinearForm,scalar,Fin.sum_univ_one]

theorem box_relaxation_bounded (a b : ℝ) (g : P → ℝ) :
    Bornology.IsBounded ((boxModel a b g).relaxationOn Set.univ) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (pt a 0) (pt b 1))).isBounded.subset
  intro p hp
  obtain ⟨hxl,hxu,hyl,hyu,_⟩ := (box_relaxation a b g p).mp hp
  constructor
  · constructor
    · intro i; fin_cases i; exact hxl
    · intro i; fin_cases i; exact hyl
  · constructor
    · intro i; fin_cases i; exact hxu
    · intro i; fin_cases i; exact hyu

theorem quadratic_C1 (a : ℝ) : ContDiff ℝ 1 (quadratic a) := by
  unfold quadratic
  fun_prop

theorem linearQuadratic_C1 (a : ℝ) : ContDiff ℝ 1 (linearQuadratic a) := by
  unfold linearQuadratic
  fun_prop

theorem xSquareRow_C1 (c : ℝ) : ContDiff ℝ 1 (xSquareRow c) := by
  unfold xSquareRow
  fun_prop

theorem original_domains_mismatch :
    Gdata.domain ≠ (asFP Gdata).base ∧ Tdata.domain ≠ (asFP Tdata).base ∧
    EmptyData.domain ≠ (asFP EmptyData).base ∧
    IntegralData.domain ≠ (asFP IntegralData).base := by
  have h (d : Data 1 1 1 2) (hd : d.domain = Set.univ)
      (hh : ∀ p, p ∈ d.model.linearRegion → p.1 0 ≤ 1) :
      d.domain ≠ (asFP d).base := by
    intro he
    have hp : pt 2 0 ∈ d.domain := by rw [hd]; trivial
    rw [he] at hp
    have hb := hh _ hp.1
    norm_num [pt,scalar] at hb
  refine ⟨h Gdata rfl ?_,h Tdata rfl ?_,h EmptyData rfl ?_,h IntegralData rfl ?_⟩
  all_goals intro p hp; exact ((box_hard _ _ _ p).mp hp).2

theorem T_fiber_minimum_unique (y : V) (x : V)
    (h : IsMinimizer (fiber T y) (fiberObjective Tf y) x) : x = scalar 0 := by
  have hm := h.2 (scalar 0) (T_fiber_minimum y).1
  have hl := ((T_fiber y x).mp h.1).1
  have hx : x 0 = 0 := by
    simp only [fiberObjective,Tf,linearQuadratic,scalar,zero_add] at hm
    linarith
  ext i; fin_cases i; exact hx

theorem T_active_iff (y : V) (i : Fin 1 ⊕ Fin 2) :
    fixedRows T y i (scalar 0) = 0 ↔ i = Sum.inr 0 := by
  rcases i with j | j
  · fin_cases j
    norm_num [fixedRows,soft,T,boxModel,xSquareRow,scalar]
  · fin_cases j <;>
      norm_num [fixedRows,hard,linearResidual,T,boxModel,LinearForm,scalar,
        Fin.sum_univ_one]

theorem T_fixed_LICQ (y : V) : FixedLICQ T (scalar 0) y (Tdg (scalar 0,y)) := by
  letI : Unique {i : Fin 1 ⊕ Fin 2 // fixedRows T y i (scalar 0) = 0} := {
    default := ⟨Sum.inr 0, (T_active_iff y _).mpr rfl⟩
    uniq := fun i => Subtype.ext ((T_active_iff y i.val).mp i.property) }
  apply linearIndependent_unique_iff.mpr
  intro hz
  change fiberLinearRow T 0 = 0 at hz
  have hh := congrArg (fun D : V →L[ℝ] ℝ => D (scalar 1)) hz
  norm_num [fixedRowD,fiberLinearRow_apply,LinearForm,T,boxModel,scalar,
    Fin.sum_univ_one] at hh

theorem G_all_minimizer_LICQ (y : V) (x : V)
    (hm : IsMinimizer (fiber G y) (fiberObjective Gf y) x) :
    FixedLICQ G x y (Gdg (x,y)) := by
  rw [G_fiber_minimum_unique y x hm]
  have he : {i : Fin 1 ⊕ Fin 2 | fixedRows G y i (scalar 0) = 0} = G_active y := by
    ext i; cases i <;> rfl
  letI : IsEmpty {i : Fin 1 ⊕ Fin 2 // fixedRows G y i (scalar 0) = 0} := ⟨by
    intro i
    have hi : i.val ∈ G_active y := by rw [← he]; exact i.property
    rw [G_active_empty] at hi
    exact hi⟩
  exact linearIndependent_empty_type

theorem T_all_minimizer_LICQ (y : V) (x : V)
    (hm : IsMinimizer (fiber T y) (fiberObjective Tf y) x) :
    FixedLICQ T x y (Tdg (x,y)) := by
  rw [T_fiber_minimum_unique y x hm]
  exact T_fixed_LICQ y

theorem Integral_fiber_minimum_unique (y : V) (x : V)
    (hm : IsMinimizer (fiber G y) (fiberObjective IntegralF y) x) : x = scalar 0 := by
  have hh := hm.2 (scalar 0) (G_fiber_minimum y).1
  have hx : x 0 = 0 := by
    norm_num [fiberObjective,IntegralF,quadratic,scalar] at hh
    nlinarith [sq_nonneg (x 0)]
  ext i; fin_cases i; exact hx

theorem Integral_all_minimizer_LICQ (y : V) (x : V)
    (hm : IsMinimizer (fiber G y) (fiberObjective IntegralF y) x) :
    FixedLICQ G x y (Gdg (x,y)) := by
  rw [Integral_fiber_minimum_unique y x hm]
  exact G_all_minimizer_LICQ y (scalar 0) (G_fiber_minimum y)

end Chapter03.OAExec.Article.Source

#print axioms Chapter03.OAExec.Article.Source.original_domains_mismatch
#print axioms Chapter03.OAExec.Article.Source.G_all_minimizer_LICQ
#print axioms Chapter03.OAExec.Article.Source.T_all_minimizer_LICQ
#print axioms Chapter03.OAExec.Article.Source.Integral_all_minimizer_LICQ
