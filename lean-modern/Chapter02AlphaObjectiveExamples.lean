module

public import Chapter02AlphaSource
public import Chapter02AlphaObjectiveSource
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

@[expose] public section

/-! Full rational-objective controls. The nonlinear objective is separate from
the ModelData linear-objective fields. The integer coordinate is genuinely
retained but fixed at zero; no combinatorial-search guarantee is asserted. -/
noncomputable section
open Chapter02
namespace Chapter02AlphaObjectiveExamples

def point (x₁ x₂ x₃ y : ℝ) : Point 3 1 := (fun i => if i.val=0 then x₁ else if i.val=1 then x₂ else x₃, fun _ => y)
@[simp] private theorem point₀ (s t u y : ℝ) : (point s t u y).1 0 = s := rfl
@[simp] private theorem point₁ (s t u y : ℝ) : (point s t u y).1 1 = t := rfl
@[simp] private theorem point₂ (s t u y : ℝ) : (point s t u y).1 2 = u := rfl
def radius (p : Point 3 1) : ℝ := (p.1 0)^2 + (p.1 1)^2 + (p.1 2)^2
def objective (c : ℝ) (p : Point 3 1) : ℝ := c * radius p / (1/100 + radius p)
def coord (i : Fin 3) : Point 3 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (RealVector 3) (RealVector 1))
def derivative (c : ℝ) (p : Point 3 1) : Point 3 1 →L[ℝ] ℝ :=
  (2*c*(1/100)/(1/100 + radius p)^2) •
    ((p.1 0) • coord 0 + (p.1 1) • coord 1 + (p.1 2) • coord 2)

def model : ModelData 3 1 1 1 where
  g := fun _ _ => -1
  A := fun _ i => if i.val=0 then -1 else if i.val=1 then -1 else 0
  B := fun _ _ => 0
  rhs := fun _ => -(8/9)
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0
def mixedRow (_ : Fin 1) (_ : RealVector 3) (_ : IntVector 1) : ℝ := -1
def mixedObjective (c : ℝ) (x : RealVector 3) (y : IntVector 1) : ℝ :=
  objective c (x, fun i => (y i : ℝ))
def domain : Set (Point 3 1) := Set.Icc (point 0 0 0 0) (point 1 1 1 0)
def sourceSet := sourceMixedFeasible model mixedRow domain
def optimum : Point 3 1 := point (4/9) (4/9) 0 0
def anchor₁ : Point 3 1 := point 1 0 0 0
def anchor₂ : Point 3 1 := point 0 1 0 0
def trial : Point 3 1 := point (4/9) (4/9) (7/9) 0
def level (c : ℝ) : ℝ := c*100/101
def optimalValue (c : ℝ) : ℝ := c*3200/3281
def slope (c : ℝ) : ℝ := c*200/10201
def firstHeight (c : ℝ) : ℝ := level c - slope c
def secondHeight (c : ℝ) : ℝ := level c - 5*slope c/9
def tolerance (c : ℝ) : ℝ := c*3/250

private theorem radius_nonneg (p : Point 3 1) : 0 ≤ radius p := by
  dsimp [radius]
  positivity

private theorem denominator_pos (p : Point 3 1) : 0 < (1/100 : ℝ) + radius p := by
  have := radius_nonneg p
  linarith

private theorem derivative_apply (c : ℝ) (p w : Point 3 1) :
    derivative c p w = (2*c*(1/100)/(1/100+radius p)^2) *
      (p.1 0*w.1 0 + p.1 1*w.1 1 + p.1 2*w.1 2) := by
  simp [derivative, coord]
  ring

private theorem actual_derivative (c : ℝ) (p : Point 3 1) :
    HasFDerivAt (objective c) (derivative c p) p := by
  have h0 := (hasDerivAt_pow 2 (coord 0 p)).comp_hasFDerivAt p (coord 0).hasFDerivAt
  have h1 := (hasDerivAt_pow 2 (coord 1 p)).comp_hasFDerivAt p (coord 1).hasFDerivAt
  have h2 := (hasDerivAt_pow 2 (coord 2 p)).comp_hasFDerivAt p (coord 2).hasFDerivAt
  have hr := (h0.add h1).add h2
  have hid := hasDerivAt_id (radius p)
  have hrat := (hid.const_mul c).div (hid.const_add (1/100 : ℝ)) (ne_of_gt (denominator_pos p))
  have hd := hrat.comp_hasFDerivAt p hr
  convert hd using 1 <;>
    ext w <;> simp [objective, derivative, coord, radius, Function.comp_def] <;> field_simp <;> ring

private theorem objective_order (c : ℝ) (hc : 0 < c) (p q : Point 3 1) :
    objective c q < objective c p ↔ radius q < radius p := by
  rw [objective, objective, div_lt_div_iff₀ (denominator_pos q) (denominator_pos p)]
  constructor <;> intro h
  · have hh : 0 < c * (radius p - radius q) := by nlinarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hc).mp hh)
  · have hh := mul_pos hc (sub_pos.mpr h)
    nlinarith

private theorem actual_pseudoconvex (c : ℝ) (hc : 0 < c) (p q : Point 3 1)
    (h : objective c q < objective c p) : derivative c p (q-p) < 0 := by
  have hr := (objective_order c hc p q).mp h
  have he : radius q - radius p =
      2*(p.1 0*(q.1 0-p.1 0)+p.1 1*(q.1 1-p.1 1)+p.1 2*(q.1 2-p.1 2)) +
      ((q.1 0-p.1 0)^2+(q.1 1-p.1 1)^2+(q.1 2-p.1 2)^2) := by
    dsimp [radius]; ring
  have hs : p.1 0*(q.1 0-p.1 0)+p.1 1*(q.1 1-p.1 1)+p.1 2*(q.1 2-p.1 2) < 0 := by
    nlinarith [sq_nonneg (q.1 0-p.1 0), sq_nonneg (q.1 1-p.1 1), sq_nonneg (q.1 2-p.1 2)]
  rw [derivative_apply]
  exact mul_neg_of_pos_of_neg (by have hd := denominator_pos p; positivity) hs

private theorem safe_bounds (c : ℝ) (hc : 0 < c) (p : Point 3 1) :
    0 ≤ objective c p ∧ objective c p < c := by
  refine ⟨div_nonneg (mul_nonneg (le_of_lt hc) (radius_nonneg p))
    (le_of_lt (denominator_pos p)), ?_⟩
  rw [objective, div_lt_iff₀ (denominator_pos p)]
  nlinarith

private theorem domain_mem (p : Point 3 1) :
    p ∈ domain ↔ (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ 1) ∧ p.2 0 = 0 := by
  simp only [domain, Set.mem_Icc, Prod.le_def, Pi.le_def, point]
  constructor
  · rintro ⟨⟨hl, hy₁⟩, hu, hy₂⟩
    refine ⟨fun i => ?_, le_antisymm (hy₂ 0) (hy₁ 0)⟩
    fin_cases i <;> simpa using And.intro (hl _) (hu _)
  · rintro ⟨hx, hy⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro i; fin_cases i <;> exact (hx _).1
    · intro i; fin_cases i; exact le_of_eq hy.symm
    · intro i; fin_cases i <;> exact (hx _).2
    · intro i; fin_cases i; exact le_of_eq hy

private theorem linear_mem (p : Point 3 1) :
    p ∈ model.linearRegion ↔ (8/9 : ℝ) ≤ p.1 0 + p.1 1 := by
  simp [ModelData.linearRegion, model, LinearForm, Fin.sum_univ_succ]
  constructor <;> intro h <;> linarith

private theorem source_mem (p : Point 3 1) :
    p ∈ sourceSet ↔ p ∈ domain ∧ (8/9 : ℝ) ≤ p.1 0 + p.1 1 := by
  constructor
  · rintro ⟨hp, hl, _⟩
    exact ⟨hp, (linear_mem p).mp hl⟩
  · rintro ⟨hp, hl⟩
    refine ⟨hp, (linear_mem p).mpr hl, fun _ => (0 : ℤ), ?_, ?_, ?_⟩
    · intro i; norm_num [IntegerBox, model]
    · ext i; fin_cases i; simpa using ((domain_mem p).mp hp).2
    · intro j; norm_num [mixedRow]

private theorem base_eq : alphaMixedBase model domain = sourceSet := by
  ext p
  constructor
  · intro hp; exact (source_mem p).mpr ⟨hp.1.1, (linear_mem p).mp hp.1.2⟩
  · rintro ⟨hp, hl, y, hy, he, _⟩
    exact ⟨⟨hp, hl⟩, y, hy, he⟩

private theorem point_mem (s t u : ℝ)
    (hs : 0 ≤ s ∧ s ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (hu : 0 ≤ u ∧ u ≤ 1)
    (hrow : (8/9 : ℝ) ≤ s+t) : point s t u 0 ∈ sourceSet := by
  rw [source_mem, domain_mem]
  refine ⟨⟨?_, rfl⟩, hrow⟩
  intro i; fin_cases i <;> assumption

private theorem optimum_mem : optimum ∈ sourceSet :=
  point_mem _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem anchor₁_mem : anchor₁ ∈ sourceSet :=
  point_mem _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem anchor₂_mem : anchor₂ ∈ sourceSet :=
  point_mem _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem trial_mem : trial ∈ sourceSet :=
  point_mem _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem values (c : ℝ) :
    objective c optimum = optimalValue c ∧ objective c anchor₁ = level c ∧
    objective c anchor₂ = level c ∧ objective c trial = level c := by
  norm_num [objective, radius, optimum, anchor₁, anchor₂, trial, optimalValue, level]
  constructor <;> ring

private theorem radius_lower (p : Point 3 1) (hp : p ∈ sourceSet) : (32/81 : ℝ) ≤ radius p := by
  have hh := (source_mem p).mp hp |>.2
  have he := sq_nonneg (p.1 0-p.1 1)
  have hs : (8/9 : ℝ)^2 ≤ (p.1 0+p.1 1)^2 := by nlinarith
  dsimp [radius]
  nlinarith [sq_nonneg (p.1 2)]

private theorem objective_le_order (c : ℝ) (hc : 0 < c) (p q : Point 3 1) :
    objective c p ≤ objective c q ↔ radius p ≤ radius q := by
  rw [← not_lt, ← not_lt]
  exact not_congr (objective_order c hc p q)

private theorem original_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer sourceSet (objective c) optimum := by
  refine ⟨optimum_mem, ?_⟩
  intro p hp
  apply (objective_le_order c hc optimum p).mpr
  norm_num [radius, optimum]
  exact radius_lower p hp

private theorem nonconvex (c : ℝ) (hc : 0 < c) :
    ¬ ConvexOn ℝ (alphaMixedBase model domain) (objective c) := by
  intro hconv
  have hu : point (8/9) 0 0 0 ∈ alphaMixedBase model domain := by
    rw [base_eq]; exact point_mem _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hv : anchor₁ ∈ alphaMixedBase model domain := by rw [base_eq]; exact anchor₁_mem
  have hm := (hconv.2) (x := point (8/9) 0 0 0) (y := anchor₁) hu hv
    (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [objective, radius, anchor₁, Prod.fst_add, Prod.smul_fst,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
  nlinarith

private theorem optimum_cut (c : ℝ) (p : Point 3 1) :
    optimalValue c + derivative c optimum (p-optimum) = optimalValue c +
      (2*c*(1/100)/(1/100+32/81)^2)*(4/9)*(p.1 0+p.1 1-8/9) := by
  rw [derivative_apply]
  simp [radius, optimum]
  ring

private theorem anchor₁_cut (c : ℝ) (p : Point 3 1) :
    level c + derivative c anchor₁ (p-anchor₁) = level c + slope c*(p.1 0-1) := by
  rw [derivative_apply]
  norm_num [radius, anchor₁, slope]
  ring_nf
  simp

private theorem anchor₂_cut (c : ℝ) (p : Point 3 1) :
    level c + derivative c anchor₂ (p-anchor₂) = level c + slope c*(p.1 1-1) := by
  rw [derivative_apply]
  norm_num [radius, anchor₂, slope]
  ring_nf
  simp

private theorem slope_pos (c : ℝ) (hc : 0 < c) : 0 < slope c := by
  dsimp [slope]; positivity

private theorem height_bounds (c : ℝ) (hc : 0 < c) :
    0 < optimalValue c ∧ optimalValue c < c ∧ 0 < firstHeight c ∧
    firstHeight c < secondHeight c ∧ secondHeight c < level c ∧ level c < c := by
  dsimp [optimalValue, firstHeight, secondHeight, level, slope]
  constructor <;> (first | positivity | constructor <;> (first | nlinarith | constructor <;>
    (first | nlinarith | constructor <;> (first | nlinarith | constructor <;> nlinarith))))

/-- A literal bounded continuous-height MILP carrier; only retained base and
finite objective linearizations occur. External cap c is retained. -/
def linearHeightSet {I : Type*} (c : ℝ) (anchors : I → Point 3 1) (v : ℝ) :
    Set (Point 3 1 × ℝ) :=
  {z | z.1 ∈ alphaMixedBase model domain ∧ 0 ≤ z.2 ∧ z.2 ≤ c ∧ z.2 ≤ v ∧
    ∀ i, v + derivative c (anchors i) (z.1-anchors i) ≤ z.2}

def initialHeightSet (c : ℝ) : Set (Point 3 1 × ℝ) :=
  {z | z.1 ∈ alphaMixedBase model domain ∧ 0 ≤ z.2 ∧ z.2 ≤ c}

def singleAnchor : Fin 1 → Point 3 1 := fun _ => anchor₁
def doubleAnchor : Fin 2 → Point 3 1 := fun i => if i.val=0 then anchor₁ else anchor₂

private theorem initial_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (initialHeightSet c) Prod.snd (anchor₁,0) := by
  refine ⟨⟨?_, le_rfl, le_of_lt hc⟩, ?_⟩
  · rw [base_eq]; exact anchor₁_mem
  · intro z hz; exact hz.2.1

private theorem one_linear_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (linearHeightSet c singleAnchor (level c)) Prod.snd (anchor₂,firstHeight c) := by
  have hb := height_bounds c hc
  have hκ := slope_pos c hc
  refine ⟨⟨?_, le_of_lt hb.2.2.1, ?_, ?_, ?_⟩, ?_⟩
  · rw [base_eq]; exact anchor₂_mem
  · linarith [hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]
  · linarith [hb.2.2.2.1, hb.2.2.2.2.1]
  · intro i; change level c + derivative c anchor₁ (anchor₂-anchor₁) ≤ firstHeight c
    rw [anchor₁_cut]
    simp [anchor₂, firstHeight]
  · intro z hz
    have hcut := hz.2.2.2.2 0
    change level c + derivative c anchor₁ (z.1-anchor₁) ≤ z.2 at hcut
    rw [anchor₁_cut] at hcut
    have hx := ((domain_mem z.1).mp hz.1.1.1).1 0 |>.1
    have hm := mul_nonneg (le_of_lt hκ) hx
    dsimp [firstHeight]; linarith

private theorem two_linear_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (linearHeightSet c doubleAnchor (level c)) Prod.snd (trial,secondHeight c) := by
  have hb := height_bounds c hc
  have hκ := slope_pos c hc
  refine ⟨⟨?_, ?_, ?_, le_of_lt hb.2.2.2.2.1, ?_⟩, ?_⟩
  · rw [base_eq]; exact trial_mem
  · linarith [hb.2.2.1, hb.2.2.2.1]
  · linarith [hb.2.2.2.2.1, hb.2.2.2.2.2]
  · intro i; fin_cases i
    · change level c + derivative c anchor₁ (trial-anchor₁) ≤ secondHeight c
      rw [anchor₁_cut]; simp [trial, secondHeight]; ring_nf; exact le_rfl
    · change level c + derivative c anchor₂ (trial-anchor₂) ≤ secondHeight c
      rw [anchor₂_cut]; simp [trial, secondHeight]; ring_nf; exact le_rfl
  · intro z hz
    have hcut₁ := hz.2.2.2.2 0
    have hcut₂ := hz.2.2.2.2 1
    change level c + derivative c anchor₁ (z.1-anchor₁) ≤ z.2 at hcut₁
    change level c + derivative c anchor₂ (z.1-anchor₂) ≤ z.2 at hcut₂
    rw [anchor₁_cut] at hcut₁
    rw [anchor₂_cut] at hcut₂
    have hrow := (linear_mem z.1).mp hz.1.1.2
    have hm := mul_le_mul_of_nonneg_left hrow (le_of_lt hκ)
    dsimp [secondHeight]; nlinarith

private theorem gap_comparisons (c : ℝ) (hc : 0 < c) :
    0 < tolerance c ∧ tolerance c < |level c-firstHeight c| ∧
    |level c-secondHeight c| = c*1000/91809 ∧
    |level c-secondHeight c| < tolerance c ∧
    objective c trial-objective c optimum = c*4900/331381 ∧
    tolerance c < objective c trial-objective c optimum ∧
    objective c optimum < secondHeight c := by
  have hκ := slope_pos c hc
  have hb := height_bounds c hc
  rw [(values c).1, (values c).2.2.2]
  rw [abs_of_pos (by linarith [hb.2.2.2.1, hb.2.2.2.2.1] : 0 < level c-firstHeight c)]
  rw [abs_of_pos (sub_pos.mpr hb.2.2.2.2.1)]
  dsimp [tolerance, firstHeight, secondHeight, slope, level, optimalValue]
  refine ⟨by positivity, by nlinarith, ?_, by nlinarith, ?_, by nlinarith, by nlinarith⟩ <;> ring

private theorem reduced_to_linear {I : Type*} (c : ℝ) (anchors : I → Point 3 1)
    (v : ℝ) (hvc : v ≤ c) (z : Point 3 1 × ℝ)
    (hz : z ∈ alphaObjectiveHeightSet sourceSet (objective c) (derivative c) anchors 0 v) :
    z ∈ linearHeightSet c anchors v := by
  refine ⟨?_, hz.2.2.1, hz.2.2.2.1.trans hvc, hz.2.2.2.1, hz.2.2.2.2⟩
  rw [base_eq]; exact hz.1

private theorem one_reduced_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (alphaObjectiveHeightSet sourceSet (objective c) (derivative c)
      singleAnchor 0 (level c)) Prod.snd (anchor₂, firstHeight c) := by
  have hm := one_linear_minimum c hc
  refine ⟨⟨anchor₂_mem, le_of_eq (values c).2.2.1, hm.1.2.1, hm.1.2.2.2.1, hm.1.2.2.2.2⟩, ?_⟩
  intro z hz
  exact hm.2 z (reduced_to_linear c singleAnchor (level c)
    (le_of_lt (height_bounds c hc).2.2.2.2.2) z hz)

private theorem two_reduced_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (alphaObjectiveHeightSet sourceSet (objective c) (derivative c)
      doubleAnchor 0 (level c)) Prod.snd (trial, secondHeight c) := by
  have hm := two_linear_minimum c hc
  refine ⟨⟨trial_mem, le_of_eq (values c).2.2.2, hm.1.2.1, hm.1.2.2.2.1, hm.1.2.2.2.2⟩, ?_⟩
  intro z hz
  exact hm.2 z (reduced_to_linear c doubleAnchor (level c)
    (le_of_lt (height_bounds c hc).2.2.2.2.2) z hz)

private theorem exact_height_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (alphaObjectiveHeightSet sourceSet (objective c) (derivative c)
      (fun _ : Fin 1 => optimum) 0 (optimalValue c)) Prod.snd (optimum, optimalValue c) := by
  refine ⟨⟨optimum_mem, le_of_eq (values c).1, le_of_lt (height_bounds c hc).1,
    le_rfl, ?_⟩, ?_⟩
  · intro i; simp
  · intro z hz
    have hcut := hz.2.2.2.2 0
    change optimalValue c + derivative c optimum (z.1-optimum) ≤ z.2 at hcut
    rw [optimum_cut] at hcut
    have hrow := (source_mem z.1).mp hz.1 |>.2
    have hp : 0 ≤ (2*c*(1/100)/(1/100+32/81)^2)*(4/9) := by positivity
    have hh := mul_nonneg hp (sub_nonneg.mpr hrow)
    dsimp; linarith

private theorem optimum_derivative_nonzero (c : ℝ) (hc : 0 < c) :
    derivative c optimum ≠ 0 := by
  intro he
  have hh := congrArg (fun L : Point 3 1 →L[ℝ] ℝ => L (point 1 0 0 0)) he
  change derivative c optimum (point 1 0 0 0) = 0 at hh
  rw [derivative_apply] at hh
  norm_num [radius, optimum] at hh
  nlinarith

private theorem all_tolerances (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ tolerance c = ε ∧
      IsMinimizer (linearHeightSet c doubleAnchor (level c)) Prod.snd (trial,secondHeight c) ∧
      IsMinimizer (alphaObjectiveHeightSet sourceSet (objective c) (derivative c)
        doubleAnchor 0 (level c)) Prod.snd (trial, secondHeight c) ∧
      |level c-secondHeight c| < ε ∧ ε < |objective c trial-objective c optimum| := by
  let c : ℝ := 250*ε/3
  have hc : 0 < c := by dsimp [c]; positivity
  have he : tolerance c = ε := by dsimp [tolerance,c]; ring
  have hg := gap_comparisons c hc
  refine ⟨c, hc, he, two_linear_minimum c hc, two_reduced_minimum c hc, ?_, ?_⟩
  · rw [← he]; exact hg.2.2.2.1
  · rw [← he]; exact lt_of_lt_of_le hg.2.2.2.2.2.1 (le_abs_self _)

def scalarDerivative (_ : ℝ) : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

private theorem unsafe_floor :
    (∀ x : ℝ, HasFDerivAt (fun t : ℝ => t) (scalarDerivative x) x) ∧
    (∀ x y : ℝ, y < x → scalarDerivative x (y-x) < 0) ∧
    IsMinimizer (alphaObjectiveHeightSet (Set.Icc (0 : ℝ) 1) (fun t => t)
      scalarDerivative (fun _ : Fin 1 => 1) 1 1) Prod.snd (1,1) ∧
    ¬ (∀ p ∈ Set.Icc (0 : ℝ) 1, 1 ≤ p) ∧
    ¬ IsMinimizer (Set.Icc (0 : ℝ) 1) (fun t => t) 1 ∧
    (1,1) ∈ alphaObjectiveHeightSet (Set.Icc (0 : ℝ) 1) (fun t => t)
      scalarDerivative (fun _ : Fin 1 => 1) 0 1 ∧
    ¬ IsMinimizer (alphaObjectiveHeightSet (Set.Icc (0 : ℝ) 1) (fun t => t)
      scalarDerivative (fun _ : Fin 1 => 1) 0 1) Prod.snd (1,1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact (ContinuousLinearMap.id ℝ ℝ).hasFDerivAt
  · intro x y h; exact sub_neg.mpr h
  · refine ⟨?_, ?_⟩
    · norm_num [alphaObjectiveHeightSet, scalarDerivative]
    · intro z hz; exact hz.2.2.1
  · intro h; have hh := h 0 (by norm_num); norm_num at hh
  · intro h; have hh := h.2 0 (by norm_num); norm_num at hh
  · norm_num [alphaObjectiveHeightSet, scalarDerivative]
  · intro h
    have hh := h.2 (0,0) (by norm_num [alphaObjectiveHeightSet, scalarDerivative])
    norm_num at hh

private theorem source_height_eq {I : Type*} (c : ℝ) (anchors : I → Point 3 1) (b v : ℝ) :
    sourceAlphaObjectiveHeightSet model mixedRow (mixedObjective c) domain
      (derivative c) anchors b v =
    alphaObjectiveHeightSet sourceSet (objective c) (derivative c) anchors b v := by
  ext z
  constructor
  · rintro ⟨hp, hl, y, hy, he, hg, hf, hb, hv, hcuts⟩
    exact ⟨⟨hp, hl, y, hy, he, hg⟩, hf, hb, hv, hcuts⟩
  · rintro ⟨⟨hp, hl, y, hy, he, hg⟩, hf, hb, hv, hcuts⟩
    exact ⟨hp, hl, y, hy, he, hg, hf, hb, hv, hcuts⟩

private theorem one_source_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (sourceAlphaObjectiveHeightSet model mixedRow (mixedObjective c) domain
      (derivative c) singleAnchor 0 (level c)) Prod.snd (anchor₂,firstHeight c) := by
  rw [source_height_eq]; exact one_reduced_minimum c hc

private theorem two_source_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (sourceAlphaObjectiveHeightSet model mixedRow (mixedObjective c) domain
      (derivative c) doubleAnchor 0 (level c)) Prod.snd (trial,secondHeight c) := by
  rw [source_height_eq]; exact two_reduced_minimum c hc

private theorem exact_source_minimum (c : ℝ) (hc : 0 < c) :
    IsMinimizer (sourceAlphaObjectiveHeightSet model mixedRow (mixedObjective c) domain
      (derivative c) (fun _ : Fin 1 => optimum) 0 (optimalValue c))
      Prod.snd (optimum, optimalValue c) := by
  rw [source_height_eq]
  exact exact_height_minimum c hc

/-- This application uses only the explicit attained height minimum, never the
independent original-minimum bound proved for the separate gap comparison. -/
private theorem source_application (c : ℝ) (hc : 0 < c) :
    sourceSet = model.feasibleOn domain ∧
    objective c optimum = optimalValue c ∧ IsMinimizer sourceSet (objective c) optimum ∧
    IsMinimizer (model.feasibleOn domain) (objective c) optimum ∧
    ∃ y : IntVector 1, y ∈ IntegerBox model.lo model.hi ∧
      optimum.2 = (fun i => (y i : ℝ)) ∧ (∀ j, mixedRow j optimum.1 y ≤ 0) ∧
      mixedObjective c optimum.1 y = optimalValue c ∧
      ∀ (x : RealVector 3) (z : IntVector 1),
        (x, fun i => (z i : ℝ)) ∈ domain →
        (x, fun i => (z i : ℝ)) ∈ model.linearRegion →
        z ∈ IntegerBox model.lo model.hi → (∀ j, mixedRow j x z ≤ 0) →
        mixedObjective c optimum.1 y ≤ mixedObjective c x z := by
  have h := source_alpha_objective_equal_height_optimal model mixedRow (mixedObjective c)
    domain (objective c) (derivative c) (fun _ : Fin 1 => optimum) 0 (optimalValue c) optimum
    (by intros; rfl) (by intros; rfl) isCompact_Icc
    (fun x _ => actual_derivative c x)
    (fun x _ y _ hxy => actual_pseudoconvex c hc x y hxy)
    (fun _ => optimum_mem) (fun _ => (values c).1)
    (fun p _ => (safe_bounds c hc p).1) (exact_source_minimum c hc)
  exact ⟨h.1, h.2.2⟩

private theorem source_objective_bounds (c : ℝ) (hc : 0 < c) :
    (∀ p ∈ sourceSet, p.2 0 = 0) ∧
    LinearForm (model.A 0) (model.B 0) optimum = model.rhs 0 ∧
    LinearForm (model.A 0) (model.B 0) trial = model.rhs 0 ∧
    (∀ p, model.objective p = 0) ∧
    objective c optimum < objective c anchor₁ ∧
    level c + derivative c anchor₁ (optimum-anchor₁) = secondHeight c ∧
    level c + derivative c anchor₂ (optimum-anchor₂) = secondHeight c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; exact ((domain_mem p).mp ((source_mem p).mp hp).1).2
  · norm_num [LinearForm, model, optimum, point, Fin.sum_univ_succ]
  · norm_num [LinearForm, model, trial, point, Fin.sum_univ_succ]
  · intro p; simp [ModelData.objective, LinearForm, model]
  · rw [(values c).1, (values c).2.1]; dsimp [optimalValue, level]; nlinarith
  · rw [anchor₁_cut]; simp [optimum, secondHeight]; ring
  · rw [anchor₂_cut]; simp [optimum, secondHeight]; ring

/-- One substantive full-model control package. The absolute-gap failure is for
an explicitly permitted finite same-level history with two final cuts, exact
feasibility and attained global minima. It is not a full state-machine, relative
error, numerical solver, all-policy or historical-software theorem. -/
theorem rational_model_controls (c : ℝ) (hc : 0 < c) :
    IsCompact domain ∧
    (∀ p, 0 < (1/100 : ℝ) + radius p) ∧
    (∀ p, HasFDerivAt (objective c) (derivative c p) p) ∧
    (∀ p q, objective c q < objective c p → derivative c p (q-p) < 0) ∧
    ¬ ConvexOn ℝ (alphaMixedBase model domain) (objective c) ∧
    (∀ j x y, model.g j (x, fun i => (y i : ℝ)) = mixedRow j x y) ∧
    (∀ x y, objective c (x, fun i => (y i : ℝ)) = mixedObjective c x y) ∧
    (∀ j p, model.g j p = -1) ∧
    alphaMixedBase model domain = sourceSet ∧ sourceSet = model.feasibleOn domain ∧
    (∀ p ∈ sourceSet, p.2 0 = 0) ∧
    LinearForm (model.A 0) (model.B 0) optimum = model.rhs 0 ∧
    LinearForm (model.A 0) (model.B 0) trial = model.rhs 0 ∧
    (∀ p, model.objective p = 0) ∧
    (∀ p, 0 ≤ objective c p ∧ objective c p < c) ∧
    (∀ p ∈ sourceSet, (32/81 : ℝ) ≤ radius p ∧ optimalValue c ≤ objective c p) ∧
    optimum ∈ sourceSet ∧ anchor₁ ∈ sourceSet ∧ anchor₂ ∈ sourceSet ∧ trial ∈ sourceSet ∧
    objective c optimum = optimalValue c ∧ 0 < optimalValue c ∧ derivative c optimum ≠ 0 ∧
    objective c anchor₁ = level c ∧ objective c anchor₂ = level c ∧ objective c trial = level c ∧
    objective c optimum < objective c anchor₁ ∧
    (∀ i, doubleAnchor i ∈ sourceSet ∧ objective c (doubleAnchor i) = level c) ∧
    IsMinimizer (sourceAlphaObjectiveHeightSet model mixedRow (mixedObjective c) domain
      (derivative c) (fun _ : Fin 1 => optimum) 0 (optimalValue c))
      Prod.snd (optimum, optimalValue c) ∧
    IsMinimizer sourceSet (objective c) optimum ∧
    IsMinimizer (model.feasibleOn domain) (objective c) optimum ∧
    (∃ y : IntVector 1, y ∈ IntegerBox model.lo model.hi ∧
      optimum.2 = (fun i => (y i : ℝ)) ∧ (∀ j, mixedRow j optimum.1 y ≤ 0) ∧
      mixedObjective c optimum.1 y = optimalValue c ∧
      ∀ (x : RealVector 3) (z : IntVector 1),
        (x, fun i => (z i : ℝ)) ∈ domain →
        (x, fun i => (z i : ℝ)) ∈ model.linearRegion →
        z ∈ IntegerBox model.lo model.hi → (∀ j, mixedRow j x z ≤ 0) →
        mixedObjective c optimum.1 y ≤ mixedObjective c x z) ∧
    IsMinimizer (initialHeightSet c) Prod.snd (anchor₁,0) ∧
    IsMinimizer (linearHeightSet c singleAnchor (level c)) Prod.snd (anchor₂,firstHeight c) ∧
    IsMinimizer (linearHeightSet c doubleAnchor (level c)) Prod.snd (trial,secondHeight c) ∧
    IsMinimizer (alphaObjectiveHeightSet sourceSet (objective c) (derivative c)
      singleAnchor 0 (level c)) Prod.snd (anchor₂,firstHeight c) ∧
    IsMinimizer (alphaObjectiveHeightSet sourceSet (objective c) (derivative c)
      doubleAnchor 0 (level c)) Prod.snd (trial,secondHeight c) ∧
    IsMinimizer (sourceAlphaObjectiveHeightSet model mixedRow (mixedObjective c) domain
      (derivative c) singleAnchor 0 (level c)) Prod.snd (anchor₂,firstHeight c) ∧
    IsMinimizer (sourceAlphaObjectiveHeightSet model mixedRow (mixedObjective c) domain
      (derivative c) doubleAnchor 0 (level c)) Prod.snd (trial,secondHeight c) ∧
    level c + derivative c anchor₁ (optimum-anchor₁) = secondHeight c ∧
    level c + derivative c anchor₂ (optimum-anchor₂) = secondHeight c ∧
    0 < tolerance c ∧ tolerance c < |level c-firstHeight c| ∧
    |level c-secondHeight c| = c*1000/91809 ∧
    |level c-secondHeight c| < tolerance c ∧
    objective c trial-objective c optimum = c*4900/331381 ∧
    tolerance c < objective c trial-objective c optimum ∧
    objective c optimum < secondHeight c ∧
    tolerance c < |objective c trial-objective c optimum| ∧
    (∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 < d ∧ tolerance d = ε ∧
      IsMinimizer (linearHeightSet d doubleAnchor (level d)) Prod.snd (trial,secondHeight d) ∧
      IsMinimizer (alphaObjectiveHeightSet sourceSet (objective d) (derivative d)
        doubleAnchor 0 (level d)) Prod.snd (trial,secondHeight d) ∧
      |level d-secondHeight d| < ε ∧ ε < |objective d trial-objective d optimum|) ∧
    (∀ x : ℝ, HasFDerivAt (fun t : ℝ => t) (scalarDerivative x) x) ∧
    (∀ x y : ℝ, y < x → scalarDerivative x (y-x) < 0) ∧
    IsMinimizer (alphaObjectiveHeightSet (Set.Icc (0 : ℝ) 1) (fun t => t)
      scalarDerivative (fun _ : Fin 1 => 1) 1 1) Prod.snd (1,1) ∧
    ¬ (∀ p ∈ Set.Icc (0 : ℝ) 1, 1 ≤ p) ∧
    ¬ IsMinimizer (Set.Icc (0 : ℝ) 1) (fun t => t) 1 ∧
    (1,1) ∈ alphaObjectiveHeightSet (Set.Icc (0 : ℝ) 1) (fun t => t)
      scalarDerivative (fun _ : Fin 1 => 1) 0 1 ∧
    ¬ IsMinimizer (alphaObjectiveHeightSet (Set.Icc (0 : ℝ) 1) (fun t => t)
      scalarDerivative (fun _ : Fin 1 => 1) 0 1) Prod.snd (1,1) := by
  have hs := source_application c hc
  have hb := source_objective_bounds c hc
  have hv := values c
  have hg := gap_comparisons c hc
  refine ⟨isCompact_Icc, denominator_pos, actual_derivative c, actual_pseudoconvex c hc,
    nonconvex c hc, (by intros; rfl), (by intros; rfl), (by intros; rfl),
    base_eq, hs.1, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, safe_bounds c hc,
    (fun p hp => ⟨radius_lower p hp, by
      rw [← hv.1]; exact (original_minimum c hc).2 p hp⟩),
    optimum_mem, anchor₁_mem, anchor₂_mem, trial_mem, hv.1, (height_bounds c hc).1,
    optimum_derivative_nonzero c hc, hv.2.1, hv.2.2.1, hv.2.2.2, hb.2.2.2.2.1, ?_,
    exact_source_minimum c hc, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2,
    initial_minimum c hc, one_linear_minimum c hc, two_linear_minimum c hc,
    one_reduced_minimum c hc, two_reduced_minimum c hc,
    one_source_minimum c hc, two_source_minimum c hc,
    hb.2.2.2.2.2.1, hb.2.2.2.2.2.2, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1,
    hg.2.2.2.2.1, hg.2.2.2.2.2.1, hg.2.2.2.2.2.2,
    lt_of_lt_of_le hg.2.2.2.2.2.1 (le_abs_self _), all_tolerances, unsafe_floor⟩
  intro i
  fin_cases i
  · exact ⟨anchor₁_mem, hv.2.1⟩
  · exact ⟨anchor₂_mem, hv.2.2.1⟩

end Chapter02AlphaObjectiveExamples

#print axioms Chapter02AlphaObjectiveExamples.rational_model_controls
