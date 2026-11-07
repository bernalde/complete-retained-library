module

public import Chapter02AlphaSource
public import Chapter02AlphaAuxiliary
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

@[expose] public section

/-! One linked cubic control. Its objective is zero, so the displayed master
minima carry no objective-dependent transport content. The auxiliary variables
are freely real; their Euclidean geometry is distinct from the mixed domain.
The epsilon=1/2 loss illustrates the source's admitted approximation caveat,
not a new convergence or implementation-wide diagnosis. -/
noncomputable section
open Chapter02
namespace Chapter02AlphaExamples

def point (s t : ℝ) : Point 1 1 := (fun _ => s, fun _ => t)
def cubic (s : ℝ) : ℝ := s ^ 3 + s + 1/2
def model : ModelData 1 1 1 0 where
  g := fun _ p => cubic (p.1 0)
  A := fun _ _ => 0
  B := fun _ _ => 0
  rhs := fun _ => 0
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0
def mixedRow (_ : Fin 1) (x : RealVector 1) (_ : IntVector 1) : ℝ := cubic (x 0)
def domain : Set (Point 1 1) := Set.Icc (point (-1) 0) (point 1 0)
def q : Point 1 1 := point 0 0
def feasiblePoint : Point 1 1 := point (-(1/2)) 0
def testPoint : Point 1 1 := point (-(9/20)) 0
def normal : Point 1 1 := point 1 0
def tangent : Point 1 1 := point 0 1
def coord : Point 1 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector 1))
def derivative (_ : Fin 1) (p : Point 1 1) : Point 1 1 →L[ℝ] ℝ :=
  (3 * (p.1 0)^2 + 1) • coord
def origins : Fin 1 → Point 1 1 := fun _ => q
def selected : Fin 1 → Set (Fin 1) := fun _ => Set.univ
def cuts (α : ℝ) : TangentFamily 1 1 1 1 :=
  alphaScaledFamily origins selected derivative (fun _ _ => α)
def noCuts : TangentFamily 1 1 1 0 where
  origin := fun i => Fin.elim0 i
  selected := fun _ => Set.univ
  derivative := fun _ _ => 0
def sourceSet := sourceMixedFeasible model mixedRow domain

private theorem domain_mem (p : Point 1 1) :
    p ∈ domain ↔ -1 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ p.2 0 = 0 := by
  simp [domain, point, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_one]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    exact ⟨ha, hc, le_antisymm hd hb⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨⟨ha, by rw [hc]⟩, hb, by rw [hc]⟩

private theorem derivative_apply (j : Fin 1) (p w : Point 1 1) :
    derivative j p w = (3*(p.1 0)^2+1)*w.1 0 := by
  simp [derivative, coord]

private theorem actual_derivative (j : Fin 1) (p : Point 1 1) :
    HasFDerivAt (model.g j) (derivative j p) p := by
  have hc := coord.hasFDerivAt (x := p)
  have hp := (hasDerivAt_pow 3 (coord p)).comp_hasFDerivAt p hc
  convert (hp.add hc).add_const (1/2 : ℝ) using 1 <;>
    ext w <;> simp [model, cubic, derivative, coord, Function.comp_def] <;> ring

private theorem cubic_strictMono : StrictMono cubic := by
  intro s t hst
  have hpos : 0 < t^2+t*s+s^2+1 := by
    nlinarith [sq_nonneg (t+s), sq_nonneg t, sq_nonneg s]
  have hm := mul_pos (sub_pos.mpr hst) hpos
  dsimp [cubic]
  nlinarith

private theorem actual_pseudoconvex (j : Fin 1) (x y : Point 1 1)
    (h : model.g j y < model.g j x) : derivative j x (y-x) < 0 := by
  have hxy : y.1 0 < x.1 0 := by
    by_contra hn
    have hc := cubic_strictMono.monotone (le_of_not_gt hn)
    exact (not_lt_of_ge hc) h
  rw [derivative_apply]
  exact mul_neg_of_pos_of_neg (by nlinarith [sq_nonneg (x.1 0)]) (sub_neg.mpr hxy)

private theorem extension : ∀ j x y,
    model.g j (x, fun i => (y i : ℝ)) = mixedRow j x y := by
  intros; rfl

private theorem mixed_base_eq : alphaMixedBase model domain = domain := by
  apply Set.Subset.antisymm
  · intro p hp; exact hp.1.1
  · intro p hp
    refine ⟨⟨hp, ?_⟩, fun _ => (0 : ℤ), ?_, ?_⟩
    · intro row; exact Fin.elim0 row
    · intro i; norm_num [IntegerBox, model]
    · ext i
      fin_cases i
      simpa using ((domain_mem p).mp hp).2.2

private theorem source_mem (p : Point 1 1) :
    p ∈ sourceSet ↔ p ∈ domain ∧ cubic (p.1 0) ≤ 0 := by
  constructor
  · rintro ⟨hp, _, y, _, _, hg⟩
    exact ⟨hp, hg 0⟩
  · rintro ⟨hp, hg⟩
    refine ⟨hp, ?_, fun _ => (0 : ℤ), ?_, ?_, ?_⟩
    · intro row; exact Fin.elim0 row
    · intro i; norm_num [IntegerBox, model]
    · ext i; fin_cases i; simpa using ((domain_mem p).mp hp).2.2
    · intro j; exact hg

private theorem feasible_point_mem : feasiblePoint ∈ sourceSet := by
  rw [source_mem, domain_mem]
  norm_num [feasiblePoint, point, cubic]

private theorem test_point_mem : testPoint ∈ sourceSet := by
  rw [source_mem, domain_mem]
  norm_num [testPoint, point, cubic]

private theorem quarter_bound (p : Point 1 1) (hp : p ∈ sourceSet) : p.1 0 < -(1/4 : ℝ) := by
  have hg := (source_mem p).mp hp |>.2
  by_contra hn
  have hm := cubic_strictMono.monotone (le_of_not_gt hn)
  norm_num [cubic] at hm
  dsimp [cubic] at hg
  linarith

private theorem nonconvex : ¬ ConvexOn ℝ domain (model.g 0) := by
  intro hc
  have hm := (hc.2) (x := point (-1) 0) (y := q)
    ((domain_mem _).mpr (by norm_num [point]))
    ((domain_mem _).mpr (by norm_num [q, point]))
    (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [model, cubic, q, point, smul_eq_mul] at hm

private theorem objective_zero (p : Point 1 1) : model.objective p = 0 := by
  simp [ModelData.objective, model, LinearForm]

private theorem source_family :
    sourceSet = model.feasibleOn domain ∧ IsCompact sourceSet ∧
    ∃ pstar ∈ sourceSet, ∃ h : ℝ, (1/4 : ℝ) < h ∧
      h = -(pstar.1 0) ∧ (∀ p ∈ sourceSet, p.1 0 ≤ -h) ∧
      (∀ α : ℝ, (sourceSet ⊆ model.masterOn (cuts α) domain) ↔ (1/2 : ℝ)/h ≤ α) ∧
      sourceSet ⊆ model.masterOn (cuts 2) domain ∧
      (∀ α : ℝ, q ∉ (cuts α).cutRegion model) := by
  have hb := source_alpha_cut_family model mixedRow domain derivative origins selected
    extension isCompact_Icc ⟨feasiblePoint, feasible_point_mem⟩
    (fun j x _ => actual_derivative j x)
    (fun j x _ y _ h => actual_pseudoconvex j x y h)
    (by intro i; rw [mixed_base_eq, domain_mem]; norm_num [origins, q, point])
    (by intro i j _; norm_num [model, origins, q, point, cubic])
  obtain ⟨heq, _, hcompact, h, hatt, hiff, _, hexcl⟩ := hb
  obtain ⟨pstar, hpstar, hpos, he, hbound, _⟩ := hatt 0 0 (Set.mem_univ _)
  have hmargin : h 0 0 = -(pstar.1 0) := by
    simpa [origins, derivative_apply, q, point] using he
  have hbig : (1/4 : ℝ) < h 0 0 := by
    have hs := quarter_bound pstar hpstar
    linarith
  have hall : ∀ α : ℝ,
      (sourceSet ⊆ model.masterOn (cuts α) domain) ↔ (1/2 : ℝ)/(h 0 0) ≤ α := by
    intro α
    simpa [sourceSet, cuts, origins, selected, model, q, point, cubic,
      Fin.forall_fin_one] using hiff (fun _ _ => α)
  refine ⟨heq, hcompact, pstar, hpstar, h 0 0, hbig, hmargin, ?_, hall, ?_, ?_⟩
  · intro p hp
    simpa [origins, derivative_apply, q, point] using hbound p hp
  · apply (hall 2).mpr
    apply (div_le_iff₀ hpos).mpr
    linarith
  · intro α
    exact hexcl (fun _ _ => α) 0 ⟨0, Set.mem_univ _⟩

private theorem cut_mem (α : ℝ) (p : Point 1 1) :
    p ∈ (cuts α).cutRegion model ↔ (1/2 : ℝ) + α * p.1 0 ≤ 0 := by
  simp [cuts, alphaScaledFamily, origins, selected, TangentFamily.cutRegion,
    model, cubic, q, point, derivative, coord]

private theorem initial_minimum : IsMinimizer (model.masterOn noCuts domain) model.objective q := by
  have hq : q ∈ alphaMixedBase model domain := by
    rw [mixed_base_eq, domain_mem]
    norm_num [q, point]
  refine ⟨⟨⟨⟨hq.1.1, ?_⟩, hq.1.2⟩, hq.2⟩, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro p _; rw [objective_zero, objective_zero]

private theorem auxiliary_control :
    (∀ w, derivative 0 q w = alphaEuclideanDot normal w) ∧
    IsMinimizer (alphaAuxiliaryRegion normal q (1/4)) (alphaAuxiliaryObjective normal q)
      (q, point 0 (1/4)) ∧
    alphaAuxiliaryObjective normal q (q, point 0 (1/4)) = 0 ∧
    (1/4 : ℝ) * Real.sqrt (alphaEuclideanDot normal normal) = 1/4 ∧
    point 0 (1/4) ∉ domain := by
  have hC := alpha_auxiliary_zero_minimum normal q tangent (1/4)
    (by norm_num) (by norm_num [alphaEuclideanDot, LinearForm, normal, point])
    (by norm_num [alphaEuclideanDot, LinearForm, normal, tangent, point])
    (by norm_num [alphaEuclideanDot, LinearForm, tangent, point])
  have he : q + (1/4 : ℝ) • tangent = point 0 (1/4) := by
    ext i <;> simp [q, point, tangent]
  rw [he] at hC
  refine ⟨?_, hC.1, hC.2.1, ?_, ?_⟩
  · intro w; simp [derivative_apply, q, point, alphaEuclideanDot, LinearForm, normal]
  · norm_num [alphaEuclideanDot, LinearForm, normal, point]
  · rw [domain_mem]; norm_num [point]

/-- One full mixed cubic model exercises the actual A/B/C interfaces. The
attained h>1/4 comes from original feasibility, not the auxiliary formula.
The objective is identically zero, so the two actual master minima are trivial
and establish no objective-dependent transport. The epsilon=1/2 calculation is
only the source-admitted approximation caveat; the zero auxiliary minimum is
the distinct diagnosis of the literal freely-real displayed program. -/
theorem cubic_model_control :
    (∀ j p, HasFDerivAt (model.g j) (derivative j p) p) ∧
    (∀ j x y, model.g j y < model.g j x → derivative j x (y-x) < 0) ∧
    ¬ ConvexOn ℝ domain (model.g 0) ∧
    (∀ j x y, model.g j (x, fun i => (y i : ℝ)) = mixedRow j x y) ∧
    alphaMixedBase model domain = domain ∧
    sourceSet = model.feasibleOn domain ∧
    IsCompact sourceSet ∧ feasiblePoint ∈ sourceSet ∧ testPoint ∈ sourceSet ∧
    (∀ p, model.objective p = 0) ∧
    IsMinimizer (model.masterOn noCuts domain) model.objective q ∧
    model.g 0 q = 1/2 ∧ (1/4 : ℝ) < model.g 0 q ∧
    (∃ pstar ∈ sourceSet, ∃ h : ℝ, (1/4 : ℝ) < h ∧
      h = -(derivative 0 q (pstar-q)) ∧
      (∀ p ∈ sourceSet, derivative 0 q (p-q) ≤ -h) ∧
      (∀ α : ℝ, (sourceSet ⊆ model.masterOn (cuts α) domain) ↔ model.g 0 q / h ≤ α) ∧
      max 1 (model.g 0 q / h) ≤ 2) ∧
    sourceSet ⊆ model.masterOn (cuts 2) domain ∧
    (∀ α : ℝ, q ∉ (cuts α).cutRegion model) ∧
    IsMinimizer (model.masterOn (cuts 2) domain) model.objective feasiblePoint ∧
    (∀ w, derivative 0 q w = alphaEuclideanDot normal w) ∧
    IsMinimizer (alphaAuxiliaryRegion normal q (1/4)) (alphaAuxiliaryObjective normal q)
      (q, point 0 (1/4)) ∧
    alphaAuxiliaryObjective normal q (q, point 0 (1/4)) = 0 ∧
    (1/4 : ℝ) * Real.sqrt (alphaEuclideanDot normal normal) = 1/4 ∧
    point 0 (1/4) ∉ domain ∧
    model.g 0 testPoint = -(329/8000) ∧
    model.g 0 q + derivative 0 q (testPoint-q) = 1/20 ∧
    model.g 0 q + 2 * derivative 0 q (testPoint-q) = -(2/5) ∧
    2 * (model.g 0 q + derivative 0 q (testPoint-q)) = 1/10 ∧
    testPoint ∉ model.masterOn (cuts 1) domain ∧
    testPoint ∈ model.masterOn (cuts 2) domain ∧
    (1/2 : ℝ) * Real.sqrt (alphaEuclideanDot normal normal) = 1/2 ∧
    model.g 0 q / ((1/2 : ℝ) * Real.sqrt (alphaEuclideanDot normal normal)) = 1 := by
  obtain ⟨heq, hcompact, pstar, hpstar, h, hbig, he, hb, hiff, houter, hexcl⟩ := source_family
  obtain ⟨hlink, haux, hzero, hformula, houtside⟩ := auxiliary_control
  refine ⟨actual_derivative, actual_pseudoconvex, nonconvex, extension, mixed_base_eq,
    heq, hcompact, feasible_point_mem, test_point_mem, objective_zero, initial_minimum,
    by norm_num [model, cubic, q, point], by norm_num [model, cubic, q, point],
    ?_, houter, hexcl, ?_, hlink, haux, hzero, hformula, houtside,
    ?_, ?_, ?_, ?_, ?_, houter test_point_mem, ?_, ?_⟩
  · refine ⟨pstar, hpstar, h, hbig, ?_, ?_, ?_, ?_⟩
    · simpa [derivative_apply, q, point] using he
    · intro p hp; simpa [derivative_apply, q, point] using hb p hp
    · intro α; simpa [model, cubic, q, point] using hiff α
    · apply max_le (by norm_num)
      norm_num [model, cubic, q, point]
      apply (div_le_iff₀ (by linarith : 0 < h)).mpr
      linarith
  · refine ⟨houter feasible_point_mem, ?_⟩
    intro p _; rw [objective_zero, objective_zero]
  · norm_num [model, cubic, testPoint, point]
  · norm_num [model, cubic, q, testPoint, point, derivative_apply]
  · norm_num [model, cubic, q, testPoint, point, derivative_apply]
  · norm_num [model, cubic, q, testPoint, point, derivative_apply]
  · intro hm
    have hc := (cut_mem 1 testPoint).mp hm.1.1.2
    norm_num [testPoint, point] at hc
  · norm_num [alphaEuclideanDot, LinearForm, normal, point]
  · norm_num [model, cubic, q, point, alphaEuclideanDot, LinearForm, normal]

#print axioms cubic_model_control

end Chapter02AlphaExamples
