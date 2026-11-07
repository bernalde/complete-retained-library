module

public import Chapter02AlphaExamples
public import Chapter02AlphaConvergence
public import Chapter02AlphaConvergenceSource
public import Chapter02ECPAnalysis
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Exact scalar mixed controls for scaled retained histories. The unbounded
scales test the unrestricted valid-scale interpretation, not the practical
W02 update policy. The alpha2 comparison uses the general cap-policy scope.
Only the final bundled theorem is a counted endpoint. -/
noncomputable section
open Chapter02
open scoped BigOperators Topology
namespace Chapter02AlphaConvergenceExamples
attribute [local instance] Classical.propDecidable

abbrev P := Point 1 1
def point (x : ℝ) : P := (fun _ => x, fun _ => 0)
def coord : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector 1))
def model : ModelData 1 1 1 0 where
  g := fun _ p => p.1 0
  A := fun _ _ => 0
  B := fun _ _ => 0
  rhs := fun _ => 0
  c1 := fun _ => -1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0
def mixedRow (_ : Fin 1) (x : RealVector 1) (_ : IntVector 1) := x 0
def derivative (_ : Fin 1) (_ : P) := coord
def domain : Set P := Set.Icc (point (-1)) (point 1)
def sourceSet := sourceMixedFeasible model mixedRow domain
def cuts (q α : ℕ → ℝ) (k : ℕ) : TangentFamily 1 1 1 k :=
  alphaScaledFamily (fun i => point (q i)) (fun _ => Set.univ) derivative (fun i _ => α i)
def master (q α : ℕ → ℝ) (k : ℕ) := model.masterOn (cuts q α k) domain

private lemma interval_mem (b : ℝ) (p : P) :
    p ∈ Set.Icc (point (-1)) (point b) ↔
      -1 ≤ p.1 0 ∧ p.1 0 ≤ b ∧ p.2 0 = 0 := by
  simp [point, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_one]
  constructor
  · rintro ⟨⟨ha,hb⟩,hc,hd⟩
    exact ⟨ha,hc,le_antisymm hd hb⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨⟨ha,by rw [hc]⟩,hb,by rw [hc]⟩

private lemma point_eq (p : P) (hy : p.2 0 = 0) : p = point (p.1 0) := by
  apply Prod.ext <;> ext i <;> fin_cases i
  · rfl
  · exact hy

private lemma domain_integer (p : P) (hp : p ∈ domain) :
    p ∈ IntegerCylinder (n := 1) model.lo model.hi := by
  refine ⟨fun _ => (0 : ℤ),?_,?_⟩
  · intro i; norm_num [model]
  · ext i
    fin_cases i
    simpa using ((interval_mem 1 p).mp hp).2.2

private lemma base_eq : alphaMixedBase model domain = domain := by
  ext p
  constructor
  · exact fun h => h.1.1
  · intro hp
    exact ⟨⟨hp,fun i => Fin.elim0 i⟩,domain_integer p hp⟩

private lemma source_mem (p : P) :
    p ∈ sourceSet ↔ -1 ≤ p.1 0 ∧ p.1 0 ≤ 0 ∧ p.2 0 = 0 := by
  constructor
  · rintro ⟨hp,_,y,_,_,hg⟩
    exact ⟨((interval_mem 1 p).mp hp).1,hg 0,((interval_mem 1 p).mp hp).2.2⟩
  · rintro ⟨ha,hb,hc⟩
    have hp : p ∈ domain := (interval_mem 1 p).mpr ⟨ha,by linarith,hc⟩
    obtain ⟨y,hy,he⟩ := domain_integer p hp
    exact ⟨hp,fun i => Fin.elim0 i,y,hy,he,fun _ => hb⟩

private lemma source_eq : sourceSet = Set.Icc (point (-1)) (point 0) := by
  ext p; exact (source_mem p).trans (interval_mem 0 p).symm

private lemma source_model_eq : sourceSet = model.feasibleOn domain := by
  ext p
  rw [source_mem,source_feasible_iff]
  constructor
  · rintro ⟨ha,hb,hc⟩
    have hp : p ∈ domain := (interval_mem 1 p).mpr ⟨ha,by linarith,hc⟩
    obtain ⟨y,hy,he⟩ := domain_integer p hp
    exact ⟨hp,fun _ => hb,fun i => Fin.elim0 i,y,hy,he⟩
  · rintro ⟨hp,hg,_,_⟩
    exact ⟨((interval_mem 1 p).mp hp).1,hg 0,((interval_mem 1 p).mp hp).2.2⟩

private lemma objective (p : P) : model.objective p = -p.1 0 := by
  simp [ModelData.objective,LinearForm,model,Fin.sum_univ_one]

private lemma actual_derivative (j : Fin 1) (p : P) :
    HasFDerivAt (model.g j) (derivative j p) p := coord.hasFDerivAt

private lemma actual_pseudo (j : Fin 1) (x y : P)
    (h : model.g j y < model.g j x) : derivative j x (y-x) < 0 := by
  exact sub_neg.mpr h

private lemma coord_norm : ‖coord‖ = 1 := by
  apply le_antisymm
  · apply coord.opNorm_le_bound (by norm_num : (0:ℝ) ≤ 1)
    intro p
    simpa [coord] using (norm_le_pi_norm p.1 0).trans (norm_fst_le p)
  · have h := coord.le_opNorm (point 1)
    norm_num [coord,point,Prod.norm_def,Pi.norm_def] at h
    exact h

private lemma scaled_norm (a : ℝ) (ha : 0 ≤ a) : ‖a • coord‖ = a := by
  apply le_antisymm
  · apply (a • coord).opNorm_le_bound ha
    intro p
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,norm_mul,Real.norm_eq_abs,
      abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm p.1 0).trans (norm_fst_le p)) ha
  · have h := (a • coord).le_opNorm (point 1)
    simpa [coord,point,Prod.norm_def,Pi.norm_def,abs_of_nonneg ha] using h

private lemma master_mem (q α : ℕ → ℝ) (k : ℕ) (p : P) :
    p ∈ master q α k ↔ p ∈ domain ∧
      ∀ i : Fin k, q i + α i * (p.1 0-q i) ≤ 0 := by
  constructor
  · intro hp
    exact ⟨hp.1.1.1,fun i => hp.1.1.2 i 0 (Set.mem_univ _)⟩
  · rintro ⟨hp,hcut⟩
    refine ⟨⟨⟨hp,?_⟩,fun i => Fin.elim0 i⟩,domain_integer p hp⟩
    intro i j _
    exact hcut i

private lemma master_interval (q α : ℕ → ℝ) (hq0 : q 0 = 1)
    (hmono : Antitone q)
    (hcut : ∀ i x, q i + α i * (x-q i) ≤ 0 ↔ x ≤ q (i+1)) (n : ℕ) :
    master q α n = Set.Icc (point (-1)) (point (q n)) := by
  ext p
  rw [master_mem,interval_mem]
  constructor
  · rintro ⟨hp,hcuts⟩
    have hd := (interval_mem 1 p).mp hp
    refine ⟨hd.1,?_,hd.2.2⟩
    cases n with
    | zero => simpa [hq0] using hd.2.1
    | succ n => exact (hcut n _).mp (hcuts ⟨n,Nat.lt_succ_self n⟩)
  · rintro ⟨ha,hb,hc⟩
    refine ⟨(interval_mem 1 p).mpr ⟨ha,?_,hc⟩,?_⟩
    · exact hb.trans (by simpa [hq0] using hmono (Nat.zero_le n))
    · intro i
      exact (hcut i _).mpr (hb.trans (hmono (Nat.succ_le_of_lt i.isLt)))

private lemma interval_unique (b : ℝ) (hb : -1 ≤ b) :
    IsMinimizer (Set.Icc (point (-1)) (point b)) model.objective (point b) ∧
    ∀ p, IsMinimizer (Set.Icc (point (-1)) (point b)) model.objective p → p = point b := by
  have hp : point b ∈ Set.Icc (point (-1)) (point b) :=
    (interval_mem b _).mpr ⟨hb,le_rfl,rfl⟩
  refine ⟨⟨hp,?_⟩,?_⟩
  · intro p h
    rw [objective,objective]
    exact neg_le_neg ((interval_mem b p).mp h).2.1
  · intro p h
    have hbounds := (interval_mem b p).mp h.1
    have hm := h.2 (point b) hp
    rw [objective,objective] at hm
    have he : p.1 0 = b := by dsimp [point] at hm; linarith
    rw [point_eq p hbounds.2.2,he]

def weight (n : ℕ) : ℝ := (1/2 : ℝ)^(n+2)
def growingScale (n : ℕ) : ℝ := (2 : ℝ)^(n+2)
def stalled (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (1-weight i)
def half (n : ℕ) : ℝ := (1/2 : ℝ)^n

private lemma weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity
private lemma weight_lt_one (n : ℕ) : weight n < 1 := by
  exact pow_lt_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) (by omega)
private lemma scale_pos (n : ℕ) : 0 < growingScale n := by unfold growingScale; positivity
private lemma scale_ge_one (n : ℕ) : 1 ≤ growingScale n := by
  exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
private lemma inverse_weights (n : ℕ) : growingScale n * weight n = 1 := by
  simp [growingScale,weight,← mul_pow]
private lemma stalled_zero : stalled 0 = 1 := by simp [stalled]
private lemma stalled_succ (n : ℕ) : stalled (n+1) = stalled n*(1-weight n) := by
  simp [stalled,Finset.prod_range_succ]
private lemma weights_sum (n : ℕ) :
    1-(∑ i ∈ Finset.range n, weight i) = 1/2+(1/2:ℝ)^(n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : (1/2:ℝ)^(n+2) = (1/2:ℝ)^(n+1)/2 := by rw [pow_succ]; ring
    simp only [weight] at ih ⊢
    rw [show n+1+1=n+2 by omega]
    linarith

private lemma stalled_bounds (n : ℕ) :
    1/2+(1/2:ℝ)^(n+1) ≤ stalled n ∧ stalled n ≤ 1 := by
  induction n with
  | zero => norm_num [stalled_zero]
  | succ n ih =>
    rw [stalled_succ]
    have hw := weight_pos n
    have hw1 := weight_lt_one n
    have hp : (1/2:ℝ)^(n+2) = (1/2:ℝ)^(n+1)/2 := by rw [pow_succ]; ring
    have hq : 0 ≤ stalled n := by
      have ht : 0 < (1/2:ℝ)^(n+1) := by positivity
      linarith
    have hmul := mul_le_mul_of_nonneg_right ih.2 hw.le
    constructor
    · dsimp [weight] at hmul ⊢
      rw [show n+1+1=n+2 by omega]
      nlinarith
    · nlinarith

private lemma stalled_pos (n : ℕ) : 0 < stalled n := by
  have h := (stalled_bounds n).1
  have hp : 0 < (1/2:ℝ)^(n+1) := by positivity
  linarith
private lemma stalled_step_lt (n : ℕ) : stalled (n+1) < stalled n := by
  rw [stalled_succ]
  nlinarith [stalled_pos n,weight_pos n]
private lemma stalled_antitone : Antitone stalled :=
  antitone_nat_of_succ_le (fun n => (stalled_step_lt n).le)

private lemma stalled_cut (n : ℕ) (x : ℝ) :
    stalled n+growingScale n*(x-stalled n) ≤ 0 ↔ x ≤ stalled (n+1) := by
  have hp := scale_pos n
  have he := congrArg (fun z => stalled n*z) (inverse_weights n)
  rw [stalled_succ]
  constructor <;> intro h
  · have hz : growingScale n * (x-stalled n*(1-weight n)) ≤ 0 := by nlinarith
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left h hp.le
    nlinarith

private lemma stalled_master (n : ℕ) :
    master stalled growingScale n = Set.Icc (point (-1)) (point (stalled n)) :=
  master_interval stalled growingScale stalled_zero
    stalled_antitone stalled_cut n

private lemma strong_validity (q a : ℝ) (hq : 0 ≤ q) (ha : 1 ≤ a)
    (p : P) (hp : p ∈ sourceSet) : q+a*(p.1 0-q) ≤ model.g 0 p := by
  have hs := ((source_mem p).mp hp).2.1
  have hm := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr (hs.trans hq))
  change q+a*(p.1 0-q) ≤ p.1 0
  nlinarith

private lemma unbounded_norms : ∀ C : ℝ, ∃ n, C < ‖growingScale n • coord‖ := by
  intro C
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1:ℝ)<2)
  refine ⟨n,?_⟩
  rw [scaled_norm _ (scale_pos n).le]
  have hp : 0 ≤ (2:ℝ)^n := by positivity
  simp only [growingScale,pow_add,pow_two]
  nlinarith

private lemma half_pos (n : ℕ) : 0 < half n := by unfold half; positivity
private lemma half_succ (n : ℕ) : half (n+1) = half n/2 := by simp [half,pow_succ]; ring
private lemma half_antitone : Antitone half := by
  apply antitone_nat_of_succ_le
  intro n
  rw [half_succ]
  linarith [half_pos n]
private lemma half_cut (n : ℕ) (x : ℝ) :
    half n+2*(x-half n) ≤ 0 ↔ x ≤ half (n+1) := by rw [half_succ]; constructor <;> intro h <;> linarith
private lemma half_master (n : ℕ) :
    master half (fun _ => 2) n = Set.Icc (point (-1)) (point (half n)) :=
  master_interval half (fun _ => 2) (by norm_num [half])
    half_antitone half_cut n
private lemma half_limit : Filter.Tendsto half Filter.atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private lemma point_continuous : Continuous point := by unfold point; fun_prop
private lemma half_point_limit :
    Filter.Tendsto (fun n => point (half n)) Filter.atTop (𝓝 (point 0)) :=
  point_continuous.continuousAt.tendsto.comp half_limit

private lemma unit_scale_master :
    master (fun _ => 1) (fun _ => 1) 1 = sourceSet := by
  ext p
  rw [master_mem,source_mem]
  simp only [Fin.forall_fin_one]
  constructor
  · rintro ⟨hp,hcut⟩
    have hh := (interval_mem 1 p).mp hp
    exact ⟨hh.1,by linarith,hh.2.2⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨(interval_mem 1 p).mpr ⟨ha,by linarith,hc⟩,by linarith⟩

/-- Actual mixed domain, ambient derivatives, original source identities and
nonconstant objective. The norm is the inherited product/operator norm. -/
def ScalarModelFacts : Prop :=
  IsCompact domain ∧
  alphaMixedBase model domain = domain ∧
  sourceSet = Set.Icc (point (-1)) (point 0) ∧
  sourceSet = model.feasibleOn domain ∧
  (∀ j x y, model.g j (x,fun i => (y i : ℝ)) = mixedRow j x y) ∧
  (∀ j p, HasFDerivAt (model.g j) (derivative j p) p) ∧
  (∀ j, Continuous (derivative j)) ∧
  (∀ j x y, model.g j y < model.g j x → derivative j x (y-x) < 0) ∧
  ‖coord‖ = 1 ∧
  (∀ p, model.objective p = -p.1 0) ∧
  IsMinimizer sourceSet model.objective (point 0) ∧
  (∀ p, IsMinimizer sourceSet model.objective p → p = point 0)

private lemma scalar_model_facts : ScalarModelFacts := by
  have hmin := interval_unique 0 (by norm_num)
  rw [← source_eq] at hmin
  exact ⟨isCompact_Icc,base_eq,source_eq,source_model_eq,by intros; rfl,
    actual_derivative,fun _ => continuous_const,actual_pseudo,coord_norm,
    objective,hmin⟩

/-- Every static cut is retained, every complete master has its stated unique
global minimizer, all original-feasible row values dominate every cut, yet
positive violations persist under the unbounded scales. -/
def GrowingScaleFacts : Prop :=
  stalled 0 = 1 ∧
  (∀ n, stalled (n+1) = stalled n*(1-weight n)) ∧
  (∀ n, stalled n = ∏ i ∈ Finset.range n, (1-weight i)) ∧
  (∀ n, 1-(∑ i ∈ Finset.range n,weight i) = 1/2+(1/2:ℝ)^(n+1)) ∧
  (∀ n, 1/2+(1/2:ℝ)^(n+1) ≤ stalled n ∧ stalled n ≤ 1) ∧
  (∀ n, stalled (n+1) < stalled n) ∧
  (∀ n, 1 ≤ growingScale n ∧ growingScale n * weight n = 1) ∧
  (∀ n p, p ∈ sourceSet →
    model.g 0 (point (stalled n)) +
      growingScale n * derivative 0 (point (stalled n)) (p-point (stalled n))
        ≤ model.g 0 p) ∧
  (∀ n,
    master stalled growingScale n = Set.Icc (point (-1)) (point (stalled n)) ∧
    IsMinimizer (master stalled growingScale n) model.objective (point (stalled n)) ∧
    ∀ p, IsMinimizer (master stalled growingScale n) model.objective p →
      p = point (stalled n)) ∧
  (∀ ε : ℝ, 0 ≤ ε → ε < 1/2 → ∀ n, ε < model.g 0 (point (stalled n))) ∧
  (∀ n, ‖growingScale n • derivative 0 (point (stalled n))‖ = growingScale n) ∧
  (∀ C : ℝ, ∃ n, C < ‖growingScale n • derivative 0 (point (stalled n))‖) ∧
  ¬ ∃ C : ℝ, ∀ i k : ℕ, i < k → (1/4:ℝ) < model.g 0 (point (stalled i)) →
    ‖growingScale i • derivative 0 (point (stalled i))‖ ≤ C

private lemma growing_scale_facts : GrowingScaleFacts := by
  refine ⟨stalled_zero,stalled_succ,fun _ => rfl,weights_sum,stalled_bounds,
    stalled_step_lt,fun n => ⟨scale_ge_one n,inverse_weights n⟩,?_,?_,?_,
    fun n => scaled_norm _ (scale_pos n).le,unbounded_norms,?_⟩
  · intro n p hp
    exact strong_validity _ _ (stalled_pos n).le (scale_ge_one n) p hp
  · intro n
    refine ⟨stalled_master n,?_⟩
    rw [stalled_master]
    exact interval_unique _ (by linarith [stalled_pos n])
  · intro ε _ he n
    have hb := (stalled_bounds n).1
    have hh : 0 < (1/2:ℝ)^(n+1) := by positivity
    change ε < stalled n
    linarith
  · rintro ⟨C,hC⟩
    obtain ⟨i,hi⟩ := unbounded_norms C
    have hb := (stalled_bounds i).1
    have hh : 0 < (1/2:ℝ)^(i+1) := by positivity
    have hc := hC i (i+1) (by omega) (by change (1/4:ℝ)<stalled i; linarith)
    exact (not_lt_of_ge hc) hi

private lemma dynamic_static_eq (q α : ℕ → ℝ) (hpos : ∀ n, 0 < q n) (n : ℕ) :
    alphaDynamicMaster domain model.g derivative 0 (fun i => point (q i))
      (fun _ => 0) (fun i _ => α i) n = master q α n := by
  ext p
  rw [master_mem]
  constructor
  · intro h
    exact ⟨h.1,fun i => h.2 i i.isLt (hpos i)⟩
  · rintro ⟨hp,hcut⟩
    exact ⟨hp,fun i hi _ => hcut ⟨i,hi⟩⟩

private lemma half_dynamic_mem (n : ℕ) :
    point (half n) ∈ alphaDynamicMaster domain model.g derivative 0
      (fun i => point (half i)) (fun _ => 0) (fun _ _ => 2) n := by
  rw [dynamic_static_eq half (fun _ => 2) half_pos,half_master]
  exact (interval_unique (half n) (by linarith [half_pos n])).1.1

private lemma half_cap_limits : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    (∀ n, ((Finset.range n).filter (fun i => ε < half i)).card ≤ N) ∧
    {i | ε < half i}.Finite ∧ ∀ᶠ k in Filter.atTop, half k ≤ ε := by
  have hc := alpha_dynamic_cap_limits domain model.g derivative 0
    (fun i => point (half i)) (fun _ => 0) (fun _ _ => 2) isCompact_Icc
    half_dynamic_mem (fun _ _ => le_rfl) (by
      intro ε _ _
      refine ⟨2,by norm_num,?_⟩
      intro i k _ _
      change ‖(2:ℝ) • coord‖ ≤ 2
      rw [scaled_norm 2 (by norm_num)])
  intro ε hε
  simpa [model,point] using hc ε hε hε.le

/-- Fixed alpha2 is in the general cap-policy helper, not asserted to satisfy
the lower bound of the conservative exhibited A policy. Exact alpha1 succeeds
after the first cut. No finite alpha2 trial is original-feasible. -/
def BoundedScaleFacts : Prop :=
  (∀ n, half n = (1/2:ℝ)^n ∧ 0 < half n) ∧
  (∀ n, master half (fun _ => 2) n = Set.Icc (point (-1)) (point (half n)) ∧
    IsMinimizer (master half (fun _ => 2) n) model.objective (point (half n)) ∧
    ∀ p, IsMinimizer (master half (fun _ => 2) n) model.objective p → p = point (half n)) ∧
  (∀ n p, p ∈ sourceSet → model.g 0 (point (half n)) +
    2 * derivative 0 (point (half n)) (p-point (half n)) ≤ model.g 0 p) ∧
  (∀ n, ‖(2:ℝ) • derivative 0 (point (half n))‖ = 2) ∧
  (∀ n, alphaDynamicMaster domain model.g derivative 0 (fun i => point (half i))
    (fun _ => 0) (fun _ _ => 2) n = master half (fun _ => 2) n) ∧
  (∀ n, point (half n) ∈ alphaDynamicMaster domain model.g derivative 0
    (fun i => point (half i)) (fun _ => 0) (fun _ _ => 2) n) ∧
  (∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    (∀ n, ((Finset.range n).filter (fun i => ε < half i)).card ≤ N) ∧
    {i | ε < half i}.Finite ∧ ∀ᶠ k in Filter.atTop, half k ≤ ε) ∧
  (∀ n, point (half n) ∉ sourceSet) ∧
  Filter.Tendsto (fun n => point (half n)) Filter.atTop (𝓝 (point 0)) ∧
  IsMinimizer sourceSet model.objective (point 0) ∧
  master (fun _ => 1) (fun _ => 1) 1 = sourceSet ∧
  IsMinimizer (master (fun _ => 1) (fun _ => 1) 1) model.objective (point 0)

private lemma bounded_scale_facts : BoundedScaleFacts := by
  have hmin : IsMinimizer sourceSet model.objective (point 0) := by
    rw [source_eq]
    exact (interval_unique 0 (by norm_num)).1
  refine ⟨fun n => ⟨rfl,half_pos n⟩,?_,?_,fun _ => scaled_norm 2 (by norm_num),
    dynamic_static_eq half (fun _ => 2) half_pos,half_dynamic_mem,half_cap_limits,
    ?_,half_point_limit,hmin,unit_scale_master,?_⟩
  · intro n
    refine ⟨half_master n,?_⟩
    rw [half_master]
    exact interval_unique _ (by linarith [half_pos n])
  · intro n p hp
    exact strong_validity _ 2 (half_pos n).le (by norm_num) p hp
  · intro n hn
    have h := ((source_mem _).mp hn).2.1
    exact (not_lt_of_ge h) (half_pos n)
  · rwa [unit_scale_master]

/-- Actual application of the new compact scale theorem to the accepted
nonconvex cubic source. Its old objective is constant; the scalar controls
above, separately, prove the nonconstant-objective master statements. -/
def CubicScaleFacts : Prop :=
  let B := Chapter02AlphaExamples.domain
  let g := Chapter02AlphaExamples.model.g
  let G := Chapter02AlphaExamples.derivative
  ¬ ConvexOn ℝ B (g 0) ∧
  alphaScaleFeasible B g = Chapter02AlphaExamples.sourceSet ∧
  (∀ j x y, g j (x,fun i => (y i : ℝ)) = Chapter02AlphaExamples.mixedRow j x y) ∧
  (∀ j p, HasFDerivAt (g j) (G j p) p) ∧
  (∀ j, Continuous (G j)) ∧
  (∀ j x y, g j y < g j x → G j x (y-x) < 0) ∧
  (∃ (a : Fin 1 → P → ℝ) (M : ℝ),
    (∀ j q, 1 ≤ a j q) ∧
    (∀ j q, q ∉ B ∨ g j q ≤ 0 → a j q = 1) ∧
    1 ≤ M ∧ (∀ j q, q ∈ B → ‖G j q‖ ≤ M) ∧
    (∀ j q, q ∈ B → 0 < g j q → ∀ α : ℝ, a j q ≤ α →
      ∀ p ∈ alphaScaleFeasible B g,
        g j q + α * G j q (p-q) ≤ g j p ∧ g j p ≤ 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧
      ∀ j q, q ∈ B → ε ≤ g j q → a j q ≤ A ∧
        ∀ ρ : ℝ, 1 ≤ ρ → ∀ α : ℝ, a j q ≤ α → α ≤ ρ * a j q →
          ‖α • G j q‖ ≤ ρ * A * M))

private lemma cubic_scale_facts : CubicScaleFacts := by
  obtain ⟨hd,hp,hn,he,hbase,hsource,_,hfeas,_⟩ :=
    Chapter02AlphaExamples.cubic_model_control
  have hG : ∀ j, Continuous (Chapter02AlphaExamples.derivative j) := by
    intro j
    unfold Chapter02AlphaExamples.derivative
    fun_prop
  have heq : alphaScaleFeasible Chapter02AlphaExamples.domain
      Chapter02AlphaExamples.model.g = Chapter02AlphaExamples.sourceSet := by
    rw [hsource]
    ext p
    constructor
    · rintro ⟨hq,hg⟩
      have hb : p ∈ alphaMixedBase Chapter02AlphaExamples.model Chapter02AlphaExamples.domain :=
        hbase.symm ▸ hq
      change ((p ∈ Chapter02AlphaExamples.domain ∧
        ∀ j, Chapter02AlphaExamples.model.g j p ≤ 0) ∧
        p ∈ Chapter02AlphaExamples.model.linearRegion) ∧
        p ∈ IntegerCylinder Chapter02AlphaExamples.model.lo Chapter02AlphaExamples.model.hi
      exact ⟨⟨⟨hq,hg⟩,hb.1.2⟩,hb.2⟩
    · intro h
      obtain ⟨hq,hg,_,_⟩ := (source_feasible_iff _ _ _).mp h
      exact ⟨hq,hg⟩
  have hne : (alphaScaleFeasible Chapter02AlphaExamples.domain
      Chapter02AlphaExamples.model.g).Nonempty := by
    rw [heq]
    exact ⟨_,hfeas⟩
  refine ⟨hn,heq,he,hd,hG,hp,?_⟩
  exact alpha_uniform_threshold_scale_control Chapter02AlphaExamples.domain
    Chapter02AlphaExamples.model.g Chapter02AlphaExamples.derivative
    isCompact_Icc hne (fun j p _ => hd j p) (fun j => (hG j).continuousOn)
    (fun j x _ y _ h => hp j x y h)

/-- One counted endpoint: actual mixed-model scale controls and a genuine
nonconvex application of the uniform safe-scale theorem. The strong W98
validity control is not a counterexample to the W02 numerical update policy. -/
theorem alpha_scale_history_controls :
    ScalarModelFacts ∧ GrowingScaleFacts ∧ BoundedScaleFacts ∧ CubicScaleFacts :=
  ⟨scalar_model_facts,growing_scale_facts,bounded_scale_facts,cubic_scale_facts⟩

end Chapter02AlphaConvergenceExamples

#print axioms Chapter02AlphaConvergenceExamples.alpha_scale_history_controls
