module

public import Chapter06
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! Chapter 7: literal split-variable and maximum-coordinate norm lifts,
their global optimizer correspondence over an arbitrary base set, and selected
regularizer/bound repairs. These results do not certify a numerical callback,
KKT existence, historical benchmark or complete ROA execution. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter06
namespace Chapter07

abbrev Vec (N : ℕ) := Fin N → ℝ
def l1 {N : ℕ} (v : Vec N) : ℝ := ∑ i, |v i|
def posPart {N : ℕ} (v : Vec N) : Vec N := fun i => max (v i) 0
def negPart {N : ℕ} (v : Vec N) : Vec N := fun i => max (-v i) 0

theorem split_identity (a : ℝ) : max a 0 - max (-a) 0 = a := by
  by_cases h : 0 ≤ a
  · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ 0)]; ring
  · rw [max_eq_right (by linarith : a ≤ 0), max_eq_left (by linarith : 0 ≤ -a)]; ring

theorem split_abs_identity (a : ℝ) : max a 0 + max (-a) 0 = |a| := by
  by_cases h : 0 ≤ a
  · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ 0), abs_of_nonneg h]; ring
  · rw [max_eq_right (by linarith : a ≤ 0), max_eq_left (by linarith : 0 ≤ -a),
      abs_of_nonpos (by linarith : a ≤ 0)]; ring

theorem abs_le_split (v a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : a-b=v) : |v| ≤ a+b := by
  rw [abs_le]; constructor <;> linarith

def L1Lift {E : Type*} {N : ℕ} (A : Set E) (v : E → Vec N) :
    Set (E × Vec N × Vec N) :=
  {p | p.1 ∈ A ∧ (∀ i, 0 ≤ p.2.1 i) ∧ (∀ i, 0 ≤ p.2.2 i) ∧
    ∀ i, p.2.1 i-p.2.2 i=v p.1 i}
def l1LiftCost {E : Type*} {N : ℕ} (p : E × Vec N × Vec N) : ℝ :=
  ∑ i, (p.2.1 i+p.2.2 i)
def l1Canonical {E : Type*} {N : ℕ} (v : E → Vec N) (z : E) :
    E × Vec N × Vec N := (z,posPart (v z),negPart (v z))

theorem l1_canonical_feasible {E : Type*} {N : ℕ} (A : Set E) (v : E → Vec N)
    {z : E} (hz : z ∈ A) : l1Canonical v z ∈ L1Lift A v := by
  refine ⟨hz, ?_, ?_, ?_⟩
  · intro i; exact le_max_right _ _
  · intro i; exact le_max_right _ _
  · intro i; exact split_identity _

theorem l1_canonical_cost {E : Type*} {N : ℕ} (v : E → Vec N) (z : E) :
    l1LiftCost (l1Canonical v z) = l1 (v z) := by
  unfold l1LiftCost l1Canonical posPart negPart l1
  apply Finset.sum_congr rfl; intro i _; exact split_abs_identity _

theorem l1_lift_dominates {E : Type*} {N : ℕ} (A : Set E) (v : E → Vec N)
    {p : E × Vec N × Vec N} (hp : p ∈ L1Lift A v) :
    l1 (v p.1) ≤ l1LiftCost p := by
  unfold l1 l1LiftCost
  apply Finset.sum_le_sum
  intro i _; exact abs_le_split _ _ _ (hp.2.1 i) (hp.2.2.1 i) (hp.2.2.2 i)

theorem l1_minimizer_lift {E : Type*} {N : ℕ} (A : Set E) (v : E → Vec N)
    {z : E} (hz : IsMinimizer A (fun z => l1 (v z)) z) :
    IsMinimizer (L1Lift A v) l1LiftCost (l1Canonical v z) := by
  refine ⟨l1_canonical_feasible A v hz.1, ?_⟩
  intro q hq; rw [l1_canonical_cost]
  exact (hz.2 q.1 hq.1).trans (l1_lift_dominates A v hq)

theorem l1_minimizer_projection {E : Type*} {N : ℕ} (A : Set E) (v : E → Vec N)
    {p : E × Vec N × Vec N} (hp : IsMinimizer (L1Lift A v) l1LiftCost p) :
    IsMinimizer A (fun z => l1 (v z)) p.1 ∧ l1LiftCost p=l1 (v p.1) := by
  have hc := hp.2 (l1Canonical v p.1) (l1_canonical_feasible A v hp.1.1)
  rw [l1_canonical_cost] at hc
  have he : l1LiftCost p=l1 (v p.1) := le_antisymm hc (l1_lift_dominates A v hp.1)
  refine ⟨⟨hp.1.1, ?_⟩, he⟩
  intro z hz
  have h := hp.2 (l1Canonical v z) (l1_canonical_feasible A v hz)
  simpa only [he,l1_canonical_cost] using h

def linf {N : ℕ} [Nonempty (Fin N)] (v : Vec N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |v i|)

theorem linf_le_iff {N : ℕ} [Nonempty (Fin N)] (v : Vec N) (s : ℝ) :
    linf v ≤ s ↔ ∀ i, |v i| ≤ s := by
  simp [linf,Finset.sup'_le_iff]

theorem linf_nonneg {N : ℕ} [Nonempty (Fin N)] (v : Vec N) : 0 ≤ linf v := by
  let i : Fin N := Classical.choice inferInstance
  exact (abs_nonneg (v i)).trans
    (Finset.le_sup' (fun i => |v i|) (Finset.mem_univ i))

def LInfLift {E : Type*} {N : ℕ} (A : Set E) (v : E → Vec N) : Set (E × ℝ) :=
  {p | p.1 ∈ A ∧ 0 ≤ p.2 ∧ ∀ i, v p.1 i ≤ p.2 ∧ -v p.1 i ≤ p.2}

theorem linf_lift_feasible_iff {E : Type*} {N : ℕ} [Nonempty (Fin N)]
    (A : Set E) (v : E → Vec N) (p : E × ℝ) :
    p ∈ LInfLift A v ↔ p.1 ∈ A ∧ linf (v p.1) ≤ p.2 := by
  constructor
  · intro h; refine ⟨h.1,(linf_le_iff _ _).mpr ?_⟩
    intro i; rw [abs_le]; exact ⟨by linarith [(h.2.2 i).2],(h.2.2 i).1⟩
  · rintro ⟨ha,h⟩
    refine ⟨ha,(linf_nonneg _).trans h, ?_⟩
    intro i
    have hi := (linf_le_iff _ _).mp h i
    rw [abs_le] at hi; exact ⟨hi.2,by linarith [hi.1]⟩

theorem linf_minimizer_lift {E : Type*} {N : ℕ} [Nonempty (Fin N)]
    (A : Set E) (v : E → Vec N) {z : E}
    (hz : IsMinimizer A (fun z => linf (v z)) z) :
    IsMinimizer (LInfLift A v) Prod.snd (z,linf (v z)) := by
  refine ⟨(linf_lift_feasible_iff A v _).mpr ⟨hz.1,le_refl _⟩, ?_⟩
  intro q hq
  have hh := (linf_lift_feasible_iff A v q).mp hq
  exact (hz.2 q.1 hh.1).trans hh.2

theorem linf_minimizer_projection {E : Type*} {N : ℕ} [Nonempty (Fin N)]
    (A : Set E) (v : E → Vec N) {p : E × ℝ}
    (hp : IsMinimizer (LInfLift A v) Prod.snd p) :
    IsMinimizer A (fun z => linf (v z)) p.1 ∧ p.2=linf (v p.1) := by
  have hh := (linf_lift_feasible_iff A v p).mp hp.1
  have he : p.2=linf (v p.1) := le_antisymm
    (hp.2 (p.1,linf (v p.1)) ((linf_lift_feasible_iff A v _).mpr ⟨hh.1,le_refl _⟩)) hh.2
  refine ⟨⟨hh.1, ?_⟩, he⟩
  intro z hz
  simpa only [he] using hp.2 (z,linf (v z))
    ((linf_lift_feasible_iff A v _).mpr ⟨hz,le_refl _⟩)

def SourceLevel {n m l r k : ℕ} (d : ModelData n m l r) (f : Point n m → ℝ)
    (c : TangentFamily n m l k) (Df : Fin k → Point n m →L[ℝ] ℝ)
    (S : Set (Point n m)) (LB UB α : ℝ) : Set (Point n m × ℝ) :=
  {p ∈ EpigraphMaster d f c Df S | p.2 ≤ Level LB UB α}
def sourceDisplacement {n m : ℕ} (center : Point n m) (p : Point n m × ℝ) : Vec (n+m) :=
  Fin.addCases (fun i => p.1.1 i-center.1 i) (fun j => p.1.2 j-center.2 j)

theorem source_l1_optimizer_correspondence {n m l r k : ℕ}
    (d : ModelData n m l r) (f : Point n m → ℝ)
    (c : TangentFamily n m l k) (Df : Fin k → Point n m →L[ℝ] ℝ)
    (S : Set (Point n m)) (LB UB α : ℝ) (center : Point n m)
    {p : (Point n m × ℝ) × Vec (n+m) × Vec (n+m)}
    (hp : IsMinimizer (L1Lift (SourceLevel d f c Df S LB UB α)
      (sourceDisplacement center)) l1LiftCost p) :
    IsMinimizer (SourceLevel d f c Df S LB UB α)
      (fun z => l1 (sourceDisplacement center z)) p.1 :=
  (l1_minimizer_projection _ _ hp).1

theorem source_linf_optimizer_correspondence {n m l r k : ℕ} [Nonempty (Fin (n+m))]
    (d : ModelData n m l r) (f : Point n m → ℝ)
    (c : TangentFamily n m l k) (Df : Fin k → Point n m →L[ℝ] ℝ)
    (S : Set (Point n m)) (LB UB α : ℝ) (center : Point n m)
    {p : (Point n m × ℝ) × ℝ}
    (hp : IsMinimizer (LInfLift (SourceLevel d f c Df S LB UB α)
      (sourceDisplacement center)) Prod.snd p) :
    IsMinimizer (SourceLevel d f c Df S LB UB α)
      (fun z => linf (sourceDisplacement center z)) p.1 :=
  (linf_minimizer_projection _ _ hp).1

theorem completed_square (g ρ z : ℝ) (hρ : ρ ≠ 0) :
    g*z+ρ*z^2 = ρ*(z+g/(2*ρ))^2-g^2/(4*ρ) := by
  field_simp; ring

theorem scaled_center_minimizer (g ρ : ℝ) (hρ : 0 < ρ) :
    IsMinimizer Set.univ (fun z : ℝ => g*z+ρ*z^2) (-g/(2*ρ)) := by
  refine ⟨Set.mem_univ _, ?_⟩
  intro z _
  change g*(-g/(2*ρ))+ρ*(-g/(2*ρ))^2 ≤ g*z+ρ*z^2
  rw [completed_square g ρ z (ne_of_gt hρ),completed_square g ρ _ (ne_of_gt hρ)]
  have hh := mul_nonneg (le_of_lt hρ) (sq_nonneg (z+g/(2*ρ)))
  simp only [neg_div, neg_add_cancel, zero_pow (by decide : 2 ≠ 0), mul_zero]
  linarith

theorem zero_hessian_no_center : ¬ ∃ z : ℝ, IsMinimizer Set.univ (fun y => -y) z := by
  rintro ⟨z,hz⟩
  have h := hz.2 (z+1) (Set.mem_univ _)
  change -z ≤ -(z+1) at h
  linarith

theorem translated_identity_not_norm : Real.sqrt ((0-(1:ℝ))^2) ≠ 0 := by norm_num

theorem zero_gradient_scaling (d : ℝ) (_hd : 0 < d) :
    |(0:ℝ)/(2*d)|=0 ∧ ¬ (0 < |(0:ℝ)/(2*d)|) := by simp

theorem finite_scaled_center_minimizer {N : ℕ} (g : Vec N) (ρ : ℝ) (hρ : 0 < ρ) :
    IsMinimizer Set.univ (fun z : Vec N => ∑ i, (g i*z i+ρ*(z i)^2))
      (fun i => -g i/(2*ρ)) := by
  refine ⟨Set.mem_univ _, ?_⟩
  intro z _
  apply Finset.sum_le_sum
  intro i _
  exact (scaled_center_minimizer (g i) ρ hρ).2 (z i) (Set.mem_univ _)

theorem scaled_center_distance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E) (d : ℝ) (hd : 0 < d) (hg : g ≠ 0) :
    ‖(-((2*(‖g‖/(2*d)))⁻¹)) • g‖ = d := by
  have hn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hρ : 0 < ‖g‖/(2*d) := div_pos hn (mul_pos (by norm_num) hd)
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv,
    abs_of_pos (mul_pos (by norm_num) hρ)]
  field_simp

theorem example_y4_fiber_singleton (x : ℝ) (h : (x-1)^2/40 ≤ 0) : x=1 := by
  have hh := sq_nonneg (x-1)
  have he : (x-1)^2=0 := by linarith
  nlinarith

theorem example_y4_no_slater : ¬ ∃ x : ℝ, (x-1)^2/40 < 0 := by
  rintro ⟨x,h⟩; nlinarith [sq_nonneg (x-1)]

def cycleRelaxed : Set (ℝ × ℝ) := {p | -1 ≤ p.1 ∧ p.1 ≤ 1 ∧
  0 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.1^2+1/4-p.2 ≤ 0}
theorem cycle_relaxation_optimum :
    IsMinimizer cycleRelaxed (fun p => p.2-p.1) (1/2,1/2) := by
  refine ⟨by norm_num [cycleRelaxed], ?_⟩
  intro p hp
  change (1/2:ℝ)-(1/2:ℝ) ≤ p.2-p.1
  nlinarith [hp.2.2.2.2,sq_nonneg (p.1-1/2)]

def cycleMaster : Set (ℝ × Bool × ℝ) := {p | -1 ≤ p.1 ∧ p.1 ≤ 1 ∧
  p.1-bit p.2.1 ≤ 0 ∧ bit p.2.1-p.1 ≤ p.2.2}
theorem cycle_master_bad_fiber_optimal :
    IsMinimizer cycleMaster (fun p => p.2.2) (0,false,0) := by
  refine ⟨by norm_num [cycleMaster,bit], ?_⟩
  intro p hp
  change (0:ℝ) ≤ p.2.2
  linarith [hp.2.2.1,hp.2.2.2]

theorem cycle_restoration_optimum :
    IsMinimizer (Set.Icc (-1:ℝ) 1) (fun x => x^2+1/4) 0 := by
  refine ⟨by norm_num, ?_⟩
  intro x _
  change (0:ℝ)^2+1/4 ≤ x^2+1/4
  nlinarith [sq_nonneg x]

theorem cycle_fiber_infeasible_and_inactive (x : ℝ) :
    0 < x^2+(1/4:ℝ) ∧ x^2+(1/4:ℝ) ≠ 0 := by
  constructor <;> nlinarith [sq_nonneg x]

theorem quadratic_singular_no_center :
    ¬ ∃ p : ℝ × ℝ, IsMinimizer Set.univ (fun q => q.1^2-q.2) p := by
  rintro ⟨p,hp⟩
  have h := hp.2 (p.1,p.2+1) (Set.mem_univ _)
  change p.1^2-p.2 ≤ p.1^2-(p.2+1) at h
  linarith

def callbackCost (p : ℝ × Fin 3) : ℝ := p.1-(p.2:ℝ)
def callbackBase : Set (ℝ × Fin 3) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1}
def callbackFeasible : Set (ℝ × Fin 3) := {p ∈ callbackBase | p.1^2-1 ≤ 0}
def callbackLevel : Set (ℝ × Fin 3) := {p ∈ callbackBase | callbackCost p ≤ -1}
def callbackDistance (p : ℝ × Fin 3) : ℝ := |p.1|+(p.2:ℝ)
theorem callback_projection_selects_one :
    IsMinimizer callbackLevel callbackDistance (0,1) := by
  refine ⟨by norm_num [callbackLevel,callbackBase,callbackCost], ?_⟩
  rintro ⟨x,y⟩ hp
  fin_cases y <;> norm_num [callbackLevel,callbackBase,callbackCost,
    callbackDistance] at *
  all_goals nlinarith [abs_nonneg x]

theorem callback_original_optimum_two :
    IsMinimizer callbackFeasible callbackCost (0,2) := by
  refine ⟨by norm_num [callbackFeasible,callbackBase], ?_⟩
  rintro ⟨x,y⟩ hp
  fin_cases y <;> norm_num [callbackCost] <;> linarith [hp.1.1]

theorem callback_stored_return_gap :
    callbackCost (0,2)=-2 ∧ callbackCost (0,1)=-1 ∧
    callbackCost (0,2)<callbackCost (0,1) ∧
    callbackCost (0,1)-callbackCost (0,2)=1 := by norm_num [callbackCost]

theorem example_g3_squared (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (11/40:ℝ)*y^((3:ℝ)/2) ≤ 10*Real.sqrt (x+1/10) ↔
      121*y^3 ≤ 160000*(x+1/10) := by
  have hpow : (y^((3:ℝ)/2))^2=y^3 := by
    rw [← Real.rpow_two,← Real.rpow_mul hy]
    norm_num [Real.rpow_natCast]
  have hs := Real.sq_sqrt (by linarith : 0 ≤ x+1/10)
  have ha : 0 ≤ (11/40:ℝ)*y^((3:ℝ)/2) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hy _)
  have hb : 0 ≤ (10:ℝ)*Real.sqrt (x+1/10) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  constructor
  · intro h
    have hh := (sq_le_sq₀ ha hb).mpr h
    rw [mul_pow,mul_pow,hpow,hs] at hh
    norm_num at hh
    nlinarith
  · intro h
    apply (sq_le_sq₀ ha hb).mp
    rw [mul_pow,mul_pow,hpow,hs]
    norm_num
    nlinarith

def exampleCost (p : ℝ × Fin 21) : ℝ := p.1-(2/9:ℝ)*(p.2:ℝ)+2
def exampleFeasible : Set (ℝ × Fin 21) := {p | 0 ≤ p.1 ∧ p.1 ≤ 20 ∧
  p.1^2/20+(p.2:ℝ) ≤ 20 ∧ (p.1-1)^2/40-(p.2:ℝ) ≤ -4 ∧
  (11/40:ℝ)*(p.2:ℝ)^((3:ℝ)/2)-10*Real.sqrt (p.1+1/10) ≤ 0}

theorem printed_example_global_minimizer :
    IsMinimizer exampleFeasible exampleCost (21/32,⟨10,by norm_num⟩) ∧
      exampleCost (21/32,⟨10,by norm_num⟩)=125/288 := by
  refine ⟨⟨?_, ?_⟩,by norm_num [exampleCost]⟩
  · refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
    have h := (example_g3_squared (21/32) 10 (by norm_num) (by norm_num)).mpr
      (by norm_num)
    change (11/40:ℝ)*10^((3:ℝ)/2)-10*Real.sqrt ((21/32:ℝ)+1/10) ≤ 0
    linarith
  · rintro ⟨x,y⟩ hp
    have h := (example_g3_squared x (y:ℝ) hp.1 (by positivity)).mp
      (by linarith [hp.2.2.2.2])
    clear hp
    fin_cases y <;> norm_num [exampleCost] at h ⊢ <;> linarith

def exampleIntegerCost (p : ℝ × ℤ) : ℝ := p.1-(2/9:ℝ)*(p.2:ℝ)+2
def exampleIntegerFeasible : Set (ℝ × ℤ) := {p | 0 ≤ p.2 ∧ p.2 ≤ 20 ∧
  0 ≤ p.1 ∧ p.1 ≤ 20 ∧ p.1^2/20+(p.2:ℝ) ≤ 20 ∧
  (p.1-1)^2/40-(p.2:ℝ) ≤ -4 ∧
  (11/40:ℝ)*(p.2:ℝ)^((3:ℝ)/2)-10*Real.sqrt (p.1+1/10) ≤ 0}

theorem printed_example_integer_global_minimizer :
    IsMinimizer exampleIntegerFeasible exampleIntegerCost (21/32,10) ∧
      exampleIntegerCost (21/32,10)=125/288 := by
  refine ⟨⟨?_, ?_⟩,by norm_num [exampleIntegerCost]⟩
  · have h := printed_example_global_minimizer.1.1
    norm_num [exampleIntegerFeasible]
    norm_num [exampleFeasible,Fin.val_natCast] at h
    exact h
  · rintro ⟨x,y⟩ hy
    have hy0 : 0 ≤ y := hy.1
    have hy20 : y ≤ 20 := hy.2.1
    let j : Fin 21 := ⟨y.toNat,by omega⟩
    have hj : (j:ℝ)=(y:ℝ) := by
      have hi : (y.toNat:ℤ)=y := by omega
      exact_mod_cast hi
    have hp : (x,j) ∈ exampleFeasible := by
      simpa [exampleFeasible,hj] using hy.2.2
    have h := printed_example_global_minimizer.1.2 (x,j) hp
    simpa [exampleCost,exampleIntegerCost,hj] using h

theorem weak_tree_bound_empty_level :
    ¬ ∃ y : ℤ, (1:ℝ)/2 ≤ (y:ℝ) ∧ (y:ℝ) ≤ 1 ∧
      (y:ℝ) ≤ Level (1/2) 1 (1/2) := by
  rintro ⟨y,hy,_,hl⟩
  have hi : (1:ℤ) ≤ y := by
    by_contra h
    have hz : y ≤ 0 := by omega
    have hr : (y:ℝ) ≤ 0 := by exact_mod_cast hz
    linarith
  have hr : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hi
  norm_num [Level] at hl; linarith

theorem processed_remaining_bound {Y : Type*} (F : Set Y) (P : Set Y)
    (value : Y → ℝ) (UB LB : ℝ)
    (hprocessed : ∀ y ∈ F ∩ P, UB ≤ value y)
    (hremaining : IsLowerBound (F\P) value LB) :
    IsLowerBound F value (min UB LB) := by
  intro y hy; by_cases hp : y ∈ P
  · exact (min_le_left _ _).trans (hprocessed y ⟨hy,hp⟩)
  · exact (min_le_right _ _).trans (hremaining y ⟨hy,hp⟩)

#print axioms split_identity
#print axioms split_abs_identity
#print axioms abs_le_split
#print axioms l1_canonical_feasible
#print axioms l1_canonical_cost
#print axioms l1_lift_dominates
#print axioms l1_minimizer_lift
#print axioms l1_minimizer_projection
#print axioms linf_le_iff
#print axioms linf_nonneg
#print axioms linf_lift_feasible_iff
#print axioms linf_minimizer_lift
#print axioms linf_minimizer_projection
#print axioms source_l1_optimizer_correspondence
#print axioms source_linf_optimizer_correspondence
#print axioms completed_square
#print axioms scaled_center_minimizer
#print axioms zero_hessian_no_center
#print axioms translated_identity_not_norm
#print axioms zero_gradient_scaling
#print axioms finite_scaled_center_minimizer
#print axioms scaled_center_distance
#print axioms example_y4_fiber_singleton
#print axioms example_y4_no_slater
#print axioms cycle_relaxation_optimum
#print axioms cycle_master_bad_fiber_optimal
#print axioms cycle_restoration_optimum
#print axioms cycle_fiber_infeasible_and_inactive
#print axioms quadratic_singular_no_center
#print axioms callback_projection_selects_one
#print axioms callback_original_optimum_two
#print axioms callback_stored_return_gap
#print axioms example_g3_squared
#print axioms printed_example_global_minimizer
#print axioms printed_example_integer_global_minimizer
#print axioms weak_tree_bound_empty_level
#print axioms processed_remaining_bound
end Chapter07
