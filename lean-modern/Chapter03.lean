module

public import Chapter07
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! Chapter 3: exact projection cuts, source-model wiring, bounded no-repeat
scope, repaired binary no-good row, and literal general-integer big-M lift.
No full algorithm trace, numerical oracle, CQ or historical implementation is assumed certified. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02
namespace Chapter03

section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ProjectionMin (K : Set E) (u v : E) : Prop :=
  v ∈ K ∧ ∀ w ∈ K, ‖u-v‖^2 ≤ ‖u-w‖^2

theorem projection_norm_min {K : Set E} {u v : E} (h : ProjectionMin K u v) :
    ∀ w ∈ K, ‖u-v‖ ≤ ‖u-w‖ := by
  intro w hw
  have hh := h.2 w hw
  nlinarith [norm_nonneg (u-v),norm_nonneg (u-w)]

theorem projection_cut_valid {K : Set E} (hK : Convex ℝ K) {u v : E}
    (h : ProjectionMin K u v) : ∀ w ∈ K, 0 ≤ @inner ℝ _ _ (v-u) (w-v) := by
  letI : Nonempty K := ⟨⟨v,h.1⟩⟩
  have he : ‖u-v‖ = ⨅ w : K, ‖u-(w:E)‖ := by
    apply le_antisymm
    · exact le_ciInf fun w => projection_norm_min h w w.2
    · exact ciInf_le ⟨(0:ℝ),Set.forall_mem_range.2 (fun w : K => norm_nonneg (u-(w:E)))⟩ ⟨v,h.1⟩
  have hv := (norm_eq_iInf_iff_real_inner_le_zero hK h.1).mp he
  intro w hw
  have hh := hv w hw
  have heq : v-u = -(u-v) := by abel
  rw [heq,inner_neg_left]; linarith

theorem projection_cut_excludes {u v : E} (h : v ≠ u) :
    @inner ℝ _ _ (v-u) (u-v) < 0 := by
  have heq : u-v = -(v-u) := by abel
  rw [heq,inner_neg_right,real_inner_self_eq_norm_sq]
  have hn := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  nlinarith

theorem projection_zero_iff {u v : E} : ‖u-v‖^2 = 0 ↔ u=v := by
  constructor
  · intro h
    have hn : ‖u-v‖=0 := by nlinarith [norm_nonneg (u-v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · rintro rfl; simp

theorem projection_exists {K : Set E} (hne : K.Nonempty) (hc : IsComplete K)
    (hK : Convex ℝ K) (u : E) : ∃ v, ProjectionMin K u v := by
  rcases exists_norm_eq_iInf_of_complete_convex hne hc hK u with ⟨v,hv,he⟩
  refine ⟨v,hv,fun w hw => ?_⟩
  have hl : ‖u-v‖ ≤ ‖u-w‖ := by
    rw [he]; exact ciInf_le ⟨(0:ℝ),Set.forall_mem_range.2 (fun w : K => norm_nonneg (u-(w:E)))⟩ ⟨w,hw⟩
  exact pow_le_pow_left₀ (norm_nonneg _) hl 2
end Projection

def yMap (n m : ℕ) : Point n m →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap.comp (LinearMap.snd ℝ _ _)
def projectedSource {n m l r : ℕ} (d : ModelData n m l r) (S : Set (Point n m)) :=
  yMap n m '' d.relaxationOn S

theorem projected_source_convex {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (hS : Convex ℝ S) (hg : ∀ j, ConvexOn ℝ S (d.g j)) :
    Convex ℝ (projectedSource d S) :=
  (source_relaxation_convex_on d S hS hg).linear_image (yMap n m)

theorem projected_source_contains_integer {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) {p : Point n m} (hp : p ∈ d.feasibleOn S) :
    yMap n m p ∈ projectedSource d S :=
  ⟨p,source_mixed_subset_relaxation d S hp,rfl⟩

theorem source_projection_minimizer {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (u : EuclideanSpace ℝ (Fin m)) {p : Point n m}
    (hp : IsMinimizer (d.relaxationOn S) (fun q => ‖u-yMap n m q‖^2) p) :
    ProjectionMin (projectedSource d S) u (yMap n m p) := by
  refine ⟨⟨p,hp.1,rfl⟩,?_⟩
  rintro w ⟨q,hq,rfl⟩; exact hp.2 q hq

theorem source_projection_attained {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (hc : IsCompact (d.relaxationOn S))
    (hne : (d.relaxationOn S).Nonempty) (u : EuclideanSpace ℝ (Fin m)) :
    ∃ p, IsMinimizer (d.relaxationOn S) (fun q => ‖u-yMap n m q‖^2) p := by
  apply compact_feasible_attainment hc hne
  have hy : Continuous (yMap n m) := (yMap n m).continuous_of_finiteDimensional
  exact ((continuous_const.sub hy).norm.pow 2).continuousOn

theorem source_projection_cut_valid {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (hS : Convex ℝ S) (hg : ∀ j, ConvexOn ℝ S (d.g j))
    {u v : EuclideanSpace ℝ (Fin m)} (h : ProjectionMin (projectedSource d S) u v)
    {p : Point n m} (hp : p ∈ d.feasibleOn S) :
    0 ≤ @inner ℝ _ _ (v-u) (yMap n m p-v) :=
  projection_cut_valid (projected_source_convex d S hS hg) h _
    (projected_source_contains_integer d S hp)

theorem source_projection_zero_feasible {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) {p : Point n m} (hp : p ∈ d.relaxationOn S)
    (y : IntVector m) (he : p.2 = fun i => (y i : ℝ)) : p ∈ d.feasibleOn S := by
  rcases hp with ⟨hn,hl,hbox⟩
  exact ⟨⟨hn,hl⟩,⟨y,by simpa [IntegerBox,he] using hbox,he⟩⟩

theorem finite_no_repeat_bound {E : Type*} (A : Finset E) (k : ℕ) (t : Fin k → E)
    (hmem : ∀ i, t i ∈ A) (hinj : Function.Injective t) : k ≤ A.card := by
  let f : Fin k → A := fun i => ⟨t i,hmem i⟩
  have hi : Function.Injective f := by
    intro i j h; apply hinj; exact congrArg Subtype.val h
  simpa using Fintype.card_le_of_injective f hi

/-- Bool encodes an exact binary variable, not a fractional relaxation. -/
def bit (b : Bool) : ℝ := if b then 1 else 0
def binaryDistance {N : ℕ} (y c : Fin N → Bool) : ℝ := ∑ i, |bit (y i)-bit (c i)|
def binaryRow {N : ℕ} (y c : Fin N → Bool) : ℝ :=
  ∑ i, if c i then 1-bit (y i) else bit (y i)

theorem binary_coordinate_abs (y c : Bool) :
    |bit y-bit c| = if c then 1-bit y else bit y := by
  cases y <;> cases c <;> norm_num [bit]

theorem binary_repaired_row {N : ℕ} (y c : Fin N → Bool) :
    binaryDistance y c = binaryRow y c := by
  unfold binaryDistance binaryRow
  apply Finset.sum_congr rfl; intro i _; exact binary_coordinate_abs _ _

theorem binary_row_zero_iff {N : ℕ} (y c : Fin N → Bool) :
    binaryRow y c = 0 ↔ y=c := by
  rw [← binary_repaired_row]
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (bit (y i)-bit (c i)))).mp h
    funext i
    have he := abs_eq_zero.mp (hz i (Finset.mem_univ i))
    cases hy : y i <;> cases hc : c i <;> simp_all [bit]
  · rintro rfl; simp [binaryDistance]

theorem binary_nogood_iff {N : ℕ} (y c : Fin N → Bool) : 1 ≤ binaryRow y c ↔ y ≠ c := by
  constructor
  · intro h he; subst y; have hz := (binary_row_zero_iff c c).mpr rfl; linarith
  · intro h
    have hex : ∃ i, y i ≠ c i := by
      by_contra hn; apply h; funext i; by_contra hi; exact hn ⟨i,hi⟩
    rcases hex with ⟨i,hi⟩
    rw [← binary_repaired_row]
    have hc : |bit (y i)-bit (c i)| = 1 := by
      cases hy : y i <;> cases hh : c i <;> simp_all [bit]
    have hl := Finset.single_le_sum (fun j _ => abs_nonneg (bit (y j)-bit (c j))) (Finset.mem_univ i)
    rwa [hc] at hl

theorem printed_binary_sign_failure : ¬ (1 ≤ -(1-bit false)) ∧ 1 ≤ |bit false-bit true| := by
  norm_num [bit]

def AbsLift (lo hi c y w : ℝ) (v : Bool) : Prop :=
  lo ≤ y ∧ y ≤ hi ∧ 0 ≤ w ∧ -w ≤ y-c ∧ y-c ≤ w ∧
  w ≤ y-c+2*(c-lo)*(1-bit v) ∧ w ≤ c-y+2*(hi-c)*bit v

theorem general_abs_lift_sound {lo hi c y w : ℝ} {v : Bool}
    (h : AbsLift lo hi c y w v) : w=|y-c| := by
  rcases h with ⟨_,_,_,hl,hu,h1,h2⟩
  cases v
  · simp only [bit,Bool.false_eq_true,↓reduceIte,sub_zero,mul_one,mul_zero,add_zero] at h1 h2
    rw [abs_of_nonpos (by linarith : y-c ≤ 0)]; linarith
  · simp only [bit,↓reduceIte,sub_self,mul_zero,add_zero,mul_one] at h1 h2
    rw [abs_of_nonneg (by linarith : 0 ≤ y-c)]; linarith

theorem general_abs_lift_complete {lo hi c y : ℝ} (hlo : lo ≤ y) (hhi : y ≤ hi) :
    ∃ v, AbsLift lo hi c y |y-c| v := by
  by_cases h : y ≤ c
  · refine ⟨false,?_⟩
    rw [abs_of_nonpos (by linarith : y-c ≤ 0)]
    simp only [AbsLift,bit,Bool.false_eq_true,↓reduceIte,sub_zero,mul_one,mul_zero,add_zero,sub_self]
    exact ⟨hlo,hhi,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · refine ⟨true,?_⟩
    rw [abs_of_nonneg (by linarith : 0 ≤ y-c)]
    simp only [AbsLift,bit,Bool.false_eq_true,↓reduceIte,sub_zero,mul_one,mul_zero,add_zero,sub_self]
    exact ⟨hlo,hhi,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem general_abs_lift_iff {lo hi c y : ℝ} :
    (∃ w v, AbsLift lo hi c y w v) ↔ lo ≤ y ∧ y ≤ hi := by
  constructor
  · rintro ⟨w,v,h⟩; exact ⟨h.1,h.2.1⟩
  · rintro ⟨hl,hu⟩; rcases general_abs_lift_complete hl hu with ⟨v,hv⟩
    exact ⟨|y-c|,v,hv⟩

theorem bigM_lower_necessary (lo c M : ℝ) (h : c-lo ≤ lo-c+M) : 2*(c-lo) ≤ M := by linarith

theorem bigM_upper_necessary (hi c M : ℝ) (h : hi-c ≤ c-hi+M) : 2*(hi-c) ≤ M := by linarith

theorem lower_endpoint_abs (lo c y : ℝ) (hl : lo ≤ y) (hc : c=lo) : |y-c|=y-lo := by
  subst c; rw [abs_of_nonneg (by linarith : 0 ≤ y-lo)]

theorem upper_endpoint_abs (hi c y : ℝ) (hh : y ≤ hi) (hc : c=hi) : |y-c|=hi-y := by
  subst c; rw [abs_of_nonpos (by linarith : y-hi ≤ 0)]; ring

theorem relative_cutoff_gap (ub opt δ : ℝ) (hδ : 0 ≤ δ)
    (h : ub-δ*max |ub| 1 ≤ opt) : ub-opt ≤ δ*max |ub| 1 := by linarith

theorem relative_cutoff_not_additive : (10:ℝ)-8 ≤ (1:ℝ)/5*max |10| 1 ∧ ¬ ((10:ℝ)-8 ≤ (1:ℝ)/5) := by norm_num

theorem positive_cutoff_excludes_incumbent (ub δ : ℝ) (hδ : 0 < δ) :
    ¬ (ub ≤ ub-δ*max |ub| 1) := by
  have hm : 0 < max |ub| 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hp := mul_pos hδ hm; linarith

/-- Source-compatible CQ failure: all fixed-NLP global minimizers exist, yet
zero-gradient feasibility tangents leave a permanent one-unit bound gap. -/
def cqOriginal : Set (ℝ × Bool) := {p | p.1^2 ≤ 0 ∧ -1 ≤ p.1 ∧ p.1 ≤ 1}
def cqCost (p : ℝ × Bool) : ℝ := -p.1+(bit p.2-1/2)^2
def cqMaster : Set (ℝ × Bool × ℝ) := {p |
  -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -p.1 ≤ p.2.2 ∧
  1/4-p.1-bit p.2.1 ≤ p.2.2 ∧ 1/4-p.1+bit p.2.1-1 ≤ p.2.2}

theorem cq_original_optimal : IsMinimizer cqOriginal cqCost (0,false) := by
  refine ⟨by norm_num [cqOriginal],?_⟩
  rintro ⟨x,y⟩ hp
  have hx : x=0 := by
    have h := hp.1; change x^2 ≤ 0 at h; nlinarith [sq_nonneg x]
  subst x; cases y <;> norm_num [cqCost,bit]

theorem cq_master_optimal : IsMinimizer cqMaster (fun p => p.2.2) (1,false,-3/4) := by
  refine ⟨by norm_num [cqMaster,bit],?_⟩
  rintro ⟨x,y,α⟩ ⟨hlo,hhi,h0,h1,h2⟩
  cases y <;> norm_num [bit] at h1 h2 ⊢ <;> linarith

theorem cq_permanent_gap : cqCost (0,false)-((1,false,-3/4) : ℝ × Bool × ℝ).2.2=1 := by
  norm_num [cqCost,bit]

end Chapter03

#print axioms Chapter03.projection_norm_min
#print axioms Chapter03.projection_cut_valid
#print axioms Chapter03.projection_cut_excludes
#print axioms Chapter03.projection_zero_iff
#print axioms Chapter03.projection_exists
#print axioms Chapter03.projected_source_convex
#print axioms Chapter03.projected_source_contains_integer
#print axioms Chapter03.source_projection_cut_valid
#print axioms Chapter03.source_projection_zero_feasible
#print axioms Chapter03.finite_no_repeat_bound
#print axioms Chapter03.binary_coordinate_abs
#print axioms Chapter03.binary_repaired_row
#print axioms Chapter03.binary_row_zero_iff
#print axioms Chapter03.binary_nogood_iff
#print axioms Chapter03.printed_binary_sign_failure
#print axioms Chapter03.general_abs_lift_sound
#print axioms Chapter03.general_abs_lift_complete
#print axioms Chapter03.general_abs_lift_iff
#print axioms Chapter03.bigM_lower_necessary
#print axioms Chapter03.bigM_upper_necessary
#print axioms Chapter03.lower_endpoint_abs
#print axioms Chapter03.upper_endpoint_abs
#print axioms Chapter03.relative_cutoff_gap
#print axioms Chapter03.relative_cutoff_not_additive
#print axioms Chapter03.positive_cutoff_excludes_incumbent

#print axioms Chapter03.source_projection_minimizer
#print axioms Chapter03.source_projection_attained

#print axioms Chapter03.cq_original_optimal
#print axioms Chapter03.cq_master_optimal
#print axioms Chapter03.cq_permanent_gap
