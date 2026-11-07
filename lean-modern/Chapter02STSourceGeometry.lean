module

public import Chapter02BBAdapter
public import Chapter02WeightedRestoration
public import Chapter02STObjective

@[expose] public section

/-! Original-coordinate geometry for a separately named repair of the held
Belotti manuscript. The actual objective is D.f. Restoration uses weighted
positive parts with an empty hard-row family. No cut exclusion, regularity,
finite progress, or oracle success is stored in a raw callback. -/
noncomputable section
open Set
open scoped BigOperators
namespace Chapter02
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def stSourceFiber (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) : Set (RealVector N) :=
  {z | z ∈ D.polyhedron ∧ ∀ i : {i : Fin N // i ∈ I}, z i = a i}

def stSourceNonlinearFiber (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) : Set (RealVector N) :=
  {z ∈ stSourceFiber D I a | ∀ j, D.c z j ≤ 0}

def STSourceIntegral (I : Finset (Fin N)) (a : RealVector N) : Prop :=
  ∀ i : {i : Fin N // i ∈ I}, ∃ k : ℤ, (k : ℝ) = a i

def STSourceFiberSlater (D : BBPolyData N l r) (I : Finset (Fin N)) : Prop :=
  ∀ a, STSourceIntegral I a → (stSourceNonlinearFiber D I a).Nonempty →
    ∃ z ∈ stSourceFiber D I a, ∀ j, D.c z j < 0

structure STSourceBatch (N : ℕ) where
  anchor : RealVector N
  restoration : Bool

def stSourceBatchValid (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (b : STSourceBatch N) : Prop :=
  STSourceIntegral I b.anchor ∧
  if b.restoration then
    stSourceNonlinearFiber D I b.anchor = ∅ ∧
    IsMinimizer (stSourceFiber D I b.anchor)
      (weightedPositive w (fun j z => D.c z j)) b.anchor
  else IsMinimizer (stSourceNonlinearFiber D I b.anchor) D.f b.anchor

def stSourceRows (D : BBPolyData N l r) (a z : RealVector N) : Prop :=
  ∀ j, D.c a j + (fderiv ℝ (fun x => D.c x j) a) (z-a) ≤ 0

def stSourceProjection (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N)) :
    Set (RealVector N) :=
  {z | z ∈ D.polyhedron ∧ B.Holds (fun i => z i) ∧ ∀ a ∈ H, stSourceRows D a z}

theorem st_source_polyhedron_convex (D : BBPolyData N l r) :
    Convex ℝ D.polyhedron := by
  intro x hx y hy a b ha hb hab j
  change ∑ i, D.coefficient j i * (a * x i + b * y i) ≤ D.rhs j
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : (∑ i, D.coefficient j i * (a * x i)) =
      a * ∑ i, D.coefficient j i * x i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have h2 : (∑ i, D.coefficient j i * (b * y i)) =
      b * ∑ i, D.coefficient j i * y i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [h1,h2]
  calc
    _ ≤ a * D.rhs j + b * D.rhs j :=
      add_le_add (mul_le_mul_of_nonneg_left (hx j) ha)
        (mul_le_mul_of_nonneg_left (hy j) hb)
    _ = D.rhs j := by rw [← add_mul,hab,one_mul]

theorem st_source_fiber_convex (D : BBPolyData N l r) (I : Finset (Fin N))
    (p : RealVector N) : Convex ℝ (stSourceFiber D I p) := by
  intro x hx y hy a b ha hb hab
  refine ⟨st_source_polyhedron_convex D hx.1 hy.1 ha hb hab, ?_⟩
  intro i
  change a * x i + b * y i = p i
  rw [hx.2 i,hy.2 i,← add_mul,hab,one_mul]

theorem st_source_fiber_closed (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) : IsClosed (stSourceFiber D I a) := by
  have he : stSourceFiber D I a = D.polyhedron ∩
      ⋂ i : {i : Fin N // i ∈ I}, {z | z i = a i} := by
    ext z; simp [stSourceFiber]
  rw [he]
  exact D.polyhedron_closed.inter (isClosed_iInter fun i =>
    isClosed_eq (continuous_apply (i : Fin N)) continuous_const)

theorem st_source_fiber_compact (D : BBPolyData N l r) (I : Finset (Fin N))
    (a : RealVector N) (hX : Bornology.IsBounded D.polyhedron) :
    IsCompact (stSourceFiber D I a) :=
  (D.polyhedron_compact hX).of_isClosed_subset (st_source_fiber_closed D I a)
    (fun _ h => h.1)

theorem st_source_nonlinear_fiber_compact (D : BBPolyData N l r)
    (I : Finset (Fin N)) (a : RealVector N)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) :
    IsCompact (stSourceNonlinearFiber D I a) := by
  have he : stSourceNonlinearFiber D I a = stSourceFiber D I a ∩
      ⋂ j, {z | D.c z j ≤ 0} := by ext z; simp [stSourceNonlinearFiber]
  rw [he]
  exact (st_source_fiber_compact D I a hX).inter_right (isClosed_iInter fun j =>
    isClosed_le ((continuous_apply j).comp hc) continuous_const)

theorem st_source_fiber_congr (D : BBPolyData N l r) (I : Finset (Fin N))
    {a b : RealVector N} (h : ∀ i : {i : Fin N // i ∈ I}, a i = b i) :
    stSourceFiber D I a = stSourceFiber D I b := by
  ext z
  simp only [stSourceFiber, Set.mem_setOf_eq]
  constructor <;> rintro ⟨hz,he⟩
  · exact ⟨hz,fun i => (he i).trans (h i)⟩
  · exact ⟨hz,fun i => (he i).trans (h i).symm⟩

theorem st_source_nonlinear_fiber_congr (D : BBPolyData N l r)
    (I : Finset (Fin N)) {a b : RealVector N}
    (h : ∀ i : {i : Fin N // i ∈ I}, a i = b i) :
    stSourceNonlinearFiber D I a = stSourceNonlinearFiber D I b := by
  unfold stSourceNonlinearFiber
  rw [st_source_fiber_congr D I h]

theorem st_source_batch_reply (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (a : RealVector N) (ha : STSourceIntegral I a)
    (hne : (stSourceFiber D I a).Nonempty)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : Continuous D.f) :
    ∃ b : STSourceBatch N, stSourceBatchValid D I w b ∧
      ∀ i : {i : Fin N // i ∈ I}, b.anchor i = a i := by
  classical
  by_cases hn : (stSourceNonlinearFiber D I a).Nonempty
  · obtain ⟨p,hp⟩ := compact_feasible_attainment
      (st_source_nonlinear_fiber_compact D I a hX hc) hn hf.continuousOn
    have he := hp.1.1.2
    refine ⟨⟨p,false⟩, ⟨?_,?_⟩,he⟩
    · intro i; obtain ⟨k,hk⟩ := ha i; exact ⟨k,hk.trans (he i).symm⟩
    · change IsMinimizer (stSourceNonlinearFiber D I p) D.f p
      rw [st_source_nonlinear_fiber_congr D I he]
      exact hp
  · obtain ⟨p,hp⟩ := compact_feasible_attainment
      (st_source_fiber_compact D I a hX) hne
      (weightedPositive_continuous w (fun j z => D.c z j)
        (fun j => (continuous_apply j).comp hc)).continuousOn
    have he := hp.1.2
    refine ⟨⟨p,true⟩,⟨?_,?_⟩,he⟩
    · intro i; obtain ⟨k,hk⟩ := ha i; exact ⟨k,hk.trans (he i).symm⟩
    · change stSourceNonlinearFiber D I p = ∅ ∧
        IsMinimizer (stSourceFiber D I p) _ p
      rw [st_source_nonlinear_fiber_congr D I he,st_source_fiber_congr D I he]
      exact ⟨Set.not_nonempty_iff_eq_empty.mp hn,hp⟩

theorem st_source_batch_anchor_polyhedron (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (b : STSourceBatch N)
    (hb : stSourceBatchValid D I w b) : b.anchor ∈ D.polyhedron := by
  cases he : b.restoration with
  | false =>
    have hm : IsMinimizer (stSourceNonlinearFiber D I b.anchor) D.f b.anchor :=
      by simpa [stSourceBatchValid,he] using hb.2
    exact hm.1.1.1
  | true =>
    have hr : stSourceNonlinearFiber D I b.anchor = ∅ ∧
        IsMinimizer (stSourceFiber D I b.anchor)
        (weightedPositive w (fun j z => D.c z j)) b.anchor :=
      by simpa [he] using hb.2
    exact hr.2.1.1

theorem st_source_batch_feasible (D : BBPolyData N l r) (I : Finset (Fin N))
    (w : Fin l → ℝ) (b : STSourceBatch N) (hb : stSourceBatchValid D I w b)
    (he : b.restoration = false) : b.anchor ∈ D.feasible I := by
  have hm : IsMinimizer (stSourceNonlinearFiber D I b.anchor) D.f b.anchor :=
    by simpa [he] using hb.2
  exact ⟨hm.1.1.1,hm.1.2,hb.1⟩

theorem st_source_restoration_excludes (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (b : STSourceBatch N)
    (hb : stSourceBatchValid D I w b) (he : b.restoration = true)
    (hw : ∀ j, 0 < w j)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun z => D.c z j))
    (hdiff : ∀ j, Differentiable ℝ (fun z => D.c z j)) :
    ¬ ∃ q ∈ stSourceFiber D I b.anchor, stSourceRows D b.anchor q := by
  have hr : stSourceNonlinearFiber D I b.anchor = ∅ ∧
      IsMinimizer (stSourceFiber D I b.anchor)
        (weightedPositive w (fun j z => D.c z j)) b.anchor := by
    simpa [he] using hb.2
  apply weighted_empty_hard_actual_minimum_excludes (stSourceFiber D I b.anchor)
    (fun j z => D.c z j) w b.anchor (fun j => fderiv ℝ (fun z => D.c z j) b.anchor)
    (st_source_fiber_convex D I b.anchor) hw hconv
    (fun j => (hdiff j b.anchor).hasFDerivAt) hr.2
  rintro ⟨x,hx,hc⟩
  have hx' : x ∈ stSourceNonlinearFiber D I b.anchor := ⟨hx,hc⟩
  rw [hr.1] at hx'; exact hx'

theorem st_source_zero_rows_no_restoration (D : BBPolyData N 0 r)
    (I : Finset (Fin N)) (w : Fin 0 → ℝ) (b : STSourceBatch N)
    (hb : stSourceBatchValid D I w b) : b.restoration = false := by
  cases he : b.restoration with
  | false => rfl
  | true =>
    have hr : stSourceNonlinearFiber D I b.anchor = ∅ ∧
        IsMinimizer (stSourceFiber D I b.anchor)
          (weightedPositive w (fun j z => D.c z j)) b.anchor := by
      simpa [he] using hb.2
    have hp : b.anchor ∈ stSourceNonlinearFiber D I b.anchor :=
      ⟨hr.2.1,fun j => Fin.elim0 j⟩
    rw [hr.1] at hp; exact False.elim hp

theorem st_source_rows_closed (D : BBPolyData N l r) (a : RealVector N) :
    IsClosed {z | stSourceRows D a z} := by
  have he : {z | stSourceRows D a z} =
      ⋂ j, {z | D.c a j + (fderiv ℝ (fun x => D.c x j) a) (z-a) ≤ 0} := by
    ext z; simp [stSourceRows]
  rw [he]
  exact isClosed_iInter fun j => isClosed_le
    (continuous_const.add ((fderiv ℝ (fun x => D.c x j) a).continuous.comp
      (continuous_id.sub continuous_const))) continuous_const

theorem st_source_projection_compact (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (hX : Bornology.IsBounded D.polyhedron) : IsCompact (stSourceProjection D B H) := by
  have he : stSourceProjection D B H = D.polyhedron ∩
      ({z | B.Holds (fun i => z i)} ∩ ⋂ a ∈ H, {z | stSourceRows D a z}) := by
    ext z
    simp only [stSourceProjection, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [he]
  apply (D.polyhedron_compact hX).inter_right
  exact (B.holds_closed (fun z i => z i)
    (fun i => continuous_apply (i : Fin N))).inter
    (isClosed_biInter fun a _ => st_source_rows_closed D a)

theorem st_source_projection_append (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (a : RealVector N) :
    stSourceProjection D B (H ++ [a]) =
      stSourceProjection D B H ∩ {z | stSourceRows D a z} := by
  ext z
  simp only [stSourceProjection, Set.mem_setOf_eq, Set.mem_inter_iff,
    List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
  tauto

theorem st_source_rows_valid (D : BBPolyData N l r) (a z : RealVector N)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hz : ∀ j, D.c z j ≤ 0) : stSourceRows D a z := by
  intro j
  exact (tangent_underestimator (hconv j) (hdiff j a).hasFDerivAt).trans (hz j)

theorem st_source_feasible_projection (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {z : RealVector N} (hz : z ∈ D.feasible I)
    (hB : B.Holds (fun i => z i)) : z ∈ stSourceProjection D B H :=
  ⟨hz.1,hB,fun a _ => st_source_rows_valid D a z hconv hdiff hz.2.1⟩

theorem st_source_same_integer_iff (P : BBPartition I n m) (a z : RealVector N) :
    (∀ i : {i : Fin N // i ∈ I}, z i = a i) ↔ (P.split z).2 = (P.split a).2 := by
  constructor
  · intro h; funext j; exact h (P.integerEquiv.symm j)
  · intro h i
    have he := congrFun h (P.integerEquiv i)
    simpa only [BBPartition.split, Equiv.symm_apply_apply] using he

theorem st_source_fiber_split_iff (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (a z : RealVector N) :
    z ∈ stSourceFiber D I a ↔
      P.split z ∈ (D.model P K).fixedLinearFiber (P.split a).2 := by
  exact and_congr (D.linear_iff P K z).symm (st_source_same_integer_iff P a z)

theorem st_source_nonlinear_fiber_split_iff (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (a z : RealVector N) :
    z ∈ stSourceNonlinearFiber D I a ↔
      P.split z ∈ (D.model P K).fixedNonlinearFiber (P.split a).2 := by
  exact and_congr (st_source_fiber_split_iff D P K a z) (D.nonlinear_iff P K z).symm

theorem st_source_fiber_minimizer_iff (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (a p : RealVector N) :
    IsMinimizer (stSourceNonlinearFiber D I a) D.f p ↔
      IsMinimizer ((D.model P K).fixedNonlinearFiber (P.split a).2)
        (D.objective P) (P.split p) := by
  constructor
  · rintro ⟨hp,hm⟩
    refine ⟨(st_source_nonlinear_fiber_split_iff D P K a p).mp hp,?_⟩
    intro q hq
    have hq' : P.join q ∈ stSourceNonlinearFiber D I a := by
      apply (st_source_nonlinear_fiber_split_iff D P K a (P.join q)).mpr
      simpa only [P.split_join] using hq
    simpa only [BBPolyData.objective_split, BBPolyData.objective,
      Function.comp_apply,P.join_split] using hm (P.join q) hq'
  · rintro ⟨hp,hm⟩
    refine ⟨(st_source_nonlinear_fiber_split_iff D P K a p).mpr hp,?_⟩
    intro q hq
    simpa only [BBPolyData.objective_split] using
      hm (P.split q) ((st_source_nonlinear_fiber_split_iff D P K a q).mp hq)

/-- Literal strict mathematical cutoff and the separately interpreted positive
absolute cutoff. Zero and negative gaps are representable for ablation controls;
progress and return theorems must state their own sign hypotheses. -/
inductive STSourcePolicy
  | strict
  | gap (epsilon : ℝ)

def STSourcePolicy.Admits (policy : STSourcePolicy) (inc : Option ℝ) (eta : ℝ) : Prop :=
  match inc, policy with
  | none, _ => True
  | some u, .strict => eta < u
  | some u, .gap epsilon => eta ≤ u - epsilon

theorem st_source_cutoff_downward (policy : STSourcePolicy) (inc : Option ℝ)
    {a b : ℝ} (ha : policy.Admits inc a) (hle : b ≤ a) : policy.Admits inc b := by
  cases inc with
  | none => trivial
  | some u => cases policy with
    | strict => exact hle.trans_lt ha
    | gap epsilon => exact hle.trans ha

theorem st_source_cutoff_strict_competitive (policy : STSourcePolicy)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    {u eta : ℝ} (h : policy.Admits (some u) eta) : eta < u := by
  rcases hpolicy with rfl | ⟨epsilon,rfl,he⟩
  · exact h
  · change eta ≤ u - epsilon at h
    linarith

theorem st_source_strict_no_improvement {u v : ℝ}
    (h : ¬ STSourcePolicy.strict.Admits (some u) v) : u ≤ v :=
  le_of_not_gt h

theorem st_source_gap_no_improvement {epsilon u v : ℝ}
    (h : ¬ (STSourcePolicy.gap epsilon).Admits (some u) v) : u < v + epsilon := by
  change ¬ v ≤ u - epsilon at h
  have := lt_of_not_ge h
  linarith

theorem st_source_cutoff_incumbent_monotone (policy : STSourcePolicy)
    {u v eta : ℝ} (hv : v ≤ u) (h : policy.Admits (some v) eta) :
    policy.Admits (some u) eta := by
  cases policy with
  | strict => exact lt_of_lt_of_le h hv
  | gap epsilon =>
    change eta ≤ v - epsilon at h
    change eta ≤ u - epsilon
    linarith

theorem st_source_zero_gap_admits_incumbent (u : ℝ) :
    (STSourcePolicy.gap 0).Admits (some u) u := by
  change u ≤ u - 0
  simp

theorem st_source_negative_gap_admits_worse (epsilon u : ℝ) (he : epsilon < 0) :
    u < u - epsilon ∧ (STSourcePolicy.gap epsilon).Admits (some u) (u-epsilon) := by
  exact ⟨by linarith,le_rfl⟩

def stSourceHeightCutoff (policy : STSourcePolicy) (inc : Option ℝ) : STHeightCutoff :=
  match inc, policy with
  | none, _ => .none
  | some u, .strict => .strict u
  | some u, .gap epsilon => .closed (u-epsilon)

theorem st_source_height_cutoff_iff (policy : STSourcePolicy) (inc : Option ℝ)
    (eta : ℝ) : (stSourceHeightCutoff policy inc).Holds eta ↔ policy.Admits inc eta := by
  cases inc <;> cases policy <;> rfl

def stSourceLP (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (policy : STSourcePolicy) (inc : Option ℝ) : Set (RealVector N × ℝ) :=
  stHeightLP D.f (stSourceProjection D B H) H (stSourceHeightCutoff policy inc)

theorem st_source_lp_mem_iff (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (policy : STSourcePolicy) (inc : Option ℝ) (p : RealVector N × ℝ) :
    p ∈ stSourceLP D B H policy inc ↔
      p.1 ∈ D.polyhedron ∧ B.Holds (fun i => p.1 i) ∧
      (∀ a ∈ H, stSourceRows D a p.1) ∧ stObjectiveCuts D.f H p.1 p.2 ∧
      policy.Admits inc p.2 := by
  rw [stSourceLP,st_height_lp_mem_iff,st_source_height_cutoff_iff]
  simp only [stSourceProjection,Set.mem_setOf_eq,and_assoc]

theorem st_source_lp_append (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (policy : STSourcePolicy) (inc : Option ℝ) (a : RealVector N) :
    stSourceLP D B (H ++ [a]) policy inc = stSourceLP D B H policy inc ∩
      {p | stSourceRows D a p.1 ∧ stTangent D.f a p.1 ≤ p.2} := by
  ext p
  simp only [st_source_lp_mem_iff,Set.mem_inter_iff,Set.mem_setOf_eq,
    List.mem_append,List.mem_singleton,or_imp,forall_and,forall_eq,
    st_objective_cuts_append]
  tauto

theorem st_source_lp_reply (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (policy : STSourcePolicy) (inc : Option ℝ)
    (hX : Bornology.IsBounded D.polyhedron) (hH : H ≠ []) :
    stSourceLP D B H policy inc = ∅ ∨
      ∃ p, IsMinimizer (stSourceLP D B H policy inc) Prod.snd p :=
  st_height_lp_empty_or_minimum D.f (stSourceProjection D B H) H
    (stSourceHeightCutoff policy inc) (st_source_projection_compact D B H hX) hH

theorem st_source_feasible_lp (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (policy : STSourcePolicy) (inc : Option ℝ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {z : RealVector N} (hz : z ∈ D.feasible I)
    (hB : B.Holds (fun i => z i)) (hcut : policy.Admits inc (D.f z)) :
    (z,D.f z) ∈ stSourceLP D B H policy inc := by
  exact ⟨st_source_feasible_projection D B H hconv hdiff hz hB,
    st_objective_cuts_valid D.f H hconvf (fun a _ => hdf a) z,
    (st_source_height_cutoff_iff policy inc (D.f z)).mpr hcut⟩

/-- Cutoff LP emptiness excludes only objective values admitted by its cutoff.
It is not a certificate of original-node infeasibility when an incumbent exists. -/
theorem st_source_empty_lp_no_improvement (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (policy : STSourcePolicy) (inc : Option ℝ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (he : stSourceLP D B H policy inc = ∅)
    {z : RealVector N} (hz : z ∈ D.feasible I) (hB : B.Holds (fun i => z i)) :
    ¬ policy.Admits inc (D.f z) := by
  intro ha
  have hp := st_source_feasible_lp D B H policy inc hconvf hdf hconv hdiff hz hB ha
  rw [he] at hp
  exact hp

theorem st_source_lp_fiber_reply (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (policy : STSourcePolicy) (inc : Option ℝ) (w : Fin l → ℝ)
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c) (hf : Continuous D.f)
    {p : RealVector N × ℝ} (hp : p ∈ stSourceLP D B H policy inc)
    (hi : STSourceIntegral I p.1) :
    ∃ b : STSourceBatch N, stSourceBatchValid D I w b ∧
      ∀ i : {i : Fin N // i ∈ I}, b.anchor i = p.1 i := by
  exact st_source_batch_reply D I w p.1 hi ⟨p.1,hp.1.1,fun _ => rfl⟩ hX hc hf

theorem st_source_feasible_fiber_support (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (a : RealVector N)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hmin : IsMinimizer (stSourceNonlinearFiber D I a) D.f a)
    (hs : ∃ z ∈ stSourceFiber D I a, ∀ j, D.c z j < 0)
    {q : RealVector N} {eta : ℝ} (hq : q ∈ stSourceFiber D I a)
    (hrows : stSourceRows D a q) (hobj : stTangent D.f a q ≤ eta) : D.f a ≤ eta := by
  have hc' : ∀ j, ConvexOn ℝ Set.univ ((D.model P K).g j) := by
    intro j
    simpa [BBPolyData.model, BBPartition.linearEquiv, Function.comp_def] using
      (hconv j).comp_linearMap P.linearEquiv.symm.toLinearMap
  have hf' : DifferentiableAt ℝ (D.objective P) (P.split a) := by
    exact (hdf.comp P.equiv.symm.differentiable) (P.split a)
  have hg' : ∀ j, DifferentiableAt ℝ ((D.model P K).g j) (P.split a) := by
    intro j
    have hh := ((hdiff j).comp P.equiv.symm.differentiable) (P.split a)
    exact hh
  have hs' : ∃ z ∈ (D.model P K).fixedLinearFiber (P.split a).2,
      ∀ j, (D.model P K).g j z < 0 := by
    obtain ⟨z,hz,hstrict⟩ := hs
    refine ⟨P.split z,(st_source_fiber_split_iff D P K a z).mp hz,?_⟩
    simpa [BBPolyData.model] using hstrict
  have hrows' : ∀ j, stTangent ((D.model P K).g j) (P.split a) (P.split q) ≤ 0 := by
    intro j
    change stTangent ((fun x => D.c x j) ∘ P.join) (P.split a) (P.split q) ≤ 0
    rw [st_tangent_split P (fun x => D.c x j) a q (hdiff j a)]
    exact hrows j
  have hobj' : stTangent (D.objective P) (P.split a) (P.split q) ≤ eta := by
    rw [BBPolyData.objective,st_tangent_split P D.f a q (hdf a)]
    exact hobj
  have hh := st_fixed_fiber_support (D.model P K) (D.objective P) (P.split a)
    (D.convex_objective P hconvf) hc' hf' hg'
    ((st_source_fiber_minimizer_iff D P K a a).mp hmin) hs'
    ((st_source_fiber_split_iff D P K a q).mp hq) hrows' hobj'
  simpa only [BBPolyData.objective_split] using hh

theorem st_source_batch_support (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (w : Fin l → ℝ) (b : STSourceBatch N)
    (hb : stSourceBatchValid D I w b) (hw : ∀ j, 0 < w j)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) {q : RealVector N} {eta : ℝ}
    (hq : q ∈ stSourceFiber D I b.anchor) (hrows : stSourceRows D b.anchor q)
    (hobj : stTangent D.f b.anchor q ≤ eta) :
    b.restoration = false ∧ D.f b.anchor ≤ eta := by
  cases he : b.restoration with
  | true =>
    exact False.elim ((st_source_restoration_excludes D I w b hb he hw hconv hdiff)
      ⟨q,hq,hrows⟩)
  | false =>
    have hm : IsMinimizer (stSourceNonlinearFiber D I b.anchor) D.f b.anchor :=
      by simpa [he] using hb.2
    exact ⟨rfl,st_source_feasible_fiber_support D P K b.anchor hconvf hdf hconv hdiff
      hm (hCQ b.anchor hb.1 ⟨b.anchor,hm.1⟩) hq hrows hobj⟩

theorem st_source_batch_blocks_competitive_revisit (D : BBPolyData N l r)
    (P : BBPartition I n m) (K : ℝ) (w : Fin l → ℝ) (b : STSourceBatch N)
    (hb : stSourceBatchValid D I w b) (hw : ∀ j, 0 < w j)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    (hCQ : STSourceFiberSlater D I) (policy : STSourcePolicy)
    (hpolicy : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0 < epsilon)
    {q : RealVector N} {eta u : ℝ}
    (hq : q ∈ stSourceFiber D I b.anchor) (hrows : stSourceRows D b.anchor q)
    (hobj : stTangent D.f b.anchor q ≤ eta)
    (hbest : b.restoration = false → u ≤ D.f b.anchor)
    (hc : policy.Admits (some u) eta) : False := by
  obtain ⟨he,hle⟩ := st_source_batch_support D P K w b hb hw hconvf hdf hconv hdiff
    hCQ hq hrows hobj
  exact (not_lt_of_ge ((hbest he).trans hle))
    (st_source_cutoff_strict_competitive policy hpolicy hc)

theorem st_source_same_fiber_node (B : BBExtendedNode {i : Fin N // i ∈ I})
    {a q : RealVector N} (hq : B.Holds (fun i => q i))
    (he : ∀ i : {i : Fin N // i ∈ I}, a i = q i) : B.Holds (fun i => a i) := by
  intro i
  simpa only [he i] using hq i

theorem st_source_lp_minimum_lower_bound (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (H : List (RealVector N))
    (policy : STSourcePolicy) (inc : Option ℝ)
    (hconvf : ConvexOn ℝ Set.univ D.f) (hdf : Differentiable ℝ D.f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (fun x => D.c x j))
    (hdiff : ∀ j, Differentiable ℝ (fun x => D.c x j))
    {p : RealVector N × ℝ} (hp : IsMinimizer (stSourceLP D B H policy inc) Prod.snd p)
    {z : RealVector N} (hz : z ∈ D.feasible I)
    (hB : B.Holds (fun i => z i)) (ha : policy.Admits inc (D.f z)) : p.2 ≤ D.f z :=
  hp.2 (z,D.f z) (st_source_feasible_lp D B H policy inc hconvf hdf hconv hdiff hz hB ha)

end Chapter02

#print axioms Chapter02.st_source_polyhedron_convex
#print axioms Chapter02.st_source_fiber_convex
#print axioms Chapter02.st_source_fiber_closed
#print axioms Chapter02.st_source_fiber_compact
#print axioms Chapter02.st_source_nonlinear_fiber_compact
#print axioms Chapter02.st_source_fiber_congr
#print axioms Chapter02.st_source_nonlinear_fiber_congr
#print axioms Chapter02.st_source_batch_reply
#print axioms Chapter02.st_source_batch_anchor_polyhedron
#print axioms Chapter02.st_source_batch_feasible
#print axioms Chapter02.st_source_restoration_excludes
#print axioms Chapter02.st_source_zero_rows_no_restoration
#print axioms Chapter02.st_source_rows_closed
#print axioms Chapter02.st_source_projection_compact
#print axioms Chapter02.st_source_projection_append
#print axioms Chapter02.st_source_rows_valid
#print axioms Chapter02.st_source_feasible_projection
#print axioms Chapter02.st_source_same_integer_iff
#print axioms Chapter02.st_source_fiber_split_iff
#print axioms Chapter02.st_source_nonlinear_fiber_split_iff
#print axioms Chapter02.st_source_fiber_minimizer_iff
#print axioms Chapter02.st_source_cutoff_downward
#print axioms Chapter02.st_source_cutoff_strict_competitive
#print axioms Chapter02.st_source_strict_no_improvement
#print axioms Chapter02.st_source_gap_no_improvement
#print axioms Chapter02.st_source_cutoff_incumbent_monotone
#print axioms Chapter02.st_source_zero_gap_admits_incumbent
#print axioms Chapter02.st_source_negative_gap_admits_worse
#print axioms Chapter02.st_source_height_cutoff_iff
#print axioms Chapter02.st_source_lp_mem_iff
#print axioms Chapter02.st_source_lp_append
#print axioms Chapter02.st_source_lp_reply
#print axioms Chapter02.st_source_feasible_lp
#print axioms Chapter02.st_source_empty_lp_no_improvement
#print axioms Chapter02.st_source_lp_fiber_reply
#print axioms Chapter02.st_source_feasible_fiber_support
#print axioms Chapter02.st_source_batch_support
#print axioms Chapter02.st_source_batch_blocks_competitive_revisit
#print axioms Chapter02.st_source_same_fiber_node
#print axioms Chapter02.st_source_lp_minimum_lower_bound
