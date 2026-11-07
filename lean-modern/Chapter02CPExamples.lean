module

public import Chapter02CPConvergence
public import Chapter02ESH
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Concrete retained-history ECP/ESH controls for CH02-S009. The source
procedures, altered-policy controls and source precision questions are kept
distinct. These are candidate proofs; independent acceptance is external. -/
noncomputable section
open Chapter02
open scoped BigOperators Topology
namespace Chapter02CPExamples

def coord {n m : ℕ} (i : Fin n) : Point n m →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (RealVector n) (RealVector m))

theorem coord_apply {n m : ℕ} (i : Fin n) (p : Point n m) : coord i p = p.1 i := rfl

theorem base_closed {n m l r : ℕ} (d : ModelData n m l r) :
    IsClosed (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) := by
  have hL : IsClosed d.linearRegion := by
    have heq : d.linearRegion = ⋂ row,
        {p | LinearForm (d.A row) (d.B row) p ≤ d.rhs row} := by
      ext p; simp [ModelData.linearRegion]
    rw [heq]
    exact isClosed_iInter fun row =>
      isClosed_le (linearForm_continuous _ _) continuous_const
  have hY : IsClosed (IntegerCylinder (n := n) d.lo d.hi) := by
    have hfin := (integerBox_finite d.lo d.hi).image
      (fun y : IntVector m => fun i => (y i : ℝ))
    have heq : IntegerCylinder (n := n) d.lo d.hi =
        Prod.snd ⁻¹' ((fun y : IntVector m => fun i => (y i : ℝ)) ''
          IntegerBox d.lo d.hi) := by
      ext p; simp [IntegerCylinder, eq_comm]
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  exact hL.inter hY

def scalarPoint {m : ℕ} (x : ℝ) (y : RealVector m) : Point 1 m := (fun _ => x, y)

/-- x in [0,1], every integer coordinate in [0,1]. -/
def scalarModel (m l : ℕ) (g : Fin l → ℝ → ℝ) (c : ℝ) : ModelData 1 m l 2 where
  g := fun j p => g j (p.1 0)
  A := fun row _ => if row = 0 then -1 else 1
  B := fun _ _ => 0
  rhs := fun row => if row = 0 then 0 else 1
  c1 := fun _ => c
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

theorem scalar_linear_iff (m l : ℕ) (g : Fin l → ℝ → ℝ) (c : ℝ) (p : Point 1 m) :
    p ∈ (scalarModel m l g c).linearRegion ↔ 0 ≤ p.1 0 ∧ p.1 0 ≤ 1 := by
  simp [ModelData.linearRegion, scalarModel, LinearForm, Fin.forall_fin_succ]

theorem scalar_objective (m l : ℕ) (g : Fin l → ℝ → ℝ) (c : ℝ) (p : Point 1 m) :
    (scalarModel m l g c).objective p = c * p.1 0 := by
  simp [ModelData.objective, scalarModel, LinearForm]

theorem scalar_base_compact (m l : ℕ) (g : Fin l → ℝ → ℝ) (c : ℝ) :
    IsCompact ((scalarModel m l g c).linearRegion ∩ IntegerCylinder (n := 1)
      (scalarModel m l g c).lo (scalarModel m l g c).hi) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Point 1 m) 1)).of_isClosed_subset
    (base_closed _) 
  rintro p ⟨hp, y, hy, heq⟩
  have hx := (scalar_linear_iff m l g c p).mp hp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i; fin_cases i; exact hx.1
  · intro i; rw [heq]; exact (hy i).1
  · intro i; fin_cases i; exact hx.2
  · intro i; rw [heq]; exact (hy i).2

def squareModel (m : ℕ) : ModelData 1 m 1 2 :=
  scalarModel m 1 (fun _ x => x^2) (-1)

theorem square_convex (m : ℕ) :
    ∀ j, ConvexOn ℝ Set.univ ((squareModel m).g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t hs ht hst
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 0-q.1 0))
  simp only [squareModel, scalarModel, Prod.fst_add, Prod.smul_fst,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [sq_nonneg (p.1 0-q.1 0)]

theorem square_smooth (m : ℕ) :
    ∀ j, ContDiff ℝ 1 ((squareModel m).g j) := by
  intro j
  exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2)

theorem square_derivative (m : ℕ) (p : Point 1 m) (j : Fin 1) :
    HasFDerivAt ((squareModel m).g j) ((2*p.1 0) • coord 0) p := by
  have h := (hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p (coord (m := m) 0).hasFDerivAt
  convert h using 1 <;> norm_num [squareModel, scalarModel, coord, Function.comp_def]

theorem square_fderiv (m : ℕ) (p : Point 1 m) (j : Fin 1) :
    fderiv ℝ ((squareModel m).g j) p = (2*p.1 0) • coord 0 :=
  (square_derivative m p j).fderiv

theorem square_base_compact (m : ℕ) :
    IsCompact ((squareModel m).linearRegion ∩ IntegerCylinder (n := 1)
      (squareModel m).lo (squareModel m).hi) := scalar_base_compact _ _ _ _

theorem square_no_strict_start (m : ℕ) :
    ¬ ∃ p : Point 1 m, ∀ j, (squareModel m).g j p < 0 := by
  rintro ⟨p, hp⟩
  exact (not_lt_of_ge (sq_nonneg (p.1 0))) (hp 0)

def halfPower (k : ℕ) : ℝ := (1/2)^k

theorem halfPower_pos (k : ℕ) : 0 < halfPower k := pow_pos (by norm_num) _
theorem halfPower_le_one (k : ℕ) : halfPower k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)
theorem halfPower_succ (k : ℕ) : halfPower (k+1) = halfPower k / 2 := by
  simp [halfPower, pow_succ]; ring
theorem halfPower_antitone : Antitone halfPower := by
  intro i k hik
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hik

def planePoint {m : ℕ} (x y : ℝ) : Point 2 m := (![x,y], 0)

/-- A literal rectangle with a fixed dummy integer vector. -/
def planeModel (m l : ℕ) (lower upper : ℝ)
    (g : Fin l → Point 2 m → ℝ) (cx cy : ℝ) : ModelData 2 m l 4 where
  g := g
  A := ![![-1,0], ![1,0], ![0,-1], ![0,1]]
  B := fun _ _ => 0
  rhs := ![-lower,upper,-lower,upper]
  c1 := ![cx,cy]
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0

theorem plane_linear_iff (m l : ℕ) (lower upper : ℝ)
    (g : Fin l → Point 2 m → ℝ) (cx cy : ℝ) (p : Point 2 m) :
    p ∈ (planeModel m l lower upper g cx cy).linearRegion ↔
      lower ≤ p.1 0 ∧ p.1 0 ≤ upper ∧ lower ≤ p.1 1 ∧ p.1 1 ≤ upper := by
  simp [ModelData.linearRegion, planeModel, LinearForm, Fin.forall_fin_succ,
    Fin.sum_univ_two]

theorem plane_objective (m l : ℕ) (lower upper : ℝ)
    (g : Fin l → Point 2 m → ℝ) (cx cy : ℝ) (p : Point 2 m) :
    (planeModel m l lower upper g cx cy).objective p = cx*p.1 0 + cy*p.1 1 := by
  simp [ModelData.objective, planeModel, LinearForm, Fin.sum_univ_two]

theorem plane_base_compact (m l : ℕ) (lower upper : ℝ)
    (g : Fin l → Point 2 m → ℝ) (cx cy : ℝ) :
    IsCompact ((planeModel m l lower upper g cx cy).linearRegion ∩
      IntegerCylinder (n := 2) (planeModel m l lower upper g cx cy).lo
        (planeModel m l lower upper g cx cy).hi) := by
  apply (isCompact_Icc : IsCompact (Set.Icc
    (planePoint (m := m) lower lower) (planePoint upper upper))).of_isClosed_subset
    (base_closed _)
  rintro p ⟨hp, y, hy, heq⟩
  have hx := (plane_linear_iff m l lower upper g cx cy p).mp hp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i; fin_cases i <;> simp only [planePoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]; exact hx.1; exact hx.2.2.1
  · intro i; rw [heq]; exact (hy i).1
  · intro i; fin_cases i <;> simp only [planePoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]; exact hx.2.1; exact hx.2.2.2
  · intro i; rw [heq]; exact (hy i).2

def diskModel (m : ℕ) (radius cx cy : ℝ) : ModelData 2 m 1 4 :=
  planeModel m 1 (-radius) radius (fun _ p => (p.1 0)^2+(p.1 1)^2-1) cx cy

theorem disk_convex (m : ℕ) (radius cx cy : ℝ) :
    ∀ j, ConvexOn ℝ Set.univ ((diskModel m radius cx cy).g j) := by
  intro j; refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t hs ht hst
  have h0 := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 0-q.1 0))
  have h1 := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 1-q.1 1))
  simp only [diskModel, planeModel, Prod.fst_add, Prod.smul_fst,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

theorem disk_smooth (m : ℕ) (radius cx cy : ℝ) :
    ∀ j, ContDiff ℝ 1 ((diskModel m radius cx cy).g j) := by
  intro j
  exact ((((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 2)).comp contDiff_fst).pow 2).add
    (((contDiff_apply ℝ (fun _ => ℝ) (1 : Fin 2)).comp contDiff_fst).pow 2)).sub contDiff_const

theorem disk_derivative (m : ℕ) (radius cx cy : ℝ) (p : Point 2 m) (j : Fin 1) :
    HasFDerivAt ((diskModel m radius cx cy).g j)
      ((2*p.1 0) • coord 0 + (2*p.1 1) • coord 1) p := by
  have h0 := (hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p (coord (m := m) 0).hasFDerivAt
  have h1 := (hasDerivAt_pow 2 (p.1 1)).comp_hasFDerivAt p (coord (m := m) 1).hasFDerivAt
  convert (h0.add h1).sub_const 1 using 1 <;>
    norm_num [diskModel, planeModel, coord, Function.comp_def]

theorem disk_fderiv (m : ℕ) (radius cx cy : ℝ) (p : Point 2 m) (j : Fin 1) :
    fderiv ℝ ((diskModel m radius cx cy).g j) p =
      (2*p.1 0) • coord 0 + (2*p.1 1) • coord 1 :=
  (disk_derivative m radius cx cy p j).fderiv

theorem disk_base_compact (m : ℕ) (radius cx cy : ℝ) :
    IsCompact ((diskModel m radius cx cy).linearRegion ∩ IntegerCylinder (n := 2)
      (diskModel m radius cx cy).lo (diskModel m radius cx cy).hi) :=
  plane_base_compact _ _ _ _ _ _ _

theorem disk_strict_start (m : ℕ) :
    planePoint (m := m) 0 0 ∈ (diskModel m 1 (-1) 0).linearRegion ∧
    ∀ j, (diskModel m 1 (-1) 0).g j (planePoint 0 0) < 0 := by
  constructor
  · change planePoint (m := m) 0 0 ∈ (planeModel m 1 (-1) 1 _ (-1) 0).linearRegion
    rw [plane_linear_iff]; norm_num [planePoint]
  · intro j; norm_num [diskModel, planeModel, planePoint]

def history {n m l : ℕ} (b : ℕ → CPBatch n m l) (k : ℕ) : List (CPBatch n m l) :=
  (List.range k).map b

theorem history_mem_iff {n m l : ℕ} (b : ℕ → CPBatch n m l) (k : ℕ)
    (a : CPBatch n m l) : a ∈ history b k ↔ ∃ i < k, b i = a := by
  simp [history, List.mem_map, List.mem_range]

theorem history_succ {n m l : ℕ} (b : ℕ → CPBatch n m l) (k : ℕ) :
    history b (k+1) = history b k ++ [b k] := by
  simp [history, List.range_succ, List.map_append]

theorem history_length {n m l : ℕ} (b : ℕ → CPBatch n m l) (k : ℕ) :
    (history b k).length = k := by simp [history]

def squareTrial (m : ℕ) (y : ℕ → IntVector m) (k : ℕ) : Point 1 m :=
  scalarPoint (halfPower k) (fun i => (y k i : ℝ))

def squareBatch (m : ℕ) (y : ℕ → IntVector m) (k : ℕ) : CPBatch 1 m 1 :=
  ⟨squareTrial m y k, squareTrial m y k, {0}⟩

theorem square_batch_cuts (m : ℕ) (y : ℕ → IntVector m) (k : ℕ) (p : Point 1 m) :
    cpBatchCuts (squareModel m) (squareBatch m y k) p ↔ p.1 0 ≤ halfPower k / 2 := by
  simp only [cpBatchCuts, squareBatch, Finset.mem_singleton, forall_eq]
  rw [square_fderiv]
  simp only [squareModel, scalarModel, squareTrial, scalarPoint,
    ContinuousLinearMap.smul_apply, smul_eq_mul, coord_apply, Prod.fst_sub, Pi.sub_apply]
  have hq := halfPower_pos k
  constructor <;> intro h <;> nlinarith

theorem square_trial_base (m : ℕ) (y : ℕ → IntVector m)
    (hy : ∀ k i, 0 ≤ y k i ∧ y k i ≤ 1) (k : ℕ) :
    squareTrial m y k ∈ cpBase (squareModel m) := by
  refine ⟨?_, y k, ?_, rfl⟩
  · exact (scalar_linear_iff _ _ _ _ _).mpr ⟨(halfPower_pos k).le, halfPower_le_one k⟩
  · intro i
    change (0:ℝ) ≤ (y k i : ℝ) ∧ (y k i : ℝ) ≤ 1
    exact ⟨by exact_mod_cast (hy k i).1, by exact_mod_cast (hy k i).2⟩

theorem square_trial_master (m : ℕ) (y : ℕ → IntVector m)
    (hy : ∀ k i, 0 ≤ y k i ∧ y k i ≤ 1) (k : ℕ) :
    squareTrial m y k ∈ cpMaster (squareModel m) (history (squareBatch m y) k) := by
  rw [cp_master_mem_iff]
  refine ⟨square_trial_base m y hy k, ?_⟩
  intro b hb
  obtain ⟨i, hik, rfl⟩ := (history_mem_iff _ _ _).mp hb
  rw [square_batch_cuts]
  change halfPower k ≤ halfPower i / 2
  rw [← halfPower_succ]
  exact halfPower_antitone (Nat.succ_le_of_lt hik)

theorem square_master_bound (m : ℕ) (y : ℕ → IntVector m) (k : ℕ)
    (p : Point 1 m) (hp : p ∈ cpMaster (squareModel m) (history (squareBatch m y) k)) :
    p.1 0 ≤ halfPower k := by
  obtain ⟨hb,hcuts⟩ := (cp_master_mem_iff _ _ _).mp hp
  cases k with
  | zero => exact (scalar_linear_iff _ _ _ _ p).mp hb.1 |>.2
  | succ k =>
    rw [halfPower_succ]
    exact (square_batch_cuts m y k p).mp
      (hcuts _ ((history_mem_iff _ _ _).mpr ⟨k,Nat.lt_succ_self k,rfl⟩))

theorem square_exact_master_minimum (m : ℕ) (y : ℕ → IntVector m)
    (hy : ∀ k i, 0 ≤ y k i ∧ y k i ≤ 1) (k : ℕ) :
    IsMinimizer (cpMaster (squareModel m) (history (squareBatch m y) k))
      (squareModel m).objective (squareTrial m y k) := by
  refine ⟨square_trial_master m y hy k, ?_⟩
  intro p hp
  have h := square_master_bound m y k p hp
  simpa only [squareModel, scalar_objective, squareTrial, scalarPoint, neg_mul,
    one_mul] using neg_le_neg h

theorem square_batch_most (m : ℕ) (y : ℕ → IntVector m) (k : ℕ) :
    CPBatchValid (squareModel m) .ecpMost (squareBatch m y k) := by
  refine ⟨rfl, by simp [squareBatch], ?_⟩
  intro j _ i
  exact le_rfl

theorem square_batch_all (m : ℕ) (y : ℕ → IntVector m) (k : ℕ) :
    CPBatchValid (squareModel m) .ecpAll (squareBatch m y k) := by
  refine ⟨rfl, ?_⟩
  intro j; fin_cases j
  simp [squareBatch, Finset.mem_singleton, squareModel, scalarModel,
    squareTrial, scalarPoint, true_iff]
  exact sq_pos_of_pos (halfPower_pos k)

theorem square_trial_not_feasible (m : ℕ) (y : ℕ → IntVector m) (k : ℕ) :
    ¬ CPFeasibleWithin (squareModel m) 0 (squareTrial m y k) := by
  intro h
  exact (not_le_of_gt (sq_pos_of_pos (halfPower_pos k))) (h 0)

theorem square_raw_step (m : ℕ) (y : ℕ → IntVector m)
    (hy : ∀ k i, 0 ≤ y k i ∧ y k i ≤ 1) (k : ℕ) :
    CPStep (squareModel m) .ecpMost 0 (history (squareBatch m y) k) (squareBatch m y k) ∧
    CPStep (squareModel m) .ecpAll 0 (history (squareBatch m y) k) (squareBatch m y k) := by
  have hm := square_exact_master_minimum m y hy k
  have hf := square_trial_not_feasible m y k
  exact ⟨⟨hm,hf,square_batch_most m y k⟩, ⟨hm,hf,square_batch_all m y k⟩⟩

theorem square_actual_infinite_chain (m : ℕ) (y : ℕ → IntVector m)
    (hy : ∀ k i, 0 ≤ y k i ∧ y k i ≤ 1) :
    history (squareBatch m y) 0 = [] ∧
    ∀ k, CPContinue (squareModel m) .ecpMost 0
      (history (squareBatch m y) k) (history (squareBatch m y) (k+1)) ∧
      (history (squareBatch m y) k).length = k := by
  refine ⟨rfl,fun k => ⟨?_, history_length _ k⟩⟩
  exact ⟨squareBatch m y k,history_succ _ k,(square_raw_step m y hy k).1⟩

theorem square_zero_original_minimum (m : ℕ) :
    IsMinimizer ((squareModel m).feasibleOn Set.univ) (squareModel m).objective
      (scalarPoint 0 (0 : RealVector m)) := by
  constructor
  · rw [source_feasible_iff]
    refine ⟨Set.mem_univ _, ?_, ?_, 0, ?_, by funext i; simp [scalarPoint]⟩
    · intro j; norm_num [squareModel, scalarModel, scalarPoint]
    · exact (scalar_linear_iff _ _ _ _ _).mpr (by norm_num [scalarPoint])
    · intro i; norm_num [squareModel, scalarModel]
  · intro p hp
    have hx := ((source_feasible_iff _ _ _).mp hp).2.1 0
    change (p.1 0)^2 ≤ 0 at hx
    have hpzero : p.1 0 = 0 := by nlinarith [sq_nonneg (p.1 0)]
    simp [squareModel, scalar_objective, scalarPoint, hpzero]

def quarterPower (k : ℕ) : ℝ := (1/4)^k
def diskScale (k : ℕ) : ℝ := Real.sqrt (1+(quarterPower k)^2)

theorem quarterPower_pos (k : ℕ) : 0 < quarterPower k := pow_pos (by norm_num) _
theorem quarterPower_le_one (k : ℕ) : quarterPower k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)
theorem quarterPower_succ (k : ℕ) : quarterPower (k+1) = quarterPower k/4 := by
  simp [quarterPower, pow_succ]; ring
theorem quarterPower_antitone : Antitone quarterPower := by
  intro i k hik
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hik
theorem diskScale_sq (k : ℕ) : (diskScale k)^2 = 1+(quarterPower k)^2 :=
  Real.sq_sqrt (by positivity)
theorem diskScale_gt_one (k : ℕ) : 1 < diskScale k := by
  have hp := quarterPower_pos k
  have hs := Real.sqrt_nonneg (1+(quarterPower k)^2)
  change 0 ≤ diskScale k at hs
  have heq := diskScale_sq k
  nlinarith [sq_pos_of_pos hp]

theorem disk_retained_inequality {i k : ℕ} (hik : i < k) :
    1 + quarterPower i * quarterPower k ≤ diskScale i := by
  have hi := quarterPower_pos i
  have hk := quarterPower_pos k
  have hi1 := quarterPower_le_one i
  have hle : quarterPower k ≤ quarterPower i / 4 := by
    rw [← quarterPower_succ]
    exact quarterPower_antitone (Nat.succ_le_of_lt hik)
  have hmul : 0 ≤ quarterPower i * quarterPower k := mul_nonneg hi.le hk.le
  have hupper : quarterPower i * quarterPower k ≤ (quarterPower i)^2/4 := by nlinarith
  have hsmall : quarterPower i * quarterPower k ≤ 1/4 := by nlinarith
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_nonneg hmul (sub_nonneg.mpr hsmall)]

def diskTrial (m k : ℕ) : Point 2 m := planePoint 1 (quarterPower k)
def diskRoot (m k : ℕ) : Point 2 m :=
  planePoint (1/diskScale k) (quarterPower k/diskScale k)
def diskBatch (m k : ℕ) : CPBatch 2 m 1 := ⟨diskTrial m k, diskRoot m k, {0}⟩

theorem disk_root_zero (m k : ℕ) (j : Fin 1) :
    (diskModel m 1 (-1) 0).g j (diskRoot m k) = 0 := by
  have hs : diskScale k ≠ 0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans (diskScale_gt_one k))
  have heq := diskScale_sq k
  dsimp [diskModel, planeModel, diskRoot, planePoint]
  field_simp
  nlinarith

theorem disk_root_line (m k : ℕ) :
    diskRoot m k = AffineMap.lineMap (planePoint 0 0) (diskTrial m k) (1/diskScale k) := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [diskRoot, diskTrial, planePoint, AffineMap.lineMap_apply_module, smul_eq_mul,
        mul_comm, div_eq_mul_inv]
  · ext i
    simp [diskRoot, diskTrial, planePoint, AffineMap.lineMap_apply_module, smul_eq_mul]

theorem disk_batch_valid (m k : ℕ) :
    CPBatchValid (diskModel m 1 (-1) 0) (.esh (planePoint 0 0)) (diskBatch m k) := by
  have hs := diskScale_gt_one k
  refine ⟨1/diskScale k, ?_, disk_root_line m k, ?_, by simp [diskBatch], ?_⟩
  · constructor
    · positivity
    · exact (div_lt_one (by linarith)).mpr hs
  · intro j; exact (disk_root_zero m k j).le
  · intro j; fin_cases j; simp [diskBatch, disk_root_zero]

theorem disk_batch_cuts (m k : ℕ) (p : Point 2 m) :
    cpBatchCuts (diskModel m 1 (-1) 0) (diskBatch m k) p ↔
      p.1 0 + quarterPower k * p.1 1 ≤ diskScale k := by
  have hs : 0 < diskScale k := (by norm_num : (0:ℝ)<1).trans (diskScale_gt_one k)
  have hsne := ne_of_gt hs
  have hsq := diskScale_sq k
  simp only [cpBatchCuts, diskBatch, Finset.mem_singleton, forall_eq]
  rw [disk_fderiv, disk_root_zero]
  simp only [diskRoot, planePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, coord_apply, Prod.fst_sub, Pi.sub_apply, zero_add]
  have heq : 2*(1/diskScale k)*(p.1 0-1/diskScale k) +
      2*(quarterPower k/diskScale k)*(p.1 1-quarterPower k/diskScale k) =
      (2/diskScale k)*(p.1 0+quarterPower k*p.1 1-diskScale k) := by
    field_simp
    nlinarith
  rw [heq]
  constructor
  · intro h
    have hh : p.1 0+quarterPower k*p.1 1-diskScale k ≤ 0 := by
      exact nonpos_of_mul_nonpos_right h (div_pos (by norm_num) hs)
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by norm_num) hs.le) (by linarith)

theorem disk_trial_base (m k : ℕ) : diskTrial m k ∈ cpBase (diskModel m 1 (-1) 0) := by
  refine ⟨?_,0,?_,by funext i; simp [diskTrial,planePoint]⟩
  · change diskTrial m k ∈ (planeModel m 1 (-1) 1 _ (-1) 0).linearRegion
    rw [plane_linear_iff]
    have h0 := quarterPower_pos k
    have h1 := quarterPower_le_one k
    simpa [diskTrial,planePoint] using (show (-1:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 1 ∧
      -1 ≤ quarterPower k ∧ quarterPower k ≤ 1 by constructor; norm_num; exact ⟨le_rfl,by linarith,h1⟩)
  · intro i; norm_num [diskModel,planeModel]

/-- Every earlier cut holds, including a finite prefix that may have been
generated in an integer-relaxed LP phase. The dummy integer is fixed to zero. -/
theorem disk_trial_master (m k : ℕ) :
    diskTrial m k ∈ cpMaster (diskModel m 1 (-1) 0) (history (diskBatch m) k) := by
  rw [cp_master_mem_iff]
  refine ⟨disk_trial_base m k,?_⟩
  intro b hb
  obtain ⟨i,hik,rfl⟩ := (history_mem_iff _ _ _).mp hb
  rw [disk_batch_cuts]
  exact disk_retained_inequality hik

theorem disk_exact_master_minimum (m k : ℕ) :
    IsMinimizer (cpMaster (diskModel m 1 (-1) 0) (history (diskBatch m) k))
      (diskModel m 1 (-1) 0).objective (diskTrial m k) := by
  refine ⟨disk_trial_master m k,?_⟩
  intro p hp
  have hb := ((cp_master_mem_iff _ _ _).mp hp).1.1
  have hx := ((plane_linear_iff _ _ _ _ _ _ _ _).mp hb).2.1
  simpa [diskModel,plane_objective,diskTrial,planePoint] using neg_le_neg hx

theorem disk_trial_not_feasible (m k : ℕ) :
    ¬ CPFeasibleWithin (diskModel m 1 (-1) 0) 0 (diskTrial m k) := by
  intro h
  have h0 := h 0
  have hp := sq_pos_of_pos (quarterPower_pos k)
  simp [diskModel,planeModel,diskTrial,planePoint] at h0
  rw [h0] at hp
  norm_num at hp

theorem disk_raw_step (m k : ℕ) :
    CPStep (diskModel m 1 (-1) 0) (.esh (planePoint 0 0)) 0
      (history (diskBatch m) k) (diskBatch m k) :=
  ⟨disk_exact_master_minimum m k,disk_trial_not_feasible m k,disk_batch_valid m k⟩

/-- Arbitrary starting index: a finite valid LP prefix is retained verbatim
before the infinite exact MILP trace. This is not a numerical LP driver. -/
theorem disk_arbitrary_prefix_chain (m start : ℕ) :
    ∀ k, CPContinue (diskModel m 1 (-1) 0) (.esh (planePoint 0 0)) 0
      (history (diskBatch m) (start+k)) (history (diskBatch m) (start+k+1)) ∧
      (history (diskBatch m) (start+k)).length = start+k := by
  intro k
  exact ⟨⟨diskBatch m (start+k),history_succ _ _,disk_raw_step m (start+k)⟩,
    history_length _ _⟩

def affineScalar (m : ℕ) (slope offset cost : ℝ) : ModelData 1 m 1 2 :=
  scalarModel m 1 (fun _ x => slope*x+offset) cost

theorem affineScalar_convex (m : ℕ) (slope offset cost : ℝ) :
    ∀ j, ConvexOn ℝ Set.univ ((affineScalar m slope offset cost).g j) := by
  intro j; refine ⟨convex_univ,?_⟩
  intro p _ q _ s t _ _ hst
  simp only [affineScalar,scalarModel,Prod.fst_add,Prod.smul_fst,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have heq : slope * (s*p.1 0+t*q.1 0)+offset =
      s*(slope*p.1 0+offset)+t*(slope*q.1 0+offset) := by
    nlinarith [congrArg (fun z : ℝ => z*offset) hst]
  exact heq.le

theorem affineScalar_smooth (m : ℕ) (slope offset cost : ℝ) :
    ∀ j, ContDiff ℝ 1 ((affineScalar m slope offset cost).g j) := by
  intro j
  exact (contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst)).add
    contDiff_const

theorem scalar_zero_base (m l : ℕ) (g : Fin l → ℝ → ℝ) (c : ℝ) :
    scalarPoint 0 (0 : RealVector m) ∈ cpBase (scalarModel m l g c) := by
  refine ⟨(scalar_linear_iff _ _ _ _ _).mpr (by norm_num [scalarPoint]),
    0,?_,by funext i; simp [scalarPoint]⟩
  intro i; norm_num [scalarModel]

theorem scalar_zero_empty_master_minimum (m l : ℕ) (g : Fin l → ℝ → ℝ)
    (c : ℝ) (hc : 0 ≤ c) :
    IsMinimizer (cpMaster (scalarModel m l g c) []) (scalarModel m l g c).objective
      (scalarPoint 0 (0 : RealVector m)) := by
  rw [cp_master_nil]
  refine ⟨scalar_zero_base m l g c,?_⟩
  intro p hp
  have hx := ((scalar_linear_iff _ _ _ _ p).mp hp.1).1
  simpa [scalar_objective,scalarPoint] using mul_nonneg hc hx

theorem tolerance_return_infeasible_gap (M : ℝ) (hM : 0 < M) :
    CPStop (affineScalar 0 (-1) (1/8) M) (1/4) [] (.point (scalarPoint 0 0)) ∧
    scalarPoint 0 (0 : RealVector 0) ∉ (affineScalar 0 (-1) (1/8) M).feasibleOn Set.univ ∧
    IsMinimizer ((affineScalar 0 (-1) (1/8) M).feasibleOn Set.univ)
      (affineScalar 0 (-1) (1/8) M).objective (scalarPoint (1/8) 0) ∧
    (affineScalar 0 (-1) (1/8) M).objective (scalarPoint (1/8) 0) -
      (affineScalar 0 (-1) (1/8) M).objective (scalarPoint 0 0) = M/8 := by
  refine ⟨?_,?_,?_,?_⟩
  · apply CPStop.point
    · exact scalar_zero_empty_master_minimum _ _ _ _ hM.le
    · intro j; norm_num [affineScalar,scalarModel,scalarPoint]
  · intro hp
    have h := ((source_feasible_iff _ _ _).mp hp).2.1 0
    norm_num [affineScalar,scalarModel,scalarPoint] at h
  · constructor
    · rw [source_feasible_iff]
      refine ⟨Set.mem_univ _,?_,?_,0,?_,by funext i; exact Fin.elim0 i⟩
      · intro j; norm_num [affineScalar,scalarModel,scalarPoint]
      · exact (scalar_linear_iff _ _ _ _ _).mpr (by norm_num [scalarPoint])
      · intro i; exact Fin.elim0 i
    · intro p hp
      have hg := ((source_feasible_iff _ _ _).mp hp).2.1 0
      change -1*p.1 0+1/8 ≤ 0 at hg
      have hx : (1:ℝ)/8 ≤ p.1 0 := by linarith
      simpa [affineScalar,scalar_objective,scalarPoint] using
        (mul_le_mul_of_nonneg_left hx hM.le)
  · simp [affineScalar,scalar_objective,scalarPoint]; ring

theorem tolerance_gap_arbitrarily_large (R : ℝ) :
    ∃ M > 0, R < (affineScalar 0 (-1) (1/8) M).objective (scalarPoint (1/8) 0) -
      (affineScalar 0 (-1) (1/8) M).objective (scalarPoint 0 0) := by
  refine ⟨8*(|R|+1),by positivity,?_⟩
  simp [affineScalar,scalar_objective,scalarPoint]
  nlinarith [le_abs_self R]

theorem ecp_empty_original_tolerance_return :
    (affineScalar 0 1 (1/8) 1).feasibleOn Set.univ = ∅ ∧
    CPStop (affineScalar 0 1 (1/8) 1) (1/4) [] (.point (scalarPoint 0 0)) := by
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨_,hg,hL,_⟩ := (source_feasible_iff _ _ _).mp hp
    have hx := ((scalar_linear_iff _ _ _ _ p).mp hL).1
    have h := hg 0
    change 1*p.1 0+1/8 ≤ 0 at h
    linarith
  · apply CPStop.point
    · exact scalar_zero_empty_master_minimum _ _ _ _ (by norm_num)
    · intro j; norm_num [affineScalar,scalarModel,scalarPoint]

/-- Source-review M3: feasible LP entry and weak MILP equality are compatible. -/
def equalityModel : ModelData 1 1 1 3 where
  g := fun _ p => 1/2-2*p.2 0
  A := ![fun _ => -1, fun _ => 1, fun _ => 1]
  B := ![fun _ => 0, fun _ => 0, fun _ => 2]
  rhs := ![0,1,2]
  c1 := fun _ => -2
  c2 := fun _ => -1
  lo := fun _ => 0
  hi := fun _ => 1

def xy (x y : ℝ) : Point 1 1 := (fun _ => x,fun _ => y)

theorem equality_linear (p : Point 1 1) : p ∈ equalityModel.linearRegion ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ p.1 0+2*p.2 0 ≤ 2 := by
  simp [ModelData.linearRegion,equalityModel,LinearForm,Fin.forall_fin_succ]

theorem equality_objective (p : Point 1 1) :
    equalityModel.objective p = -2*p.1 0-p.2 0 := by
  simp [ModelData.objective,equalityModel,LinearForm]; ring

theorem equality_convex : ∀ j, ConvexOn ℝ Set.univ (equalityModel.g j) := by
  intro j; refine ⟨convex_univ,?_⟩
  intro p _ q _ s t _ _ hst
  simp only [equalityModel,Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith

theorem equality_smooth : ∀ j, ContDiff ℝ 1 (equalityModel.g j) := by
  intro j
  exact contDiff_const.sub (contDiff_const.mul
    ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd))

theorem equality_base_compact : IsCompact (cpBase equalityModel) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (xy 0 0) (xy 1 1))).of_isClosed_subset
    (base_closed _)
  rintro p ⟨hp,y,hy,heq⟩
  have hx := equality_linear p |>.mp hp
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i; exact hx.1
  · intro i; rw [heq]; exact (hy i).1
  · intro i; fin_cases i; exact hx.2.1
  · intro i; rw [heq]; exact (hy i).2

def equalityLPBase : Set (Point 1 1) :=
  {p | p ∈ equalityModel.linearRegion ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1}

theorem equality_lp_minimum : IsMinimizer equalityLPBase equalityModel.objective (xy 1 (1/2)) := by
  constructor
  · exact ⟨(equality_linear _).mpr (by norm_num [xy]),by norm_num [xy]⟩
  · intro p hp
    have hx := (equality_linear p).mp hp.1
    simp only [equality_objective,xy]
    linarith

theorem equality_initialization_minimum :
    IsMinimizer equalityLPBase (fun p => equalityModel.g 0 p) (xy 0 1) ∧
    CPInterior equalityModel (.esh (xy 0 1)) := by
  constructor
  · refine ⟨⟨(equality_linear _).mpr (by norm_num [xy]),by norm_num [xy]⟩,?_⟩
    intro p hp
    change 1/2-2*1 ≤ 1/2-2*p.2 0
    linarith [hp.2.2]
  · exact ⟨(equality_linear _).mpr (by norm_num [xy]),by intro j; norm_num [equalityModel,xy]⟩

theorem equality_integer_cases (p : Point 1 1) (hp : p ∈ cpBase equalityModel) :
    p.2 0 = 0 ∨ p.2 0 = 1 := by
  obtain ⟨y,hy,heq⟩ := hp.2
  have hybound : (0:ℝ) ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 1 := hy 0
  have hy0 : 0 ≤ y 0 := by exact_mod_cast hybound.1
  have hy1 : y 0 ≤ 1 := by exact_mod_cast hybound.2
  have h : y 0 = 0 ∨ y 0 = 1 := by omega
  simpa [heq] using h

theorem equality_milp_minimum :
    IsMinimizer (cpMaster equalityModel []) equalityModel.objective (xy 1 0) := by
  rw [cp_master_nil]
  constructor
  · exact ⟨(equality_linear _).mpr (by norm_num [xy]),0,
      by intro i; norm_num [equalityModel],by funext i; simp [xy]⟩
  · intro p hp
    have hx := (equality_linear p).mp hp.1
    have hy := equality_integer_cases p hp
    simp only [equality_objective,xy]
    rcases hy with h | h <;> rw [h] <;> linarith

theorem equality_original_minimum :
    IsMinimizer (equalityModel.feasibleOn Set.univ) equalityModel.objective (xy 0 1) := by
  constructor
  · rw [source_feasible_iff]
    refine ⟨Set.mem_univ _,?_,(equality_linear _).mpr (by norm_num [xy]),
      fun _ => (1:ℤ),?_,by funext i; simp [xy]⟩
    · intro j; norm_num [equalityModel,xy]
    · intro i; norm_num [equalityModel]
  · intro p hp
    obtain ⟨_,hg,hL,hY⟩ := (source_feasible_iff _ _ _).mp hp
    have hy := equality_integer_cases p ⟨hL,hY⟩
    have hx := (equality_linear p).mp hL
    have hg0 := hg 0
    change (1:ℝ)/2-2*p.2 0 ≤ 0 at hg0
    simp only [equality_objective,xy]
    rcases hy with h | h
    · rw [h] at hg0; norm_num at hg0
    · have hb := hx.2.2
      rw [h] at hb
      rw [h]
      linarith

theorem equality_full_model_control :
    equalityModel.g 0 (xy 1 (1/2)) < 0 ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1,
      equalityModel.g 0 (AffineMap.lineMap (xy 0 1) (xy 1 (1/2)) t) < 0) ∧
    CPStop equalityModel (1/2) [] (.point (xy 1 0)) ∧
    equalityModel.g 0 (xy 1 0) = 1/2 := by
  refine ⟨by norm_num [equalityModel,xy],?_,?_,by norm_num [equalityModel,xy]⟩
  · intro t ht
    simp [equalityModel,xy,AffineMap.lineMap_apply_module,smul_eq_mul]
    linarith [ht.1,ht.2]
  · exact .point _ equality_milp_minimum (by intro j; norm_num [equalityModel,xy])

def integerPoint (y : ℝ) : Point 0 1 := (0,fun _ => y)
def integerCoord : Point 0 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.snd ℝ (RealVector 0) (RealVector 1))

/-- Original mixed feasible set is empty, although the relaxed strict start
y=1/2 is available. This separates approximate return from infeasibility. -/
def integerCurve : ModelData 0 1 1 0 where
  g := fun _ p => (p.2 0-1/2)^2-1/8
  A := fun _ _ => 0
  B := fun _ _ => 0
  rhs := fun _ => 0
  c1 := fun _ => 0
  c2 := fun _ => 1
  lo := fun _ => 0
  hi := fun _ => 1

theorem integerCurve_objective (p : Point 0 1) : integerCurve.objective p = p.2 0 := by
  simp [ModelData.objective,integerCurve,LinearForm]

theorem integerCurve_cases (p : Point 0 1) (hp : p ∈ cpBase integerCurve) :
    p.2 0 = 0 ∨ p.2 0 = 1 := by
  obtain ⟨y,hy,heq⟩ := hp.2
  have hybound : (0:ℝ) ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 1 := hy 0
  have h0 : 0 ≤ y 0 := by exact_mod_cast hybound.1
  have h1 : y 0 ≤ 1 := by exact_mod_cast hybound.2
  have h : y 0 = 0 ∨ y 0 = 1 := by omega
  simpa [heq] using h

theorem integerCurve_endpoint_base (y : ℤ) (hy : 0 ≤ y ∧ y ≤ 1) :
    integerPoint y ∈ cpBase integerCurve := by
  refine ⟨?_,fun _ => y,?_,rfl⟩
  · intro row; exact Fin.elim0 row
  · intro i; change (0:ℝ) ≤ (y:ℝ) ∧ (y:ℝ) ≤ 1
    exact ⟨by exact_mod_cast hy.1,by exact_mod_cast hy.2⟩

theorem integerCurve_compact : IsCompact (cpBase integerCurve) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (integerPoint 0) (integerPoint 1))).of_isClosed_subset
    (base_closed _)
  rintro p ⟨_,y,hy,heq⟩
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; exact Fin.elim0 i
  · intro i; rw [heq]; exact (hy i).1
  · intro i; exact Fin.elim0 i
  · intro i; rw [heq]; exact (hy i).2

theorem integerCurve_convex : ∀ j, ConvexOn ℝ Set.univ (integerCurve.g j) := by
  intro j; refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.2 0-q.2 0))
  simp only [integerCurve,Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have htEq : t=1-s := by linarith
  have heq : s*((p.2 0-1/2)^2-1/8)+t*((q.2 0-1/2)^2-1/8)-
      ((s*p.2 0+t*q.2 0-1/2)^2-1/8) = s*t*(p.2 0-q.2 0)^2 := by
    rw [htEq]; ring
  linarith

theorem integerCurve_smooth : ∀ j, ContDiff ℝ 1 (integerCurve.g j) := by
  intro j
  exact ((((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd).sub
    contDiff_const).pow 2).sub contDiff_const

theorem integerCurve_derivative (p : Point 0 1) (j : Fin 1) :
    HasFDerivAt (integerCurve.g j) ((2*(p.2 0-1/2)) • integerCoord) p := by
  have h := ((hasDerivAt_pow 2 (p.2 0-1/2)).comp_hasFDerivAt p
    (integerCoord.hasFDerivAt.sub_const (1/2))).sub_const (1/8)
  convert h using 1 <;> norm_num [integerCurve,integerCoord,Function.comp_def]

theorem integerCurve_strict_start : CPInterior integerCurve (.esh (integerPoint (1/2))) := by
  constructor
  · intro row; exact Fin.elim0 row
  · intro j; norm_num [integerCurve,integerPoint]

theorem integerCurve_original_empty : integerCurve.feasibleOn Set.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨_,hg,hL,hY⟩ := (source_feasible_iff _ _ _).mp hp
  have hy := integerCurve_cases p ⟨hL,hY⟩
  have hg0 := hg 0
  change (p.2 0-1/2)^2-1/8 ≤ 0 at hg0
  rcases hy with h | h <;> rw [h] at hg0 <;> norm_num at hg0

theorem integerCurve_first_minimum :
    IsMinimizer (cpMaster integerCurve []) integerCurve.objective (integerPoint 0) := by
  rw [cp_master_nil]
  refine ⟨by simpa using integerCurve_endpoint_base 0 (by norm_num),?_⟩
  intro p hp
  rcases integerCurve_cases p hp with h | h <;>
    simp [integerCurve_objective,integerPoint,h]

theorem esh_empty_original_tolerance_return :
    integerCurve.feasibleOn Set.univ = ∅ ∧ CPInterior integerCurve (.esh (integerPoint (1/2))) ∧
    CPStop integerCurve (1/4) [] (.point (integerPoint 0)) := by
  refine ⟨integerCurve_original_empty,integerCurve_strict_start,?_⟩
  exact .point _ integerCurve_first_minimum (by intro j; norm_num [integerCurve,integerPoint])

def lowerRoot : ℝ := 1/2-Real.sqrt 2/4
def upperRoot : ℝ := 1/2+Real.sqrt 2/4
def lowerBatch : CPBatch 0 1 1 := ⟨integerPoint 0,integerPoint lowerRoot,{0}⟩
def upperBatch : CPBatch 0 1 1 := ⟨integerPoint 1,integerPoint upperRoot,{0}⟩

theorem sqrt_two_bounds : 0 < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  constructor
  · positivity
  · exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

theorem integerCurve_root_bounds : 0 < lowerRoot ∧ lowerRoot < 1/2 ∧
    1/2 < upperRoot ∧ upperRoot < 1 := by
  obtain ⟨h0,h2⟩ := sqrt_two_bounds
  dsimp [lowerRoot,upperRoot]
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

theorem integerCurve_roots (j : Fin 1) :
    integerCurve.g j (integerPoint lowerRoot) = 0 ∧
    integerCurve.g j (integerPoint upperRoot) = 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  simp only [integerCurve,integerPoint,lowerRoot,upperRoot]
  constructor <;> nlinarith

theorem integerCurve_root_line :
    integerPoint lowerRoot = AffineMap.lineMap (integerPoint (1/2)) (integerPoint 0) (Real.sqrt 2/2) ∧
    integerPoint upperRoot = AffineMap.lineMap (integerPoint (1/2)) (integerPoint 1) (Real.sqrt 2/2) := by
  constructor <;> apply Prod.ext
  · ext i; exact Fin.elim0 i
  · ext i; simp [integerPoint,lowerRoot,AffineMap.lineMap_apply_module,smul_eq_mul]; ring
  · ext i; exact Fin.elim0 i
  · ext i; simp [integerPoint,upperRoot,AffineMap.lineMap_apply_module,smul_eq_mul]; ring

theorem integerCurve_batches_valid :
    CPBatchValid integerCurve (.esh (integerPoint (1/2))) lowerBatch ∧
    CPBatchValid integerCurve (.esh (integerPoint (1/2))) upperBatch := by
  have ht : Real.sqrt 2/2 ∈ Set.Ioo (0:ℝ) 1 := by
    obtain ⟨h0,h2⟩ := sqrt_two_bounds
    constructor <;> linarith
  constructor
  · refine ⟨Real.sqrt 2/2,ht,integerCurve_root_line.1,
      fun j => (integerCurve_roots j).1.le,by simp [lowerBatch],?_⟩
    intro j; fin_cases j; simp [lowerBatch,integerCurve_roots]
  · refine ⟨Real.sqrt 2/2,ht,integerCurve_root_line.2,
      fun j => (integerCurve_roots j).2.le,by simp [upperBatch],?_⟩
    intro j; fin_cases j; simp [upperBatch,integerCurve_roots]

theorem integerCurve_lower_cut (p : Point 0 1) :
    cpBatchCuts integerCurve lowerBatch p ↔ lowerRoot ≤ p.2 0 := by
  simp only [cpBatchCuts,lowerBatch,Finset.mem_singleton,forall_eq]
  rw [(integerCurve_derivative _ _).fderiv,(integerCurve_roots 0).1]
  change 0+2*(lowerRoot-1/2)*(p.2 0-lowerRoot) ≤ 0 ↔ lowerRoot ≤ p.2 0
  have hl := integerCurve_root_bounds.2.1
  constructor <;> intro h <;> nlinarith

theorem integerCurve_upper_cut (p : Point 0 1) :
    cpBatchCuts integerCurve upperBatch p ↔ p.2 0 ≤ upperRoot := by
  simp only [cpBatchCuts,upperBatch,Finset.mem_singleton,forall_eq]
  rw [(integerCurve_derivative _ _).fderiv,(integerCurve_roots 0).2]
  change 0+2*(upperRoot-1/2)*(p.2 0-upperRoot) ≤ 0 ↔ p.2 0 ≤ upperRoot
  have hu := integerCurve_root_bounds.2.2.1
  constructor <;> intro h <;> nlinarith

theorem integerCurve_second_minimum :
    IsMinimizer (cpMaster integerCurve [lowerBatch]) integerCurve.objective (integerPoint 1) := by
  constructor
  · rw [cp_master_mem_iff]
    refine ⟨by simpa using integerCurve_endpoint_base 1 (by norm_num),?_⟩
    intro b hb
    have heq : b = lowerBatch := by simpa using hb
    subst b; rw [integerCurve_lower_cut]
    have h := integerCurve_root_bounds
    change lowerRoot ≤ 1
    linarith [h.2.1]
  · intro p hp
    obtain ⟨hb,hcuts⟩ := (cp_master_mem_iff _ _ _).mp hp
    have hcut := (integerCurve_lower_cut p).mp (hcuts lowerBatch (by simp))
    rcases integerCurve_cases p hb with h | h
    · have hlo := integerCurve_root_bounds.1
      rw [h] at hcut
      linarith
    · simp [integerCurve_objective,integerPoint,h]

theorem integerCurve_two_cuts_empty : cpMaster integerCurve [lowerBatch,upperBatch] = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hb,hcuts⟩ := (cp_master_mem_iff _ _ _).mp hp
  have hlo := (integerCurve_lower_cut p).mp (hcuts lowerBatch (by simp))
  have hup := (integerCurve_upper_cut p).mp (hcuts upperBatch (by simp))
  have hroot := integerCurve_root_bounds
  rcases integerCurve_cases p hb with h | h
  · rw [h] at hlo; linarith [hroot.1]
  · rw [h] at hup; linarith [hroot.2.2.2]

theorem integerCurve_actual_small_tolerance_trace :
    CPStep integerCurve (.esh (integerPoint (1/2))) (1/16) [] lowerBatch ∧
    CPStep integerCurve (.esh (integerPoint (1/2))) (1/16) [lowerBatch] upperBatch ∧
    CPStop integerCurve (1/16) [lowerBatch,upperBatch] .infeasible ∧
    ([lowerBatch,upperBatch] : List (CPBatch 0 1 1)).length = 2 := by
  refine ⟨⟨integerCurve_first_minimum,?_,integerCurve_batches_valid.1⟩,
    ⟨integerCurve_second_minimum,?_,integerCurve_batches_valid.2⟩,
    .empty integerCurve_two_cuts_empty,rfl⟩
  · intro h; have hh := h 0; norm_num [integerCurve,lowerBatch,integerPoint] at hh
  · intro h; have hh := h 0; norm_num [integerCurve,upperBatch,integerPoint] at hh

def zeroRowsModel : ModelData 1 0 0 2 := scalarModel 0 0 (fun j => Fin.elim0 j) 1

theorem zero_rows_every_tolerance_return (eps : ℝ) :
    IsCompact (cpBase zeroRowsModel) ∧
    CPStop zeroRowsModel eps [] (.point (scalarPoint 0 0)) := by
  refine ⟨scalar_base_compact _ _ _ _,?_⟩
  exact .point _ (scalar_zero_empty_master_minimum _ _ _ _ (by norm_num))
    (cp_zero_rows_pass _ _ _)

def emptyBaseModel : ModelData 1 0 0 2 :=
  {zeroRowsModel with rhs := fun row => if row=0 then -1 else 0}

theorem empty_base_literal : cpBase emptyBaseModel = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hlo := hp.1 (0 : Fin 2)
  have hup := hp.1 (1 : Fin 2)
  norm_num [emptyBaseModel,zeroRowsModel,scalarModel,LinearForm] at hlo hup
  linarith

theorem empty_base_every_tolerance_return (eps : ℝ) :
    IsCompact (cpBase emptyBaseModel) ∧ CPStop emptyBaseModel eps [] .infeasible := by
  refine ⟨by rw [empty_base_literal]; exact isCompact_empty,?_⟩
  exact cp_empty_base_stop _ _ _ empty_base_literal

def zeroRowModel : ModelData 1 0 1 2 := affineScalar 0 0 0 0
def zeroRowBatch (all : Bool) : CPBatch 1 0 1 :=
  ⟨scalarPoint 0 0,scalarPoint 0 0,if all then ∅ else {0}⟩

theorem zeroRow_cuts (b : CPBatch 1 0 1) (p : Point 1 0) : cpBatchCuts zeroRowModel b p := by
  intro j hj
  simp [zeroRowModel,affineScalar,scalarModel]

theorem zeroRow_master (H : List (CPBatch 1 0 1)) : cpMaster zeroRowModel H = cpBase zeroRowModel := by
  ext p
  simp only [cp_master_mem_iff]
  exact ⟨And.left,fun hp => ⟨hp,fun b _ => zeroRow_cuts b p⟩⟩

theorem zeroRow_minimum (H : List (CPBatch 1 0 1)) :
    IsMinimizer (cpMaster zeroRowModel H) zeroRowModel.objective (scalarPoint 0 0) := by
  rw [zeroRow_master]
  refine ⟨scalar_zero_base _ _ _ _,?_⟩
  intro p hp
  simp [zeroRowModel,affineScalar,scalar_objective]

theorem zeroRow_negative_steps (eps : ℝ) (heps : eps < 0) (k : ℕ) :
    CPStep zeroRowModel .ecpMost eps (history (fun _ => zeroRowBatch false) k) (zeroRowBatch false) ∧
    CPStep zeroRowModel .ecpAll eps (history (fun _ => zeroRowBatch true) k) (zeroRowBatch true) := by
  have hf : ¬ CPFeasibleWithin zeroRowModel eps (scalarPoint 0 0) := by
    intro h
    have hh := h 0
    norm_num [zeroRowModel,affineScalar,scalarModel] at hh
    linarith
  refine ⟨⟨zeroRow_minimum _,hf,?_⟩,⟨zeroRow_minimum _,hf,?_⟩⟩
  · refine ⟨rfl,by simp [zeroRowBatch],?_⟩
    intro j _ i; exact le_rfl
  · refine ⟨rfl,?_⟩
    intro j; simp [zeroRowBatch,zeroRowModel,affineScalar,scalarModel]

theorem zeroRow_no_strict_start_but_every_root :
    (¬ ∃ a : Point 1 0, ∀ j, zeroRowModel.g j a < 0) ∧
    ∀ a q : Point 1 0, ∀ t : ℝ, ∀ j,
      zeroRowModel.g j (AffineMap.lineMap a q t) = 0 := by
  constructor
  · rintro ⟨a,ha⟩
    have h := ha 0
    norm_num [zeroRowModel,affineScalar,scalarModel] at h
  · intro a q t j
    simp [zeroRowModel,affineScalar,scalarModel]

theorem zeroRow_control_hypotheses : IsCompact (cpBase zeroRowModel) ∧
    (∀ j, ConvexOn ℝ Set.univ (zeroRowModel.g j)) ∧
    (∀ j, ContDiff ℝ 1 (zeroRowModel.g j)) :=
  ⟨scalar_base_compact _ _ _ _,affineScalar_convex _ _ _ _,affineScalar_smooth _ _ _ _⟩

/-- Deliberately altered transition: every iteration discards all cuts before
the master solve. This relation is not CPContinue. -/
def ResetStep {n m l r : ℕ} (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (_H K : List (CPBatch n m l)) : Prop := ∃ b, CPStep d mode eps [] b ∧ K=[]

theorem deletion_repeat_control (eps : ℝ) (heps : eps < 1) :
    ResetStep (squareModel 0) .ecpMost eps [] [] ∧
    squareTrial 0 (fun _ => 0) 0 ∉
      cpMaster (squareModel 0) [squareBatch 0 (fun _ => 0) 0] ∧
    ¬ CPContinue (squareModel 0) .ecpMost eps [] [] := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨squareBatch 0 (fun _ => 0) 0,⟨?_,?_,square_batch_most _ _ _⟩,rfl⟩
    · exact square_exact_master_minimum 0 (fun _ => 0) (by intro k i; exact Fin.elim0 i) 0
    · intro h
      have hh := h 0
      norm_num [squareBatch,squareTrial,scalarPoint,squareModel,scalarModel,halfPower] at hh
      linarith
  · intro hp
    have hcut := ((cp_master_mem_iff _ _ _).mp hp).2 (squareBatch 0 (fun _ => 0) 0) (by simp)
    rw [square_batch_cuts] at hcut
    norm_num [squareTrial,scalarPoint,halfPower] at hcut
  · rintro ⟨b,hb,_⟩
    have := congrArg List.length hb
    simp at this

def diskECPBatch (x y : ℝ) : CPBatch 2 1 1 :=
  ⟨planePoint x y,planePoint x y,{0}⟩

theorem disk_ecp_cut_formula (x y : ℝ) (p : Point 2 1) :
    cpBatchCuts (diskModel 1 3 0 0) (diskECPBatch x y) p ↔
      x^2+y^2-1+2*x*(p.1 0-x)+2*y*(p.1 1-y) ≤ 0 := by
  simp only [cpBatchCuts,diskECPBatch,Finset.mem_singleton,forall_eq]
  rw [disk_fderiv]
  simp [diskModel,planeModel,planePoint,coord,smul_eq_mul]
  ring_nf
  rfl

theorem disk_three_base (x y : ℝ) (hx : -3 ≤ x ∧ x ≤ 3) (hy : -3 ≤ y ∧ y ≤ 3) :
    planePoint (m := 1) x y ∈ cpBase (diskModel 1 3 0 0) := by
  refine ⟨?_,0,?_,by funext i; simp [planePoint]⟩
  · change planePoint (m := 1) x y ∈ (planeModel 1 1 (-3) 3 _ 0 0).linearRegion
    rw [plane_linear_iff]; simpa [planePoint] using ⟨hx.1,hx.2,hy.1,hy.2⟩
  · intro i; norm_num [diskModel,planeModel]

theorem same_row_violation_increases :
    CPStep (diskModel 1 3 0 0) .ecpMost 0 [] (diskECPBatch 2 0) ∧
    CPStep (diskModel 1 3 0 0) .ecpMost 0 [diskECPBatch 2 0] (diskECPBatch 0 3) ∧
    (diskModel 1 3 0 0).g 0 (planePoint 2 0) = 3 ∧
    (diskModel 1 3 0 0).g 0 (planePoint 0 3) = 8 := by
  have hvalid (x y : ℝ) : CPBatchValid (diskModel 1 3 0 0) .ecpMost (diskECPBatch x y) := by
    refine ⟨rfl,by simp [diskECPBatch],?_⟩
    intro j _ i; exact le_rfl
  have hmin0 : IsMinimizer (cpMaster (diskModel 1 3 0 0) [])
      (diskModel 1 3 0 0).objective (planePoint 2 0) := by
    rw [cp_master_nil]
    refine ⟨disk_three_base _ _ (by norm_num) (by norm_num),?_⟩
    intro p hp; simp [diskModel,plane_objective]
  have hmin1 : IsMinimizer (cpMaster (diskModel 1 3 0 0) [diskECPBatch 2 0])
      (diskModel 1 3 0 0).objective (planePoint 0 3) := by
    constructor
    · rw [cp_master_mem_iff]
      refine ⟨disk_three_base _ _ (by norm_num) (by norm_num),?_⟩
      intro b hb
      have heq : b = diskECPBatch 2 0 := by simpa using hb
      subst b
      rw [disk_ecp_cut_formula]; norm_num [planePoint]
    · intro p hp; simp [diskModel,plane_objective]
  refine ⟨⟨hmin0,?_,hvalid _ _⟩,⟨hmin1,?_,hvalid _ _⟩,?_,?_⟩
  · intro h; have hh := h 0; norm_num [diskModel,planeModel,diskECPBatch,planePoint] at hh
  · intro h; have hh := h 0; norm_num [diskModel,planeModel,diskECPBatch,planePoint] at hh
  · norm_num [diskModel,planeModel,planePoint]
  · norm_num [diskModel,planeModel,planePoint]

def arbitraryModel : ModelData 2 0 2 4 :=
  planeModel 0 2 0 1 (fun j p => if j=0 then (p.1 0)^2 else p.1 1-1/2) (-1) (-2)
def arbitraryTrial (k : ℕ) : Point 2 0 := planePoint (halfPower k) 1
def arbitraryBatch (k : ℕ) : CPBatch 2 0 2 := ⟨arbitraryTrial k,arbitraryTrial k,{0}⟩

theorem arbitrary_convex : ∀ j, ConvexOn ℝ Set.univ (arbitraryModel.g j) := by
  intro j; refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 0-q.1 0))
  fin_cases j <;> simp [arbitraryModel,planeModel,smul_eq_mul] <;> nlinarith

theorem arbitrary_smooth : ∀ j, ContDiff ℝ 1 (arbitraryModel.g j) := by
  intro j; fin_cases j
  · exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 2)).comp contDiff_fst).pow 2)
  · exact ((contDiff_apply ℝ (fun _ => ℝ) (1 : Fin 2)).comp contDiff_fst).sub contDiff_const

theorem arbitrary_compact : IsCompact (cpBase arbitraryModel) := plane_base_compact _ _ _ _ _ _ _

theorem arbitrary_first_derivative (p : Point 2 0) :
    fderiv ℝ (arbitraryModel.g 0) p = (2*p.1 0) • coord 0 := by
  have h := (hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p (coord (m := 0) 0).hasFDerivAt
  have hh : HasFDerivAt (arbitraryModel.g 0) ((2*p.1 0) • coord 0) p := by
    convert h using 1 <;> norm_num [arbitraryModel,planeModel,coord,Function.comp_def]
  exact hh.fderiv

theorem arbitrary_cut (k : ℕ) (p : Point 2 0) :
    cpBatchCuts arbitraryModel (arbitraryBatch k) p ↔ p.1 0 ≤ halfPower k/2 := by
  simp only [cpBatchCuts,arbitraryBatch,Finset.mem_singleton,forall_eq]
  rw [arbitrary_first_derivative]
  simp only [arbitraryModel,planeModel,arbitraryTrial,planePoint,if_pos rfl,
    Matrix.cons_val_zero,ContinuousLinearMap.smul_apply,smul_eq_mul,coord_apply,
    Prod.fst_sub,Pi.sub_apply]
  simp only [ite_true]
  have h := halfPower_pos k
  constructor <;> intro hh <;> nlinarith

theorem arbitrary_master_minimum (k : ℕ) :
    IsMinimizer (cpMaster arbitraryModel (history arbitraryBatch k))
      arbitraryModel.objective (arbitraryTrial k) := by
  have hb : arbitraryTrial k ∈ cpBase arbitraryModel := by
    refine ⟨?_,0,?_,by funext i; exact Fin.elim0 i⟩
    · apply (plane_linear_iff _ _ _ _ _ _ _ _).mpr
      change 0 ≤ halfPower k ∧ halfPower k ≤ 1 ∧ (0:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 1
      exact ⟨(halfPower_pos k).le,halfPower_le_one k,by norm_num,le_rfl⟩
    · intro i; exact Fin.elim0 i
  constructor
  · rw [cp_master_mem_iff]
    refine ⟨hb,?_⟩
    intro b hmem
    obtain ⟨i,hik,rfl⟩ := (history_mem_iff _ _ _).mp hmem
    rw [arbitrary_cut]
    change halfPower k ≤ halfPower i/2
    rw [← halfPower_succ]
    exact halfPower_antitone (Nat.succ_le_of_lt hik)
  · intro p hp
    obtain ⟨hbp,hcuts⟩ := (cp_master_mem_iff _ _ _).mp hp
    have hbox := (plane_linear_iff _ _ _ _ _ _ _ _).mp hbp.1
    have hx : p.1 0 ≤ halfPower k := by
      cases k with
      | zero => exact hbox.2.1
      | succ k =>
        rw [halfPower_succ]
        exact (arbitrary_cut k p).mp
          (hcuts _ ((history_mem_iff _ _ _).mpr ⟨k,Nat.lt_succ_self k,rfl⟩))
    simp [arbitraryModel,plane_objective,arbitraryTrial,planePoint]
    linarith [hbox.2.2.2]

theorem arbitrary_positive_selection_fails_forever (k : ℕ) :
    IsMinimizer (cpMaster arbitraryModel (history arbitraryBatch k))
      arbitraryModel.objective (arbitraryTrial k) ∧
    (∀ j ∈ (arbitraryBatch k).rows, 0 < arbitraryModel.g j (arbitraryTrial k)) ∧
    ¬ CPFeasibleWithin arbitraryModel (1/4) (arbitraryTrial k) := by
  refine ⟨arbitrary_master_minimum k,?_,?_⟩
  · intro j hj
    have hj0 : j=0 := by simpa [arbitraryBatch] using hj
    subst j
    simpa [arbitraryModel,planeModel,arbitraryTrial,planePoint] using sq_pos_of_pos (halfPower_pos k)
  · intro h; have hh := h 1
    norm_num [arbitraryModel,planeModel,arbitraryTrial,planePoint] at hh

theorem arbitrary_policy_rejected_from_second (k : ℕ) :
    ¬ CPBatchValid arbitraryModel .ecpMost (arbitraryBatch (k+1)) ∧
    ¬ CPBatchValid arbitraryModel .ecpAll (arbitraryBatch (k+1)) := by
  have hq := halfPower_le_one k
  have hpos := halfPower_pos k
  constructor
  · intro h
    have hh := h.2.2 0 (by simp [arbitraryBatch]) 1
    simp [arbitraryModel,planeModel,arbitraryBatch,arbitraryTrial,planePoint,halfPower_succ] at hh
    nlinarith
  · intro h
    have hh := (h.2 1).mpr (by norm_num [arbitraryModel,planeModel,arbitraryBatch,arbitraryTrial,planePoint])
    norm_num [arbitraryBatch] at hh

def noncompactModel : ModelData 2 0 1 0 where
  g := fun _ p => (p.1 0)^2-p.1 1
  A := fun _ _ => 0
  B := fun _ _ => 0
  rhs := fun _ => 0
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0
def noncompactTrial (k : ℕ) : Point 2 0 := planePoint k ((k:ℝ)^2-1)
def noncompactBatch (k : ℕ) : CPBatch 2 0 1 := ⟨noncompactTrial k,noncompactTrial k,{0}⟩

theorem noncompact_base_univ : cpBase noncompactModel = Set.univ := by
  ext p; simp only [Set.mem_univ,iff_true]
  refine ⟨?_,0,?_,?_⟩
  · intro row; exact Fin.elim0 row
  · intro i; exact Fin.elim0 i
  · funext i; exact Fin.elim0 i

theorem noncompact_base_not_compact : ¬ IsCompact (cpBase noncompactModel) := by
  rw [noncompact_base_univ]
  intro h
  have hi := h.image (coord (n := 2) (m := 0) 0).continuous
  have heq : coord (n := 2) (m := 0) 0 '' Set.univ = Set.univ := by
    ext x; simp only [Set.mem_univ,iff_true]
    exact ⟨planePoint x 0,Set.mem_univ _,rfl⟩
  rw [heq] at hi
  obtain ⟨b,hb⟩ := hi.bddAbove
  have hbad := hb (Set.mem_univ (b+1))
  linarith

theorem noncompact_convex : ∀ j, ConvexOn ℝ Set.univ (noncompactModel.g j) := by
  intro j; refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 0-q.1 0))
  simp only [noncompactModel,Prod.fst_add,Prod.smul_fst,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith

theorem noncompact_smooth : ∀ j, ContDiff ℝ 1 (noncompactModel.g j) := by
  intro j
  exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 2)).comp contDiff_fst).pow 2).sub
    ((contDiff_apply ℝ (fun _ => ℝ) (1 : Fin 2)).comp contDiff_fst)

theorem noncompact_derivative (p : Point 2 0) (j : Fin 1) :
    fderiv ℝ (noncompactModel.g j) p = (2*p.1 0) • coord 0-coord 1 := by
  have h := ((hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p
    (coord (m := 0) 0).hasFDerivAt).sub (coord 1).hasFDerivAt
  have hh : HasFDerivAt (noncompactModel.g j) ((2*p.1 0) • coord 0-coord 1) p := by
    convert h using 1 <;> (try ext w) <;>
      norm_num [noncompactModel,coord,Function.comp_def,Pi.sub_apply]
  exact hh.fderiv

theorem noncompact_retained_cut {i k : ℕ} (hik : i < k) :
    cpBatchCuts noncompactModel (noncompactBatch i) (noncompactTrial k) := by
  intro j hj
  rw [noncompact_derivative]
  have hdiff : (i:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hik)
  simp [noncompactModel,noncompactBatch,noncompactTrial,planePoint,coord,smul_eq_mul]
  nlinarith [sq_nonneg ((k:ℝ)-(i:ℝ)-1)]

theorem noncompact_actual_step (k : ℕ) :
    CPStep noncompactModel .ecpMost (1/2) (history noncompactBatch k) (noncompactBatch k) := by
  refine ⟨⟨?_,?_⟩,?_,rfl,by simp [noncompactBatch],?_⟩
  · rw [cp_master_mem_iff]
    refine ⟨by rw [noncompact_base_univ]; trivial,?_⟩
    intro b hb
    obtain ⟨i,hik,rfl⟩ := (history_mem_iff _ _ _).mp hb
    exact noncompact_retained_cut hik
  · intro p hp; simp [ModelData.objective,noncompactModel,LinearForm]
  · intro h; have hh := h 0
    norm_num [noncompactModel,noncompactBatch,noncompactTrial,planePoint] at hh
  · intro j _ i; exact le_rfl

theorem noncompact_infinite_chain :
    ∀ k, CPContinue noncompactModel .ecpMost (1/2)
      (history noncompactBatch k) (history noncompactBatch (k+1)) ∧
      (history noncompactBatch k).length = k := by
  intro k
  exact ⟨⟨noncompactBatch k,history_succ _ k,noncompact_actual_step k⟩,history_length _ _⟩

def squareExecution (m : ℕ) (y : ℕ → IntVector m)
    (hy : ∀ k i, 0 ≤ y k i ∧ y k i ≤ 1) : CPExecution (squareModel m) .ecpMost 0 [] where
  history := history (squareBatch m y)
  batch := squareBatch m y
  initial := rfl
  append := history_succ _
  step k := (square_raw_step m y hy k).1

def diskExecution (m start : ℕ) : CPExecution (diskModel m 1 (-1) 0)
    (.esh (planePoint 0 0)) 0 (history (diskBatch m) start) where
  history k := history (diskBatch m) (start+k)
  batch k := diskBatch m (start+k)
  initial := by simp
  append k := by simpa [Nat.add_assoc] using history_succ (diskBatch m) (start+k)
  step k := disk_raw_step m (start+k)

theorem disk_no_integer_infinite_control :
    Nonempty (CPExecution (diskModel 0 1 (-1) 0) (.esh (planePoint 0 0)) 0 []) :=
  ⟨diskExecution 0 0⟩

theorem disk_fixed_integer_infinite_control :
    Nonempty (CPExecution (diskModel 1 1 (-1) 0) (.esh (planePoint 0 0)) 0 []) :=
  ⟨diskExecution 1 0⟩

/-- Literal relaxed integer box for the finite LP prefix. In this particular
model all such coordinates are fixed to zero, so integrality changes nothing. -/
def diskLPMaster (m k : ℕ) : Set (Point 2 m) :=
  {p | p ∈ (diskModel m 1 (-1) 0).linearRegion ∧
    (∀ i, (0:ℝ) ≤ p.2 i ∧ p.2 i ≤ 0) ∧
    ∀ b ∈ history (diskBatch m) k, cpBatchCuts (diskModel m 1 (-1) 0) b p}

theorem disk_lp_master_eq (m k : ℕ) :
    diskLPMaster m k = cpMaster (diskModel m 1 (-1) 0) (history (diskBatch m) k) := by
  ext p
  rw [cp_master_mem_iff]
  constructor
  · rintro ⟨hL,hY,hcuts⟩
    refine ⟨⟨hL,0,?_,?_⟩,hcuts⟩
    · intro i; norm_num [diskModel,planeModel]
    · funext i
      have h := le_antisymm (hY i).2 (hY i).1
      simpa using h
  · rintro ⟨⟨hL,y,hy,heq⟩,hcuts⟩
    refine ⟨hL,?_,hcuts⟩
    intro i
    rw [heq]
    exact hy i

/-- Post-test LP ordering: K exact LP choices each fail epsLP=0, generate the
root cut, and retain it; the cap then hands H_K to the MILP execution. -/
theorem disk_finite_lp_prefix_composes (m K : ℕ) :
    (∀ k < K, IsMinimizer (diskLPMaster m k) (diskModel m 1 (-1) 0).objective
      (diskTrial m k) ∧ ¬ CPFeasibleWithin (diskModel m 1 (-1) 0) 0 (diskTrial m k) ∧
      CPBatchValid (diskModel m 1 (-1) 0) (.esh (planePoint 0 0)) (diskBatch m k)) ∧
    (history (diskBatch m) K).length = K ∧
    Nonempty (CPExecution (diskModel m 1 (-1) 0) (.esh (planePoint 0 0)) 0
      (history (diskBatch m) K)) := by
  refine ⟨?_,history_length _ _,⟨diskExecution m K⟩⟩
  intro k hk
  rw [disk_lp_master_eq]
  exact ⟨disk_exact_master_minimum m k,disk_trial_not_feasible m k,disk_batch_valid m k⟩

def parityIntegers (k : ℕ) : IntVector 1 := fun _ => ((k%2 : ℕ) : ℤ)

theorem parityIntegers_bounded : ∀ k i, 0 ≤ parityIntegers k i ∧ parityIntegers k i ≤ 1 := by
  intro k i
  have h : k%2 ≤ 1 := by omega
  change (0:ℤ) ≤ ((k%2 : ℕ):ℤ) ∧ ((k%2 : ℕ):ℤ) ≤ 1
  exact ⟨by positivity,by exact_mod_cast h⟩

def alternatingExecution : CPExecution (squareModel 1) .ecpMost 0 [] :=
  squareExecution 1 parityIntegers parityIntegers_bounded

theorem alternating_even_limit :
    Filter.Tendsto (fun k => alternatingExecution.trial (2*k)) Filter.atTop (𝓝 (xy 0 0)) := by
  have hindex : StrictMono (fun k : ℕ => 2*k) := by intro i k hik; dsimp only; omega
  have hp : Filter.Tendsto halfPower Filter.atTop (𝓝 (0:ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply (Prod.tendsto_iff _ _).mpr
  constructor
  · apply tendsto_pi_nhds.mpr
    intro i
    simpa [alternatingExecution,squareExecution,CPExecution.trial,squareBatch,
      squareTrial,scalarPoint,xy,Function.comp_def] using hp.comp hindex.tendsto_atTop
  · apply tendsto_pi_nhds.mpr
    intro i
    simp [alternatingExecution,squareExecution,CPExecution.trial,squareBatch,
      squareTrial,scalarPoint,parityIntegers,xy,Nat.mul_mod]

theorem alternating_odd_limit :
    Filter.Tendsto (fun k => alternatingExecution.trial (2*k+1)) Filter.atTop (𝓝 (xy 0 1)) := by
  have hindex : StrictMono (fun k : ℕ => 2*k+1) := by intro i k hik; dsimp only; omega
  have hp : Filter.Tendsto halfPower Filter.atTop (𝓝 (0:ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply (Prod.tendsto_iff _ _).mpr
  constructor
  · apply tendsto_pi_nhds.mpr
    intro i
    simpa [alternatingExecution,squareExecution,CPExecution.trial,squareBatch,
      squareTrial,scalarPoint,xy,Function.comp_def] using hp.comp hindex.tendsto_atTop
  · apply tendsto_pi_nhds.mpr
    intro i
    simp [alternatingExecution,squareExecution,CPExecution.trial,squareBatch,
      squareTrial,scalarPoint,parityIntegers,xy,Nat.mul_mod,Nat.add_mod]

theorem alternating_no_full_point_limit :
    ¬ ∃ p, Filter.Tendsto alternatingExecution.trial Filter.atTop (𝓝 p) := by
  rintro ⟨p,hp⟩
  have heven : StrictMono (fun k : ℕ => 2*k) := by intro i k hik; dsimp only; omega
  have hodd : StrictMono (fun k : ℕ => 2*k+1) := by intro i k hik; dsimp only; omega
  have hp0 : p = xy 0 0 := tendsto_nhds_unique (hp.comp heven.tendsto_atTop) alternating_even_limit
  have hp1 : p = xy 0 1 := tendsto_nhds_unique (hp.comp hodd.tendsto_atTop) alternating_odd_limit
  have hh := congrArg (fun q : Point 1 1 => q.2 0) (hp0.symm.trans hp1)
  norm_num [xy] at hh

theorem alternating_two_optimal_cluster_points :
    MapClusterPt (xy 0 0) Filter.atTop alternatingExecution.trial ∧
    MapClusterPt (xy 0 1) Filter.atTop alternatingExecution.trial ∧
    IsMinimizer ((squareModel 1).feasibleOn Set.univ) (squareModel 1).objective (xy 0 0) ∧
    IsMinimizer ((squareModel 1).feasibleOn Set.univ) (squareModel 1).objective (xy 0 1) := by
  have heven : StrictMono (fun k : ℕ => 2*k) := by intro i k hik; dsimp only; omega
  have hodd : StrictMono (fun k : ℕ => 2*k+1) := by intro i k hik; dsimp only; omega
  have hc0 : MapClusterPt (xy 0 0) Filter.atTop alternatingExecution.trial :=
    alternating_even_limit.mapClusterPt.of_comp heven.tendsto_atTop
  have hc1 : MapClusterPt (xy 0 1) Filter.atTop alternatingExecution.trial :=
    alternating_odd_limit.mapClusterPt.of_comp hodd.tendsto_atTop
  have hlim := source_cp_zero_execution_limiting (squareModel 1) .ecpMost
    (square_base_compact 1) (square_convex 1) (square_smooth 1) trivial alternatingExecution
  exact ⟨hc0,hc1,hlim.cluster_minimizer _ hc0,hlim.cluster_minimizer _ hc1⟩

theorem alternating_each_integer_fiber_infinite :
    {k | (alternatingExecution.trial k).2 0 = 0}.Infinite ∧
    {k | (alternatingExecution.trial k).2 0 = 1}.Infinite := by
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro k
    refine ⟨2*(k+1),?_,by omega⟩
    simp [alternatingExecution,squareExecution,CPExecution.trial,squareBatch,
      squareTrial,scalarPoint,parityIntegers,Nat.mul_mod]
  · apply Set.infinite_of_forall_exists_gt
    intro k
    refine ⟨2*(k+1)+1,?_,by omega⟩
    change (((2*(k+1)+1)%2 : ℕ) : ℝ) = 1
    norm_num [Nat.mul_mod,Nat.add_mod]

theorem disk_original_minimum (m : ℕ) :
    IsMinimizer ((diskModel m 1 (-1) 0).feasibleOn Set.univ)
      (diskModel m 1 (-1) 0).objective (planePoint 1 0) := by
  constructor
  · rw [source_feasible_iff]
    refine ⟨Set.mem_univ _,?_,?_,0,?_,by funext i; simp [planePoint]⟩
    · intro j; norm_num [diskModel,planeModel,planePoint]
    · exact (plane_linear_iff _ _ _ _ _ _ _ _).mpr (by norm_num [planePoint])
    · intro i; norm_num [diskModel,planeModel]
  · intro p hp
    have hL := ((source_feasible_iff _ _ _).mp hp).2.2.1
    have hx := ((plane_linear_iff _ _ _ _ _ _ _ _).mp hL).2.1
    simpa [diskModel,plane_objective,planePoint] using neg_le_neg hx

theorem disk_strict_point_is_initialization_minimum (m : ℕ) :
    IsMinimizer (diskModel m 1 (-1) 0).linearRegion
      (fun p => (diskModel m 1 (-1) 0).g 0 p) (planePoint 0 0) := by
  refine ⟨(disk_strict_start m).1,?_⟩
  intro p hp
  simp [diskModel,planeModel,planePoint]
  nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.1 1)]

theorem history_trace {n m l r : ℕ} (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (b : ℕ → CPBatch n m l) (k : ℕ)
    (hstep : ∀ i < k, CPStep d mode eps (history b i) (b i)) :
    CPTrace d mode eps [] (history b k) := by
  induction k with
  | zero => exact cp_trace_nil _ _ _ _
  | succ k ih =>
    rw [history_succ]
    apply cp_trace_append d mode eps (ih (fun i hi => hstep i (by omega)))
    simpa using hstep k (Nat.lt_succ_self k)

theorem square_positive_tolerance_actual_return (m : ℕ) (y : ℕ → IntVector m)
    (hy : ∀ k i, 0 ≤ y k i ∧ y k i ≤ 1) (eps : ℝ) (heps : 0 < eps) :
    ∃ k, CPTrace (squareModel m) .ecpMost eps [] (history (squareBatch m y) k) ∧
      CPStop (squareModel m) eps (history (squareBatch m y) k) (.point (squareTrial m y k)) ∧
      (history (squareBatch m y) k).length = k := by
  classical
  have hp : Filter.Tendsto halfPower Filter.atTop (𝓝 (0:ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs : Filter.Tendsto (fun k => (halfPower k)^2) Filter.atTop (𝓝 (0:ℝ)) := by
    simpa using hp.pow 2
  have hevent := (tendsto_order.mp hs).2 eps heps
  obtain ⟨k,hk⟩ := hevent.exists
  have hex : ∃ k, CPFeasibleWithin (squareModel m) eps (squareTrial m y k) :=
    ⟨k,fun _ => hk.le⟩
  let K := Nat.find hex
  refine ⟨K,?_,.point _ (square_exact_master_minimum m y hy K) (Nat.find_spec hex),history_length _ _⟩
  apply history_trace
  intro i hi
  exact ⟨square_exact_master_minimum m y hy i,Nat.find_min hex hi,square_batch_most _ _ _⟩

def zeroRowMostExecution (eps : ℝ) (heps : eps < 0) : CPExecution zeroRowModel .ecpMost eps [] where
  history := history (fun _ => zeroRowBatch false)
  batch := fun _ => zeroRowBatch false
  initial := rfl
  append := history_succ _
  step k := (zeroRow_negative_steps eps heps k).1

def zeroRowAllExecution (eps : ℝ) (heps : eps < 0) : CPExecution zeroRowModel .ecpAll eps [] where
  history := history (fun _ => zeroRowBatch true)
  batch := fun _ => zeroRowBatch true
  initial := rfl
  append := history_succ _
  step k := (zeroRow_negative_steps eps heps k).2

def noncompactExecution : CPExecution noncompactModel .ecpMost (1/2) [] where
  history := history noncompactBatch
  batch := noncompactBatch
  initial := rfl
  append := history_succ _
  step := noncompact_actual_step

/-- Deliberately weakened ECP selection, retaining a nonempty set of positive
rows rather than the source maximum/all policies. -/
def ArbitraryViolatedStep {n m l r : ℕ} (d : ModelData n m l r) (eps : ℝ)
    (H : List (CPBatch n m l)) (b : CPBatch n m l) : Prop :=
  IsMinimizer (cpMaster d H) d.objective b.trial ∧
  ¬ CPFeasibleWithin d eps b.trial ∧ b.origin=b.trial ∧ b.rows.Nonempty ∧
  ∀ j ∈ b.rows, 0 < d.g j b.trial

theorem arbitrary_actual_altered_chain : ∀ k,
    ArbitraryViolatedStep arbitraryModel (1/4) (history arbitraryBatch k) (arbitraryBatch k) ∧
    history arbitraryBatch (k+1) = history arbitraryBatch k ++ [arbitraryBatch k] ∧
    (history arbitraryBatch k).length = k := by
  intro k
  obtain ⟨hmin,hpos,hfail⟩ := arbitrary_positive_selection_fails_forever k
  exact ⟨⟨hmin,hfail,rfl,by simp [arbitraryBatch],hpos⟩,history_succ _ _,history_length _ _⟩

theorem tolerance_gap_esh_strict_start (M : ℝ) :
    CPInterior (affineScalar 0 (-1) (1/8) M) (.esh (scalarPoint 1 0)) := by
  constructor
  · exact (scalar_linear_iff _ _ _ _ _).mpr (by norm_num [scalarPoint])
  · intro j; norm_num [affineScalar,scalarModel,scalarPoint]

/-- Explicit section 2.2 ordering: the exact LP point is tested for original
feasibility and ends preprocessing without a root/cut; the empty history then
enters the MILP weak guard. This is a returned-point strictness control. The
NLP and LP points already have negative residuals, so it does not contradict
the literal reading 'some point found in any phase has residual < epsilon'. -/
theorem equality_section22_feasible_lp_break_then_milp :
    IsMinimizer equalityLPBase (fun p => equalityModel.g 0 p) (xy 0 1) ∧
    CPInterior equalityModel (.esh (xy 0 1)) ∧
    IsMinimizer equalityLPBase equalityModel.objective (xy 1 (1/2)) ∧
    CPFeasibleWithin equalityModel 0 (xy 1 (1/2)) ∧
    CPStop equalityModel (1/2) [] (.point (xy 1 0)) ∧
    ¬ equalityModel.g 0 (xy 1 0) < 1/2 := by
  exact ⟨equality_initialization_minimum.1,equality_initialization_minimum.2,
    equality_lp_minimum,by intro j; norm_num [equalityModel,xy],
    equality_full_model_control.2.2.1,by norm_num [equalityModel,xy]⟩

def integerCurveECPLower : CPBatch 0 1 1 := ⟨integerPoint 0,integerPoint 0,{0}⟩
def integerCurveECPUpper : CPBatch 0 1 1 := ⟨integerPoint 1,integerPoint 1,{0}⟩

theorem integerCurve_ecp_cuts (p : Point 0 1) :
    (cpBatchCuts integerCurve integerCurveECPLower p ↔ (1:ℝ)/8 ≤ p.2 0) ∧
    (cpBatchCuts integerCurve integerCurveECPUpper p ↔ p.2 0 ≤ (7:ℝ)/8) := by
  constructor
  · simp only [cpBatchCuts,integerCurveECPLower,Finset.mem_singleton,forall_eq]
    rw [(integerCurve_derivative _ _).fderiv]
    change (0-1/2)^2-1/8+(2*(0-1/2))*(p.2 0-0) ≤ 0 ↔ (1:ℝ)/8 ≤ p.2 0
    constructor <;> intro h <;> linarith
  · simp only [cpBatchCuts,integerCurveECPUpper,Finset.mem_singleton,forall_eq]
    rw [(integerCurve_derivative _ _).fderiv]
    change (1-1/2)^2-1/8+(2*(1-1/2))*(p.2 0-1) ≤ 0 ↔ p.2 0 ≤ (7:ℝ)/8
    constructor <;> intro h <;> linarith

theorem integerCurve_ecp_second_minimum :
    IsMinimizer (cpMaster integerCurve [integerCurveECPLower]) integerCurve.objective (integerPoint 1) := by
  constructor
  · rw [cp_master_mem_iff]
    refine ⟨by simpa using integerCurve_endpoint_base 1 (by norm_num),?_⟩
    intro b hb
    have heq : b = integerCurveECPLower := by simpa using hb
    subst b
    rw [(integerCurve_ecp_cuts _).1]; norm_num [integerPoint]
  · intro p hp
    obtain ⟨hb,hcuts⟩ := (cp_master_mem_iff _ _ _).mp hp
    have hcut := (integerCurve_ecp_cuts p).1.mp (hcuts integerCurveECPLower (by simp))
    rcases integerCurve_cases p hb with h | h
    · rw [h] at hcut; norm_num at hcut
    · simp [integerCurve_objective,integerPoint,h]

theorem integerCurve_ecp_two_cuts_empty :
    cpMaster integerCurve [integerCurveECPLower,integerCurveECPUpper] = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hb,hcuts⟩ := (cp_master_mem_iff _ _ _).mp hp
  have hlo := (integerCurve_ecp_cuts p).1.mp (hcuts integerCurveECPLower (by simp))
  have hup := (integerCurve_ecp_cuts p).2.mp (hcuts integerCurveECPUpper (by simp))
  rcases integerCurve_cases p hb with h | h
  · rw [h] at hlo; norm_num at hlo
  · rw [h] at hup; norm_num at hup

/-- The ECP tangent constants differ from the ESH radical root constants. -/
theorem integerCurve_ecp_actual_small_tolerance_trace :
    CPStep integerCurve .ecpMost (1/16) [] integerCurveECPLower ∧
    CPStep integerCurve .ecpMost (1/16) [integerCurveECPLower] integerCurveECPUpper ∧
    CPStop integerCurve (1/16) [integerCurveECPLower,integerCurveECPUpper] .infeasible ∧
    ([integerCurveECPLower,integerCurveECPUpper] : List (CPBatch 0 1 1)).length=2 := by
  refine ⟨⟨integerCurve_first_minimum,?_,rfl,by simp [integerCurveECPLower],?_⟩,
    ⟨integerCurve_ecp_second_minimum,?_,rfl,by simp [integerCurveECPUpper],?_⟩,
    .empty integerCurve_ecp_two_cuts_empty,rfl⟩
  · intro h; have hh := h 0; norm_num [integerCurve,integerCurveECPLower,integerPoint] at hh
  · intro j hj i; exact le_rfl
  · intro h; have hh := h 0; norm_num [integerCurve,integerCurveECPUpper,integerPoint] at hh
  · intro j hj i; exact le_rfl

theorem integerCurve_esh_trace_record :
    CPTrace integerCurve (.esh (integerPoint (1/2))) (1/16) [] [lowerBatch,upperBatch] := by
  have h0 := integerCurve_actual_small_tolerance_trace.1
  have h1 := integerCurve_actual_small_tolerance_trace.2.1
  have hfirst : CPTrace integerCurve (.esh (integerPoint (1/2))) (1/16) [] [lowerBatch] := by
    simpa using cp_trace_append integerCurve (.esh (integerPoint (1/2))) (1/16)
      (cp_trace_nil integerCurve (.esh (integerPoint (1/2))) (1/16) []) h0
  simpa using cp_trace_append integerCurve (.esh (integerPoint (1/2))) (1/16) hfirst h1

theorem integerCurve_ecp_trace_record :
    CPTrace integerCurve .ecpMost (1/16) [] [integerCurveECPLower,integerCurveECPUpper] := by
  have h0 := integerCurve_ecp_actual_small_tolerance_trace.1
  have h1 := integerCurve_ecp_actual_small_tolerance_trace.2.1
  have hfirst : CPTrace integerCurve .ecpMost (1/16) [] [integerCurveECPLower] := by
    simpa using cp_trace_append integerCurve .ecpMost (1/16)
      (cp_trace_nil integerCurve .ecpMost (1/16) []) h0
  simpa using cp_trace_append integerCurve .ecpMost (1/16) hfirst h1

theorem noncompact_original_minimum :
    IsMinimizer (noncompactModel.feasibleOn Set.univ) noncompactModel.objective (planePoint 0 0) := by
  constructor
  · rw [source_feasible_iff]
    refine ⟨Set.mem_univ _,?_,?_,0,?_,by funext i; exact Fin.elim0 i⟩
    · intro j; norm_num [noncompactModel,planePoint]
    · intro row; exact Fin.elim0 row
    · intro i; exact Fin.elim0 i
  · intro p hp; simp [ModelData.objective,noncompactModel,LinearForm]

end Chapter02CPExamples

#print axioms Chapter02CPExamples.coord_apply
#print axioms Chapter02CPExamples.base_closed
#print axioms Chapter02CPExamples.scalar_linear_iff
#print axioms Chapter02CPExamples.scalar_objective
#print axioms Chapter02CPExamples.scalar_base_compact
#print axioms Chapter02CPExamples.square_convex
#print axioms Chapter02CPExamples.square_smooth
#print axioms Chapter02CPExamples.square_derivative
#print axioms Chapter02CPExamples.square_fderiv
#print axioms Chapter02CPExamples.square_base_compact
#print axioms Chapter02CPExamples.square_no_strict_start
#print axioms Chapter02CPExamples.halfPower_pos
#print axioms Chapter02CPExamples.halfPower_le_one
#print axioms Chapter02CPExamples.halfPower_succ
#print axioms Chapter02CPExamples.halfPower_antitone
#print axioms Chapter02CPExamples.plane_linear_iff
#print axioms Chapter02CPExamples.plane_objective
#print axioms Chapter02CPExamples.plane_base_compact
#print axioms Chapter02CPExamples.disk_convex
#print axioms Chapter02CPExamples.disk_smooth
#print axioms Chapter02CPExamples.disk_derivative
#print axioms Chapter02CPExamples.disk_fderiv
#print axioms Chapter02CPExamples.disk_base_compact
#print axioms Chapter02CPExamples.disk_strict_start
#print axioms Chapter02CPExamples.history_mem_iff
#print axioms Chapter02CPExamples.history_succ
#print axioms Chapter02CPExamples.history_length
#print axioms Chapter02CPExamples.square_batch_cuts
#print axioms Chapter02CPExamples.square_trial_base
#print axioms Chapter02CPExamples.square_trial_master
#print axioms Chapter02CPExamples.square_master_bound
#print axioms Chapter02CPExamples.square_exact_master_minimum
#print axioms Chapter02CPExamples.square_batch_most
#print axioms Chapter02CPExamples.square_batch_all
#print axioms Chapter02CPExamples.square_trial_not_feasible
#print axioms Chapter02CPExamples.square_raw_step
#print axioms Chapter02CPExamples.square_actual_infinite_chain
#print axioms Chapter02CPExamples.square_zero_original_minimum
#print axioms Chapter02CPExamples.quarterPower_pos
#print axioms Chapter02CPExamples.quarterPower_le_one
#print axioms Chapter02CPExamples.quarterPower_succ
#print axioms Chapter02CPExamples.quarterPower_antitone
#print axioms Chapter02CPExamples.diskScale_sq
#print axioms Chapter02CPExamples.diskScale_gt_one
#print axioms Chapter02CPExamples.disk_retained_inequality
#print axioms Chapter02CPExamples.disk_root_zero
#print axioms Chapter02CPExamples.disk_root_line
#print axioms Chapter02CPExamples.disk_batch_valid
#print axioms Chapter02CPExamples.disk_batch_cuts
#print axioms Chapter02CPExamples.disk_trial_base
#print axioms Chapter02CPExamples.disk_trial_master
#print axioms Chapter02CPExamples.disk_exact_master_minimum
#print axioms Chapter02CPExamples.disk_trial_not_feasible
#print axioms Chapter02CPExamples.disk_raw_step
#print axioms Chapter02CPExamples.disk_arbitrary_prefix_chain
#print axioms Chapter02CPExamples.affineScalar_convex
#print axioms Chapter02CPExamples.affineScalar_smooth
#print axioms Chapter02CPExamples.scalar_zero_base
#print axioms Chapter02CPExamples.scalar_zero_empty_master_minimum
#print axioms Chapter02CPExamples.tolerance_return_infeasible_gap
#print axioms Chapter02CPExamples.tolerance_gap_arbitrarily_large
#print axioms Chapter02CPExamples.ecp_empty_original_tolerance_return
#print axioms Chapter02CPExamples.equality_linear
#print axioms Chapter02CPExamples.equality_objective
#print axioms Chapter02CPExamples.equality_convex
#print axioms Chapter02CPExamples.equality_smooth
#print axioms Chapter02CPExamples.equality_base_compact
#print axioms Chapter02CPExamples.equality_lp_minimum
#print axioms Chapter02CPExamples.equality_initialization_minimum
#print axioms Chapter02CPExamples.equality_integer_cases
#print axioms Chapter02CPExamples.equality_milp_minimum
#print axioms Chapter02CPExamples.equality_original_minimum
#print axioms Chapter02CPExamples.equality_full_model_control
#print axioms Chapter02CPExamples.integerCurve_objective
#print axioms Chapter02CPExamples.integerCurve_cases
#print axioms Chapter02CPExamples.integerCurve_endpoint_base
#print axioms Chapter02CPExamples.integerCurve_compact
#print axioms Chapter02CPExamples.integerCurve_convex
#print axioms Chapter02CPExamples.integerCurve_smooth
#print axioms Chapter02CPExamples.integerCurve_derivative
#print axioms Chapter02CPExamples.integerCurve_strict_start
#print axioms Chapter02CPExamples.integerCurve_original_empty
#print axioms Chapter02CPExamples.integerCurve_first_minimum
#print axioms Chapter02CPExamples.esh_empty_original_tolerance_return
#print axioms Chapter02CPExamples.sqrt_two_bounds
#print axioms Chapter02CPExamples.integerCurve_root_bounds
#print axioms Chapter02CPExamples.integerCurve_roots
#print axioms Chapter02CPExamples.integerCurve_root_line
#print axioms Chapter02CPExamples.integerCurve_batches_valid
#print axioms Chapter02CPExamples.integerCurve_lower_cut
#print axioms Chapter02CPExamples.integerCurve_upper_cut
#print axioms Chapter02CPExamples.integerCurve_second_minimum
#print axioms Chapter02CPExamples.integerCurve_two_cuts_empty
#print axioms Chapter02CPExamples.integerCurve_actual_small_tolerance_trace
#print axioms Chapter02CPExamples.zero_rows_every_tolerance_return
#print axioms Chapter02CPExamples.empty_base_literal
#print axioms Chapter02CPExamples.empty_base_every_tolerance_return
#print axioms Chapter02CPExamples.zeroRow_cuts
#print axioms Chapter02CPExamples.zeroRow_master
#print axioms Chapter02CPExamples.zeroRow_minimum
#print axioms Chapter02CPExamples.zeroRow_negative_steps
#print axioms Chapter02CPExamples.zeroRow_no_strict_start_but_every_root
#print axioms Chapter02CPExamples.zeroRow_control_hypotheses
#print axioms Chapter02CPExamples.deletion_repeat_control
#print axioms Chapter02CPExamples.disk_ecp_cut_formula
#print axioms Chapter02CPExamples.disk_three_base
#print axioms Chapter02CPExamples.same_row_violation_increases
#print axioms Chapter02CPExamples.arbitrary_convex
#print axioms Chapter02CPExamples.arbitrary_smooth
#print axioms Chapter02CPExamples.arbitrary_compact
#print axioms Chapter02CPExamples.arbitrary_first_derivative
#print axioms Chapter02CPExamples.arbitrary_cut
#print axioms Chapter02CPExamples.arbitrary_master_minimum
#print axioms Chapter02CPExamples.arbitrary_positive_selection_fails_forever
#print axioms Chapter02CPExamples.arbitrary_policy_rejected_from_second
#print axioms Chapter02CPExamples.noncompact_base_univ
#print axioms Chapter02CPExamples.noncompact_base_not_compact
#print axioms Chapter02CPExamples.noncompact_convex
#print axioms Chapter02CPExamples.noncompact_smooth
#print axioms Chapter02CPExamples.noncompact_derivative
#print axioms Chapter02CPExamples.noncompact_retained_cut
#print axioms Chapter02CPExamples.noncompact_actual_step
#print axioms Chapter02CPExamples.noncompact_infinite_chain
#print axioms Chapter02CPExamples.disk_no_integer_infinite_control
#print axioms Chapter02CPExamples.disk_fixed_integer_infinite_control
#print axioms Chapter02CPExamples.disk_lp_master_eq
#print axioms Chapter02CPExamples.disk_finite_lp_prefix_composes
#print axioms Chapter02CPExamples.parityIntegers_bounded
#print axioms Chapter02CPExamples.alternating_even_limit
#print axioms Chapter02CPExamples.alternating_odd_limit
#print axioms Chapter02CPExamples.alternating_no_full_point_limit
#print axioms Chapter02CPExamples.alternating_two_optimal_cluster_points
#print axioms Chapter02CPExamples.alternating_each_integer_fiber_infinite
#print axioms Chapter02CPExamples.disk_original_minimum
#print axioms Chapter02CPExamples.disk_strict_point_is_initialization_minimum
#print axioms Chapter02CPExamples.history_trace
#print axioms Chapter02CPExamples.square_positive_tolerance_actual_return
#print axioms Chapter02CPExamples.arbitrary_actual_altered_chain
#print axioms Chapter02CPExamples.tolerance_gap_esh_strict_start
#print axioms Chapter02CPExamples.equality_section22_feasible_lp_break_then_milp
#print axioms Chapter02CPExamples.integerCurve_ecp_cuts
#print axioms Chapter02CPExamples.integerCurve_ecp_second_minimum
#print axioms Chapter02CPExamples.integerCurve_ecp_two_cuts_empty
#print axioms Chapter02CPExamples.integerCurve_ecp_actual_small_tolerance_trace
#print axioms Chapter02CPExamples.integerCurve_esh_trace_record
#print axioms Chapter02CPExamples.integerCurve_ecp_trace_record
#print axioms Chapter02CPExamples.noncompact_original_minimum
#print axioms Chapter02CPExamples.squareExecution
#print axioms Chapter02CPExamples.diskExecution
#print axioms Chapter02CPExamples.alternatingExecution
#print axioms Chapter02CPExamples.zeroRowMostExecution
#print axioms Chapter02CPExamples.zeroRowAllExecution
#print axioms Chapter02CPExamples.noncompactExecution
