module

public import Chapter02STSourceDriver
public import Chapter02STCQExamples
public import Chapter02BBAdapterExamples
public import Mathlib.Tactic

@[expose] public section

/-! Original-coordinate source-process controls. F1a uses the actual initialized
cutoff process and cumulative callback history. Its full-space CQ is valid,
while the explicitly required feasible-fiber CQ fails. -/
noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02STSourceExamples

def f1aI : Finset (Fin 2) := {1}
def f1aY : {i : Fin 2 // i ∈ f1aI} := ⟨1,by simp [f1aI]⟩
def point (x y : ℝ) : RealVector 2 := ![x,y]
def coord (i : Fin 2) : RealVector 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i

def f1aData (delta : ℝ) : BBPolyData 2 1 4 where
  coefficient := ![![-1,0],![1,0],![0,-1],![0,1]]
  rhs := ![2,2,0,1]
  c := fun z _ => (z 0)^2-z 1
  f := fun z => -z 0+delta*z 1

theorem f1a_polyhedron (delta : ℝ) (z : RealVector 2) :
    z ∈ (f1aData delta).polyhedron ↔
      (-2 ≤ z 0 ∧ z 0 ≤ 2) ∧ (0 ≤ z 1 ∧ z 1 ≤ 1) := by
  simp [BBPolyData.polyhedron,f1aData,Fin.forall_fin_succ,Fin.sum_univ_succ,and_assoc]
  intros
  constructor <;> intro h <;> linarith

theorem f1a_bounded (delta : ℝ) : Bornology.IsBounded (f1aData delta).polyhedron := by
  apply (isCompact_Icc : IsCompact (Set.Icc (point (-2) 0) (point 2 1))).isBounded.subset
  intro z hz
  obtain ⟨hx,hy⟩ := (f1a_polyhedron delta z).mp hz
  constructor <;> intro i <;> fin_cases i <;> simp_all [point]

theorem f1a_enclosing (delta : ℝ) : (f1aData delta).Encloses 2 := by
  refine ⟨by norm_num,?_⟩
  intro z hz i
  obtain ⟨hx,hy⟩ := (f1a_polyhedron delta z).mp hz
  apply abs_le.mpr
  fin_cases i <;> dsimp <;> constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem f1a_C2 (delta : ℝ) :
    ContDiff ℝ 2 (f1aData delta).f ∧ ContDiff ℝ 2 (f1aData delta).c := by
  constructor <;> dsimp [f1aData] <;> fun_prop

theorem f1a_convex (delta : ℝ) :
    ConvexOn ℝ Set.univ (f1aData delta).f ∧
      ∀ j, ConvexOn ℝ Set.univ (fun z => (f1aData delta).c z j) := by
  constructor
  · refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [f1aData]
    ring_nf
    exact le_rfl
  · intro j
    have hs : ConvexOn ℝ Set.univ (fun t : ℝ => t^2) := (by decide : Even 2).convexOn_pow
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hs.2 (Set.mem_univ (x 0)) (Set.mem_univ (y 0)) ha hb hab
    dsimp [f1aData] at hh ⊢
    nlinarith

theorem f1a_objective_derivative (delta : ℝ) (a : RealVector 2) :
    HasFDerivAt (f1aData delta).f (-coord 0+delta • coord 1) a := by
  exact ((coord 0).hasFDerivAt.neg).add ((coord 1).hasFDerivAt.const_smul delta)

theorem f1a_row_derivative (delta : ℝ) (a : RealVector 2) (j : Fin 1) :
    HasFDerivAt (fun z => (f1aData delta).c z j) ((2*a 0) • coord 0-coord 1) a := by
  have hh := ((hasDerivAt_pow 2 (a 0)).comp_hasFDerivAt a (coord 0).hasFDerivAt).fun_sub
    (coord 1).hasFDerivAt
  simpa [coord,f1aData,Function.comp_def] using hh

theorem f1a_objective_tangent (delta : ℝ) (a q : RealVector 2) :
    stTangent (f1aData delta).f a q = -q 0+delta*q 1 := by
  rw [stTangent,(f1a_objective_derivative delta a).fderiv]
  simp [f1aData,coord]
  ring

theorem f1a_zero_rows (delta : ℝ) (q : RealVector 2) :
    stSourceRows (f1aData delta) (point 0 0) q ↔ -q 1 ≤ 0 := by
  have hd : ∀ j : Fin 1, fderiv ℝ (fun z => (f1aData delta).c z j) (point 0 0) = -coord 1 := by
    intro j
    simpa [point] using (f1a_row_derivative delta (point 0 0) j).fderiv
  unfold stSourceRows
  simp_rw [hd]
  simp [f1aData,point,coord]
  rfl

theorem f1a_integral_zero : STSourceIntegral f1aI (point 0 0) := by
  intro i
  have hi : (i : Fin 2) = 1 := by simpa only [f1aI,Finset.mem_singleton] using i.property
  exact ⟨0,by simp [hi,point]⟩

theorem f1a_fixed_zero (delta : ℝ) (z : RealVector 2) :
    z ∈ stSourceNonlinearFiber (f1aData delta) f1aI (point 0 0) ↔ z = point 0 0 := by
  constructor
  · intro hz
    have hy := hz.1.2 f1aY
    have hg := hz.2 (0 : Fin 1)
    change z 1 = 0 at hy
    change (z 0)^2-z 1 ≤ 0 at hg
    have hx : z 0=0 := by nlinarith [sq_nonneg (z 0)]
    funext i
    fin_cases i <;> simp [point,hx,hy]
  · rintro rfl
    exact ⟨⟨(f1a_polyhedron delta _).mpr (by norm_num [point]),fun _ => rfl⟩,
      fun _ => by norm_num [f1aData,point]⟩

def f1aBatch : STSourceBatch 2 := ⟨point 0 0,false⟩

theorem f1a_batch_valid (delta : ℝ) :
    stSourceBatchValid (f1aData delta) f1aI (fun _ => 1) f1aBatch := by
  refine ⟨f1a_integral_zero,?_⟩
  change IsMinimizer (stSourceNonlinearFiber (f1aData delta) f1aI (point 0 0))
    (f1aData delta).f (point 0 0)
  refine ⟨(f1a_fixed_zero delta _).mpr rfl,?_⟩
  intro z hz
  rw [(f1a_fixed_zero delta z).mp hz]

theorem f1a_fiber_CQ_fails (delta : ℝ) : ¬ STSourceFiberSlater (f1aData delta) f1aI := by
  intro h
  obtain ⟨z,hz,hg⟩ := h (point 0 0) f1a_integral_zero
    ⟨point 0 0,(f1a_fixed_zero delta _).mpr rfl⟩
  have hy := hz.2 f1aY
  have hh := hg (0 : Fin 1)
  change z 1=0 at hy
  change (z 0)^2-z 1<0 at hh
  nlinarith [sq_nonneg (z 0)]

/-- Full-space CQ includes all four actual polyhedral rows. -/
def F1aFullMFCQ (delta : ℝ) (z : RealVector 2) : Prop :=
  ∃ v : RealVector 2,
    (∀ j, (f1aData delta).c z j=0 →
      (fderiv ℝ (fun x => (f1aData delta).c x j) z) v < 0) ∧
    (∀ k, (∑ i, (f1aData delta).coefficient k i*z i)=(f1aData delta).rhs k →
      (∑ i, (f1aData delta).coefficient k i*v i)<0)

theorem f1a_full_mfcq (delta : ℝ) (z : RealVector 2) : F1aFullMFCQ delta z := by
  refine ⟨point 0 (1/2)-z,?_,?_⟩
  · intro j hj
    rw [(f1a_row_derivative delta z j).fderiv]
    change (z 0)^2-z 1=0 at hj
    change (2*z 0)*(0-z 0)-(1/2-z 1)<0
    nlinarith [sq_nonneg (z 0)]
  · intro k hk
    fin_cases k <;> norm_num [f1aData,point,Fin.sum_univ_succ] at hk ⊢ <;> linarith

theorem f1a_source_CQ (delta : ℝ) :
    (∃ z ∈ (f1aData delta).polyhedron, ∀ j, (f1aData delta).c z j<0) ∧
    ∀ z ∈ convexHull ℝ ((f1aData delta).feasible f1aI), F1aFullMFCQ delta z := by
  exact ⟨⟨point 0 (1/2),(f1a_polyhedron delta _).mpr (by norm_num [point]),
    fun _ => by norm_num [f1aData,point]⟩,fun z _ => f1a_full_mfcq delta z⟩

def f1aHistory (k : ℕ) : List (STSourceBatch 2) := List.replicate (k+1) f1aBatch
def f1aState (k : ℕ) : STSourceState f1aI :=
  ⟨[],f1aHistory k,some (point 0 0),[BBExtendedNode.root],none⟩

theorem f1a_history_succ (k : ℕ) : f1aHistory (k+1) = f1aHistory k ++ [f1aBatch] := by
  simp only [f1aHistory,List.replicate_add,List.replicate_one]

theorem f1a_initialization (delta : ℝ) :
    STSourceInitialize (f1aData delta) f1aI (fun _ => 1) (some (f1aState 0)) := by
  have hh := STSourceInitialize.seeded (w := fun _ => 1) (point 0 0) f1aBatch
    ((f1a_polyhedron delta _).mpr (by norm_num [point])) f1a_integral_zero
    (f1a_batch_valid delta) (fun _ => rfl)
  simpa [stSourceInitial,f1aState,f1aHistory,stSourceBatchInc,f1aBatch,stSourceBest] using hh

theorem f1a_lp_iff (delta epsilon : ℝ) (k : ℕ) (q : RealVector 2 × ℝ) :
    q ∈ stSourceLP (I := f1aI) (f1aData delta) BBExtendedNode.root (stSourceAnchors (f1aState k))
      (.gap epsilon) (stSourceInc (f1aData delta) (f1aState k)) ↔
      ((-2 ≤ q.1 0 ∧ q.1 0 ≤ 2) ∧ (0 ≤ q.1 1 ∧ q.1 1 ≤ 1)) ∧
        -q.1 0+delta*q.1 1 ≤ q.2 ∧ q.2 ≤ -epsilon := by
  have hi : stSourceInc (f1aData delta) (f1aState k) = some 0 := by
    simp [stSourceInc,f1aState,f1aData,point]
  have ha : stSourceAnchors (f1aState k) = List.replicate (k+1) (point 0 0) := by
    simp [stSourceAnchors,f1aState,f1aHistory,f1aBatch]
  rw [st_source_lp_mem_iff,hi,ha,f1a_polyhedron]
  simp only [BBExtendedNode.holds_root,true_and,STSourcePolicy.Admits,zero_sub]
  constructor
  · rintro ⟨hX,hrows,hobj,hcut⟩
    have ht := hobj (point 0 0) (by simp)
    exact ⟨hX,by simpa only [f1a_objective_tangent] using ht,hcut⟩
  · rintro ⟨hX,hobj,hcut⟩
    refine ⟨hX,?_,?_,hcut⟩
    · intro a ha
      have he : a = point 0 0 := (List.mem_replicate.mp ha).2
      rw [he,f1a_zero_rows]
      linarith [hX.2.1]
    · intro a ha
      simpa only [f1a_objective_tangent] using hobj

theorem f1a_lp_minimum (delta epsilon : ℝ) (hd : 0 ≤ delta) (he : epsilon ≤ 2) (k : ℕ) :
    IsMinimizer (stSourceLP (I := f1aI) (f1aData delta) BBExtendedNode.root
      (stSourceAnchors (f1aState k)) (.gap epsilon)
      (stSourceInc (f1aData delta) (f1aState k))) Prod.snd (point 2 0,-2) := by
  refine ⟨(f1a_lp_iff delta epsilon k _).mpr (by norm_num [point]; linarith),?_⟩
  intro q hq
  obtain ⟨hX,hobj,hcut⟩ := (f1a_lp_iff delta epsilon k q).mp hq
  have hn := mul_nonneg hd hX.2.1
  dsimp
  linarith [hX.1.2]

theorem f1a_lp_unique (delta epsilon : ℝ) (hd : 0 < delta) (he : epsilon ≤ 2)
    (k : ℕ) (q : RealVector 2 × ℝ)
    (hq : IsMinimizer (stSourceLP (I := f1aI) (f1aData delta) BBExtendedNode.root
      (stSourceAnchors (f1aState k)) (.gap epsilon)
      (stSourceInc (f1aData delta) (f1aState k))) Prod.snd q) : q = (point 2 0,-2) := by
  have hm := f1a_lp_minimum delta epsilon hd.le he k
  have h1 := hm.2 q hq.1
  have h2 := hq.2 (point 2 0,-2) hm.1
  obtain ⟨hX,hobj,hcut⟩ := (f1a_lp_iff delta epsilon k q).mp hq.1
  have hheight : q.2 = -2 := by dsimp at h1 h2; linarith
  have hy : q.1 1=0 := by nlinarith [hX.1.2,hX.2.1]
  have hx : q.1 0=2 := by rw [hy] at hobj; linarith [hX.1.2]
  apply Prod.ext
  · funext i; fin_cases i <;> simp [point,hx,hy]
  · exact hheight

theorem f1a_actual_process (delta epsilon : ℝ) (hd : 0 ≤ delta) (he : epsilon ≤ 2) (k : ℕ) :
    STSourceProcess (f1aData delta) f1aI (fun _ => 1) (.gap epsilon)
      (f1aState k) (f1aState (k+1)) := by
  have hi : STSourceIntegral f1aI (point 2 0) := by
    intro i
    have hh : (i : Fin 2)=1 := by simpa only [f1aI,Finset.mem_singleton] using i.property
    exact ⟨0,by simp [hh,point]⟩
  have hy : ∀ i : {i : Fin 2 // i ∈ f1aI}, f1aBatch.anchor i = (point 2 0) i := by
    intro i
    have hh : (i : Fin 2)=1 := by simpa only [f1aI,Finset.mem_singleton] using i.property
    simp [f1aBatch,hh,point]
  refine ⟨_,STSourceSelect.choose [] (f1aHistory k) (some (point 0 0)) [] []
    BBExtendedNode.root,?_⟩
  have hr := STSourceResolve.callback (f1a_lp_minimum delta epsilon hd he k) hi
    (f1a_batch_valid delta) hy (live := [])
  simpa [f1aState,f1a_history_succ,stSourceBatchInc,f1aBatch,stSourceBest] using hr

theorem f1a_actual_traces (delta epsilon : ℝ) (hd : 0 ≤ delta) (he : epsilon ≤ 2) (k : ℕ) :
    STSourceTrace (f1aData delta) f1aI (fun _ => 1) (.gap epsilon) k (f1aState 0) (f1aState k) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
    exact st_cutoff_trace_append_step (f1aData delta) (fun _ => 1) (.gap epsilon) ih (f1a_actual_process delta epsilon hd he k)

theorem f1a_no_stop (k : ℕ) (out : Option (RealVector 2)) : ¬ STSourceStop (f1aState k) out := by
  intro h
  cases h with
  | exhausted hr he => simp [f1aState] at he

theorem f1a_source_nontermination (delta epsilon : ℝ) (hd : 0 < delta)
    (_hd1 : delta < 1) (_he0 : 0 < epsilon) (he2 : epsilon ≤ 2) :
    Bornology.IsBounded (f1aData delta).polyhedron ∧
    ContDiff ℝ 2 (f1aData delta).f ∧ ContDiff ℝ 2 (f1aData delta).c ∧
    ConvexOn ℝ Set.univ (f1aData delta).f ∧
    (∀ j, ConvexOn ℝ Set.univ (fun z => (f1aData delta).c z j)) ∧
    (∀ z ∈ convexHull ℝ ((f1aData delta).feasible f1aI), F1aFullMFCQ delta z) ∧
    ¬ STSourceFiberSlater (f1aData delta) f1aI ∧
    STSourceInitialize (f1aData delta) f1aI (fun _ => 1) (some (f1aState 0)) ∧
    (∀ k, STSourceProcess (f1aData delta) f1aI (fun _ => 1) (.gap epsilon)
      (f1aState k) (f1aState (k+1))) ∧ (∀ k out, ¬ STSourceStop (f1aState k) out) := by
  exact ⟨f1a_bounded delta,(f1a_C2 delta).1,(f1a_C2 delta).2,(f1a_convex delta).1,
    (f1a_convex delta).2,(f1a_source_CQ delta).2,f1a_fiber_CQ_fails delta,
    f1a_initialization delta,f1a_actual_process delta epsilon hd.le he2,f1a_no_stop⟩


theorem f1a_original_optimum (delta : ℝ) (hd : delta ≤ 1) :
    IsMinimizer ((f1aData delta).feasible f1aI) (f1aData delta).f (point 1 1) := by
  refine ⟨⟨(f1a_polyhedron delta _).mpr (by norm_num [point]),
    fun _ => by norm_num [f1aData,point],?_⟩,?_⟩
  · intro i
    have hi : (i : Fin 2)=1 := by simpa only [f1aI,Finset.mem_singleton] using i.property
    exact ⟨1,by simp [hi,point]⟩
  · intro z hz
    have hX := (f1a_polyhedron delta z).mp hz.1
    obtain ⟨k,hk⟩ := hz.2.2 f1aY
    change (k : ℝ)=z 1 at hk
    have hk0 : (0 : ℤ)≤k := by exact_mod_cast (show (0 : ℝ)≤(k : ℝ) by rw [hk]; exact hX.2.1)
    have hk1 : k≤(1 : ℤ) := by exact_mod_cast (show (k : ℝ)≤(1 : ℝ) by rw [hk]; exact hX.2.2)
    have hg := hz.2.1 (0 : Fin 1)
    change (z 0)^2-z 1≤0 at hg
    have hcases : k=0 ∨ k=1 := by omega
    rcases hcases with rfl | rfl
    · have hy : z 1=0 := by simpa using hk.symm
      have hx : z 0=0 := by nlinarith [sq_nonneg (z 0)]
      simp [f1aData,point,hx,hy]
      linarith
    · have hy : z 1=1 := by simpa using hk.symm
      have hx : z 0≤1 := by nlinarith [sq_nonneg (z 0-1)]
      simp only [f1aData,point,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,hy,mul_one]
      linarith

/-- Full original-coordinate stationarity restricted to the fixed integer
fiber, including all polyhedral multipliers and complementarity rows. -/
def F1aFiberKKT (delta : ℝ) (a : RealVector 2) : Prop :=
  ∃ (lambda : Fin 1 → ℝ) (mu : Fin 4 → ℝ),
    (∀ j, 0≤lambda j) ∧ (∀ k, 0≤mu k) ∧
    (∀ j, lambda j*(f1aData delta).c a j=0) ∧
    (∀ k, mu k*((∑ i, (f1aData delta).coefficient k i*a i)-(f1aData delta).rhs k)=0) ∧
    ∀ v : RealVector 2, v 1=0 →
      (fderiv ℝ (f1aData delta).f a) v +
      (∑ j,lambda j*(fderiv ℝ (fun x => (f1aData delta).c x j) a) v) +
      (∑ k,mu k*(∑ i,(f1aData delta).coefficient k i*v i))=0

theorem f1a_no_fiber_KKT (delta : ℝ) : ¬ F1aFiberKKT delta (point 0 0) := by
  rintro ⟨lambda,mu,hl,hm,hc,hcomp,hstat⟩
  have hm0 : mu 0=0 := by
    have hh := hcomp 0
    norm_num [f1aData,point,Fin.sum_univ_succ] at hh
    linarith
  have hm1 : mu 1=0 := by
    have hh := hcomp 1
    norm_num [f1aData,point,Fin.sum_univ_succ] at hh
    linarith
  have hd : ∀ j : Fin 1, fderiv ℝ (fun x => (f1aData delta).c x j) (point 0 0) = -coord 1 := by
    intro j
    simpa [point] using (f1a_row_derivative delta (point 0 0) j).fderiv
  have hh := hstat (point 1 0) (by norm_num [point])
  rw [(f1a_objective_derivative delta (point 0 0)).fderiv] at hh
  simp_rw [hd] at hh
  norm_num [f1aData,point,coord,Fin.sum_univ_succ,hm0,hm1] at hh

theorem f1a_actual_micro_traces (delta epsilon : ℝ) (hd : 0≤delta) (he : epsilon≤2) (k : ℕ) :
    STSourceMicroTrace (f1aData delta) f1aI (fun _ => 1) (.gap epsilon)
      (2*k) (f1aState 0) (f1aState k) :=
  st_cutoff_trace_micro (f1aData delta) (fun _ => 1) (.gap epsilon)
    (f1a_actual_traces delta epsilon hd he k)


/-! C7: original coordinate order (integer y, continuous t, integer z), genuine
quadratic objective, quadratic row coupling both integer coordinates, unit cube.
All four integer fibers have t=5/16 and objective25/256. -/
abbrev c7I := Chapter02BBAdapterExamples.indices
abbrev c7P := Chapter02BBAdapterExamples.partition
def c7Y : {i : Fin 3 // i ∈ c7I} := ⟨0,by simp [Chapter02BBAdapterExamples.indices]⟩
def c7Z : {i : Fin 3 // i ∈ c7I} := ⟨2,by simp [Chapter02BBAdapterExamples.indices]⟩
def c7Point (y t z : ℝ) : RealVector 3 := fun i => if i=0 then y else if i=1 then t else z
def c7Coord (i : Fin 3) : RealVector 3 →L[ℝ] ℝ := ContinuousLinearMap.proj i

def c7Data : BBPolyData 3 1 6 where
  coefficient := ![![-1,0,0],![1,0,0],![0,-1,0],![0,1,0],![0,0,-1],![0,0,1]]
  rhs := ![0,1,0,1,0,1]
  c := fun q _ => (q 0-1/2)^2/4+(q 2-1/2)^2-q 1
  f := fun q => (q 1)^2

theorem c7_polyhedron (q : RealVector 3) :
    q ∈ c7Data.polyhedron ↔ ∀ i, 0≤q i ∧ q i≤1 := by
  simp [BBPolyData.polyhedron,c7Data,Fin.forall_fin_succ,Fin.sum_univ_succ,and_assoc]

theorem c7_bounded : Bornology.IsBounded c7Data.polyhedron := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : RealVector 3) 1)).isBounded.subset
  intro q hq
  have hh := (c7_polyhedron q).mp hq
  exact ⟨fun i => (hh i).1,fun i => (hh i).2⟩

theorem c7_enclosing : c7Data.Encloses 1 := by
  refine ⟨by norm_num,?_⟩
  intro q hq i
  have hh := (c7_polyhedron q).mp hq i
  exact abs_le.mpr ⟨by linarith,hh.2⟩

theorem c7_C2 : ContDiff ℝ 2 c7Data.f ∧ ContDiff ℝ 2 c7Data.c := by
  constructor
  · dsimp [c7Data]; fun_prop
  · dsimp [c7Data]; simp only [div_eq_mul_inv]; fun_prop

theorem c7_convex : ConvexOn ℝ Set.univ c7Data.f ∧
    ∀ j, ConvexOn ℝ Set.univ (fun q => c7Data.c q j) := by
  constructor
  · simpa [c7Data] using Chapter02BBAdapterExamples.shifted_square_convex 1 0
  · intro j
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    have h0 := (Chapter02BBAdapterExamples.shifted_square_convex 0 (1/2)).2 hx hy ha hb hab
    have h2 := (Chapter02BBAdapterExamples.shifted_square_convex 2 (1/2)).2 hx hy ha hb hab
    dsimp [c7Data] at h0 h2 ⊢
    nlinarith

theorem c7_integral (y z : ℝ) (hy : y=0 ∨ y=1) (hz : z=0 ∨ z=1) (t : ℝ) :
    STSourceIntegral c7I (c7Point y t z) := by
  intro i
  have hi : (i : Fin 3)=0 ∨ (i : Fin 3)=2 := by
    simpa only [Chapter02BBAdapterExamples.indices,Finset.mem_insert,Finset.mem_singleton] using i.property
  rcases hi with hi | hi
  · rcases hy with rfl | rfl
    · exact ⟨0,by simp [c7Point,hi]⟩
    · exact ⟨1,by simp [c7Point,hi]⟩
  · rcases hz with rfl | rfl
    · exact ⟨0,by simp [c7Point,hi]⟩
    · exact ⟨1,by simp [c7Point,hi]⟩

def c7Batch (y z : ℝ) : STSourceBatch 3 := ⟨c7Point y (5/16) z,false⟩

theorem c7_batch_valid (y z : ℝ) (hy : y=0 ∨ y=1) (hz : z=0 ∨ z=1) :
    stSourceBatchValid c7Data c7I (fun _ => 1) (c7Batch y z) := by
  refine ⟨c7_integral y z hy hz _,?_⟩
  change IsMinimizer (stSourceNonlinearFiber c7Data c7I (c7Point y (5/16) z))
    c7Data.f (c7Point y (5/16) z)
  refine ⟨⟨⟨?_,fun _ => rfl⟩,?_⟩,?_⟩
  · apply (c7_polyhedron _).mpr
    intro i
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      fin_cases i <;> norm_num [c7Point]
  · intro j
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> norm_num [c7Data,c7Point,Fin.ext_iff]
  · intro q hq
    have hqy := hq.1.2 c7Y
    have hqz := hq.1.2 c7Z
    change q 0=y at hqy
    change q 2=z at hqz
    have hg := hq.2 (0 : Fin 1)
    change (q 0-1/2)^2/4+(q 2-1/2)^2-q 1≤0 at hg
    change (5/16 : ℝ)^2≤(q 1)^2
    rw [hqy,hqz] at hg
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      norm_num at hg <;> nlinarith

theorem c7_fiber_CQ : STSourceFiberSlater c7Data c7I := by
  intro a ha hne
  obtain ⟨q,hq⟩ := hne
  have hX := (c7_polyhedron q).mp hq.1.1
  have he0 : q 0=a 0 := hq.1.2 c7Y
  have ha0 : 0≤a 0 ∧ a 0≤1 := by rw [← he0]; exact hX 0
  have he2 : q 2=a 2 := hq.1.2 c7Z
  have ha2 : 0≤a 2 ∧ a 2≤1 := by rw [← he2]; exact hX 2
  refine ⟨c7Point (a 0) 1 (a 2),⟨?_,?_⟩,?_⟩
  · apply (c7_polyhedron _).mpr
    intro i
    fin_cases i
    · simpa [c7Point] using ha0
    · norm_num [c7Point]
    · simpa [c7Point] using ha2
  · intro i
    have hi : (i : Fin 3)=0 ∨ (i : Fin 3)=2 := by
      simpa only [Chapter02BBAdapterExamples.indices,Finset.mem_insert,Finset.mem_singleton] using i.property
    rcases hi with hi | hi <;> simp [c7Point,hi]
  · intro j
    change (a 0-1/2)^2/4+(a 2-1/2)^2-1<0
    nlinarith [mul_nonneg ha0.1 (sub_nonneg.mpr ha0.2),
      mul_nonneg ha2.1 (sub_nonneg.mpr ha2.2)]

theorem c7_objective_derivative (a : RealVector 3) :
    HasFDerivAt c7Data.f ((2*a 1) • c7Coord 1) a := by
  simpa [c7Data,c7Coord,Function.comp_def] using
    (hasDerivAt_pow 2 (a 1)).comp_hasFDerivAt a (c7Coord 1).hasFDerivAt

theorem c7_row_derivative (a : RealVector 3) (j : Fin 1) :
    HasFDerivAt (fun q => c7Data.c q j)
      (((2*(a 0-1/2))/4) • c7Coord 0 + (2*(a 2-1/2)) • c7Coord 2-c7Coord 1) a := by
  have h0 := ((hasDerivAt_pow 2 (a 0-1/2)).comp_hasFDerivAt a
    ((c7Coord 0).hasFDerivAt.sub_const (1/2))).const_smul (1/4 : ℝ)
  have h2 := (hasDerivAt_pow 2 (a 2-1/2)).comp_hasFDerivAt a
    ((c7Coord 2).hasFDerivAt.sub_const (1/2))
  have hh := (h0.add h2).sub (c7Coord 1).hasFDerivAt
  convert hh using 1 <;> ext q <;> simp [c7Data,c7Coord,Function.comp_def] <;> ring

theorem c7_objective_tangent (y z : ℝ) (q : RealVector 3) :
    stTangent c7Data.f (c7Batch y z).anchor q = (5/8)*q 1-25/256 := by
  rw [stTangent,(c7_objective_derivative _).fderiv]
  simp [c7Data,c7Batch,c7Point,c7Coord]
  ring

def c7Row (y z : ℝ) (q : RealVector 3) : ℝ :=
  (y/2-1/4)*q 0+(2*z-1)*q 2-q 1+5/16-y^2/4-z^2

theorem c7_rows (y z : ℝ) (q : RealVector 3) :
    stSourceRows c7Data (c7Batch y z).anchor q ↔ c7Row y z q≤0 := by
  unfold stSourceRows
  simp_rw [(c7_row_derivative _ _).fderiv]
  simp only [Fin.forall_fin_one]
  simp [c7Data,c7Batch,c7Point,c7Coord,c7Row]
  constructor <;> intro h <;> nlinarith


abbrev C7Node := BBExtendedNode {i : Fin 3 // i ∈ c7I}
def c7Root : C7Node := BBExtendedNode.root
def c7Left : C7Node := c7Root.left c7Y (1/2)
def c7Right : C7Node := c7Root.right c7Y (1/2)
def c7LL : C7Node := c7Left.left c7Z (1/2)
def c7LR : C7Node := c7Left.right c7Z (1/2)
def c7RL : C7Node := c7Right.left c7Z (1/2)
def c7RR : C7Node := c7Right.right c7Z (1/2)

theorem c7_node_holds (B : C7Node) (q : RealVector 3) :
    B.Holds (fun i => q i) ↔
      (B.lower c7Y ≤ (q 0 : WithBot ℝ) ∧ (q 0 : WithTop ℝ) ≤ B.upper c7Y) ∧
      (B.lower c7Z ≤ (q 2 : WithBot ℝ) ∧ (q 2 : WithTop ℝ) ≤ B.upper c7Z) := by
  constructor
  · intro h; exact ⟨h c7Y,h c7Z⟩
  · intro h i
    have hi : (i : Fin 3)=0 ∨ (i : Fin 3)=2 := by
      simpa only [Chapter02BBAdapterExamples.indices,Finset.mem_insert,Finset.mem_singleton] using i.property
    rcases hi with hi | hi
    · have he : i=c7Y := Subtype.ext hi
      simpa only [he,c7Y] using h.1
    · have he : i=c7Z := Subtype.ext hi
      simpa only [he,c7Z] using h.2

def c7State (H : List (ℝ × ℝ)) (live : List C7Node) : STSourceState c7I :=
  ⟨[],H.map (fun a => c7Batch a.1 a.2),some (c7Point 1 (5/16) 1),live,none⟩

def c7LP (H : List (ℝ × ℝ)) (B : C7Node) : Set (RealVector 3 × ℝ) :=
  stSourceLP c7Data B (stSourceAnchors (c7State H [])) (.gap (1/256))
    (stSourceInc c7Data (c7State H []))

theorem c7_lp_iff (H : List (ℝ × ℝ)) (hH : H≠[]) (B : C7Node) (q : RealVector 3 × ℝ) :
    q ∈ c7LP H B ↔ (∀ i,0≤q.1 i ∧ q.1 i≤1) ∧ B.Holds (fun i => q.1 i) ∧
      (∀ a∈H,c7Row a.1 a.2 q.1≤0) ∧ (5/8)*q.1 1-25/256≤q.2 ∧ q.2≤24/256 := by
  rw [c7LP,st_source_lp_mem_iff,c7_polyhedron]
  have hinc : stSourceInc c7Data (c7State H []) = some (25/256) := by
    norm_num [stSourceInc,c7State,c7Data,c7Point]
  have hanchors : stSourceAnchors (c7State H []) = H.map (fun a => (c7Batch a.1 a.2).anchor) := by
    simp [stSourceAnchors,c7State,List.map_map,Function.comp_def]
  rw [hinc,hanchors]
  change _ ↔ _
  constructor
  · rintro ⟨hX,hB,hr,ho,hcut⟩
    have hex : ∃ a,a∈H := List.exists_mem_of_ne_nil _ hH
    obtain ⟨a,ha⟩ := hex
    have ht := ho _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    rw [c7_objective_tangent] at ht
    refine ⟨hX,hB,?_,ht,?_⟩
    · intro b hb
      exact (c7_rows b.1 b.2 q.1).mp (hr _ (List.mem_map.mpr ⟨b,hb,rfl⟩))
    · norm_num [STSourcePolicy.Admits] at hcut ⊢
      exact hcut
  · rintro ⟨hX,hB,hr,ho,hcut⟩
    refine ⟨hX,hB,?_,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact (c7_rows b.1 b.2 q.1).mpr (hr b hb)
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      simpa only [c7_objective_tangent] using ho
    · norm_num [STSourcePolicy.Admits]
      linarith

theorem c7_zero_height_minimum (H : List (ℝ × ℝ)) (hH : H≠[]) (B : C7Node)
    (q : RealVector 3) (hq : (q,-25/256)∈c7LP H B) :
    IsMinimizer (c7LP H B) Prod.snd (q,-25/256) := by
  refine ⟨hq,?_⟩
  intro p hp
  have hh := (c7_lp_iff H hH B p).mp hp
  have ht := (hh.1 1).1
  dsimp
  linarith [hh.2.2.2.1]

theorem c7_initialization :
    STSourceInitialize c7Data c7I (fun _ => 1) (some (c7State [(1,1)] [c7Root])) := by
  have hb := c7_batch_valid 1 1 (Or.inr rfl) (Or.inr rfl)
  have ha := st_source_batch_anchor_polyhedron c7Data c7I (fun _ => 1) (c7Batch 1 1) hb
  have hh := STSourceInitialize.seeded (c7Batch 1 1).anchor (c7Batch 1 1) ha hb.1 hb
    (fun _ => rfl)
  simpa [stSourceInitial,c7State,c7Root,stSourceBatchInc,c7Batch,stSourceBest] using hh

theorem c7_min_root : IsMinimizer (c7LP [(1,1)] c7Root) Prod.snd
    (c7Point (1/2) 0 (1/2),-25/256) := by
  apply c7_zero_height_minimum _ (by simp)
  rw [c7_lp_iff _ (by simp)]
  constructor
  · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
  · refine ⟨BBExtendedNode.holds_root _,?_⟩
    norm_num [c7Point,c7Row,Fin.ext_iff]

theorem c7_min_right_first : IsMinimizer (c7LP [(1,1)] c7Right) Prod.snd
    (c7Point 1 0 0,-25/256) := by
  apply c7_zero_height_minimum _ (by simp)
  rw [c7_lp_iff _ (by simp),c7_node_holds]
  constructor
  · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
  · norm_num [c7Point,c7Right,c7Root,c7Y,c7Z,BBExtendedNode.right,BBExtendedNode.root,
    c7Row,Function.update,Fin.ext_iff]

theorem c7_min_right_second : IsMinimizer (c7LP [(1,1),(1,0)] c7Right) Prod.snd
    (c7Point 1 0 (1/2),-25/256) := by
  apply c7_zero_height_minimum _ (by simp)
  rw [c7_lp_iff _ (by simp),c7_node_holds]
  constructor
  · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
  · norm_num [c7Point,c7Right,c7Root,c7Y,c7Z,BBExtendedNode.right,BBExtendedNode.root,
    c7Row,Function.update,Fin.ext_iff]

theorem c7_min_left : IsMinimizer (c7LP [(1,1),(1,0)] c7Left) Prod.snd
    (c7Point 0 0 (1/2),-25/256) := by
  apply c7_zero_height_minimum _ (by simp)
  rw [c7_lp_iff _ (by simp),c7_node_holds]
  constructor
  · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
  · norm_num [c7Point,c7Left,c7Root,c7Y,c7Z,BBExtendedNode.left,BBExtendedNode.root,
    c7Row,Function.update,Fin.ext_iff]


theorem c7_LL_fixed (q : RealVector 3) (hq : q∈c7Data.polyhedron)
    (hB : c7LL.Holds (fun i => q i)) : q 0=0 ∧ q 2=0 := by
  have hX := (c7_polyhedron q).mp hq
  rw [c7_node_holds] at hB
  norm_num [c7LL,c7Left,c7Root,c7Y,c7Z,BBExtendedNode.left,BBExtendedNode.root,
    Function.update,Fin.ext_iff] at hB
  exact ⟨le_antisymm hB.1 (hX 0).1,le_antisymm hB.2 (hX 2).1⟩

theorem c7_LR_fixed (q : RealVector 3) (hq : q∈c7Data.polyhedron)
    (hB : c7LR.Holds (fun i => q i)) : q 0=0 ∧ q 2=1 := by
  have hX := (c7_polyhedron q).mp hq
  rw [c7_node_holds] at hB
  norm_num [c7LR,c7Left,c7Root,c7Y,c7Z,BBExtendedNode.left,BBExtendedNode.right,
    BBExtendedNode.root,Function.update,Fin.ext_iff] at hB
  exact ⟨le_antisymm hB.1 (hX 0).1,le_antisymm (hX 2).2 hB.2⟩

theorem c7_RL_fixed (q : RealVector 3) (hq : q∈c7Data.polyhedron)
    (hB : c7RL.Holds (fun i => q i)) : q 0=1 ∧ q 2=0 := by
  have hX := (c7_polyhedron q).mp hq
  rw [c7_node_holds] at hB
  norm_num [c7RL,c7Right,c7Root,c7Y,c7Z,BBExtendedNode.left,BBExtendedNode.right,
    BBExtendedNode.root,Function.update,Fin.ext_iff] at hB
  exact ⟨le_antisymm (hX 0).2 hB.1,le_antisymm hB.2 (hX 2).1⟩

theorem c7_RR_fixed (q : RealVector 3) (hq : q∈c7Data.polyhedron)
    (hB : c7RR.Holds (fun i => q i)) : q 0=1 ∧ q 2=1 := by
  have hX := (c7_polyhedron q).mp hq
  rw [c7_node_holds] at hB
  norm_num [c7RR,c7Right,c7Root,c7Y,c7Z,BBExtendedNode.right,
    BBExtendedNode.root,Function.update,Fin.ext_iff] at hB
  exact ⟨le_antisymm (hX 0).2 hB.1,le_antisymm (hX 2).2 hB.2⟩

theorem c7_leaf_closed (H : List (ℝ × ℝ)) (hH : H≠[]) (B : C7Node)
    (y z : ℝ) (hy : y=0 ∨ y=1) (hz : z=0 ∨ z=1)
    (hm : (y,z)∈H)
    (hfix : ∀ q∈c7Data.polyhedron, B.Holds (fun i => q i) → q 0=y ∧ q 2=z) :
    c7LP H B=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := (c7_lp_iff H hH B q).mp hq
  obtain ⟨hqy,hqz⟩ := hfix q.1 ((c7_polyhedron _).mpr hh.1) hh.2.1
  have hr := hh.2.2.1 (y,z) hm
  have ho := hh.2.2.2.1
  have hc := hh.2.2.2.2
  simp only [c7Row,Prod.fst,Prod.snd,hqy,hqz] at hr
  rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> norm_num at hr <;> linarith

theorem c7_min_LL : IsMinimizer (c7LP [(1,1),(1,0)] c7LL) Prod.snd
    (c7Point 0 (1/16) 0,-15/256) := by
  refine ⟨?_,?_⟩
  · rw [c7_lp_iff _ (by simp),c7_node_holds]
    constructor
    · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
    · norm_num [c7Point,c7LL,c7Left,c7Root,c7Y,c7Z,BBExtendedNode.left,BBExtendedNode.root,
      c7Row,Function.update,Fin.ext_iff]
  · intro q hq
    have hh := (c7_lp_iff _ (by simp) c7LL q).mp hq
    obtain ⟨hy,hz⟩ := c7_LL_fixed q.1 ((c7_polyhedron _).mpr hh.1) hh.2.1
    have hr := hh.2.2.1 (1,0) (by simp)
    norm_num [c7Row,hy,hz] at hr
    dsimp
    linarith [hh.2.2.2.1]

theorem c7_min_LR : IsMinimizer (c7LP [(1,1),(1,0),(0,0)] c7LR) Prod.snd
    (c7Point 0 (1/16) 1,-15/256) := by
  refine ⟨?_,?_⟩
  · rw [c7_lp_iff _ (by simp),c7_node_holds]
    constructor
    · intro i; fin_cases i <;> norm_num [c7Point,Fin.ext_iff]
    · norm_num [c7Point,c7LR,c7Left,c7Root,c7Y,c7Z,BBExtendedNode.left,BBExtendedNode.right,
      BBExtendedNode.root,c7Row,Function.update,Fin.ext_iff]
  · intro q hq
    have hh := (c7_lp_iff _ (by simp) c7LR q).mp hq
    obtain ⟨hy,hz⟩ := c7_LR_fixed q.1 ((c7_polyhedron _).mpr hh.1) hh.2.1
    have hr := hh.2.2.1 (1,1) (by simp)
    norm_num [c7Row,hy,hz] at hr
    dsimp
    linarith [hh.2.2.2.1]

theorem c7_same_fiber (y z t : ℝ) :
    ∀ i : {i : Fin 3 // i∈c7I}, (c7Batch y z).anchor i=(c7Point y t z) i := by
  intro i
  have hi : (i : Fin 3)=0 ∨ (i : Fin 3)=2 := by
    simpa only [Chapter02BBAdapterExamples.indices,Finset.mem_insert,Finset.mem_singleton] using i.property
  rcases hi with hi | hi <;> simp [c7Batch,c7Point,hi,Fin.ext_iff]

theorem c7_callback_step (H : List (ℝ × ℝ)) (pre post : List C7Node) (B : C7Node)
    (y z t eta : ℝ) (hy : y=0 ∨ y=1) (hz : z=0 ∨ z=1)
    (hq : IsMinimizer (c7LP H B) Prod.snd (c7Point y t z,eta)) :
    STSourceProcess c7Data c7I (fun _ => 1) (.gap (1/256))
      (c7State H (pre++B::post)) (c7State (H++[(y,z)]) (B::(pre++post))) := by
  refine ⟨_,STSourceSelect.choose [] _ _ pre post B,?_⟩
  have hh := STSourceResolve.callback (live := pre++post) hq
    (c7_integral y z hy hz t) (c7_batch_valid y z hy hz) (c7_same_fiber y z t)
  simpa [c7LP,c7State,stSourceBatchInc,c7Batch,stSourceBest,c7Data,c7Point] using hh

theorem c7_branch_step (H : List (ℝ × ℝ)) (pre post : List C7Node) (B : C7Node)
    (q : RealVector 3 × ℝ) (i : {i : Fin 3 // i∈c7I})
    (hq : IsMinimizer (c7LP H B) Prod.snd q) (hf : BBFractional (q.1 i)) :
    STSourceProcess c7Data c7I (fun _ => 1) (.gap (1/256))
      (c7State H (pre++B::post))
      (c7State H ([B.left i (q.1 i),B.right i (q.1 i)]++(pre++post))) := by
  exact ⟨_,STSourceSelect.choose [] _ _ pre post B,STSourceResolve.branch i hq hf⟩

theorem c7_empty_step (H : List (ℝ × ℝ)) (pre post : List C7Node) (B : C7Node)
    (he : c7LP H B=∅) :
    STSourceProcess c7Data c7I (fun _ => 1) (.gap (1/256))
      (c7State H (pre++B::post)) (c7State H (pre++post)) :=
  ⟨_,STSourceSelect.choose [] _ _ pre post B,STSourceResolve.empty he⟩


def c7Run : ℕ → STSourceState c7I
  | 0 => c7State [(1,1)] [c7Root]
  | 1 => c7State [(1,1)] [c7Left,c7Right]
  | 2 => c7State [(1,1),(1,0)] [c7Right,c7Left]
  | 3 => c7State [(1,1),(1,0)] [c7RL,c7RR,c7Left]
  | 4 => c7State [(1,1),(1,0)] [c7RR,c7Left]
  | 5 => c7State [(1,1),(1,0)] [c7Left]
  | 6 => c7State [(1,1),(1,0)] [c7LL,c7LR]
  | 7 => c7State [(1,1),(1,0),(0,0)] [c7LL,c7LR]
  | 8 => c7State [(1,1),(1,0),(0,0)] [c7LR]
  | 9 => c7State [(1,1),(1,0),(0,0),(0,1)] [c7LR]
  | _ => c7State [(1,1),(1,0),(0,0),(0,1)] []

theorem c7_half_fractional : BBFractional (1/2 : ℝ) :=
  Chapter02BBAdapterExamples.fractional _ (by norm_num) (by norm_num)

theorem c7_steps (k : Fin 10) :
    STSourceProcess c7Data c7I (fun _ => 1) (.gap (1/256)) (c7Run k) (c7Run (k+1)) := by
  fin_cases k
  · simpa [c7Run,c7Left,c7Right,c7Point,c7Y] using
      c7_branch_step [(1,1)] [] [] c7Root _ c7Y c7_min_root
        (by simpa [c7Point,c7Y] using c7_half_fractional)
  · simpa [c7Run] using c7_callback_step [(1,1)] [c7Left] [] c7Right
      1 0 0 (-25/256) (Or.inr rfl) (Or.inl rfl) c7_min_right_first
  · simpa [c7Run,c7RL,c7RR,c7Point,c7Z,Fin.ext_iff] using
      c7_branch_step [(1,1),(1,0)] [] [c7Left] c7Right _ c7Z c7_min_right_second
        (by simpa [c7Point,c7Z,Fin.ext_iff] using c7_half_fractional)
  · exact c7_empty_step _ [] [c7RR,c7Left] c7RL
      (c7_leaf_closed _ (by simp) c7RL 1 0 (Or.inr rfl) (Or.inl rfl)
        (by simp) c7_RL_fixed)
  · exact c7_empty_step _ [] [c7Left] c7RR
      (c7_leaf_closed _ (by simp) c7RR 1 1 (Or.inr rfl) (Or.inr rfl)
        (by simp) c7_RR_fixed)
  · simpa [c7Run,c7LL,c7LR,c7Point,c7Z,Fin.ext_iff] using
      c7_branch_step [(1,1),(1,0)] [] [] c7Left _ c7Z c7_min_left
        (by simpa [c7Point,c7Z,Fin.ext_iff] using c7_half_fractional)
  · simpa [c7Run] using c7_callback_step [(1,1),(1,0)] [] [c7LR] c7LL
      0 0 (1/16) (-15/256) (Or.inl rfl) (Or.inl rfl) c7_min_LL
  · exact c7_empty_step _ [] [c7LR] c7LL
      (c7_leaf_closed _ (by simp) c7LL 0 0 (Or.inl rfl) (Or.inl rfl)
        (by simp) c7_LL_fixed)
  · simpa [c7Run] using c7_callback_step [(1,1),(1,0),(0,0)] [] [] c7LR
      0 1 (1/16) (-15/256) (Or.inl rfl) (Or.inr rfl) c7_min_LR
  · exact c7_empty_step _ [] [] c7LR
      (c7_leaf_closed _ (by simp) c7LR 0 1 (Or.inl rfl) (Or.inr rfl)
        (by simp) c7_LR_fixed)

theorem c7_trace_prefix (k : ℕ) (hk : k≤10) :
    STSourceTrace c7Data c7I (fun _ => 1) (.gap (1/256)) k (c7Run 0) (c7Run k) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
    exact st_cutoff_trace_append_step c7Data (fun _ => 1) (.gap (1/256)) (ih (by omega)) (c7_steps ⟨k,by omega⟩)

theorem c7_ten_process_trace :
    STSourceInitialize c7Data c7I (fun _ => 1) (some (c7Run 0)) ∧
    STSourceTrace c7Data c7I (fun _ => 1) (.gap (1/256)) 10 (c7Run 0) (c7Run 10) ∧
    STSourceMicroTrace c7Data c7I (fun _ => 1) (.gap (1/256)) 20 (c7Run 0) (c7Run 10) ∧
    STSourceStop (c7Run 10) (some (c7Point 1 (5/16) 1)) := by
  have ht := c7_trace_prefix 10 (by omega)
  exact ⟨c7_initialization,ht,st_cutoff_trace_micro c7Data (fun _ => 1) (.gap (1/256)) ht,
    .exhausted rfl rfl⟩

theorem c7_final_certificate :
    STSourceReturnCertificate c7Data c7I (.gap (1/256)) (some (c7Point 1 (5/16) 1)) := by
  have hi := (st_cutoff_initialization_invariant c7Data c7I (fun _ => 1)
    (.gap (1/256)) c7_initialization).1
  have hf := (c7_C2.1).differentiable (by norm_num)
  have hg : ∀ j, Differentiable ℝ (fun q => c7Data.c q j) :=
    fun j => ((contDiff_apply ℝ (fun _ => ℝ) j).comp c7_C2.2).differentiable (by norm_num)
  have hs := st_cutoff_trace_invariant c7Data (fun _ => 1) (.gap (1/256))
    c7_convex.1 hf c7_convex.2 hg hi c7_ten_process_trace.2.1
  exact st_source_stop_sound c7Data (fun _ => 1) (.gap (1/256)) hs c7_ten_process_trace.2.2.2

theorem c7_actual_rank_bound :
    10 ≤ (bbRootNode (c7Data.model c7P 1)).weight + (stSourceBox c7P 1).card := by
  have hi := (st_cutoff_initialization_invariant c7Data c7I (fun _ => 1)
    (.gap (1/256)) c7_initialization).1
  have hf := (c7_C2.1).differentiable (by norm_num)
  have hg : ∀ j, Differentiable ℝ (fun q => c7Data.c q j) :=
    fun j => ((contDiff_apply ℝ (fun _ => ℝ) j).comp c7_C2.2).differentiable (by norm_num)
  have hb := st_cutoff_trace_potential_bound c7Data (fun _ => 1) (.gap (1/256))
    c7P 1 c7_enclosing (fun _ => by norm_num) (Or.inr ⟨1/256,rfl,by norm_num⟩)
    c7_convex.1 hf c7_convex.2 hg c7_fiber_CQ hi c7_ten_process_trace.2.1
  have hib := st_cutoff_initial_potential_bound c7Data c7P 1 (c7Batch 1 1)
  have he : stSourceInitial c7Data c7I (c7Batch 1 1)=c7Run 0 := by
    simp [stSourceInitial,c7Run,c7State,stSourceBatchInc,c7Batch,stSourceBest,c7Root]
  rw [he] at hib
  simp only [c7Run] at hb hib
  omega

theorem c7_explicit_root_rank :
    (bbRootNode (c7Data.model c7P 1)).rank=4 ∧ (bbRootNode (c7Data.model c7P 1)).weight=31 := by
  norm_num [bbRootNode,BBPolyData.model,BBNode.rank,BBNode.span,BBNode.weight,Fin.sum_univ_succ]

end Chapter02STSourceExamples

#print axioms Chapter02STSourceExamples.f1a_polyhedron
#print axioms Chapter02STSourceExamples.f1a_bounded
#print axioms Chapter02STSourceExamples.f1a_enclosing
#print axioms Chapter02STSourceExamples.f1a_C2
#print axioms Chapter02STSourceExamples.f1a_convex
#print axioms Chapter02STSourceExamples.f1a_objective_derivative
#print axioms Chapter02STSourceExamples.f1a_row_derivative
#print axioms Chapter02STSourceExamples.f1a_objective_tangent
#print axioms Chapter02STSourceExamples.f1a_zero_rows
#print axioms Chapter02STSourceExamples.f1a_integral_zero
#print axioms Chapter02STSourceExamples.f1a_fixed_zero
#print axioms Chapter02STSourceExamples.f1a_batch_valid
#print axioms Chapter02STSourceExamples.f1a_fiber_CQ_fails
#print axioms Chapter02STSourceExamples.f1a_full_mfcq
#print axioms Chapter02STSourceExamples.f1a_source_CQ
#print axioms Chapter02STSourceExamples.f1a_history_succ
#print axioms Chapter02STSourceExamples.f1a_initialization
#print axioms Chapter02STSourceExamples.f1a_lp_iff
#print axioms Chapter02STSourceExamples.f1a_lp_minimum
#print axioms Chapter02STSourceExamples.f1a_lp_unique
#print axioms Chapter02STSourceExamples.f1a_actual_process
#print axioms Chapter02STSourceExamples.f1a_actual_traces
#print axioms Chapter02STSourceExamples.f1a_no_stop
#print axioms Chapter02STSourceExamples.f1a_source_nontermination
#print axioms Chapter02STSourceExamples.f1a_original_optimum
#print axioms Chapter02STSourceExamples.f1a_no_fiber_KKT
#print axioms Chapter02STSourceExamples.f1a_actual_micro_traces
#print axioms Chapter02STSourceExamples.c7_polyhedron
#print axioms Chapter02STSourceExamples.c7_bounded
#print axioms Chapter02STSourceExamples.c7_enclosing
#print axioms Chapter02STSourceExamples.c7_C2
#print axioms Chapter02STSourceExamples.c7_convex
#print axioms Chapter02STSourceExamples.c7_integral
#print axioms Chapter02STSourceExamples.c7_batch_valid
#print axioms Chapter02STSourceExamples.c7_fiber_CQ
#print axioms Chapter02STSourceExamples.c7_objective_derivative
#print axioms Chapter02STSourceExamples.c7_row_derivative
#print axioms Chapter02STSourceExamples.c7_objective_tangent
#print axioms Chapter02STSourceExamples.c7_rows
#print axioms Chapter02STSourceExamples.c7_node_holds
#print axioms Chapter02STSourceExamples.c7_lp_iff
#print axioms Chapter02STSourceExamples.c7_zero_height_minimum
#print axioms Chapter02STSourceExamples.c7_initialization
#print axioms Chapter02STSourceExamples.c7_min_root
#print axioms Chapter02STSourceExamples.c7_min_right_first
#print axioms Chapter02STSourceExamples.c7_min_right_second
#print axioms Chapter02STSourceExamples.c7_min_left
#print axioms Chapter02STSourceExamples.c7_LL_fixed
#print axioms Chapter02STSourceExamples.c7_LR_fixed
#print axioms Chapter02STSourceExamples.c7_RL_fixed
#print axioms Chapter02STSourceExamples.c7_RR_fixed
#print axioms Chapter02STSourceExamples.c7_leaf_closed
#print axioms Chapter02STSourceExamples.c7_min_LL
#print axioms Chapter02STSourceExamples.c7_min_LR
#print axioms Chapter02STSourceExamples.c7_same_fiber
#print axioms Chapter02STSourceExamples.c7_callback_step
#print axioms Chapter02STSourceExamples.c7_branch_step
#print axioms Chapter02STSourceExamples.c7_empty_step
#print axioms Chapter02STSourceExamples.c7_half_fractional
#print axioms Chapter02STSourceExamples.c7_steps
#print axioms Chapter02STSourceExamples.c7_trace_prefix
#print axioms Chapter02STSourceExamples.c7_ten_process_trace
#print axioms Chapter02STSourceExamples.c7_final_certificate
#print axioms Chapter02STSourceExamples.c7_actual_rank_bound
#print axioms Chapter02STSourceExamples.c7_explicit_root_rank
