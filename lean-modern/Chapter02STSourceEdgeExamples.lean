module

public import Chapter02STSourceDriver
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-! Source initialization boundaries: empty/full integral-coordinate sets,
empty X, nonempty X with empty mixed affine base, and an invalid selected fiber
in a globally feasible problem. These controls use actual source relations. -/
noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02STSourceEdgeExamples

def point (a : ℝ) : RealVector 1 := fun _ => a
def data (lo hi : ℝ) : BBPolyData 1 1 2 where
  coefficient := ![fun _ => -1,fun _ => 1]
  rhs := ![-lo,hi]
  c := fun _ _ => -1
  f := fun q => (q 0)^2

theorem polyhedron_iff (lo hi : ℝ) (q : RealVector 1) :
    q ∈ (data lo hi).polyhedron ↔ lo≤q 0 ∧ q 0≤hi := by
  simp [BBPolyData.polyhedron,data,Fin.sum_univ_one,Fin.forall_fin_succ]

theorem bounded (lo hi : ℝ) : Bornology.IsBounded (data lo hi).polyhedron := by
  apply (isCompact_Icc : IsCompact (Set.Icc (point lo) (point hi))).isBounded.subset
  intro q hq
  have hh := (polyhedron_iff lo hi q).mp hq
  constructor <;> intro i <;> fin_cases i <;> simp_all [point]

theorem smooth (lo hi : ℝ) : ContDiff ℝ 2 (data lo hi).f ∧ ContDiff ℝ 2 (data lo hi).c := by
  constructor <;> dsimp [data] <;> fun_prop

theorem convex (lo hi : ℝ) : ConvexOn ℝ Set.univ (data lo hi).f ∧
    ∀ j, ConvexOn ℝ Set.univ (fun q => (data lo hi).c q j) := by
  constructor
  · have hs : ConvexOn ℝ Set.univ (fun t : ℝ => t^2) := (by decide : Even 2).convexOn_pow
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    exact hs.2 (Set.mem_univ (x 0)) (Set.mem_univ (y 0)) ha hb hab
  · intro j
    exact convexOn_const _ convex_univ

theorem fiber_CQ (lo hi : ℝ) (I : Finset (Fin 1)) : STSourceFiberSlater (data lo hi) I := by
  intro a ha hne
  obtain ⟨q,hq⟩ := hne
  exact ⟨q,hq.1,fun _ => by norm_num [data]⟩

theorem integral_zero (I : Finset (Fin 1)) : STSourceIntegral I (point 0) :=
  fun _ => ⟨0,by norm_num [point]⟩

def batch : STSourceBatch 1 := ⟨point 0,false⟩

theorem batch_valid (I : Finset (Fin 1)) : stSourceBatchValid (data 0 1) I (fun _ => 1) batch := by
  refine ⟨integral_zero I,?_⟩
  change IsMinimizer (stSourceNonlinearFiber (data 0 1) I (point 0)) (data 0 1).f (point 0)
  refine ⟨⟨⟨(polyhedron_iff _ _ _).mpr (by norm_num [point]),fun _ => rfl⟩,
    fun _ => by norm_num [data]⟩,?_⟩
  intro q hq
  simpa [data,point] using sq_nonneg (q 0)

def initial (I : Finset (Fin 1)) : STSourceState I := stSourceInitial (data 0 1) I batch
def finalState (I : Finset (Fin 1)) : STSourceState I :=
  ⟨[],[batch],some (point 0),[],none⟩

theorem initialization (I : Finset (Fin 1)) :
    STSourceInitialize (data 0 1) I (fun _ => 1) (some (initial I)) :=
  .seeded (point 0) batch ((polyhedron_iff _ _ _).mpr (by norm_num [point]))
    (integral_zero I) (batch_valid I) (fun _ => rfl)

theorem zero_derivative (lo hi : ℝ) :
    HasFDerivAt (𝕜 := ℝ) (data lo hi).f 0 (point 0) := by
  have hh := (hasDerivAt_pow 2 (0 : ℝ)).comp_hasFDerivAt (point 0)
    (ContinuousLinearMap.proj (0 : Fin 1) : RealVector 1 →L[ℝ] ℝ).hasFDerivAt
  simpa [data,point,Function.comp_def] using hh

theorem zero_tangent (lo hi : ℝ) (q : RealVector 1) :
    stTangent (data lo hi).f (point 0) q=0 := by
  rw [stTangent,(zero_derivative lo hi).fderiv]
  norm_num [data,point]

theorem initial_LP_empty (I : Finset (Fin 1)) (policy : STSourcePolicy)
    (hp : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0<epsilon) :
    stSourceLP (data 0 1) (BBExtendedNode.root (ι := {i : Fin 1 // i∈I}))
      (stSourceAnchors (initial I)) policy (stSourceInc (data 0 1) (initial I)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := (st_source_lp_mem_iff (data 0 1) _ _ policy _ q).mp hq
  have ha : point 0∈stSourceAnchors (initial I) := by
    simp [initial,stSourceInitial,stSourceAnchors,batch]
  have ht := hh.2.2.2.1 (point 0) ha
  rw [zero_tangent] at ht
  have hc : policy.Admits (some 0) q.2 := by
    simpa [stSourceInc,initial,stSourceInitial,stSourceBatchInc,stSourceBest,batch,data,point]
      using hh.2.2.2.2
  exact (not_lt_of_ge ht) (st_source_cutoff_strict_competitive policy hp hc)

theorem actual_one_process (I : Finset (Fin 1)) (policy : STSourcePolicy)
    (hp : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0<epsilon) :
    STSourceProcess (data 0 1) I (fun _ => 1) policy (initial I) (finalState I) := by
  refine ⟨_,STSourceSelect.choose [] [batch] (some (point 0)) [] [] BBExtendedNode.root,?_⟩
  simpa [initial,stSourceInitial,stSourceAnchors,stSourceInc,stSourceBatchInc,
    stSourceBest,batch,finalState] using
    STSourceResolve.empty (w := fun _ => 1) (live := []) (initial_LP_empty I policy hp)

theorem actual_edge_trace (I : Finset (Fin 1)) (policy : STSourcePolicy)
    (hp : policy = .strict ∨ ∃ epsilon, policy = .gap epsilon ∧ 0<epsilon) :
    STSourceInitialize (data 0 1) I (fun _ => 1) (some (initial I)) ∧
    STSourceTrace (data 0 1) I (fun _ => 1) policy 1 (initial I) (finalState I) ∧
    STSourceMicroTrace (data 0 1) I (fun _ => 1) policy 2 (initial I) (finalState I) ∧
    STSourceStop (finalState I) (some (point 0)) := by
  have ht : STSourceTrace (data 0 1) I (fun _ => 1) policy 1 (initial I) (finalState I) :=
    .cons (actual_one_process I policy hp) (.nil _)
  exact ⟨initialization I,ht,st_cutoff_trace_micro (data 0 1) (fun _ => 1) policy ht,
    .exhausted rfl rfl⟩

theorem empty_I_control : STSourceTrace (data 0 1) ∅ (fun _ => 1) .strict
    1 (initial ∅) (finalState ∅) := (actual_edge_trace ∅ .strict (Or.inl rfl)).2.1

theorem full_I_control : STSourceTrace (data 0 1) Finset.univ (fun _ => 1) .strict
    1 (initial Finset.univ) (finalState Finset.univ) :=
  (actual_edge_trace Finset.univ .strict (Or.inl rfl)).2.1

theorem all_source_hypotheses (I : Finset (Fin 1)) :
    Bornology.IsBounded (data 0 1).polyhedron ∧
    ContDiff ℝ 2 (data 0 1).f ∧ ContDiff ℝ 2 (data 0 1).c ∧
    ConvexOn ℝ Set.univ (data 0 1).f ∧
    (∀ j, ConvexOn ℝ Set.univ (fun q => (data 0 1).c q j)) ∧
    STSourceFiberSlater (data 0 1) I :=
  ⟨bounded 0 1,(smooth 0 1).1,(smooth 0 1).2,(convex 0 1).1,(convex 0 1).2,fiber_CQ 0 1 I⟩

theorem empty_X : (data 1 0).polyhedron=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := (polyhedron_iff _ _ q).mp hq
  linarith

theorem empty_X_initialization (I : Finset (Fin 1)) :
    STSourceInitialize (data 1 0) I (fun _ => 1) none ∧ (data 1 0).feasible I=∅ := by
  have hi := st_cutoff_empty_X_initialization (data 1 0) I (fun _ => 1) empty_X
  exact ⟨hi,st_cutoff_empty_initialization_sound (data 1 0) I (fun _ => 1) hi⟩

theorem fractional_X_nonempty : (data (1/2) (1/2)).polyhedron.Nonempty :=
  ⟨point (1/2),(polyhedron_iff _ _ _).mpr ⟨le_rfl,le_rfl⟩⟩

theorem fractional_mixed_empty : stSourceMixedAffine (data (1/2) (1/2)) Finset.univ=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro q ⟨hq,hi⟩
  have hx := (polyhedron_iff _ _ q).mp hq
  have he : q 0=1/2 := le_antisymm hx.2 hx.1
  obtain ⟨k,hk⟩ := hi ⟨0,Finset.mem_univ _⟩
  change (k : ℝ)=q 0 at hk
  have h0 : (0 : ℤ)<k := by exact_mod_cast (show (0 : ℝ)<(k : ℝ) by rw [hk,he]; norm_num)
  have h1 : k<(1 : ℤ) := by exact_mod_cast (show (k : ℝ)<(1 : ℝ) by rw [hk,he]; norm_num)
  omega

theorem fractional_X_initialization :
    STSourceInitialize (data (1/2) (1/2)) Finset.univ (fun _ => 1) none ∧
    (data (1/2) (1/2)).feasible Finset.univ=∅ := by
  have hi := STSourceInitialize.empty (w := fun _ => 1) fractional_mixed_empty
  exact ⟨hi,st_cutoff_empty_initialization_sound _ _ _ hi⟩

theorem invalid_selected_fiber :
    stSourceFiber (data 0 1) Finset.univ (point 2)=∅ ∧
    ((data 0 1).feasible Finset.univ).Nonempty ∧
    ¬ STSourceInitialize (data 0 1) Finset.univ (fun _ => 1) none := by
  have hf : point 0∈(data 0 1).feasible Finset.univ :=
    st_source_batch_feasible _ _ _ batch (batch_valid Finset.univ) rfl
  refine ⟨?_,⟨point 0,hf⟩,?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨hq,he⟩
    have hx := (polyhedron_iff _ _ q).mp hq
    have hy := he ⟨0,Finset.mem_univ _⟩
    change q 0=2 at hy
    linarith
  · intro h
    have he := st_cutoff_empty_initialization_sound _ _ _ h
    rw [he] at hf
    exact hf


def zeroData : BBPolyData 0 0 0 where
  coefficient := Fin.elim0
  rhs := Fin.elim0
  c := fun _ => Fin.elim0
  f := fun _ => 0

def zeroPoint : RealVector 0 := fun _ => 0
def zeroBatch : STSourceBatch 0 := ⟨zeroPoint,false⟩
def zeroInitial : STSourceState (∅ : Finset (Fin 0)) := stSourceInitial zeroData ∅ zeroBatch
def zeroFinal : STSourceState (∅ : Finset (Fin 0)) := ⟨[],[zeroBatch],some zeroPoint,[],none⟩

theorem zero_polyhedron : zeroData.polyhedron=Set.univ := by
  ext q
  simp [BBPolyData.polyhedron,zeroData]

theorem zero_bounded : Bornology.IsBounded zeroData.polyhedron := by
  apply (isCompact_singleton : IsCompact ({zeroPoint} : Set (RealVector 0))).isBounded.subset
  intro q hq
  apply Set.mem_singleton_iff.mpr
  funext i
  exact Fin.elim0 i

theorem zero_batch_valid : stSourceBatchValid zeroData ∅ (fun j => Fin.elim0 j) zeroBatch := by
  refine ⟨?_,?_⟩
  · intro i; exact Fin.elim0 i.val
  · change IsMinimizer (stSourceNonlinearFiber zeroData ∅ zeroPoint) zeroData.f zeroPoint
    refine ⟨⟨⟨?_,fun _ => rfl⟩,fun j => Fin.elim0 j⟩,fun _ _ => le_rfl⟩
    rw [zero_polyhedron]
    exact Set.mem_univ _

theorem zero_initialization : STSourceInitialize zeroData ∅ (fun j => Fin.elim0 j) (some zeroInitial) :=
  .seeded zeroPoint zeroBatch (by rw [zero_polyhedron]; exact Set.mem_univ _)
    zero_batch_valid.1 zero_batch_valid (fun _ => rfl)

theorem zero_source_hypotheses :
    Bornology.IsBounded zeroData.polyhedron ∧ ContDiff ℝ 2 zeroData.f ∧
    ContDiff ℝ 2 zeroData.c ∧ ConvexOn ℝ Set.univ zeroData.f ∧
    (∀ j, ConvexOn ℝ Set.univ (fun q => zeroData.c q j)) ∧ STSourceFiberSlater zeroData ∅ := by
  refine ⟨zero_bounded,contDiff_const,contDiff_const,convexOn_const _ convex_univ,
    fun j => Fin.elim0 j,?_⟩
  intro a ha hn
  obtain ⟨q,hq⟩ := hn
  exact ⟨q,hq.1,fun j => Fin.elim0 j⟩

theorem zero_lp_empty : stSourceLP zeroData (BBExtendedNode.root (ι := {i : Fin 0 // i∈(∅ : Finset (Fin 0))}))
    (stSourceAnchors zeroInitial) .strict (stSourceInc zeroData zeroInitial)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := (st_source_lp_mem_iff zeroData _ _ .strict _ q).mp hq
  have ha : zeroPoint∈stSourceAnchors zeroInitial := by
    simp [zeroInitial,stSourceInitial,stSourceAnchors,zeroBatch]
  have ht := hh.2.2.2.1 zeroPoint ha
  have hc := hh.2.2.2.2
  norm_num [stTangent,zeroData] at ht
  change _ < _ at hc
  have hc' : q.2<0 := by
    simpa [stSourceInc,zeroInitial,stSourceInitial,stSourceBatchInc,stSourceBest,zeroBatch,zeroData,
      STSourcePolicy.Admits] using hc
  linarith

theorem zero_dimensions_actual_trace :
    STSourceInitialize zeroData ∅ (fun j => Fin.elim0 j) (some zeroInitial) ∧
    STSourceTrace zeroData ∅ (fun j => Fin.elim0 j) .strict 1 zeroInitial zeroFinal ∧
    STSourceStop zeroFinal (some zeroPoint) := by
  have hp : STSourceProcess zeroData ∅ (fun j => Fin.elim0 j) .strict zeroInitial zeroFinal := by
    refine ⟨_,STSourceSelect.choose [] [zeroBatch] (some zeroPoint) [] [] BBExtendedNode.root,?_⟩
    simpa [zeroInitial,stSourceInitial,stSourceAnchors,stSourceInc,stSourceBatchInc,
      stSourceBest,zeroBatch,zeroFinal] using
      STSourceResolve.empty (w := fun j => Fin.elim0 j) (live := []) zero_lp_empty
  exact ⟨zero_initialization,.cons hp (.nil _),.exhausted rfl rfl⟩

theorem zero_rows_restoration_impossible (b : STSourceBatch 0)
    (hb : stSourceBatchValid zeroData ∅ (fun j => Fin.elim0 j) b) : b.restoration=false :=
  st_source_zero_rows_no_restoration zeroData ∅ (fun j => Fin.elim0 j) b hb

end Chapter02STSourceEdgeExamples

#print axioms Chapter02STSourceEdgeExamples.polyhedron_iff
#print axioms Chapter02STSourceEdgeExamples.bounded
#print axioms Chapter02STSourceEdgeExamples.smooth
#print axioms Chapter02STSourceEdgeExamples.convex
#print axioms Chapter02STSourceEdgeExamples.fiber_CQ
#print axioms Chapter02STSourceEdgeExamples.integral_zero
#print axioms Chapter02STSourceEdgeExamples.batch_valid
#print axioms Chapter02STSourceEdgeExamples.initialization
#print axioms Chapter02STSourceEdgeExamples.zero_derivative
#print axioms Chapter02STSourceEdgeExamples.zero_tangent
#print axioms Chapter02STSourceEdgeExamples.initial_LP_empty
#print axioms Chapter02STSourceEdgeExamples.actual_one_process
#print axioms Chapter02STSourceEdgeExamples.actual_edge_trace
#print axioms Chapter02STSourceEdgeExamples.empty_I_control
#print axioms Chapter02STSourceEdgeExamples.full_I_control
#print axioms Chapter02STSourceEdgeExamples.all_source_hypotheses
#print axioms Chapter02STSourceEdgeExamples.empty_X
#print axioms Chapter02STSourceEdgeExamples.empty_X_initialization
#print axioms Chapter02STSourceEdgeExamples.fractional_X_nonempty
#print axioms Chapter02STSourceEdgeExamples.fractional_mixed_empty
#print axioms Chapter02STSourceEdgeExamples.fractional_X_initialization
#print axioms Chapter02STSourceEdgeExamples.invalid_selected_fiber
#print axioms Chapter02STSourceEdgeExamples.zero_polyhedron
#print axioms Chapter02STSourceEdgeExamples.zero_bounded
#print axioms Chapter02STSourceEdgeExamples.zero_batch_valid
#print axioms Chapter02STSourceEdgeExamples.zero_initialization
#print axioms Chapter02STSourceEdgeExamples.zero_source_hypotheses
#print axioms Chapter02STSourceEdgeExamples.zero_lp_empty
#print axioms Chapter02STSourceEdgeExamples.zero_dimensions_actual_trace
#print axioms Chapter02STSourceEdgeExamples.zero_rows_restoration_impossible
