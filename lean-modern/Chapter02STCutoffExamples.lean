module

public import Chapter02STSourceDriver
public import Mathlib.Tactic

@[expose] public section

/-! Actual source-initialized cutoff controls. A positive cutoff may return a
strictly suboptimal incumbent within its promised gap. Zero closed cutoff can
repeat an already solved fiber; this is an ablation outside positive epsilon. -/
noncomputable section
open Chapter02
namespace Chapter02STCutoffExamples

def point (y : ℝ) : RealVector 1 := fun _ => y
def indices : Finset (Fin 1) := Finset.univ

def model (upper delta : ℝ) : BBPolyData 1 1 2 where
  coefficient := ![![-1],![1]]
  rhs := ![0,upper]
  c := fun _ _ => -1
  f := fun z => delta*z 0

theorem polyhedron_iff (upper delta : ℝ) (z : RealVector 1) :
    z ∈ (model upper delta).polyhedron ↔ 0≤z 0 ∧ z 0≤upper := by
  simp [BBPolyData.polyhedron,model,Fin.forall_fin_succ]

theorem bounded (upper delta : ℝ) : Bornology.IsBounded (model upper delta).polyhedron := by
  apply (isCompact_Icc : IsCompact (Set.Icc (point 0) (point upper))).isBounded.subset
  intro z hz
  have hh := (polyhedron_iff upper delta z).mp hz
  constructor <;> intro i <;> fin_cases i
  · exact hh.1
  · exact hh.2

theorem smooth (upper delta : ℝ) :
    ContDiff ℝ 2 (model upper delta).f ∧ ContDiff ℝ 2 (model upper delta).c := by
  constructor <;> dsimp [model] <;> fun_prop

theorem convex (upper delta : ℝ) : ConvexOn ℝ Set.univ (model upper delta).f ∧
    ∀ j, ConvexOn ℝ Set.univ (fun z => (model upper delta).c z j) := by
  constructor
  · refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [model]
    ring_nf
    exact le_rfl
  · intro j
    exact convexOn_const _ convex_univ

theorem fiber_CQ (upper delta : ℝ) : STSourceFiberSlater (model upper delta) indices := by
  intro a hi hne
  obtain ⟨z,hz⟩ := hne
  exact ⟨z,hz.1,fun _ => by norm_num [model]⟩

theorem integral (k : ℤ) : STSourceIntegral indices (point k) := fun _ => ⟨k,rfl⟩

theorem objective_tangent (upper delta : ℝ) (a z : RealVector 1) :
    stTangent (model upper delta).f a z = delta*z 0 := by
  have hd : HasFDerivAt (model upper delta).f
      (delta • (ContinuousLinearMap.proj (0 : Fin 1) : RealVector 1 →L[ℝ] ℝ)) a :=
    by simpa [model] using ((ContinuousLinearMap.proj (0 : Fin 1) : RealVector 1 →L[ℝ] ℝ).hasFDerivAt (x := a)).const_mul delta
  rw [stTangent,hd.fderiv]
  change delta*a 0+delta*(z 0-a 0)=delta*z 0
  ring

theorem rows (upper delta : ℝ) (a z : RealVector 1) :
    stSourceRows (model upper delta) a z := by
  intro j
  norm_num [model,stTangent]

def batch (y : ℝ) : STSourceBatch 1 := ⟨point y,false⟩

theorem batch_valid (upper delta : ℝ) (k : ℤ) (hk : 0≤(k:ℝ) ∧ (k:ℝ)≤upper) :
    stSourceBatchValid (model upper delta) indices (fun _ => 1) (batch k) := by
  refine ⟨integral k,?_⟩
  change IsMinimizer (stSourceNonlinearFiber (model upper delta) indices (point k))
    (model upper delta).f (point k)
  refine ⟨⟨⟨(polyhedron_iff upper delta _).mpr hk,fun _ => rfl⟩,
    fun _ => by norm_num [model]⟩,?_⟩
  intro z hz
  have he := hz.1.2 ⟨0,Finset.mem_univ 0⟩
  change z 0=(k:ℝ) at he
  simp [model,point,he]

theorem lp_iff (upper delta : ℝ) (H : List (RealVector 1)) (hH : H≠[])
    (policy : STSourcePolicy) (inc : Option ℝ) (q : RealVector 1 × ℝ) :
    q ∈ stSourceLP (I := indices) (model upper delta) BBExtendedNode.root H policy inc ↔
      (0≤q.1 0 ∧ q.1 0≤upper) ∧ delta*q.1 0≤q.2 ∧ policy.Admits inc q.2 := by
  rw [st_source_lp_mem_iff,polyhedron_iff]
  constructor
  · rintro ⟨hX,hB,hr,ho,hcut⟩
    obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil _ hH
    exact ⟨hX,by simpa only [objective_tangent] using ho a ha,hcut⟩
  · rintro ⟨hX,ho,hcut⟩
    exact ⟨hX,BBExtendedNode.holds_root _,fun a _ => rows upper delta a q.1,
      fun a _ => by simpa only [objective_tangent] using ho,hcut⟩

def p2Initial : STSourceState indices :=
  stSourceInitial (model 1 (1/2)) indices (batch 1)
def p2Final : STSourceState indices := ⟨[],[batch 1],some (point 1),[],none⟩

theorem p2_initialization :
    STSourceInitialize (model 1 (1/2)) indices (fun _ => 1) (some p2Initial) := by
  exact .seeded (point 1) (batch 1) ((polyhedron_iff _ _ _).mpr (by norm_num [point]))
    (by simpa using integral 1) (by simpa using batch_valid 1 (1/2) 1 (by norm_num)) (fun _ => rfl)

theorem p2_lp_empty : stSourceLP (I := indices) (model 1 (1/2)) BBExtendedNode.root
    (stSourceAnchors p2Initial) (.gap 1) (stSourceInc (model 1 (1/2)) p2Initial) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hH : stSourceAnchors p2Initial≠[] := by simp [p2Initial,stSourceInitial,stSourceAnchors]
  have hh := (lp_iff 1 (1/2) _ hH (.gap 1) _ q).mp hq
  norm_num [p2Initial,stSourceInitial,stSourceInc,stSourceBatchInc,batch,
    stSourceBest,model,point,STSourcePolicy.Admits] at hh
  linarith [hh.1.1,hh.2.1,hh.2.2]

theorem p2_process : STSourceProcess (model 1 (1/2)) indices (fun _ => 1) (.gap 1)
    p2Initial p2Final := by
  refine ⟨_,STSourceSelect.choose [] [batch 1] (some (point 1)) [] [] BBExtendedNode.root,?_⟩
  exact .empty p2_lp_empty

theorem p2_trace : STSourceTrace (model 1 (1/2)) indices (fun _ => 1) (.gap 1)
    1 p2Initial p2Final := .cons p2_process (.nil _)

theorem p2_stop : STSourceStop p2Final (some (point 1)) := .exhausted rfl rfl

theorem p2_zero_feasible : point 0 ∈ (model 1 (1/2)).feasible indices := by
  exact ⟨(polyhedron_iff _ _ _).mpr (by norm_num [point]),
    fun _ => by norm_num [model],fun i => ⟨0,by simp [point]⟩⟩

theorem p2_true_optimum : IsMinimizer ((model 1 (1/2)).feasible indices)
    (model 1 (1/2)).f (point 0) := by
  refine ⟨p2_zero_feasible,?_⟩
  intro z hz
  have hx := (polyhedron_iff 1 (1/2) z).mp hz.1
  change (1/2:ℝ)*0≤(1/2)*z 0
  linarith [hx.1]

theorem p2_return_nonoptimal : ¬ IsMinimizer ((model 1 (1/2)).feasible indices)
    (model 1 (1/2)).f (point 1) := by
  intro h
  have hh := h.2 (point 0) p2_zero_feasible
  norm_num [model,point] at hh

theorem p2_return_gap : STSourceReturnCertificate (model 1 (1/2)) indices (.gap 1)
    (some (point 1)) := by
  have hi := (st_cutoff_initialization_invariant (model 1 (1/2)) indices (fun _ => 1)
    (.gap 1) p2_initialization).1
  have hconv := convex 1 (1/2)
  have hsmooth := smooth 1 (1/2)
  have hs := st_cutoff_trace_invariant (model 1 (1/2)) (fun _ => 1) (.gap 1)
    hconv.1 (hsmooth.1.differentiable (by norm_num)) hconv.2
    (fun j => ((contDiff_apply ℝ (fun _ => ℝ) j).comp hsmooth.2).differentiable (by norm_num)) hi p2_trace
  exact st_source_stop_sound _ _ _ hs p2_stop

def p4History (k : ℕ) : List (STSourceBatch 1) := List.replicate (k+1) (batch 0)
def p4State (k : ℕ) : STSourceState indices :=
  ⟨[],p4History k,some (point 0),[BBExtendedNode.root],none⟩

theorem p4_history_succ (k : ℕ) : p4History (k+1)=p4History k++[batch 0] := by
  simp only [p4History,List.replicate_add,List.replicate_one]

theorem p4_initialization :
    STSourceInitialize (model 0 0) indices (fun _ => 1) (some (p4State 0)) := by
  have hh := STSourceInitialize.seeded (w := fun _ => 1) (point 0) (batch 0)
    ((polyhedron_iff 0 0 _).mpr (by norm_num [point])) (by simpa using integral 0)
    (by simpa using batch_valid 0 0 0 (by norm_num)) (fun _ => rfl)
  simpa [p4State,p4History,stSourceInitial,stSourceBatchInc,batch,stSourceBest] using hh

theorem p4_lp_iff (k : ℕ) (policy : STSourcePolicy) (q : RealVector 1 × ℝ) :
    q ∈ stSourceLP (I := indices) (model 0 0) BBExtendedNode.root
      (stSourceAnchors (p4State k)) policy (stSourceInc (model 0 0) (p4State k)) ↔
      q.1 0=0 ∧ 0≤q.2 ∧ policy.Admits (some 0) q.2 := by
  rw [lp_iff 0 0 _ (by simp [stSourceAnchors,p4State,p4History])]
  simp only [zero_mul,stSourceInc,p4State,Option.map_some,model]
  constructor
  · rintro ⟨hx,ho,hc⟩; exact ⟨le_antisymm hx.2 hx.1,ho,hc⟩
  · rintro ⟨hx,ho,hc⟩; exact ⟨by simp [hx],ho,hc⟩

theorem p4_lp_minimum (k : ℕ) : IsMinimizer
    (stSourceLP (I := indices) (model 0 0) BBExtendedNode.root (stSourceAnchors (p4State k))
      (.gap 0) (stSourceInc (model 0 0) (p4State k))) Prod.snd (point 0,0) := by
  refine ⟨(p4_lp_iff k (.gap 0) _).mpr (by norm_num [point,STSourcePolicy.Admits]),?_⟩
  intro q hq
  exact ((p4_lp_iff k (.gap 0) q).mp hq).2.1

theorem p4_process (k : ℕ) : STSourceProcess (model 0 0) indices (fun _ => 1) (.gap 0)
    (p4State k) (p4State (k+1)) := by
  refine ⟨_,STSourceSelect.choose [] (p4History k) (some (point 0)) [] [] BBExtendedNode.root,?_⟩
  have hh := STSourceResolve.callback (live := []) (p4_lp_minimum k) (by simpa using integral 0)
    (b := batch 0) (by simpa using batch_valid 0 0 0 (by norm_num)) (fun _ => rfl)
  simpa [p4State,p4_history_succ,stSourceBatchInc,batch,stSourceBest,model,point] using hh

theorem p4_traces (k : ℕ) : STSourceTrace (model 0 0) indices (fun _ => 1) (.gap 0)
    k (p4State 0) (p4State k) := by
  induction k with
  | zero => exact .nil _
  | succ k ih => exact st_cutoff_trace_append_step _ _ _ ih (p4_process k)

theorem p4_no_stop (k : ℕ) (out : Option (RealVector 1)) : ¬ STSourceStop (p4State k) out := by
  intro h
  cases h with
  | exhausted hr he => simp [p4State] at he

theorem p4_strict_empty (k : ℕ) : stSourceLP (I := indices) (model 0 0) BBExtendedNode.root
    (stSourceAnchors (p4State k)) .strict (stSourceInc (model 0 0) (p4State k)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := (p4_lp_iff k .strict q).mp hq
  exact (not_lt_of_ge hh.2.1) hh.2.2

theorem p4_positive_gap_empty (k : ℕ) (epsilon : ℝ) (he : 0<epsilon) :
    stSourceLP (I := indices) (model 0 0) BBExtendedNode.root
      (stSourceAnchors (p4State k)) (.gap epsilon) (stSourceInc (model 0 0) (p4State k)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := (p4_lp_iff k (.gap epsilon) q).mp hq
  have hc : q.2≤0-epsilon := hh.2.2
  linarith [hh.2.1]


theorem p2_exact_gap : (model 1 (1/2)).f (point 1)-(model 1 (1/2)).f (point 0)=1/2 ∧
    (1/2:ℝ)<1 := by norm_num [model,point]

theorem p4_micro_traces (k : ℕ) : STSourceMicroTrace (model 0 0) indices (fun _ => 1)
    (.gap 0) (2*k) (p4State 0) (p4State k) :=
  st_cutoff_trace_micro _ _ _ (p4_traces k)

theorem p4_history_actual (k : ℕ) : (p4State k).history.length=k+1 ∧
    ∀ b∈(p4State k).history, stSourceBatchValid (model 0 0) indices (fun _ => 1) b := by
  constructor
  · simp [p4State,p4History]
  · intro b hb
    have he : b=batch 0 := (List.mem_replicate.mp hb).2
    rw [he]
    simpa using batch_valid 0 0 0 (by norm_num)

theorem p2_full_control :
    Bornology.IsBounded (model 1 (1/2)).polyhedron ∧
    ContDiff ℝ 2 (model 1 (1/2)).f ∧ ContDiff ℝ 2 (model 1 (1/2)).c ∧
    ConvexOn ℝ Set.univ (model 1 (1/2)).f ∧
    (∀ j,ConvexOn ℝ Set.univ (fun z => (model 1 (1/2)).c z j)) ∧
    STSourceFiberSlater (model 1 (1/2)) indices ∧
    STSourceInitialize (model 1 (1/2)) indices (fun _ => 1) (some p2Initial) ∧
    STSourceTrace (model 1 (1/2)) indices (fun _ => 1) (.gap 1) 1 p2Initial p2Final ∧
    STSourceStop p2Final (some (point 1)) ∧
    STSourceReturnCertificate (model 1 (1/2)) indices (.gap 1) (some (point 1)) ∧
    ¬ IsMinimizer ((model 1 (1/2)).feasible indices) (model 1 (1/2)).f (point 1) :=
  ⟨bounded 1 (1/2),(smooth 1 (1/2)).1,(smooth 1 (1/2)).2,
    (convex 1 (1/2)).1,(convex 1 (1/2)).2,fiber_CQ 1 (1/2),p2_initialization,
    p2_trace,p2_stop,p2_return_gap,p2_return_nonoptimal⟩

theorem p4_full_zero_ablation :
    Bornology.IsBounded (model 0 0).polyhedron ∧
    ContDiff ℝ 2 (model 0 0).f ∧ ContDiff ℝ 2 (model 0 0).c ∧
    ConvexOn ℝ Set.univ (model 0 0).f ∧
    (∀ j,ConvexOn ℝ Set.univ (fun z => (model 0 0).c z j)) ∧
    STSourceFiberSlater (model 0 0) indices ∧
    STSourceInitialize (model 0 0) indices (fun _ => 1) (some (p4State 0)) ∧
    (∀ k, STSourceProcess (model 0 0) indices (fun _ => 1) (.gap 0) (p4State k) (p4State (k+1))) ∧
    ∀ k out, ¬ STSourceStop (p4State k) out :=
  ⟨bounded 0 0,(smooth 0 0).1,(smooth 0 0).2,(convex 0 0).1,(convex 0 0).2,
    fiber_CQ 0 0,p4_initialization,p4_process,p4_no_stop⟩

end Chapter02STCutoffExamples

#print axioms Chapter02STCutoffExamples.polyhedron_iff
#print axioms Chapter02STCutoffExamples.bounded
#print axioms Chapter02STCutoffExamples.smooth
#print axioms Chapter02STCutoffExamples.convex
#print axioms Chapter02STCutoffExamples.fiber_CQ
#print axioms Chapter02STCutoffExamples.integral
#print axioms Chapter02STCutoffExamples.objective_tangent
#print axioms Chapter02STCutoffExamples.rows
#print axioms Chapter02STCutoffExamples.batch_valid
#print axioms Chapter02STCutoffExamples.lp_iff
#print axioms Chapter02STCutoffExamples.p2_initialization
#print axioms Chapter02STCutoffExamples.p2_lp_empty
#print axioms Chapter02STCutoffExamples.p2_process
#print axioms Chapter02STCutoffExamples.p2_trace
#print axioms Chapter02STCutoffExamples.p2_stop
#print axioms Chapter02STCutoffExamples.p2_zero_feasible
#print axioms Chapter02STCutoffExamples.p2_true_optimum
#print axioms Chapter02STCutoffExamples.p2_return_nonoptimal
#print axioms Chapter02STCutoffExamples.p2_return_gap
#print axioms Chapter02STCutoffExamples.p4_history_succ
#print axioms Chapter02STCutoffExamples.p4_initialization
#print axioms Chapter02STCutoffExamples.p4_lp_iff
#print axioms Chapter02STCutoffExamples.p4_lp_minimum
#print axioms Chapter02STCutoffExamples.p4_process
#print axioms Chapter02STCutoffExamples.p4_traces
#print axioms Chapter02STCutoffExamples.p4_no_stop
#print axioms Chapter02STCutoffExamples.p4_strict_empty
#print axioms Chapter02STCutoffExamples.p4_positive_gap_empty
#print axioms Chapter02STCutoffExamples.p2_exact_gap
#print axioms Chapter02STCutoffExamples.p4_micro_traces
#print axioms Chapter02STCutoffExamples.p4_history_actual
#print axioms Chapter02STCutoffExamples.p2_full_control
#print axioms Chapter02STCutoffExamples.p4_full_zero_ablation
