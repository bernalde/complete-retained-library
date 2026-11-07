module

public import Chapter07SingleTreeAugment
public import Chapter07SingleTreeAuxiliary
public import Chapter07
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! Exact source-state controls for the explicitly qualified single-tree repair.
The core processes its own node fiber before one optional extra batch. -/
noncomputable section
open Set Chapter02
open scoped BigOperators
namespace Chapter07.SingleTreeControls
open SingleTree

def I : Finset (Fin 2) := SingleTreeSource.integerIndices 1 1
def partition : BBPartition I 1 1 := SingleTreeSource.partition 1 1
def yi : {i : Fin 2 // i ∈ I} := ⟨1, by simp [I,SingleTreeSource.integerIndices]⟩
def point (x y : ℝ) : RealVector 2 := ![x,y]
def coord (i : Fin 2) : RealVector 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i

theorem integer_index (i : {i : Fin 2 // i ∈ I}) : i.val = 1 := by
  have h := i.property
  simp only [I,SingleTreeSource.integerIndices,Finset.mem_filter,Finset.mem_univ,true_and] at h
  apply Fin.ext
  have hi := i.val.isLt
  omega

def d : BBPolyData 2 1 4 where
  coefficient := ![![-1,0],![1,0],![0,-1],![0,1]]
  rhs := ![0,1,0,2]
  c := fun z _ => (z 0)^2-1
  f := fun z => z 0-z 1

theorem hard_iff (z : RealVector 2) : z ∈ d.polyhedron ↔
    0 ≤ z 0 ∧ z 0 ≤ 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ 2 := by
  simp [BBPolyData.polyhedron,d,Fin.forall_fin_succ,Fin.sum_univ_succ,and_assoc]

theorem hard_bounded : Bornology.IsBounded d.polyhedron := by
  apply (isCompact_Icc : IsCompact (Icc (point 0 0) (point 1 2))).isBounded.subset
  intro z hz
  obtain ⟨hx0,hx1,hy0,hy1⟩ := (hard_iff z).mp hz
  constructor <;> intro i <;> fin_cases i <;> simp_all [point]

theorem enclosing : d.Encloses 2 := by
  refine ⟨by norm_num,?_⟩
  intro z hz i
  obtain ⟨hx0,hx1,hy0,hy1⟩ := (hard_iff z).mp hz
  apply abs_le.mpr
  fin_cases i <;> dsimp <;> constructor <;> linarith

theorem C2 : ContDiff ℝ 2 d.f ∧ ContDiff ℝ 2 d.c := by
  constructor <;> dsimp [d] <;> fun_prop

theorem convex : ConvexOn ℝ univ d.f ∧ ∀ j, ConvexOn ℝ univ (fun z => d.c z j) := by
  constructor
  · refine ⟨convex_univ,?_⟩
    intro x _ y _ a b _ _ _
    dsimp [d]
    ring_nf
    exact le_rfl
  · intro j
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    change (a*x 0+b*y 0)^2-1 ≤ a*((x 0)^2-1)+b*((y 0)^2-1)
    have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0-y 0))
    have hb' : b=1-a := by linarith
    subst b
    nlinarith

theorem fiber_slater : STSourceFiberSlater d I := by
  intro a hi hn
  obtain ⟨z,hz⟩ := hn
  have he := hz.1.2 yi
  change z 1=a 1 at he
  obtain ⟨_,_,hy0,hy1⟩ := (hard_iff z).mp hz.1.1
  refine ⟨point 0 (a 1),⟨(hard_iff _).mpr ?_,?_⟩,?_⟩
  · simp [point]; constructor <;> linarith
  · intro i; simp [integer_index i,point]
  · intro j; norm_num [d,point]

theorem point_integral (y : ℤ) : STSourceIntegral I (point 0 (y:ℝ)) := by
  intro i
  exact ⟨y,by simp [integer_index i,point]⟩

def batch (y : ℤ) : STSourceBatch 2 := ⟨point 0 (y:ℝ),false⟩

theorem batch_valid (y : ℤ) (hy0 : (0:ℝ) ≤ y) (hy2 : (y:ℝ) ≤ 2) :
    stSourceBatchValid d I (fun _ => 1) (batch y) := by
  refine ⟨point_integral y,?_⟩
  change IsMinimizer (stSourceNonlinearFiber d I (point 0 (y:ℝ))) d.f (point 0 (y:ℝ))
  refine ⟨⟨⟨(hard_iff _).mpr ?_,fun _ => rfl⟩,?_⟩,?_⟩
  · simpa [point] using And.intro (by norm_num : (0:ℝ) ≤ 0) (And.intro (by norm_num : (0:ℝ) ≤ 1) (And.intro hy0 hy2))
  · intro j; norm_num [d,point]
  · intro z hz
    have hx := (hard_iff z).mp hz.1.1
    have hy := hz.1.2 yi
    change z 1=(y:ℝ) at hy
    change 0-(y:ℝ) ≤ z 0-z 1
    linarith

theorem batch0_valid : stSourceBatchValid d I (fun _ => 1) (batch 0) :=
  batch_valid 0 (by norm_num) (by norm_num)
theorem batch2_valid : stSourceBatchValid d I (fun _ => 1) (batch 2) :=
  batch_valid 2 (by norm_num) (by norm_num)

theorem objective_derivative (a : RealVector 2) : HasFDerivAt d.f (coord 0-coord 1) a :=
  (coord 0).hasFDerivAt.sub (coord 1).hasFDerivAt

theorem row_derivative (a : RealVector 2) (j : Fin 1) :
    HasFDerivAt (fun z => d.c z j) ((2*a 0) • coord 0) a := by
  have h := ((hasDerivAt_pow 2 (a 0)).comp_hasFDerivAt a (coord 0).hasFDerivAt).sub_const 1
  simpa [d,coord,Function.comp_def] using h

theorem objective_tangent (a z : RealVector 2) : stTangent d.f a z=z 0-z 1 := by
  rw [stTangent,(objective_derivative a).fderiv]
  simp [d,coord]
  ring

theorem zero_rows (y : ℝ) (z : RealVector 2) : stSourceRows d (point 0 y) z := by
  intro j
  rw [(row_derivative (point 0 y) j).fderiv]
  norm_num [d,point,coord]

def start : STSourceState I := stSourceInitial d I (batch 0)
def selected : STSourceState I := ⟨[],[batch 0],some (point 0 0),[],some BBExtendedNode.root⟩
def core : STSourceState I := ⟨[],[batch 0,batch 2],some (point 0 2),[BBExtendedNode.root],none⟩
def augmented : STSourceState I := appendAux d core (some (batch 2))
def q : RealVector 2 × ℝ := (point 0 2,-2)

theorem initialization : STSourceInitialize d I (fun _ => 1) (some start) :=
  .seeded (point 0 0) (batch 0) ((hard_iff _).mpr (by norm_num [point]))
    (by simpa using point_integral 0) batch0_valid (by intro i; simp [batch,point])

theorem start_invariant : STSourceInvariant d I (fun _ => 1) .strict start :=
  (st_cutoff_initialization_invariant d I (fun _ => 1) .strict initialization).1

theorem selection : STSourceSelect start selected := by
  simpa [start,stSourceInitial,selected,stSourceBatchInc,batch,stSourceBest,point] using
    (STSourceSelect.choose (I:=I) [] [batch 0] (some (point 0 0)) [] [] BBExtendedNode.root)

theorem initial_lp_iff (p : RealVector 2 × ℝ) :
    p ∈ stSourceLP (I:=I) d BBExtendedNode.root [point 0 0] .strict (some 0) ↔
      p.1 ∈ d.polyhedron ∧ p.1 0-p.1 1 ≤ p.2 ∧ p.2 < 0 := by
  rw [st_source_lp_mem_iff]
  simp [BBExtendedNode.root,BBExtendedNode.Holds,zero_rows,stObjectiveCuts,
    objective_tangent,STSourcePolicy.Admits]

theorem initial_lp_minimum :
    IsMinimizer (stSourceLP (I:=I) d BBExtendedNode.root [point 0 0] .strict (some 0)) Prod.snd q := by
  refine ⟨(initial_lp_iff q).mpr ⟨(hard_iff _).mpr ?_,?_,?_⟩,?_⟩
  · norm_num [q,point]
  · norm_num [q,point]
  · norm_num [q]
  · intro p hp
    obtain ⟨hx,hf,_⟩ := (initial_lp_iff p).mp hp
    obtain ⟨hx0,_,_,hy2⟩ := (hard_iff p.1).mp hx
    change (-2:ℝ) ≤ p.2
    linarith

theorem core_callback : Callback d I (fun _ => 1) .strict selected core := by
  have h := Callback.actual (D:=d) (I:=I) (w:=fun _ => 1) (policy:=.strict)
    (seeds:=[]) (H:=[batch 0]) (inc:=some (point 0 0)) (live:=[])
    (B:=BBExtendedNode.root) (q:=q) (b:=batch 2)
    (by simpa [batch,point,d] using initial_lp_minimum)
    (by simpa [q] using point_integral 2) batch2_valid (fun _ => rfl)
  simpa [selected,core,stSourceBatchInc,batch,stSourceBest,d,point] using h

theorem core_process : STSourceProcess d I (fun _ => 1) .strict start core :=
  ⟨selected,selection,core_callback.toResolve⟩

theorem extra_process : Process d I (fun _ => 1) .strict start augmented :=
  .aux selection core_callback (batch 2) batch2_valid

theorem candidate_feasible : point 0 2 ∈ d.feasible I :=
  st_source_batch_feasible d I (fun _ => 1) (batch 2) batch2_valid rfl

theorem retained_best : augmented.incumbent=some (point 0 2) := by
  simp [augmented,appendAux,core,stSourceBatchInc,batch,stSourceBest]

theorem retained_frontier : stSourceFrontier augmented=stSourceFrontier core :=
  appendAux_frontier d core (some (batch 2))

theorem repeated_key : stSourceKey partition (batch 2).anchor ∈ stSourceSeen partition core.history := by
  classical
  simp [stSourceSeen,core]

theorem repeated_potential : stSourcePotential partition 2 augmented=stSourcePotential partition 2 core :=
  appendAux_repeated_key_potential d partition 2 core (batch 2) repeated_key

theorem augmented_invariant : STSourceInvariant d I (fun _ => 1) .strict augmented :=
  process_invariant d (fun _ => 1) .strict convex.1 (C2.1.differentiable (by norm_num))
    convex.2 (fun j => ((contDiff_pi.mp C2.2 j).differentiable (by norm_num))) start_invariant extra_process

theorem macro_progress : stSourcePotential partition 2 augmented+1 ≤ stSourcePotential partition 2 start :=
  process_potential_drop d partition 2 enclosing (fun _ => 1) (fun _ => by norm_num)
    .strict (Or.inl rfl) convex.1 (C2.1.differentiable (by norm_num))
    convex.2 (fun j => (contDiff_pi.mp C2.2 j).differentiable (by norm_num)) fiber_slater start_invariant extra_process


theorem actual_post_core_bounds : stSourceInc d core=some (-2) ∧
    ∀ z ∈ d.polyhedron, (-2:ℝ) ≤ d.f z := by
  constructor
  · norm_num [stSourceInc,core,d,point]
  · intro z hz
    obtain ⟨hx0,_,_,hy2⟩ := (hard_iff z).mp hz
    change (-2:ℝ) ≤ z 0-z 1
    linarith

theorem actual_candidate_retention : point 0 2 ∈ d.feasible I ∧
    augmented.incumbent=some (point 0 2) ∧ d.f (point 0 2)=-2 :=
  ⟨candidate_feasible,retained_best,by norm_num [d,point]⟩

/-- Post-core U=L=-2, so the auxiliary cap is -2 for every alpha. -/
theorem post_core_cap (alpha : ℝ) : (1-alpha)*(-2)+alpha*(-2)=(-2:ℝ) := by ring

def postHistory : STObjectiveHistory (RealVector 2) := ⟨point 0 0,[point 0 2]⟩

theorem post_history : postHistory.anchors=stSourceAnchors core := by
  simp [postHistory,STObjectiveHistory.anchors,stSourceAnchors,core,batch]

def distance (z : RealVector 2) : ℝ := |z 0|+|z 1-2|

theorem distance_continuous : Continuous distance := by unfold distance; fun_prop

theorem q_capped : q ∈ SingleTreeAuxiliary.capped d I postHistory (-2) := by
  rw [SingleTreeAuxiliary.capped_iff,st_objective_envelope_le_iff]
  refine ⟨⟨(hard_iff _).mpr ?_,?_,?_⟩,?_,?_⟩
  · norm_num [q,point]
  · simpa [q] using point_integral 2
  · intro a ha
    simp [postHistory,STObjectiveHistory.anchors] at ha
    rcases ha with rfl | rfl <;> exact zero_rows _ _
  · intro a ha
    rw [objective_tangent]
    norm_num [q,point]
  · norm_num [q]

theorem q_auxiliary_minimum :
    IsMinimizer (SingleTreeAuxiliary.capped d I postHistory (-2)) (fun p => distance p.1) q := by
  refine ⟨q_capped,?_⟩
  intro p hp
  norm_num [distance,q,point]
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

def extra_reply : SingleTreeAuxiliary.Reply d I (fun _ => 1) postHistory (-2) distance :=
  .processed q q_auxiliary_minimum (batch 2) batch2_valid (fun _ => rfl)

theorem actual_nonempty_extra : extra_reply.extra=some (batch 2) ∧
    Process d I (fun _ => 1) .strict start augmented ∧
    augmented.incumbent=some (point 0 2) ∧ stSourceFrontier augmented=stSourceFrontier core ∧
    stSourcePotential partition 2 augmented=stSourcePotential partition 2 core :=
  ⟨rfl,extra_process,retained_best,retained_frontier,repeated_potential⟩


namespace WeakBound

def d : BBPolyData 1 0 2 where
  coefficient := ![![-1],![1]]
  rhs := ![-(1/2),1]
  c := fun _ j => Fin.elim0 j
  f := fun z => z 0

def I : Finset (Fin 1) := Finset.univ
def coordinate : RealVector 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
def anchor : RealVector 1 := fun _ => 1
def history : STObjectiveHistory (RealVector 1) := ⟨anchor,[]⟩

theorem hard_iff (z : RealVector 1) : z ∈ d.polyhedron ↔ (1/2:ℝ) ≤ z 0 ∧ z 0 ≤ 1 := by
  simp [BBPolyData.polyhedron,d,Fin.forall_fin_succ,Fin.sum_univ_succ]

theorem objective_tangent (a z : RealVector 1) : stTangent d.f a z=z 0 := by
  have h : HasFDerivAt d.f coordinate a := coordinate.hasFDerivAt
  rw [stTangent,h.fderiv]
  simp [d,coordinate]

/-- Exact adapter to the earlier accepted weak-bound empty-level witness. -/
theorem capped_empty :
    ¬ (SingleTreeAuxiliary.capped d I history (Chapter06.Level (1/2) 1 (1/2))).Nonempty := by
  rintro ⟨p,hp⟩
  have he := (SingleTreeAuxiliary.capped_iff d I history _ p).mp hp
  have hh := (hard_iff p.1).mp he.1.1
  obtain ⟨y,hy⟩ := he.1.2.1 ⟨0,by simp [I]⟩
  have ho := (st_objective_envelope_le_iff d.f history p.1 p.2).mp he.2.1
  have ht := ho anchor (by simp [history,STObjectiveHistory.anchors])
  rw [objective_tangent] at ht
  change (y:ℝ)=p.1 0 at hy
  apply Chapter07.weak_tree_bound_empty_level
  exact ⟨y,by linarith [hh.1],by linarith [hh.2],by linarith [he.2.2]⟩

def reply : SingleTreeAuxiliary.Reply d I (fun j => Fin.elim0 j)
    history (Chapter06.Level (1/2) 1 (1/2)) (fun _ => 0) := .skipped capped_empty

theorem no_extra : reply.extra=none := rfl

end WeakBound

/-- Empty auxiliary selection cannot erase a completed ordinary process. This
is a generic adapter, with the unchanged accepted weak-bound control above
providing an actual skipped reply. -/
theorem none_fallback {N n m l r : ℕ} {J : Finset (Fin N)}
    (D : BBPolyData N l r) (P : BBPartition J n m) (K : ℝ)
    (w : Fin l → ℝ) (policy : STSourcePolicy) {s t : STSourceState J}
    (hc : STSourceProcess D J w policy s t) :
    Process D J w policy s (appendAux D t none) ∧ appendAux D t none=t ∧
    stSourcePotential P K (appendAux D t none)=stSourcePotential P K t :=
  ⟨.core hc,rfl,rfl⟩


/-- The concrete weak-bound skipped reply supplies the none adapter itself. -/
theorem weak_reply_fallback {n m : ℕ} (P : BBPartition WeakBound.I n m) (K : ℝ)
    (policy : STSourcePolicy) {s t : STSourceState WeakBound.I}
    (hc : STSourceProcess WeakBound.d WeakBound.I (fun j => Fin.elim0 j) policy s t) :
    Process WeakBound.d WeakBound.I (fun j => Fin.elim0 j) policy s
      (appendAux WeakBound.d t WeakBound.reply.extra) ∧
    appendAux WeakBound.d t WeakBound.reply.extra=t ∧
    stSourcePotential P K (appendAux WeakBound.d t WeakBound.reply.extra)=stSourcePotential P K t :=
  none_fallback WeakBound.d P K (fun j => Fin.elim0 j) policy hc

end Chapter07.SingleTreeControls

#print axioms Chapter07.SingleTreeControls.hard_bounded
#print axioms Chapter07.SingleTreeControls.C2
#print axioms Chapter07.SingleTreeControls.convex
#print axioms Chapter07.SingleTreeControls.fiber_slater
#print axioms Chapter07.SingleTreeControls.batch_valid
#print axioms Chapter07.SingleTreeControls.initialization
#print axioms Chapter07.SingleTreeControls.initial_lp_minimum
#print axioms Chapter07.SingleTreeControls.core_callback
#print axioms Chapter07.SingleTreeControls.augmented_invariant
#print axioms Chapter07.SingleTreeControls.macro_progress
#print axioms Chapter07.SingleTreeControls.q_auxiliary_minimum
#print axioms Chapter07.SingleTreeControls.actual_nonempty_extra

#print axioms Chapter07.SingleTreeControls.WeakBound.capped_empty
#print axioms Chapter07.SingleTreeControls.none_fallback

#print axioms Chapter07.SingleTreeControls.weak_reply_fallback

#print axioms Chapter07.SingleTreeControls.actual_post_core_bounds
#print axioms Chapter07.SingleTreeControls.actual_candidate_retention
