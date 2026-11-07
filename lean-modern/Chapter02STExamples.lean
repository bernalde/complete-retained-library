module

public import Chapter02STDriver
public import Chapter02SourceRestorationExamples
public import Chapter02OAEdgeExamples

@[expose] public section

/-! Actual source-initialized controls for the main thesis single-tree repair.
The strict-worse repeated-callback relation is a separately named reading,
not the weak process and not a claim about every literature algorithm. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter02STExamples

def pt (x t y : ℝ) : Point 2 1 := (![x,t],fun _ => y)
def cx : Point 2 1 →L[ℝ] ℝ := Chapter02CPExamples.coord 0

def tieModel : ModelData 2 1 1 6 where
  g := fun _ p => (p.1 0)^2-1
  A := ![![1,0],![-1,0],![0,1],![0,-1],![0,-1],![0,-1]]
  B := ![fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => -1,fun _ => 1]
  rhs := ![2,2,1,1,1/2,1]
  c1 := ![0,1]
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

theorem tie_objective (p : Point 2 1) : tieModel.objective p=p.1 1 := by
  simp [tieModel,ModelData.objective,LinearForm,Fin.sum_univ_two]

theorem tie_linear (p : Point 2 1) : p∈tieModel.linearRegion ↔
    -2≤p.1 0 ∧ p.1 0≤2 ∧ -1≤p.1 1 ∧ p.1 1≤1 ∧
      -p.2 0-1/2≤p.1 1 ∧ p.2 0-1≤p.1 1 := by
  simp [ModelData.linearRegion,tieModel,LinearForm,Fin.sum_univ_two,Fin.forall_fin_succ]
  constructor <;> intro h <;> rcases h with ⟨h1,h2,h3,h4,h5,h6⟩ <;>
    constructor <;> try linarith
  · exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem tie_base_compact : IsCompact (bbMixedBase tieModel tieModel.lo tieModel.hi) := by
  change IsCompact (tieModel.linearRegion ∩ IntegerCylinder (n:=2) tieModel.lo tieModel.hi)
  apply (isCompact_Icc : IsCompact (Set.Icc (pt (-2) (-1) 0) (pt 2 1 1))).of_isClosed_subset
    (Chapter02CPExamples.base_closed _)
  rintro p ⟨hp,y,hy,heq⟩
  obtain ⟨hx0,hx1,ht0,ht1,_,_⟩ := (tie_linear p).mp hp
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i <;> simpa [pt] using (by assumption : _)
  · intro i; rw [heq]; exact (hy i).1
  · intro i; fin_cases i <;> simpa [pt] using (by assumption : _)
  · intro i; rw [heq]; exact (hy i).2

theorem tie_rows_convex : ∀j,ConvexOn ℝ Set.univ (tieModel.g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have hh := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 0-q.1 0))
  simp only [tieModel,Prod.fst_add,Prod.smul_fst,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have he : t=1-s := by linarith
  rw [he] at hh ⊢
  nlinarith

theorem tie_rows_C2 : ∀j,ContDiff ℝ 2 (tieModel.g j) := by
  intro j
  exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 2)).comp contDiff_fst).pow 2).sub contDiff_const

theorem tie_rows_diff : ∀j,Differentiable ℝ (tieModel.g j) :=
  fun j => (tie_rows_C2 j).differentiable (by norm_num)

theorem tie_derivative (p : Point 2 1) (j : Fin 1) :
    HasFDerivAt (tieModel.g j) ((2*p.1 0) • cx) p := by
  have hh := ((hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p cx.hasFDerivAt).sub_const 1
  simpa [tieModel,cx,Chapter02CPExamples.coord,Function.comp_def] using hh

theorem tie_fiber_slater : OAFiberSlater tieModel := by
  intro y hy _
  have hy0 := (hy 0).1
  have hy1 := (hy 0).2
  change (0 : ℝ)≤(y 0 : ℝ) at hy0
  change (y 0 : ℝ)≤1 at hy1
  refine ⟨pt 0 1 (y 0),⟨(tie_linear _).mpr ?_,?_⟩,?_⟩
  · norm_num [pt]; constructor <;> linarith
  · ext i; fin_cases i; rfl
  · intro j; norm_num [tieModel,pt]

def tieRootPoint : Point 2 1 := pt 0 (-3/4) (1/4)
def tieRightTrial : Point 2 1 := pt 2 0 1
def tieLeftTrial : Point 2 1 := pt 2 (-1/2) 0
def tieRightAnchor : Point 2 1 := pt 0 0 1
def tieLeftAnchor : Point 2 1 := pt 0 (-1/2) 0

theorem tie_root_minimum :
    IsMinimizer (tieModel.relaxationOn Set.univ) tieModel.objective tieRootPoint := by
  refine ⟨⟨⟨Set.mem_univ _,fun _ => by norm_num [tieModel,tieRootPoint,pt]⟩,
    (tie_linear _).mpr (by norm_num [tieRootPoint,pt]),?_⟩,?_⟩
  · intro i; norm_num [tieModel,tieRootPoint,pt]
  · intro p hp
    obtain ⟨_,_,_,_,h1,h2⟩ := (tie_linear p).mp hp.2.1
    rw [tie_objective,tie_objective]
    norm_num [tieRootPoint,pt]
    linarith

def tieSeeds : List (STSeed 2 1 1) := [⟨tieRootPoint,Set.univ⟩]
def tieRightBatch : OABatch 2 1 := ⟨fun _ => 1,tieRightAnchor,none⟩
def tieLeftBatch : OABatch 2 1 := ⟨fun _ => 0,tieLeftAnchor,none⟩

theorem tie_seed_trivial (q : Point 2 1) : q∈stSeedRegion tieModel tieSeeds := by
  intro a ha j hj
  have he : a=⟨tieRootPoint,Set.univ⟩ := by simpa [tieSeeds] using ha
  subst a
  rw [(tie_derivative _ _).fderiv]
  norm_num [tieRootPoint,pt,tieModel]

theorem tie_right_batch_valid : oaBatchValid tieModel tieRightBatch := by
  refine ⟨fun _ => by norm_num [tieModel,tieRightBatch],by ext i; norm_num [tieRightBatch,tieRightAnchor,pt,oaIntCast],?_,?_⟩
  · exact ⟨⟨(tie_linear _).mpr (by norm_num [tieRightBatch,tieRightAnchor,pt]),by ext i; norm_num [tieRightBatch,tieRightAnchor,pt,oaIntCast]⟩,
      fun _ => by norm_num [tieRightBatch,tieRightAnchor,tieModel,pt]⟩
  · intro p hp
    have hy : p.2 0=1 := by simpa [tieRightBatch,oaIntCast] using congrFun hp.1.2 0
    have hrow := ((tie_linear p).mp hp.1.1).2.2.2.2.2
    rw [tie_objective,tie_objective]
    norm_num [tieRightBatch,tieRightAnchor,pt]
    simp only [hy] at hrow
    linarith

theorem tie_left_batch_valid : oaBatchValid tieModel tieLeftBatch := by
  refine ⟨fun _ => by norm_num [tieModel,tieLeftBatch],by ext i; norm_num [tieLeftBatch,tieLeftAnchor,pt,oaIntCast],?_,?_⟩
  · exact ⟨⟨(tie_linear _).mpr (by norm_num [tieLeftBatch,tieLeftAnchor,pt]),by ext i; norm_num [tieLeftBatch,tieLeftAnchor,pt,oaIntCast]⟩,
      fun _ => by norm_num [tieLeftBatch,tieLeftAnchor,tieModel,pt]⟩
  · intro p hp
    have hy : p.2 0=0 := by simpa [tieLeftBatch,oaIntCast] using congrFun hp.1.2 0
    have hrow := ((tie_linear p).mp hp.1.1).2.2.2.2.1
    rw [tie_objective,tie_objective]
    norm_num [tieLeftBatch,tieLeftAnchor,pt]
    simp only [hy] at hrow
    linarith

theorem tie_batch_cuts_trivial (b : OABatch 2 1)
    (hb : b=tieRightBatch ∨ b=tieLeftBatch) (q : Point 2 1) : oaBatchCuts tieModel b q := by
  intro j hj
  unfold tangentRow
  rw [show oaBatchDerivative tieModel b j=(2*b.anchor.1 0) • cx by exact (tie_derivative _ _).fderiv]
  rcases hb with rfl | rfl <;>
    norm_num [tangentRow,tieRightBatch,tieLeftBatch,tieRightAnchor,tieLeftAnchor,pt,tieModel]

def tieRootRecord : BBRecord 1 := ⟨bbRootNode tieModel,(-3/4 : ℝ)⟩
def tieLeftRecord : BBRecord 1 := ⟨⟨fun _ => 0,fun _ => 0⟩,(-3/4 : ℝ)⟩
def tieRightRecord : BBRecord 1 := ⟨⟨fun _ => 1,fun _ => 1⟩,(-3/4 : ℝ)⟩


def TieHistory (H : List (OABatch 2 1)) : Prop := ∀b∈H,b=tieRightBatch ∨ b=tieLeftBatch

theorem tie_lp_iff (H : List (OABatch 2 1)) (hH : TieHistory H) (N : BBNode 1) (q : Point 2 1) :
    q∈stLP tieModel tieSeeds H N ↔ q∈tieModel.linearRegion ∧ q∈N.box := by
  constructor
  · intro h; exact ⟨h.1,h.2.1⟩
  · rintro ⟨hl,hb⟩
    exact ⟨hl,hb,tie_seed_trivial q,fun b hb => tie_batch_cuts_trivial b (hH b hb) q⟩

theorem tie_root_lp_minimum (H : List (OABatch 2 1)) (hH : TieHistory H) :
    IsMinimizer (stLP tieModel tieSeeds H tieRootRecord.node) tieModel.objective tieRootPoint := by
  refine ⟨(tie_lp_iff _ hH _ _).mpr ⟨(tie_linear _).mpr (by norm_num [tieRootPoint,pt]),?_⟩,?_⟩
  · intro i; norm_num [tieRootRecord,bbRootNode,tieModel,tieRootPoint,pt]
  · intro p hp
    obtain ⟨_,_,_,_,h1,h2⟩ := (tie_linear p).mp hp.1
    rw [tie_objective,tie_objective]
    norm_num [tieRootPoint,pt]
    linarith

theorem tie_right_lp_minimum (H : List (OABatch 2 1)) (hH : TieHistory H) :
    IsMinimizer (stLP tieModel tieSeeds H tieRightRecord.node) tieModel.objective tieRightTrial := by
  refine ⟨(tie_lp_iff _ hH _ _).mpr ⟨(tie_linear _).mpr (by norm_num [tieRightTrial,pt]),?_⟩,?_⟩
  · intro i; norm_num [tieRightRecord,tieRightTrial,pt]
  · intro p hp
    have hy := hp.2.1 (0 : Fin 1)
    change (1 : ℝ)≤p.2 0 ∧ p.2 0≤1 at hy
    have hrow := ((tie_linear p).mp hp.1).2.2.2.2.2
    rw [tie_objective,tie_objective]
    norm_num [tieRightTrial,pt]
    linarith [hy.1,hy.2]

theorem tie_left_lp_minimum (H : List (OABatch 2 1)) (hH : TieHistory H) :
    IsMinimizer (stLP tieModel tieSeeds H tieLeftRecord.node) tieModel.objective tieLeftTrial := by
  refine ⟨(tie_lp_iff _ hH _ _).mpr ⟨(tie_linear _).mpr (by norm_num [tieLeftTrial,pt]),?_⟩,?_⟩
  · intro i; norm_num [tieLeftRecord,tieLeftTrial,pt]
  · intro p hp
    have hy := hp.2.1 (0 : Fin 1)
    change (0 : ℝ)≤p.2 0 ∧ p.2 0≤0 at hy
    have hrow := ((tie_linear p).mp hp.1).2.2.2.2.1
    rw [tie_objective,tie_objective]
    norm_num [tieLeftTrial,pt]
    linarith [hy.1,hy.2]

def tieRightRaised : BBRecord 1 := ⟨tieRightRecord.node,(0 : ℝ)⟩
def tieLeftRaised : BBRecord 1 := ⟨tieLeftRecord.node,(-1/2 : ℝ)⟩
def tieOA1 : OAState 2 1 := oaAppend tieModel (oaInit none) tieRightBatch
def tieOA2 : OAState 2 1 := oaAppend tieModel tieOA1 tieLeftBatch

def tieS0 : STState 2 1 1 := stInitial tieModel tieRootPoint none
def tieS1 : STState 2 1 1 := ⟨tieSeeds,oaInit none,[tieLeftRecord,tieRightRecord],none⟩
def tieS2 : STState 2 1 1 := ⟨tieSeeds,tieOA1,[tieRightRaised,tieLeftRecord],none⟩
def tieS3 : STState 2 1 1 := ⟨tieSeeds,tieOA1,[tieLeftRecord],none⟩
def tieS4 : STState 2 1 1 := ⟨tieSeeds,tieOA2,[tieLeftRaised],none⟩
def tieS5 : STState 2 1 1 := ⟨tieSeeds,tieOA2,[],none⟩

theorem tie_initialization : STInitialize tieModel none (.inr tieS0) :=
  .seeded tieRootPoint tie_root_minimum

theorem tie_children : bbChildren tieRootRecord 0 tieRootPoint tieModel.objective=
    [tieLeftRecord,tieRightRecord] := by
  have hl : tieRootRecord.node.left 0 (tieRootPoint.2 0)=tieLeftRecord.node := by
    apply congrArg₂ BBNode.mk <;> funext i <;> fin_cases i <;>
      norm_num [tieRootRecord,tieLeftRecord,bbRootNode,BBNode.left,tieModel,tieRootPoint,pt,Function.update_apply]
  have hr : tieRootRecord.node.right 0 (tieRootPoint.2 0)=tieRightRecord.node := by
    apply congrArg₂ BBNode.mk <;> funext i <;> fin_cases i <;>
      norm_num [tieRootRecord,tieRightRecord,bbRootNode,BBNode.right,tieModel,tieRootPoint,pt,Function.update_apply]
  simp only [bbChildren,hl,hr,tie_objective]
  norm_num [tieRootRecord,tieRootPoint,pt,tieLeftRecord,tieRightRecord]

theorem tie_raise_right : stRaised tieModel tieRightRecord tieRightTrial=tieRightRaised := by
  norm_num [stRaised,tieRightRecord,tieRightRaised,tie_objective,tieRightTrial,pt]

theorem tie_raise_left : stRaised tieModel tieLeftRecord tieLeftTrial=tieLeftRaised := by
  norm_num [stRaised,tieLeftRecord,tieLeftRaised,tie_objective,tieLeftTrial,pt]

theorem tie_step1 : STProcess tieModel tieS0 tieS1 := by
  refine ⟨⟨tieSeeds,oaInit none,[],some tieRootRecord⟩,?_,?_⟩
  · simpa [tieS0,stInitial,tieSeeds,tieRootRecord,tie_objective,tieRootPoint,pt] using
      STSelect.choose tieSeeds (oaInit none) [] [] tieRootRecord
  · have hh := STResolve.branch (d:=tieModel) (seeds:=tieSeeds) (o:=oaInit none)
      (live:=[]) (b:=tieRootRecord) 0
      (tie_root_lp_minimum [] (by simp [TieHistory])) (by simp [oaCompetitive,oaInit])
      (show BBFractional (tieRootPoint.2 0) by
        rintro ⟨z,hz⟩
        have h0 : (0 : ℝ)<(z : ℝ) := by rw [hz]; norm_num [tieRootPoint,pt]
        have h1 : (z : ℝ)<1 := by rw [hz]; norm_num [tieRootPoint,pt]
        have hi0 : 0<z := by exact_mod_cast h0
        have hi1 : z<1 := by exact_mod_cast h1
        omega)
    simpa only [tie_children,List.append_nil,tieS1] using hh

theorem tie_step2 : STProcess tieModel tieS1 tieS2 := by
  refine ⟨⟨tieSeeds,oaInit none,[tieLeftRecord],some tieRightRecord⟩,?_,?_⟩
  · exact STSelect.choose tieSeeds (oaInit none) [tieLeftRecord] [] tieRightRecord
  · have hh := STResolve.callback (d:=tieModel) (seeds:=tieSeeds) (o:=oaInit none)
      (live:=[tieLeftRecord]) (b:=tieRightRecord)
      (tie_right_lp_minimum [] (by simp [TieHistory])) (by simp [oaCompetitive,oaInit])
      tie_right_batch_valid
      (show tieRightTrial.2=oaIntCast tieRightBatch.integer by ext i; norm_num [tieRightTrial,tieRightBatch,pt,oaIntCast])
    simpa only [tie_raise_right,tieS2,tieOA1] using hh

theorem tie_step3 : STProcess tieModel tieS2 tieS3 := by
  refine ⟨⟨tieSeeds,tieOA1,[tieLeftRecord],some tieRightRaised⟩,?_,?_⟩
  · exact STSelect.choose tieSeeds tieOA1 [] [tieLeftRecord] tieRightRaised
  · exact STResolve.prune
      (tie_right_lp_minimum tieOA1.history (by simp [TieHistory,tieOA1,oaAppend,oaInit]))
      (by norm_num [bbPrunable,tieOA1,oaAppend,oaInit,tieRightBatch,oaBest,tie_objective,
        tieRightAnchor,tieRightTrial,pt])

theorem tie_step4 : STProcess tieModel tieS3 tieS4 := by
  refine ⟨⟨tieSeeds,tieOA1,[],some tieLeftRecord⟩,?_,?_⟩
  · exact STSelect.choose tieSeeds tieOA1 [] [] tieLeftRecord
  · have hh := STResolve.callback (d:=tieModel) (seeds:=tieSeeds) (o:=tieOA1)
      (live:=[]) (b:=tieLeftRecord)
      (tie_left_lp_minimum tieOA1.history (by simp [TieHistory,tieOA1,oaAppend,oaInit]))
      (by norm_num [oaCompetitive,tieOA1,oaAppend,oaInit,tieRightBatch,oaBest,tie_objective,
        tieRightAnchor,tieLeftTrial,pt]) tie_left_batch_valid
      (show tieLeftTrial.2=oaIntCast tieLeftBatch.integer by ext i; norm_num [tieLeftTrial,tieLeftBatch,pt,oaIntCast])
    simpa only [tie_raise_left,tieS4,tieOA2] using hh

theorem tie_step5 : STProcess tieModel tieS4 tieS5 := by
  refine ⟨⟨tieSeeds,tieOA2,[],some tieLeftRaised⟩,?_,?_⟩
  · exact STSelect.choose tieSeeds tieOA2 [] [] tieLeftRaised
  · exact STResolve.prune
      (tie_left_lp_minimum tieOA2.history (by simp [TieHistory,tieOA2,tieOA1,oaAppend,oaInit]))
      (by norm_num [bbPrunable,tieOA2,tieOA1,oaAppend,oaInit,tieRightBatch,tieLeftBatch,oaBest,
        tie_objective,tieRightAnchor,tieLeftAnchor,tieLeftTrial,pt])

theorem tie_five_process_trace : STTrace tieModel 5 tieS0 tieS5 :=
  .cons tie_step1 (.cons tie_step2 (.cons tie_step3 (.cons tie_step4 (.cons tie_step5 (.nil tieS5)))))

theorem tie_final_stop : STStop tieModel 0 tieS5 (.solution tieLeftAnchor) := by
  apply STStop.exhausted rfl rfl
  norm_num [tieS5,tieOA2,tieOA1,oaAppend,oaInit,tieRightBatch,tieLeftBatch,oaBest,
    tie_objective,tieRightAnchor,tieLeftAnchor,pt]

theorem tie_source_full_trace_optimal :
    STInitialize tieModel none (.inr tieS0) ∧ STTrace tieModel 5 tieS0 tieS5 ∧
    IsMinimizer (tieModel.feasibleOn Set.univ) tieModel.objective tieLeftAnchor := by
  refine ⟨tie_initialization,tie_five_process_trace,?_⟩
  exact st_zero_certificate_exact tieModel (.solution tieLeftAnchor)
    (st_initialized_stop_sound tieModel tie_base_compact tie_rows_convex tie_rows_diff
      (by norm_num) none (by simp) tie_initialization (st_trace_micro tieModel tie_five_process_trace)
      tie_final_stop)


/-- Only the strict-worse callback arm is changed. Exact LP/fiber replies,
selection, inherited max and global histories are retained literally. This
relation does not purport to encode a full historical QG phase protocol. -/
inductive StrictCallbackResolve (d : ModelData n m l r) :
    STState n m l → STState n m l → Prop
  | callback {seeds : List (STSeed n m l)} {o : OAState n m}
      {live : List (BBRecord m)} {b : BBRecord m} {q : Point n m} {batch : OABatch n m}
      (hq : IsMinimizer (stLP d seeds o.history b.node) d.objective q)
      (hkeep : ¬bbPrunable .source d.objective o.incumbent (d.objective q))
      (hb : oaBatchValid d batch) (hy : q.2=oaIntCast batch.integer) :
      StrictCallbackResolve d ⟨seeds,o,live,some b⟩
        ⟨seeds,oaAppend d o batch,stRaised d b q::live,none⟩

def StrictCallbackProcess (d : ModelData n m l r) (s t : STState n m l) : Prop :=
  ∃w,STSelect s w ∧ StrictCallbackResolve d w t

def tieRepeatOA (k : ℕ) : OAState 2 1 := ⟨List.replicate (k+1) tieRightBatch,some tieRightAnchor⟩
def tieRepeat (k : ℕ) : STState 2 1 1 :=
  ⟨tieSeeds,tieRepeatOA k,[tieRightRaised,tieLeftRecord],none⟩

theorem tie_repeat_start : tieRepeat 0=tieS2 := by
  simp [tieRepeat,tieRepeatOA,tieS2,tieOA1,oaAppend,oaInit,tieRightBatch,oaBest]

theorem tie_repeat_append (k : ℕ) : oaAppend tieModel (tieRepeatOA k) tieRightBatch=tieRepeatOA (k+1) := by
  simp [oaAppend,tieRepeatOA,tieRightBatch,oaBest,List.replicate_succ',Nat.add_assoc]

theorem tie_raise_right_again : stRaised tieModel tieRightRaised tieRightTrial=tieRightRaised := by
  simp [stRaised,tieRightRaised,tie_objective,tieRightTrial,pt]

theorem tie_repeat_lp_minimum (k : ℕ) :
    IsMinimizer (stLP tieModel tieSeeds (tieRepeatOA k).history tieRightRaised.node)
      tieModel.objective tieRightTrial := by
  apply tie_right_lp_minimum
  intro b hb
  left
  exact List.eq_of_mem_replicate hb

theorem tie_repeat_actual_strict_callback (k : ℕ) :
    StrictCallbackProcess tieModel (tieRepeat k) (tieRepeat (k+1)) := by
  refine ⟨⟨tieSeeds,tieRepeatOA k,[tieLeftRecord],some tieRightRaised⟩,?_,?_⟩
  · exact STSelect.choose tieSeeds (tieRepeatOA k) [] [tieLeftRecord] tieRightRaised
  · have hh := StrictCallbackResolve.callback (d:=tieModel) (seeds:=tieSeeds) (o:=tieRepeatOA k)
      (live:=[tieLeftRecord]) (b:=tieRightRaised) (tie_repeat_lp_minimum k)
      (by simp [bbPrunable,tieRepeatOA,tie_objective,tieRightAnchor,tieRightTrial,pt])
      tie_right_batch_valid
      (show tieRightTrial.2=oaIntCast tieRightBatch.integer by ext i; norm_num [tieRightTrial,tieRightBatch,pt,oaIntCast])
    simpa only [tie_repeat_append,tie_raise_right_again,tieRepeat] using hh

theorem tie_repeat_global_bound (k : ℕ) : stGlobalBound tieModel (tieRepeat k)=bbValue (-3/4) := by
  norm_num [stGlobalBound,stBoundState,stFrontier,tieRepeat,tieRepeatOA,bbGlobalBound,
    bbIncBound,bbLiveBound,bbValue,tieRightRaised,tieLeftRecord,tie_objective,tieRightAnchor,pt]

theorem tie_repeat_trial_infeasible : tieRightTrial∉tieModel.nonlinearRegion := by
  intro h
  have hh := h (0 : Fin 1)
  norm_num [tieRightTrial,pt,tieModel] at hh

theorem tie_repeat_no_global_stop (k : ℕ) {eps : ℝ} (heps : eps<1/2) :
    ¬∃out,STStop tieModel eps (tieRepeat k) out := by
  rintro ⟨out,hstop⟩
  cases hstop with
  | infeasible ready empty inc => cases empty
  | exhausted ready empty inc => cases empty
  | @gap u lower ready inc bound test =>
    have hu : u=tieRightAnchor := by simpa [tieRepeat,tieRepeatOA] using inc.symm
    rw [hu,tie_objective] at test
    norm_num [tieRightAnchor,pt] at test
    rw [tie_repeat_global_bound] at bound
    have hb := bb_value_le_value.mp bound
    linarith

theorem tie_repeat_weak_guard_closes (k : ℕ) :
    bbPrunable .weak tieModel.objective (tieRepeatOA k).incumbent
      (tieModel.objective tieRightTrial) ∧
    ¬oaCompetitive tieModel 0 (tieRepeatOA k) tieRightTrial := by
  simp [bbPrunable,oaCompetitive,tieRepeatOA,tie_objective,tieRightTrial,tieRightAnchor,pt]

theorem tie_source_initialized_strict_stall {eps : ℝ} (heps : eps<1/2) :
    STInitialize tieModel none (.inr tieS0) ∧ STTrace tieModel 2 tieS0 (tieRepeat 0) ∧
    (∀k,StrictCallbackProcess tieModel (tieRepeat k) (tieRepeat (k+1))) ∧
    (∀k,¬∃out,STStop tieModel eps (tieRepeat k) out) ∧
    (∀k,(tieRepeat k).oa.history.length=k+1) := by
  refine ⟨tie_initialization,?_,tie_repeat_actual_strict_callback,
    fun k => tie_repeat_no_global_stop k heps,?_⟩
  · rw [tie_repeat_start]
    exact .cons tie_step1 (.cons tie_step2 (.nil tieS2))
  · intro k; simp [tieRepeat,tieRepeatOA]


theorem tie_prefix2 : STTrace tieModel 2 tieS0 tieS2 :=
  .cons tie_step1 (.cons tie_step2 (.nil tieS2))
theorem tie_prefix3 : STTrace tieModel 3 tieS0 tieS3 :=
  .cons tie_step1 (.cons tie_step2 (.cons tie_step3 (.nil tieS3)))

def tieWorkingLeft : STState 2 1 1 := ⟨tieSeeds,tieOA1,[],some tieLeftRecord⟩
def tieOmittedLeft : STState 2 1 1 := ⟨tieSeeds,tieOA1,[tieRightRaised],none⟩
def tieOmittedWorking : STState 2 1 1 := ⟨tieSeeds,tieOA1,[],none⟩

theorem tie_select_working_left : STSelect tieS3 tieWorkingLeft :=
  STSelect.choose tieSeeds tieOA1 [] [] tieLeftRecord

theorem tie_working_reachable : STMicroTrace tieModel 7 tieS0 tieWorkingLeft := by
  have hh := st_micro_trace_trans tieModel (st_trace_micro tieModel tie_prefix3)
    (STMicroTrace.cons (.select tie_select_working_left) (.nil tieWorkingLeft))
  exact hh

theorem tie_working_bound : stGlobalBound tieModel tieWorkingLeft=bbValue (-3/4) := by
  norm_num [stGlobalBound,stBoundState,stFrontier,tieWorkingLeft,tieOA1,oaAppend,oaInit,
    tieRightBatch,oaBest,bbGlobalBound,bbIncBound,bbLiveBound,bbValue,tieLeftRecord,
    tie_objective,tieRightAnchor,pt]

theorem tie_omitted_bounds :
    stGlobalBound tieModel tieOmittedLeft=bbValue 0 ∧
    stGlobalBound tieModel tieOmittedWorking=bbValue 0 := by
  constructor <;>
    norm_num [stGlobalBound,stBoundState,stFrontier,tieOmittedLeft,tieOmittedWorking,tieOA1,
      oaAppend,oaInit,tieRightBatch,oaBest,bbGlobalBound,bbIncBound,bbLiveBound,bbValue,
      tieRightRaised,tie_objective,tieRightAnchor,pt]

theorem tie_omitted_sibling_unsound : ¬STInvariant tieModel tieOmittedLeft := by
  intro hs
  have hb := st_global_bound_sound tieModel tieOmittedLeft hs tieLeftAnchor
    tie_source_full_trace_optimal.2.2.1
  rw [tie_omitted_bounds.1,tie_objective] at hb
  have hh := bb_value_le_value.mp hb
  norm_num [tieLeftAnchor,pt] at hh

theorem tie_omitted_working_unsound : ¬STInvariant tieModel tieOmittedWorking := by
  intro hs
  have hb := st_global_bound_sound tieModel tieOmittedWorking hs tieLeftAnchor
    tie_source_full_trace_optimal.2.2.1
  rw [tie_omitted_bounds.2,tie_objective] at hb
  have hh := bb_value_le_value.mp hb
  norm_num [tieLeftAnchor,pt] at hh

theorem tie_positive_tolerance_actual_stop : STStop tieModel (3/4) tieS2 (.solution tieRightAnchor) := by
  apply STStop.gap (-3/4) rfl
  · simp [tieS2,tieOA1,oaAppend,oaInit,tieRightBatch,oaBest]
  · rw [←tie_repeat_start,tie_repeat_global_bound]
  · norm_num [tie_objective,tieRightAnchor,pt]

theorem tie_positive_tolerance_return :
    OAReturnCertificate tieModel (3/4) (.solution tieRightAnchor) ∧
    tieModel.objective tieLeftAnchor<tieModel.objective tieRightAnchor := by
  refine ⟨st_initialized_stop_sound tieModel tie_base_compact tie_rows_convex tie_rows_diff
    (by norm_num) none (by simp) tie_initialization (st_trace_micro tieModel tie_prefix2)
    tie_positive_tolerance_actual_stop,?_⟩
  norm_num [tie_objective,tieLeftAnchor,tieRightAnchor,pt]

theorem tie_empty_frontier_incumbent_required :
    stGlobalBound tieModel tieS5=bbValue (-1/2) ∧
    bbLiveBound (stFrontier tieS5)=⊤ := by
  constructor
  · norm_num [stGlobalBound,stBoundState,stFrontier,tieS5,tieOA2,tieOA1,oaAppend,oaInit,
      tieRightBatch,tieLeftBatch,oaBest,bbGlobalBound,bbIncBound,bbLiveBound,bbValue,
      tie_objective,tieRightAnchor,tieLeftAnchor,pt]
  · rfl

theorem tie_all_chosen_callback_trials_infeasible :
    tieRightTrial∉tieModel.nonlinearRegion ∧ tieLeftTrial∉tieModel.nonlinearRegion := by
  refine ⟨tie_repeat_trial_infeasible,?_⟩
  intro h
  have hh := h (0 : Fin 1)
  norm_num [tieModel,tieLeftTrial,pt] at hh


def rpt := Chapter02SourceRestorationExamples.pt

def rootGapModel : ModelData 1 1 1 2 :=
  Chapter02SourceRestorationExamples.boxModel 1
    (fun _ p => (p.1 0)^2+(p.2 0-1/2)^2) 1 1 1 0

theorem root_gap_linear (p : Point 1 1) : p∈rootGapModel.linearRegion ↔ -1≤p.1 0 ∧ p.1 0≤1 :=
  Chapter02SourceRestorationExamples.box_linear _ _ _ _ _ _ _
theorem root_gap_objective (p : Point 1 1) : rootGapModel.objective p=p.1 0 := by
  simpa [rootGapModel] using Chapter02SourceRestorationExamples.box_objective 1
    (fun _ p => (p.1 0)^2+(p.2 0-1/2)^2) 1 1 1 0 p

theorem root_gap_base_compact : IsCompact (bbMixedBase rootGapModel rootGapModel.lo rootGapModel.hi) :=
  Chapter02SourceRestorationExamples.box_base_compact _ _ _ _ _ _

theorem root_gap_rows_convex : ∀j,ConvexOn ℝ Set.univ (rootGapModel.g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have hx := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 0-q.1 0))
  have hy := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.2 0-q.2 0))
  simp only [rootGapModel,Chapter02SourceRestorationExamples.boxModel,
    Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have he : t=1-s := by linarith
  rw [he] at hx hy ⊢
  nlinarith

theorem root_gap_rows_C2 : ∀j,ContDiff ℝ 2 (rootGapModel.g j) := by
  intro j
  exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).add
    ((((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd).sub contDiff_const).pow 2)

theorem root_gap_rows_diff : ∀j,Differentiable ℝ (rootGapModel.g j) :=
  fun j => (root_gap_rows_C2 j).differentiable (by norm_num)

theorem root_gap_derivative (p : Point 1 1) (j : Fin 1) :
    HasFDerivAt (rootGapModel.g j)
      ((2*p.1 0) • Chapter02SourceRestorationExamples.cx+
        (2*(p.2 0-1/2)) • Chapter02SourceRestorationExamples.cy) p := by
  have h1 := (hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p Chapter02SourceRestorationExamples.cx.hasFDerivAt
  have h2 := (hasDerivAt_pow 2 (p.2 0-1/2)).comp_hasFDerivAt p
    (Chapter02SourceRestorationExamples.cy.hasFDerivAt.sub_const (1/2))
  simpa [rootGapModel,Chapter02SourceRestorationExamples.boxModel,Chapter02SourceRestorationExamples.cx,
    Chapter02SourceRestorationExamples.cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY,
    Function.comp_def] using h1.fun_add h2

theorem root_gap_nlp_minimum :
    IsMinimizer (rootGapModel.relaxationOn Set.univ) rootGapModel.objective (rpt 0 (1/2)) := by
  refine ⟨⟨⟨Set.mem_univ _,fun _ => by norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,
    Chapter02SourceRestorationExamples.pt]⟩,(root_gap_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_⟩,?_⟩
  · intro i; norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt]
  · intro p hp
    have hg := hp.1.2 (0 : Fin 1)
    change (p.1 0)^2+(p.2 0-1/2)^2≤0 at hg
    have hx : p.1 0=0 := by nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.2 0-1/2)]
    simp [root_gap_objective,rpt,Chapter02SourceRestorationExamples.pt,hx]

theorem root_gap_every_integer_fiber_empty (y : IntVector 1) :
    ¬(rootGapModel.fixedNonlinearFiber (oaIntCast y)).Nonempty := by
  rintro ⟨p,hp⟩
  have hy := congrFun hp.1.2 0
  have hg := hp.2 (0 : Fin 1)
  change (p.1 0)^2+(p.2 0-1/2)^2≤0 at hg
  have hh : p.2 0=1/2 := by nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.2 0-1/2)]
  change p.2 0=(y 0 : ℝ) at hy
  have h0 : (0 : ℝ)<(y 0 : ℝ) := by rw [←hy,hh]; norm_num
  have h1 : (y 0 : ℝ)<1 := by rw [←hy,hh]; norm_num
  have hz0 : 0<y 0 := by exact_mod_cast h0
  have hz1 : y 0<1 := by exact_mod_cast h1
  omega

theorem root_gap_fiber_slater_vacuous : OAFiberSlater rootGapModel := by
  intro y hy hn
  exact (root_gap_every_integer_fiber_empty y hn).elim

def gapSeeds : List (STSeed 1 1 1) := [⟨rpt 0 (1/2),Set.univ⟩]
def gapBatch (y : ℤ) : OABatch 1 1 := ⟨fun _ => y,rpt 0 y,some (1/4)⟩
def gapRoot : BBRecord 1 := ⟨bbRootNode rootGapModel,(0 : ℝ)⟩
def gapLeft : BBRecord 1 := ⟨⟨fun _ => 0,fun _ => 0⟩,(0 : ℝ)⟩
def gapRight : BBRecord 1 := ⟨⟨fun _ => 1,fun _ => 1⟩,(0 : ℝ)⟩

theorem gap_seed_trivial (q : Point 1 1) : q∈stSeedRegion rootGapModel gapSeeds := by
  intro a ha j hj
  have he : a=⟨rpt 0 (1/2),Set.univ⟩ := by simpa [gapSeeds] using ha
  subst a
  rw [(root_gap_derivative _ _).fderiv]
  norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt]

theorem gap_batch_valid (y : ℤ) (hy : y=0 ∨ y=1) : oaBatchValid rootGapModel (gapBatch y) := by
  refine ⟨?_,by ext i; simp [gapBatch,rpt,Chapter02SourceRestorationExamples.pt,oaIntCast],
    root_gap_every_integer_fiber_empty (fun _ => y),?_,?_⟩
  · intro i; rcases hy with rfl | rfl <;> norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,gapBatch]
  · refine ⟨⟨(root_gap_linear _).mpr (by norm_num [gapBatch,rpt,Chapter02SourceRestorationExamples.pt]),?_,⟩,?_⟩
    · ext i; simp [gapBatch,rpt,Chapter02SourceRestorationExamples.pt,oaIntCast]
    · intro j; rcases hy with rfl | rfl <;>
        norm_num [gapBatch,rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt]
  · intro q hq
    have hqy : q.1.2 0=(y : ℝ) := by simpa [gapBatch,oaIntCast] using congrFun hq.1.2 0
    have hg := hq.2 (0 : Fin 1)
    change (q.1.1 0)^2+(q.1.2 0-1/2)^2≤q.2 at hg
    change (1/4 : ℝ)≤q.2
    rw [hqy] at hg
    rcases hy with rfl | rfl <;> norm_num at hg <;> nlinarith [sq_nonneg (q.1.1 0)]

theorem gap_batch_zero_cut (q : Point 1 1) : oaBatchCuts rootGapModel (gapBatch 0) q ↔ 1/4≤q.2 0 := by
  unfold oaBatchCuts SelectedOARows
  simp only [oaBatchRows,gapBatch]
  constructor
  · intro h
    have hh := h (0 : Fin 1) (by norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt])
    unfold tangentRow oaBatchDerivative at hh
    rw [(root_gap_derivative _ _).fderiv] at hh
    norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt,
      Chapter02SourceRestorationExamples.cx,Chapter02SourceRestorationExamples.cy,
      Chapter02Examples.coordX,Chapter02KKTExamples.coordY] at hh
    linarith
  · intro h j hj
    unfold tangentRow oaBatchDerivative
    rw [(root_gap_derivative _ _).fderiv]
    norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt,
      Chapter02SourceRestorationExamples.cx,Chapter02SourceRestorationExamples.cy,
      Chapter02Examples.coordX,Chapter02KKTExamples.coordY]
    linarith

theorem gap_lp_minimum_of_mem (H : List (OABatch 1 1)) (N : BBNode 1) (q : Point 1 1)
    (hq : q∈stLP rootGapModel gapSeeds H N) (hx : q.1 0=-1) :
    IsMinimizer (stLP rootGapModel gapSeeds H N) rootGapModel.objective q := by
  refine ⟨hq,?_⟩
  intro p hp
  rw [root_gap_objective,root_gap_objective,hx]
  exact ((root_gap_linear p).mp hp.1).1

theorem gap_first_lp_minimum :
    IsMinimizer (stLP rootGapModel gapSeeds [] gapRoot.node) rootGapModel.objective (rpt (-1) 0) := by
  apply gap_lp_minimum_of_mem
  · refine ⟨(root_gap_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_,
      gap_seed_trivial _,by simp⟩
    intro i; norm_num [gapRoot,bbRootNode,rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt]
  · rfl

def gapS0 : STState 1 1 1 := stInitial rootGapModel (rpt 0 (1/2)) none
def gapOA1 : OAState 1 1 := oaAppend rootGapModel (oaInit none) (gapBatch 0)
def gapS1 : STState 1 1 1 := ⟨gapSeeds,gapOA1,[gapRoot],none⟩

theorem gap_initialization : STInitialize rootGapModel none (.inr gapS0) :=
  .seeded _ root_gap_nlp_minimum

theorem gap_raise_keeps_nlp_bound : stRaised rootGapModel gapRoot (rpt (-1) 0)=gapRoot := by
  norm_num [stRaised,gapRoot,root_gap_objective,rpt,Chapter02SourceRestorationExamples.pt]

theorem gap_first_callback : STProcess rootGapModel gapS0 gapS1 := by
  refine ⟨⟨gapSeeds,oaInit none,[],some gapRoot⟩,?_,?_⟩
  · simpa [gapS0,stInitial,gapSeeds,gapRoot,root_gap_objective,rpt,Chapter02SourceRestorationExamples.pt]
      using STSelect.choose gapSeeds (oaInit none) [] [] gapRoot
  · have hh := STResolve.callback (d:=rootGapModel) (seeds:=gapSeeds) (o:=oaInit none)
      (live:=[]) (b:=gapRoot) gap_first_lp_minimum (by simp [oaCompetitive,oaInit])
      (gap_batch_valid 0 (Or.inl rfl))
      (show (rpt (-1) 0).2=oaIntCast (gapBatch 0).integer by ext i; norm_num [rpt,Chapter02SourceRestorationExamples.pt,gapBatch,oaIntCast])
    simpa only [gap_raise_keeps_nlp_bound,gapS1,gapOA1] using hh

theorem root_nlp_bound_strictly_above_lp :
    STInitialize rootGapModel none (.inr gapS0) ∧ STProcess rootGapModel gapS0 gapS1 ∧
    gapRoot.lower=(0 : ℝ) ∧ rootGapModel.objective (rpt (-1) 0)=-1 ∧
    (rootGapModel.objective (rpt (-1) 0) : WithBot ℝ)<gapRoot.lower := by
  exact ⟨gap_initialization,gap_first_callback,rfl,by norm_num [root_gap_objective,rpt,Chapter02SourceRestorationExamples.pt],by norm_num [gapRoot,root_gap_objective,rpt,Chapter02SourceRestorationExamples.pt]⟩


theorem gap_batch_one_cut (q : Point 1 1) : oaBatchCuts rootGapModel (gapBatch 1) q ↔ q.2 0≤3/4 := by
  unfold oaBatchCuts SelectedOARows
  simp only [oaBatchRows,gapBatch]
  constructor
  · intro h
    have hh := h (0 : Fin 1) (by norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt])
    unfold tangentRow oaBatchDerivative at hh
    rw [(root_gap_derivative _ _).fderiv] at hh
    norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt,
      Chapter02SourceRestorationExamples.cx,Chapter02SourceRestorationExamples.cy,
      Chapter02Examples.coordX,Chapter02KKTExamples.coordY] at hh
    linarith
  · intro h j hj
    unfold tangentRow oaBatchDerivative
    rw [(root_gap_derivative _ _).fderiv]
    norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt,
      Chapter02SourceRestorationExamples.cx,Chapter02SourceRestorationExamples.cy,
      Chapter02Examples.coordX,Chapter02KKTExamples.coordY]
    linarith

theorem gap_second_lp_minimum :
    IsMinimizer (stLP rootGapModel gapSeeds gapOA1.history gapRoot.node)
      rootGapModel.objective (rpt (-1) (1/4)) := by
  apply gap_lp_minimum_of_mem
  · refine ⟨(root_gap_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_,gap_seed_trivial _,?_⟩
    · intro i; norm_num [gapRoot,bbRootNode,rootGapModel,Chapter02SourceRestorationExamples.boxModel,rpt,Chapter02SourceRestorationExamples.pt]
    · intro b hb
      have he : b=gapBatch 0 := by simpa [gapOA1,oaAppend,oaInit] using hb
      rw [he,gap_batch_zero_cut]
      norm_num [rpt,Chapter02SourceRestorationExamples.pt]
  · rfl

theorem gap_right_lp_minimum :
    IsMinimizer (stLP rootGapModel gapSeeds gapOA1.history gapRight.node)
      rootGapModel.objective (rpt (-1) 1) := by
  apply gap_lp_minimum_of_mem
  · refine ⟨(root_gap_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_,gap_seed_trivial _,?_⟩
    · intro i; norm_num [gapRight,rpt,Chapter02SourceRestorationExamples.pt]
    · intro b hb
      have he : b=gapBatch 0 := by simpa [gapOA1,oaAppend,oaInit] using hb
      rw [he,gap_batch_zero_cut]
      norm_num [rpt,Chapter02SourceRestorationExamples.pt]
  · rfl

def gapOA2 : OAState 1 1 := oaAppend rootGapModel gapOA1 (gapBatch 1)
def gapS2 : STState 1 1 1 := ⟨gapSeeds,gapOA1,[gapLeft,gapRight],none⟩
def gapS3 : STState 1 1 1 := ⟨gapSeeds,gapOA1,[gapRight],none⟩
def gapS4 : STState 1 1 1 := ⟨gapSeeds,gapOA2,[gapRight],none⟩
def gapS5 : STState 1 1 1 := ⟨gapSeeds,gapOA2,[],none⟩

theorem gap_children : bbChildren gapRoot 0 (rpt (-1) (1/4)) rootGapModel.objective=[gapLeft,gapRight] := by
  have hl : gapRoot.node.left 0 ((rpt (-1) (1/4)).2 0)=gapLeft.node := by
    apply congrArg₂ BBNode.mk <;> funext i <;> fin_cases i <;>
      norm_num [gapRoot,gapLeft,bbRootNode,BBNode.left,rootGapModel,Chapter02SourceRestorationExamples.boxModel,
        rpt,Chapter02SourceRestorationExamples.pt,Function.update_apply]
  have hr : gapRoot.node.right 0 ((rpt (-1) (1/4)).2 0)=gapRight.node := by
    apply congrArg₂ BBNode.mk <;> funext i <;> fin_cases i <;>
      norm_num [gapRoot,gapRight,bbRootNode,BBNode.right,rootGapModel,Chapter02SourceRestorationExamples.boxModel,
        rpt,Chapter02SourceRestorationExamples.pt,Function.update_apply]
  simp only [bbChildren,hl,hr,root_gap_objective]
  norm_num [gapRoot,gapLeft,gapRight,rpt,Chapter02SourceRestorationExamples.pt]

theorem gap_step2 : STProcess rootGapModel gapS1 gapS2 := by
  refine ⟨⟨gapSeeds,gapOA1,[],some gapRoot⟩,STSelect.choose gapSeeds gapOA1 [] [] gapRoot,?_⟩
  have hh := STResolve.branch (d:=rootGapModel) (seeds:=gapSeeds) (o:=gapOA1)
    (live:=[]) (b:=gapRoot) 0 gap_second_lp_minimum
    (by simp [oaCompetitive,gapOA1,oaAppend,oaInit,gapBatch])
    (show BBFractional ((rpt (-1) (1/4)).2 0) by
      rintro ⟨z,hz⟩
      have h0 : (0 : ℝ)<(z : ℝ) := by rw [hz]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]
      have h1 : (z : ℝ)<1 := by rw [hz]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]
      have hz0 : 0<z := by exact_mod_cast h0
      have hz1 : z<1 := by exact_mod_cast h1
      omega)
  simpa only [gap_children,List.append_nil,gapS2] using hh

theorem gap_left_lp_empty : stLP rootGapModel gapSeeds gapOA1.history gapLeft.node=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hb := hp.2.1 (0 : Fin 1)
  change (0 : ℝ)≤p.2 0 ∧ p.2 0≤0 at hb
  have hc := (gap_batch_zero_cut p).mp (hp.2.2.2 (gapBatch 0) (by simp [gapOA1,oaAppend,oaInit]))
  linarith [hb.2]

theorem gap_step3 : STProcess rootGapModel gapS2 gapS3 :=
  ⟨_,STSelect.choose gapSeeds gapOA1 [] [gapRight] gapLeft,STResolve.empty gap_left_lp_empty⟩

theorem gap_step4 : STProcess rootGapModel gapS3 gapS4 := by
  refine ⟨⟨gapSeeds,gapOA1,[],some gapRight⟩,STSelect.choose gapSeeds gapOA1 [] [] gapRight,?_⟩
  have hh := STResolve.callback (d:=rootGapModel) (seeds:=gapSeeds) (o:=gapOA1)
    (live:=[]) (b:=gapRight) gap_right_lp_minimum
    (by simp [oaCompetitive,gapOA1,oaAppend,oaInit,gapBatch]) (gap_batch_valid 1 (Or.inr rfl))
    (show (rpt (-1) 1).2=oaIntCast (gapBatch 1).integer by ext i; norm_num [rpt,Chapter02SourceRestorationExamples.pt,gapBatch,oaIntCast])
  have hr : stRaised rootGapModel gapRight (rpt (-1) 1)=gapRight := by
    norm_num [stRaised,gapRight,root_gap_objective,rpt,Chapter02SourceRestorationExamples.pt]
  simpa only [hr,gapS4,gapOA2] using hh

theorem gap_right_lp_empty : stLP rootGapModel gapSeeds gapOA2.history gapRight.node=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hb := hp.2.1 (0 : Fin 1)
  change (1 : ℝ)≤p.2 0 ∧ p.2 0≤1 at hb
  have hc := (gap_batch_one_cut p).mp (hp.2.2.2 (gapBatch 1) (by simp [gapOA2,oaAppend]))
  linarith [hb.1]

theorem gap_step5 : STProcess rootGapModel gapS4 gapS5 :=
  ⟨_,STSelect.choose gapSeeds gapOA2 [] [] gapRight,STResolve.empty gap_right_lp_empty⟩

theorem gap_five_process_trace : STTrace rootGapModel 5 gapS0 gapS5 :=
  .cons gap_first_callback (.cons gap_step2 (.cons gap_step3 (.cons gap_step4 (.cons gap_step5 (.nil gapS5)))))

theorem gap_final_infeasible : STStop rootGapModel 0 gapS5 .infeasible := by
  apply STStop.infeasible rfl rfl
  simp [gapS5,gapOA2,gapOA1,oaAppend,oaInit,gapBatch]

theorem gap_source_full_return :
    STInitialize rootGapModel none (.inr gapS0) ∧ STTrace rootGapModel 5 gapS0 gapS5 ∧
      ¬(rootGapModel.feasibleOn Set.univ).Nonempty := by
  exact ⟨gap_initialization,gap_five_process_trace,
    st_initialized_stop_sound rootGapModel root_gap_base_compact root_gap_rows_convex root_gap_rows_diff
      (by norm_num) none (by simp) gap_initialization (st_trace_micro _ gap_five_process_trace) gap_final_infeasible⟩

def gapReset : STState 1 1 1 := ⟨gapSeeds,gapOA1,[⟨gapRoot.node,(-1 : ℝ)⟩],none⟩

theorem gap_reset_lowers_bound :
    stGlobalBound rootGapModel gapS0=bbValue 0 ∧ stGlobalBound rootGapModel gapS1=bbValue 0 ∧
    stGlobalBound rootGapModel gapReset=bbValue (-1) := by
  constructor
  · norm_num [stGlobalBound,stBoundState,stFrontier,gapS0,stInitial,oaInit,bbGlobalBound,
      bbIncBound,bbLiveBound,bbValue,root_gap_objective,rpt,Chapter02SourceRestorationExamples.pt]
  · constructor <;> norm_num [stGlobalBound,stBoundState,stFrontier,gapS1,gapReset,gapRoot,gapOA1,
      oaAppend,oaInit,gapBatch,bbGlobalBound,bbIncBound,bbLiveBound,bbValue]

theorem gap_reset_not_legal_process : ¬STProcess rootGapModel gapS0 gapReset := by
  intro h
  have hm := st_process_global_bound_mono rootGapModel
    (st_initial_invariant rootGapModel _ none (by simp) root_gap_nlp_minimum) h
  change stGlobalBound rootGapModel gapS0≤stGlobalBound rootGapModel gapReset at hm
  rw [gap_reset_lowers_bound.1,gap_reset_lowers_bound.2.2] at hm
  have hh := bb_value_le_value.mp hm
  norm_num at hh


theorem empty_mixed_base_unbounded_initialization :
    IsCompact (bbMixedBase OAEdgeExamples.badRelaxationModel
      OAEdgeExamples.badRelaxationModel.lo OAEdgeExamples.badRelaxationModel.hi) ∧
    (OAEdgeExamples.badRelaxationModel.relaxationOn Set.univ).Nonempty ∧
    STInitialize OAEdgeExamples.badRelaxationModel none (.inl .infeasible) ∧
    ¬(OAEdgeExamples.badRelaxationModel.feasibleOn Set.univ).Nonempty := by
  have hu : ∀B : ℝ,∃q∈OAEdgeExamples.badRelaxationModel.relaxationOn Set.univ,
      OAEdgeExamples.badRelaxationModel.objective q<B := by
    intro B
    exact ⟨((fun _ => B-1),(fun _ => 1/2)),OAEdgeExamples.badRelaxation_feasible_line (B-1),by
      rw [OAEdgeExamples.badRelaxation_objective]; dsimp; linarith⟩
  have hi : STInitialize OAEdgeExamples.badRelaxationModel none (.inl .infeasible) := .unbounded hu
  refine ⟨OAEdgeExamples.badRelaxation_compact,⟨_,OAEdgeExamples.badRelaxation_feasible_line 0⟩,hi,?_⟩
  exact st_initialize_return_sound OAEdgeExamples.badRelaxationModel OAEdgeExamples.badRelaxation_compact
    (fun j => Fin.elim0 j) (by norm_num : (0 : ℝ)≤0) none hi

def tpt {m : ℕ} (t : ℝ) (y : RealVector m) : Point 1 m := (fun _ => t,y)
def timeModel (m l : ℕ) (G : Fin l → Point 1 m → ℝ) (T U : ℝ) : ModelData 1 m l 2 where
  g := G
  A := ![fun _ => 1,fun _ => -1]
  B := fun _ _ => 0
  rhs := ![T,0]
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => U

theorem time_linear (m l : ℕ) (G : Fin l → Point 1 m → ℝ) (T U : ℝ) (p : Point 1 m) :
    p∈(timeModel m l G T U).linearRegion ↔ 0≤p.1 0 ∧ p.1 0≤T := by
  simp [timeModel,ModelData.linearRegion,LinearForm,Fin.forall_fin_succ,and_comm]

theorem time_objective (m l : ℕ) (G : Fin l → Point 1 m → ℝ) (T U : ℝ) (p : Point 1 m) :
    (timeModel m l G T U).objective p=p.1 0 := by
  simp [timeModel,ModelData.objective,LinearForm]

theorem time_base_compact (m l : ℕ) (G : Fin l → Point 1 m → ℝ) (T U : ℝ) :
    IsCompact (bbMixedBase (timeModel m l G T U)
      (timeModel m l G T U).lo (timeModel m l G T U).hi) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (tpt 0 (fun _ => 0)) (tpt T (fun _ => U)))).of_isClosed_subset
    (Chapter02CPExamples.base_closed _)
  rintro p ⟨hp,y,hy,heq⟩
  have hx := (time_linear _ _ _ _ _ _).mp hp
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i; exact hx.1
  · intro i; rw [heq]; exact (hy i).1
  · intro i; fin_cases i; exact hx.2
  · intro i; rw [heq]; exact (hy i).2

def improveModel : ModelData 1 1 2 2 := timeModel 1 2
  (fun j p => if j=0 then (p.2 0-1/2)^2-p.1 0 else (p.2 0-3/2)^2-2) 3 2

theorem improve_linear (p : Point 1 1) : p∈improveModel.linearRegion ↔ 0≤p.1 0 ∧ p.1 0≤3 :=
  time_linear _ _ _ _ _ _
theorem improve_objective (p : Point 1 1) : improveModel.objective p=p.1 0 :=
  time_objective _ _ _ _ _ _
theorem improve_base_compact : IsCompact (bbMixedBase improveModel improveModel.lo improveModel.hi) :=
  time_base_compact _ _ _ _ _

theorem improve_rows_convex : ∀j,ConvexOn ℝ Set.univ (improveModel.g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have hh := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.2 0-q.2 0))
  have he : t=1-s := by linarith
  fin_cases j <;>
    simp [improveModel,timeModel,smul_eq_mul] <;>
    rw [he] at hh ⊢ <;> nlinarith

theorem improve_rows_C2 : ∀j,ContDiff ℝ 2 (improveModel.g j) := by
  intro j
  fin_cases j
  · exact ((((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd).sub contDiff_const).pow 2).sub
      ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst)
  · exact ((((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd).sub contDiff_const).pow 2).sub
      contDiff_const

theorem improve_rows_diff : ∀j,Differentiable ℝ (improveModel.g j) :=
  fun j => (improve_rows_C2 j).differentiable (by norm_num)

theorem improve_derivative (p : Point 1 1) (j : Fin 2) :
    HasFDerivAt (improveModel.g j)
      (if j=0 then (2*(p.2 0-1/2)) • Chapter02SourceRestorationExamples.cy-Chapter02SourceRestorationExamples.cx
       else (2*(p.2 0-3/2)) • Chapter02SourceRestorationExamples.cy) p := by
  fin_cases j
  · have hh := ((hasDerivAt_pow 2 (p.2 0-1/2)).comp_hasFDerivAt p
      (Chapter02SourceRestorationExamples.cy.hasFDerivAt.sub_const (1/2))).fun_sub
        Chapter02SourceRestorationExamples.cx.hasFDerivAt
    simpa [improveModel,timeModel,Chapter02SourceRestorationExamples.cx,Chapter02SourceRestorationExamples.cy,
      Chapter02Examples.coordX,Chapter02KKTExamples.coordY,Function.comp_def] using hh
  · have hh := ((hasDerivAt_pow 2 (p.2 0-3/2)).comp_hasFDerivAt p
      (Chapter02SourceRestorationExamples.cy.hasFDerivAt.sub_const (3/2))).sub_const 2
    simpa [improveModel,timeModel,Chapter02SourceRestorationExamples.cy,
      Chapter02KKTExamples.coordY,Function.comp_def] using hh

theorem improve_root_minimum :
    IsMinimizer (improveModel.relaxationOn Set.univ) improveModel.objective (rpt 0 (1/2)) := by
  refine ⟨⟨⟨Set.mem_univ _,?_⟩,(improve_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_⟩,?_⟩
  · intro j; fin_cases j <;> norm_num [improveModel,timeModel,rpt,Chapter02SourceRestorationExamples.pt]
  · intro i; norm_num [improveModel,timeModel,rpt,Chapter02SourceRestorationExamples.pt]
  · intro p hp
    rw [improve_objective,improve_objective]
    exact ((improve_linear p).mp hp.2.1).1

theorem improve_zero_fiber_empty :
    ¬(improveModel.fixedNonlinearFiber (oaIntCast (fun _ => 0))).Nonempty := by
  rintro ⟨p,hp⟩
  have hy : p.2 0=0 := by simpa [oaIntCast] using congrFun hp.1.2 0
  have hg := hp.2 (1 : Fin 2)
  norm_num [improveModel,timeModel,hy] at hg

theorem improve_fiber_slater : OAFiberSlater improveModel := by
  intro y hy hn
  have hyb := hy (0 : Fin 1)
  change (0 : ℝ)≤(y 0 : ℝ) ∧ (y 0 : ℝ)≤2 at hyb
  have h0 : 0≤y 0 := by exact_mod_cast hyb.1
  have h2 : y 0≤2 := by exact_mod_cast hyb.2
  have hz : y 0≠0 := by
    intro he
    have hey : y=(fun _ => 0) := by ext i; fin_cases i; exact he
    rw [hey] at hn
    exact improve_zero_fiber_empty hn
  have hcases : y 0=1 ∨ y 0=2 := by omega
  refine ⟨rpt 3 (y 0),⟨(improve_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_⟩,?_⟩
  · ext i; fin_cases i; rfl
  · intro j; rcases hcases with he | he <;> fin_cases j <;>
      norm_num [improveModel,timeModel,rpt,Chapter02SourceRestorationExamples.pt,he]


theorem tie_four_process_trace : STTrace tieModel 4 tieS0 tieS4 :=
  .cons tie_step1 (.cons tie_step2 (.cons tie_step3 (.cons tie_step4 (.nil tieS4))))

theorem tie_fourth_global_bound : stGlobalBound tieModel tieS4=bbValue (-1/2) := by
  norm_num [stGlobalBound,stBoundState,stFrontier,tieS4,tieOA2,tieOA1,oaAppend,oaInit,
    tieRightBatch,tieLeftBatch,oaBest,bbGlobalBound,bbIncBound,bbLiveBound,bbValue,
    tieLeftRaised,tie_objective,tieRightAnchor,tieLeftAnchor,pt]

theorem tie_fourth_zero_gap_stop : STStop tieModel 0 tieS4 (.solution tieLeftAnchor) := by
  apply STStop.gap (-1/2) rfl
  · norm_num [tieS4,tieOA2,tieOA1,oaAppend,oaInit,tieRightBatch,tieLeftBatch,oaBest,
      tie_objective,tieRightAnchor,tieLeftAnchor,pt]
  · rw [tie_fourth_global_bound]
  · norm_num [tie_objective,tieLeftAnchor,pt]

/-- A selector realizing the four processing cycles and then the actual gap
stop. The fifth raw cleanup cycle is deliberately absent from this run. -/
def tieGapSelector : STSelector tieModel 0 := by
  classical
  let fallback := Classical.choice (st_selector_exists tieModel 0 tie_base_compact tie_rows_diff)
  intro s
  exact if h0 : s=tieS0 then ⟨.inr tieS1,by intro _ _; rw [h0]; exact tie_step1⟩ else
    if h1 : s=tieS1 then ⟨.inr tieS2,by intro _ _; rw [h1]; exact tie_step2⟩ else
    if h2 : s=tieS2 then ⟨.inr tieS3,by intro _ _; rw [h2]; exact tie_step3⟩ else
    if h3 : s=tieS3 then ⟨.inr tieS4,by intro _ _; rw [h3]; exact tie_step4⟩ else
    if h4 : s=tieS4 then ⟨.inl (.solution tieLeftAnchor),by intro _ _; rw [h4]; exact tie_fourth_zero_gap_stop⟩ else
    fallback s

theorem tie_state_signatures :
    (tieS0.oa.history.length,tieS0.live.length)=(0,1) ∧
    (tieS1.oa.history.length,tieS1.live.length)=(0,2) ∧
    (tieS2.oa.history.length,tieS2.live.length)=(1,2) ∧
    (tieS3.oa.history.length,tieS3.live.length)=(1,1) ∧
    (tieS4.oa.history.length,tieS4.live.length)=(2,1) := by
  norm_num [tieS0,tieS1,tieS2,tieS3,tieS4,stInitial,tieOA2,tieOA1,oaAppend,oaInit]

theorem tie_selector_choices :
    (tieGapSelector tieS0).val=.inr tieS1 ∧
    (tieGapSelector tieS1).val=.inr tieS2 ∧
    (tieGapSelector tieS2).val=.inr tieS3 ∧
    (tieGapSelector tieS3).val=.inr tieS4 ∧
    (tieGapSelector tieS4).val=.inl (.solution tieLeftAnchor) := by
  have distinct {s t : STState 2 1 1}
      (h : (s.oa.history.length,s.live.length)≠(t.oa.history.length,t.live.length)) : s≠t := by
    intro he; exact h (congrArg (fun s => (s.oa.history.length,s.live.length)) he)
  have h10 : tieS1≠tieS0 := distinct (by rw [tie_state_signatures.1,tie_state_signatures.2.1]; decide)
  have h20 : tieS2≠tieS0 := distinct (by rw [tie_state_signatures.1,tie_state_signatures.2.2.1]; decide)
  have h21 : tieS2≠tieS1 := distinct (by rw [tie_state_signatures.2.1,tie_state_signatures.2.2.1]; decide)
  have h30 : tieS3≠tieS0 := distinct (by rw [tie_state_signatures.1,tie_state_signatures.2.2.2.1]; decide)
  have h31 : tieS3≠tieS1 := distinct (by rw [tie_state_signatures.2.1,tie_state_signatures.2.2.2.1]; decide)
  have h32 : tieS3≠tieS2 := distinct (by rw [tie_state_signatures.2.2.1,tie_state_signatures.2.2.2.1]; decide)
  have h40 : tieS4≠tieS0 := distinct (by rw [tie_state_signatures.1,tie_state_signatures.2.2.2.2]; decide)
  have h41 : tieS4≠tieS1 := distinct (by rw [tie_state_signatures.2.1,tie_state_signatures.2.2.2.2]; decide)
  have h42 : tieS4≠tieS2 := distinct (by rw [tie_state_signatures.2.2.1,tie_state_signatures.2.2.2.2]; decide)
  have h43 : tieS4≠tieS3 := distinct (by rw [tie_state_signatures.2.2.2.1,tie_state_signatures.2.2.2.2]; decide)
  simp [tieGapSelector,h10,h20,h21,h30,h31,h32,h40,h41,h42,h43]

theorem tie_gap_first_driver_return :
    stRun tieModel 0 tieGapSelector tieS0 5=.stopped tieS4 (.solution tieLeftAnchor) := by
  simp only [stRun,tie_selector_choices.1,tie_selector_choices.2.1,
    tie_selector_choices.2.2.1,tie_selector_choices.2.2.2.1,tie_selector_choices.2.2.2.2]

theorem tie_gap_first_initialized_certificate :
    STInitialize tieModel none (.inr tieS0) ∧ STTrace tieModel 4 tieS0 tieS4 ∧
    STStop tieModel 0 tieS4 (.solution tieLeftAnchor) ∧
    OAReturnCertificate tieModel 0 (.solution tieLeftAnchor) := by
  exact ⟨tie_initialization,tie_four_process_trace,tie_fourth_zero_gap_stop,
    st_initialized_stop_sound tieModel tie_base_compact tie_rows_convex tie_rows_diff
      (by norm_num) none (by simp) tie_initialization (st_trace_micro _ tie_four_process_trace)
      tie_fourth_zero_gap_stop⟩


/-! Restoration is followed by a strictly better feasible incumbent. -/
def improveSeeds : List (STSeed 1 1 2) := [⟨rpt 0 (1/2),Set.univ⟩]
def improveBatch (y : ℤ) : OABatch 1 1 :=
  ⟨fun _ => y,rpt ((y-1/2)^2) y,none⟩
def improveRestore : OABatch 1 1 := ⟨fun _ => 0,rpt (1/4) 0,some (1/4)⟩

theorem improve_tangent (a q : Point 1 1) (j : Fin 2) :
    tangentRow improveModel (fun j => fderiv ℝ (improveModel.g j) a) a j q=
    if j=0 then (a.2 0-1/2)^2-a.1 0 + 2*(a.2 0-1/2)*(q.2 0-a.2 0)-(q.1 0-a.1 0)
    else (a.2 0-3/2)^2-2+2*(a.2 0-3/2)*(q.2 0-a.2 0) := by
  unfold tangentRow
  dsimp only
  rw [(improve_derivative a j).fderiv]
  fin_cases j <;> simp [improveModel,timeModel,Chapter02SourceRestorationExamples.cx,
    Chapter02SourceRestorationExamples.cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY]
  all_goals ring

theorem improve_seed_iff (q : Point 1 1) :
    q∈stSeedRegion improveModel improveSeeds ↔ 0≤q.1 0 ∧ 0≤q.2 0 := by
  change (∀a∈improveSeeds,∀j∈a.selected,
    tangentRow improveModel (fun j => fderiv ℝ (improveModel.g j) a.origin) a.origin j q≤0) ↔ _
  simp only [improveSeeds,List.mem_singleton,forall_eq,Set.mem_univ,forall_true_left,improve_tangent]
  simp [Fin.forall_fin_succ,rpt,Chapter02SourceRestorationExamples.pt]
  intro h0
  norm_num
  constructor <;> intro h <;> linarith

theorem improve_batch_valid (y : ℤ) (hy : y=1 ∨ y=2) : oaBatchValid improveModel (improveBatch y) := by
  refine ⟨?_,by ext i; simp [improveBatch,rpt,Chapter02SourceRestorationExamples.pt,oaIntCast],?_,?_⟩
  · intro i; rcases hy with rfl | rfl <;> norm_num [improveBatch,improveModel,timeModel]
  · refine ⟨⟨(improve_linear _).mpr ?_,by ext i; simp [improveBatch,rpt,Chapter02SourceRestorationExamples.pt,oaIntCast]⟩,?_⟩
    · rcases hy with rfl | rfl <;> norm_num [improveBatch,rpt,Chapter02SourceRestorationExamples.pt]
    · intro j; rcases hy with rfl | rfl <;> fin_cases j <;>
        norm_num [improveBatch,improveModel,timeModel,rpt,Chapter02SourceRestorationExamples.pt]
  · intro q hq
    have he : q.2 0=(y : ℝ) := by simpa [improveBatch,oaIntCast] using congrFun hq.1.2 0
    have hg := hq.2 (0 : Fin 2)
    change (q.2 0-1/2)^2-q.1 0≤0 at hg
    rw [improve_objective,improve_objective]
    change ((y : ℝ)-1/2)^2≤q.1 0
    rw [he] at hg
    linarith

theorem improve_restore_valid : oaBatchValid improveModel improveRestore := by
  refine ⟨fun _ => by norm_num [improveRestore,improveModel,timeModel],
    by ext i; norm_num [improveRestore,rpt,Chapter02SourceRestorationExamples.pt,oaIntCast],
    improve_zero_fiber_empty,?_,?_⟩
  · refine ⟨⟨(improve_linear _).mpr (by norm_num [improveRestore,rpt,Chapter02SourceRestorationExamples.pt]),
      by ext i; norm_num [improveRestore,rpt,Chapter02SourceRestorationExamples.pt,oaIntCast]⟩,?_⟩
    intro j; fin_cases j <;> norm_num [improveRestore,improveModel,timeModel,rpt,Chapter02SourceRestorationExamples.pt]
  · intro q hq
    have hy : q.1.2 0=0 := by simpa [improveRestore,oaIntCast] using congrFun hq.1.2 0
    have hg := hq.2 (1 : Fin 2)
    change (q.1.2 0-3/2)^2-2≤q.2 at hg
    norm_num [hy] at hg
    exact hg

theorem improve_feasible_cuts (y : ℤ) (q : Point 1 1) :
    oaBatchCuts improveModel (improveBatch y) q ↔
    2*(y-1/2)*(q.2 0-y)≤q.1 0-(y-1/2)^2 ∧
    (y-3/2)^2-2+2*(y-3/2)*(q.2 0-y)≤0 := by
  unfold oaBatchCuts SelectedOARows oaBatchDerivative
  simp only [oaBatchRows,improveBatch,Set.mem_univ,forall_true_left,improve_tangent]
  simp [Fin.forall_fin_succ,rpt,Chapter02SourceRestorationExamples.pt]

theorem improve_restore_cut (q : Point 1 1) :
    oaBatchCuts improveModel improveRestore q ↔ 1/12≤q.2 0 := by
  unfold oaBatchCuts SelectedOARows oaBatchDerivative
  simp only [oaBatchRows,improveRestore,improve_tangent]
  norm_num [Fin.forall_fin_succ,improveModel,timeModel,rpt,Chapter02SourceRestorationExamples.pt]
  constructor <;> intro h <;> linarith

def improveRoot : BBRecord 1 := ⟨bbRootNode improveModel,(0 : ℝ)⟩
def improveLeft : BBRecord 1 := ⟨⟨fun _ => 0,fun _ => 0⟩,(0 : ℝ)⟩
def improveRight : BBRecord 1 := ⟨⟨fun _ => 1,fun _ => 2⟩,(0 : ℝ)⟩
def improveOA1 : OAState 1 1 := oaAppend improveModel (oaInit none) (improveBatch 2)
def improveOA2 : OAState 1 1 := oaAppend improveModel improveOA1 improveRestore
def improveOA3 : OAState 1 1 := oaAppend improveModel improveOA2 (improveBatch 1)

theorem improve_histories : improveOA1.history=[improveBatch 2] ∧
    improveOA2.history=[improveBatch 2,improveRestore] ∧
    improveOA3.history=[improveBatch 2,improveRestore,improveBatch 1] := by
  simp [improveOA1,improveOA2,improveOA3,oaAppend,oaInit]

theorem improve_incumbents : improveOA1.incumbent=some (rpt (9/4) 2) ∧
    improveOA2.incumbent=some (rpt (9/4) 2) ∧ improveOA3.incumbent=some (rpt (1/4) 1) := by
  norm_num [improveOA1,improveOA2,improveOA3,oaAppend,oaInit,oaBest,improveBatch,improveRestore,
    improve_objective,rpt,Chapter02SourceRestorationExamples.pt]

theorem improve_lp_zero_minimum (H : List (OABatch 1 1)) (N : BBNode 1) (y : ℝ)
    (hq : rpt 0 y∈stLP improveModel improveSeeds H N) :
    IsMinimizer (stLP improveModel improveSeeds H N) improveModel.objective (rpt 0 y) :=
  ⟨hq,fun p hp => by rw [improve_objective,improve_objective]; exact ((improve_linear p).mp hp.1).1⟩

theorem improve_root_lp :
    IsMinimizer (stLP improveModel improveSeeds [] improveRoot.node) improveModel.objective (rpt 0 (1/2)) := by
  apply improve_lp_zero_minimum
  refine ⟨(improve_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_,
    (improve_seed_iff _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),by simp⟩
  intro i; norm_num [improveRoot,bbRootNode,improveModel,timeModel,rpt,Chapter02SourceRestorationExamples.pt]

theorem improve_right_first_lp :
    IsMinimizer (stLP improveModel improveSeeds [] improveRight.node) improveModel.objective (rpt 0 2) := by
  apply improve_lp_zero_minimum
  refine ⟨(improve_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_,
    (improve_seed_iff _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),by simp⟩
  intro i; norm_num [improveRight,rpt,Chapter02SourceRestorationExamples.pt]

theorem improve_left_lp :
    IsMinimizer (stLP improveModel improveSeeds improveOA1.history improveLeft.node) improveModel.objective (rpt 0 0) := by
  apply improve_lp_zero_minimum
  refine ⟨(improve_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_,
    (improve_seed_iff _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_⟩
  · intro i; norm_num [improveLeft,rpt,Chapter02SourceRestorationExamples.pt]
  · intro b hb
    have he : b=improveBatch 2 := by simpa [improve_histories.1] using hb
    rw [he,improve_feasible_cuts]
    norm_num [rpt,Chapter02SourceRestorationExamples.pt]

theorem improve_right_second_lp :
    IsMinimizer (stLP improveModel improveSeeds improveOA2.history improveRight.node) improveModel.objective (rpt 0 1) := by
  apply improve_lp_zero_minimum
  refine ⟨(improve_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_,
    (improve_seed_iff _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_⟩
  · intro i; norm_num [improveRight,rpt,Chapter02SourceRestorationExamples.pt]
  · intro b hb
    have he : b=improveBatch 2 ∨ b=improveRestore := by simpa [improve_histories.2.1] using hb
    rcases he with rfl | rfl
    · rw [improve_feasible_cuts]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]
    · rw [improve_restore_cut]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]

theorem improve_left_empty : stLP improveModel improveSeeds improveOA2.history improveLeft.node=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hy := hp.2.1 (0 : Fin 1)
  change (0 : ℝ)≤p.2 0 ∧ p.2 0≤0 at hy
  have hc := (improve_restore_cut p).mp (hp.2.2.2 improveRestore (by simp [improve_histories.2.1]))
  linarith [hy.2]

theorem improve_final_lp :
    IsMinimizer (stLP improveModel improveSeeds improveOA3.history improveRight.node)
      improveModel.objective (rpt (1/4) 1) := by
  refine ⟨⟨(improve_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_,
    (improve_seed_iff _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),?_⟩,?_⟩
  · intro i; norm_num [improveRight,rpt,Chapter02SourceRestorationExamples.pt]
  · intro b hb
    have he : b=improveBatch 2 ∨ b=improveRestore ∨ b=improveBatch 1 := by simpa [improve_histories.2.2] using hb
    rcases he with rfl | rfl | rfl
    · rw [improve_feasible_cuts]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]
    · rw [improve_restore_cut]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]
    · rw [improve_feasible_cuts]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]
  · intro p hp
    have hy := hp.2.1 (0 : Fin 1)
    change (1 : ℝ)≤p.2 0 ∧ p.2 0≤2 at hy
    have hc := (improve_feasible_cuts 1 p).mp (hp.2.2.2 (improveBatch 1) (by simp [improve_histories.2.2]))
    norm_num at hc
    rw [improve_objective,improve_objective]
    change (1/4 : ℝ)≤p.1 0
    linarith [hy.1,hc.1]


def improveS0 : STState 1 1 2 := stInitial improveModel (rpt 0 (1/2)) none
def improveS1 : STState 1 1 2 := ⟨improveSeeds,oaInit none,[improveLeft,improveRight],none⟩
def improveS2 : STState 1 1 2 := ⟨improveSeeds,improveOA1,[improveRight,improveLeft],none⟩
def improveS3 : STState 1 1 2 := ⟨improveSeeds,improveOA2,[improveLeft,improveRight],none⟩
def improveS4 : STState 1 1 2 := ⟨improveSeeds,improveOA2,[improveRight],none⟩
def improveS5 : STState 1 1 2 := ⟨improveSeeds,improveOA3,[improveRight],none⟩
def improveS6 : STState 1 1 2 := ⟨improveSeeds,improveOA3,[],none⟩

theorem improve_initialization : STInitialize improveModel none (.inr improveS0) :=
  .seeded _ improve_root_minimum

theorem improve_children : bbChildren improveRoot 0 (rpt 0 (1/2)) improveModel.objective=
    [improveLeft,improveRight] := by
  have hl : improveRoot.node.left 0 ((rpt 0 (1/2)).2 0)=improveLeft.node := by
    apply congrArg₂ BBNode.mk <;> funext i <;> fin_cases i <;>
      norm_num [improveRoot,improveLeft,bbRootNode,BBNode.left,improveModel,timeModel,
        rpt,Chapter02SourceRestorationExamples.pt,Function.update_apply]
  have hr : improveRoot.node.right 0 ((rpt 0 (1/2)).2 0)=improveRight.node := by
    apply congrArg₂ BBNode.mk <;> funext i <;> fin_cases i <;>
      norm_num [improveRoot,improveRight,bbRootNode,BBNode.right,improveModel,timeModel,
        rpt,Chapter02SourceRestorationExamples.pt,Function.update_apply]
  simp only [bbChildren,hl,hr,improve_objective]
  norm_num [improveRoot,improveLeft,improveRight,rpt,Chapter02SourceRestorationExamples.pt]

theorem improve_raise_zero (b : BBRecord 1) (hb : b.lower=(0 : ℝ)) (y : ℝ) :
    stRaised improveModel b (rpt 0 y)=b := by
  cases b with
  | mk N lb => simp_all [stRaised,improve_objective,rpt,Chapter02SourceRestorationExamples.pt]

theorem improve_step1 : STProcess improveModel improveS0 improveS1 := by
  refine ⟨⟨improveSeeds,oaInit none,[],some improveRoot⟩,?_,?_⟩
  · simpa [improveS0,stInitial,improveSeeds,improveRoot,improve_objective,rpt,Chapter02SourceRestorationExamples.pt]
      using STSelect.choose improveSeeds (oaInit none) [] [] improveRoot
  · have hh := STResolve.branch (d:=improveModel) (seeds:=improveSeeds) (o:=oaInit none)
      (live:=[]) (b:=improveRoot) 0 improve_root_lp (by simp [oaCompetitive,oaInit])
      (show BBFractional ((rpt 0 (1/2)).2 0) by
        rintro ⟨z,hz⟩
        have h0 : (0 : ℝ)<(z : ℝ) := by rw [hz]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]
        have h1 : (z : ℝ)<1 := by rw [hz]; norm_num [rpt,Chapter02SourceRestorationExamples.pt]
        have hi0 : 0<z := by exact_mod_cast h0
        have hi1 : z<1 := by exact_mod_cast h1
        omega)
    simpa only [improve_children,List.append_nil,improveS1] using hh

theorem improve_step2 : STProcess improveModel improveS1 improveS2 := by
  refine ⟨⟨improveSeeds,oaInit none,[improveLeft],some improveRight⟩,
    STSelect.choose improveSeeds (oaInit none) [improveLeft] [] improveRight,?_⟩
  have hh := STResolve.callback (d:=improveModel) (seeds:=improveSeeds) (o:=oaInit none)
    (live:=[improveLeft]) (b:=improveRight) improve_right_first_lp (by simp [oaCompetitive,oaInit])
    (improve_batch_valid 2 (Or.inr rfl))
    (show (rpt 0 2).2=oaIntCast (improveBatch 2).integer by ext i; norm_num [rpt,Chapter02SourceRestorationExamples.pt,improveBatch,oaIntCast])
  simpa only [improve_raise_zero improveRight rfl,improveS2,improveOA1] using hh

theorem improve_step3 : STProcess improveModel improveS2 improveS3 := by
  refine ⟨⟨improveSeeds,improveOA1,[improveRight],some improveLeft⟩,
    STSelect.choose improveSeeds improveOA1 [improveRight] [] improveLeft,?_⟩
  have hh := STResolve.callback (d:=improveModel) (seeds:=improveSeeds) (o:=improveOA1)
    (live:=[improveRight]) (b:=improveLeft) improve_left_lp
    (by intro u hu; rw [improve_incumbents.1] at hu; cases hu;
        norm_num [improve_objective,rpt,Chapter02SourceRestorationExamples.pt])
    improve_restore_valid
    (show (rpt 0 0).2=oaIntCast improveRestore.integer by ext i; norm_num [rpt,Chapter02SourceRestorationExamples.pt,improveRestore,oaIntCast])
  simpa only [improve_raise_zero improveLeft rfl,improveS3,improveOA2] using hh

theorem improve_step4 : STProcess improveModel improveS3 improveS4 :=
  ⟨_,STSelect.choose improveSeeds improveOA2 [] [improveRight] improveLeft,STResolve.empty improve_left_empty⟩

theorem improve_step5 : STProcess improveModel improveS4 improveS5 := by
  refine ⟨⟨improveSeeds,improveOA2,[],some improveRight⟩,
    STSelect.choose improveSeeds improveOA2 [] [] improveRight,?_⟩
  have hh := STResolve.callback (d:=improveModel) (seeds:=improveSeeds) (o:=improveOA2)
    (live:=[]) (b:=improveRight) improve_right_second_lp
    (by intro u hu; rw [improve_incumbents.2.1] at hu; cases hu;
        norm_num [improve_objective,rpt,Chapter02SourceRestorationExamples.pt])
    (improve_batch_valid 1 (Or.inl rfl))
    (show (rpt 0 1).2=oaIntCast (improveBatch 1).integer by ext i; norm_num [rpt,Chapter02SourceRestorationExamples.pt,improveBatch,oaIntCast])
  simpa only [improve_raise_zero improveRight rfl,improveS5,improveOA3] using hh

theorem improve_step6 : STProcess improveModel improveS5 improveS6 := by
  refine ⟨_,STSelect.choose improveSeeds improveOA3 [] [] improveRight,STResolve.prune improve_final_lp ?_⟩
  simp [bbPrunable,improve_incumbents.2.2]

theorem improve_six_process_trace : STTrace improveModel 6 improveS0 improveS6 :=
  .cons improve_step1 (.cons improve_step2 (.cons improve_step3 (.cons improve_step4
    (.cons improve_step5 (.cons improve_step6 (.nil improveS6))))))

theorem improve_final_stop : STStop improveModel 0 improveS6 (.solution (rpt (1/4) 1)) :=
  .exhausted rfl rfl improve_incumbents.2.2

theorem restoration_then_strict_incumbent_improvement :
    STInitialize improveModel none (.inr improveS0) ∧ STTrace improveModel 6 improveS0 improveS6 ∧
    improveS2.oa.incumbent=some (rpt (9/4) 2) ∧ improveS3.oa.incumbent=some (rpt (9/4) 2) ∧
    improveS5.oa.incumbent=some (rpt (1/4) 1) ∧
    improveModel.objective (rpt (1/4) 1) < improveModel.objective (rpt (9/4) 2) ∧
    IsMinimizer (improveModel.feasibleOn Set.univ) improveModel.objective (rpt (1/4) 1) := by
  exact ⟨improve_initialization,improve_six_process_trace,improve_incumbents.1,
    improve_incumbents.2.1,improve_incumbents.2.2,
    by norm_num [improve_objective,rpt,Chapter02SourceRestorationExamples.pt],
    st_zero_certificate_exact improveModel _ (st_initialized_stop_sound improveModel improve_base_compact
      improve_rows_convex improve_rows_diff (by norm_num) none (by simp) improve_initialization
      (st_trace_micro _ improve_six_process_trace) improve_final_stop)⟩


/-! A callback cut reaches a waiting sibling through the shared history. -/
def spt (t y z : ℝ) : Point 1 2 := tpt t ![y,z]
def siblingModel : ModelData 1 2 1 2 := timeModel 2 1
  (fun _ p => (p.2 0-1/2)^2/4+(p.2 1-1/2)^2-p.1 0) 1 1

def scx : Point 1 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector 2))
def scy (i : Fin 2) : Point 1 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (RealVector 1) (RealVector 2))

theorem sibling_linear (p : Point 1 2) : p∈siblingModel.linearRegion ↔ 0≤p.1 0 ∧ p.1 0≤1 :=
  time_linear _ _ _ _ _ _
theorem sibling_objective (p : Point 1 2) : siblingModel.objective p=p.1 0 :=
  time_objective _ _ _ _ _ _
theorem sibling_base_compact : IsCompact (bbMixedBase siblingModel siblingModel.lo siblingModel.hi) :=
  time_base_compact _ _ _ _ _

theorem sibling_rows_convex : ∀j,ConvexOn ℝ Set.univ (siblingModel.g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have hh0 := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.2 0-q.2 0))
  have hh1 := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.2 1-q.2 1))
  have he : t=1-s := by linarith
  simp [siblingModel,timeModel,smul_eq_mul]
  rw [he] at hh0 hh1 ⊢
  nlinarith

theorem sibling_rows_C2 : ∀j,ContDiff ℝ 2 (siblingModel.g j) := by
  intro j
  exact ((((((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 2)).comp contDiff_snd).sub contDiff_const).pow 2).div_const 4).add
    ((((contDiff_apply ℝ (fun _ => ℝ) (1 : Fin 2)).comp contDiff_snd).sub contDiff_const).pow 2)).sub
    ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst)

theorem sibling_rows_diff : ∀j,Differentiable ℝ (siblingModel.g j) :=
  fun j => (sibling_rows_C2 j).differentiable (by norm_num)

theorem sibling_derivative (p : Point 1 2) (j : Fin 1) :
    HasFDerivAt (siblingModel.g j) (((2*(p.2 0-1/2))/4) • scy 0+
      (2*(p.2 1-1/2)) • scy 1-scx) p := by
  have h0 := ((hasDerivAt_pow 2 (p.2 0-1/2)).comp_hasFDerivAt p
    ((scy 0).hasFDerivAt.sub_const (1/2))).const_mul (1/4)
  have h1 := (hasDerivAt_pow 2 (p.2 1-1/2)).comp_hasFDerivAt p
    ((scy 1).hasFDerivAt.sub_const (1/2))
  have hh := (h0.fun_add h1).fun_sub scx.hasFDerivAt
  convert hh using 1 <;> simp [siblingModel,timeModel,scx,scy,Function.comp_def,smul_smul,div_eq_mul_inv] <;> ring_nf

theorem sibling_fiber_slater : OAFiberSlater siblingModel := by
  intro y hy _
  have hy0 := hy (0 : Fin 2)
  have hy1 := hy (1 : Fin 2)
  change (0 : ℝ)≤(y 0 : ℝ) ∧ (y 0 : ℝ)≤1 at hy0
  change (0 : ℝ)≤(y 1 : ℝ) ∧ (y 1 : ℝ)≤1 at hy1
  have hsq0 : ((y 0 : ℝ)-1/2)^2≤1/4 := by nlinarith [mul_nonneg hy0.1 (sub_nonneg.mpr hy0.2)]
  have hsq1 : ((y 1 : ℝ)-1/2)^2≤1/4 := by nlinarith [mul_nonneg hy1.1 (sub_nonneg.mpr hy1.2)]
  refine ⟨tpt 1 (oaIntCast y),⟨(sibling_linear _).mpr (by norm_num [tpt]),rfl⟩,?_⟩
  intro j
  change ((y 0 : ℝ)-1/2)^2/4+((y 1 : ℝ)-1/2)^2-1<0
  linarith

theorem sibling_root_minimum :
    IsMinimizer (siblingModel.relaxationOn Set.univ) siblingModel.objective (spt 0 (1/2) (1/2)) := by
  refine ⟨⟨⟨Set.mem_univ _,fun _ => by norm_num [siblingModel,timeModel,spt,tpt]⟩,
    (sibling_linear _).mpr (by norm_num [spt,tpt]),?_⟩,?_⟩
  · intro i; fin_cases i <;> norm_num [siblingModel,timeModel,spt,tpt]
  · intro p hp
    rw [sibling_objective,sibling_objective]
    exact ((sibling_linear p).mp hp.2.1).1

def siblingSeeds : List (STSeed 1 2 1) := [⟨spt 0 (1/2) (1/2),Set.univ⟩]
def siblingBatch : OABatch 1 2 := ⟨fun _ => 1,spt (5/16) 1 1,none⟩
def siblingRoot : BBRecord 2 := ⟨bbRootNode siblingModel,(0 : ℝ)⟩
def siblingLeft : BBRecord 2 := ⟨⟨![0,0],![0,1]⟩,(0 : ℝ)⟩
def siblingRight : BBRecord 2 := ⟨⟨![1,0],![1,1]⟩,(0 : ℝ)⟩

theorem sibling_seed_iff (q : Point 1 2) :
    q∈stSeedRegion siblingModel siblingSeeds ↔ 0≤q.1 0 := by
  constructor
  · intro h
    have hh := h ⟨spt 0 (1/2) (1/2),Set.univ⟩ (by simp [siblingSeeds]) 0 (Set.mem_univ _)
    rw [(sibling_derivative _ _).fderiv] at hh
    norm_num [siblingModel,timeModel,spt,tpt,scx,scy] at hh
    exact hh
  · intro h a ha j hj
    have he : a=⟨spt 0 (1/2) (1/2),Set.univ⟩ := by simpa [siblingSeeds] using ha
    subst a
    rw [(sibling_derivative _ _).fderiv]
    norm_num [siblingModel,timeModel,spt,tpt,scx,scy]
    exact h

theorem sibling_batch_valid : oaBatchValid siblingModel siblingBatch := by
  refine ⟨fun _ => by norm_num [siblingModel,timeModel,siblingBatch],
    by ext i; fin_cases i <;> norm_num [siblingBatch,spt,tpt,oaIntCast],?_,?_⟩
  · exact ⟨⟨(sibling_linear _).mpr (by norm_num [siblingBatch,spt,tpt]),
      by ext i; fin_cases i <;> norm_num [siblingBatch,spt,tpt,oaIntCast]⟩,
      fun _ => by norm_num [siblingBatch,spt,tpt,siblingModel,timeModel]⟩
  · intro q hq
    have hy0 : q.2 0=1 := by simpa [siblingBatch,oaIntCast] using congrFun hq.1.2 0
    have hy1 : q.2 1=1 := by simpa [siblingBatch,oaIntCast] using congrFun hq.1.2 1
    have hg := hq.2 (0 : Fin 1)
    change (q.2 0-1/2)^2/4+(q.2 1-1/2)^2-q.1 0≤0 at hg
    norm_num [hy0,hy1] at hg
    rw [sibling_objective,sibling_objective]
    change (5/16 : ℝ)≤q.1 0
    linarith

theorem sibling_cut (q : Point 1 2) :
    oaBatchCuts siblingModel siblingBatch q ↔ q.2 0/4+q.2 1-15/16≤q.1 0 := by
  have ht (j : Fin 1) : tangentRow siblingModel (oaBatchDerivative siblingModel siblingBatch)
      siblingBatch.anchor j q=q.2 0/4+q.2 1-15/16-q.1 0 := by
    unfold tangentRow oaBatchDerivative
    rw [(sibling_derivative _ _).fderiv]
    norm_num [siblingBatch,siblingModel,timeModel,spt,tpt,scx,scy,Matrix.vecHead,Matrix.vecTail]
    ring_nf
  simp only [oaBatchCuts,SelectedOARows,oaBatchRows,siblingBatch,Set.mem_univ,forall_true_left]
  change (∀j,tangentRow siblingModel (oaBatchDerivative siblingModel siblingBatch) siblingBatch.anchor j q≤0) ↔ _
  simp only [ht,forall_const]
  constructor <;> intro h <;> linarith

theorem sibling_empty_history_lp_iff (N : BBNode 2) (q : Point 1 2) :
    q∈stLP siblingModel siblingSeeds [] N ↔ q∈siblingModel.linearRegion ∧ q∈N.box := by
  constructor
  · exact fun h => ⟨h.1,h.2.1⟩
  · rintro ⟨hl,hb⟩
    exact ⟨hl,hb,(sibling_seed_iff q).mpr ((sibling_linear q).mp hl).1,by simp⟩

theorem sibling_empty_history_lp_min (N : BBNode 2) (y z : ℝ) (hb : spt 0 y z∈N.box) :
    IsMinimizer (stLP siblingModel siblingSeeds [] N) siblingModel.objective (spt 0 y z) := by
  refine ⟨(sibling_empty_history_lp_iff N _).mpr ⟨(sibling_linear _).mpr (by norm_num [spt,tpt]),hb⟩,?_⟩
  intro p hp
  rw [sibling_objective,sibling_objective]
  exact ((sibling_linear p).mp hp.1).1

theorem sibling_root_lp :
    IsMinimizer (stLP siblingModel siblingSeeds [] siblingRoot.node) siblingModel.objective (spt 0 (1/2) (1/2)) := by
  apply sibling_empty_history_lp_min
  intro i; fin_cases i <;> norm_num [siblingRoot,bbRootNode,siblingModel,timeModel,spt,tpt]

theorem sibling_right_lp :
    IsMinimizer (stLP siblingModel siblingSeeds [] siblingRight.node) siblingModel.objective (spt 0 1 1) := by
  apply sibling_empty_history_lp_min
  intro i; fin_cases i <;> norm_num [siblingRight,spt,tpt]

theorem sibling_waiting_old_lp :
    IsMinimizer (stLP siblingModel siblingSeeds [] siblingLeft.node) siblingModel.objective (spt 0 0 1) := by
  apply sibling_empty_history_lp_min
  intro i; fin_cases i <;> norm_num [siblingLeft,spt,tpt]

def siblingOA1 : OAState 1 2 := oaAppend siblingModel (oaInit none) siblingBatch
def siblingS0 : STState 1 2 1 := stInitial siblingModel (spt 0 (1/2) (1/2)) none
def siblingS1 : STState 1 2 1 := ⟨siblingSeeds,oaInit none,[siblingLeft,siblingRight],none⟩
def siblingS2 : STState 1 2 1 := ⟨siblingSeeds,siblingOA1,[siblingRight,siblingLeft],none⟩

theorem sibling_initialization : STInitialize siblingModel none (.inr siblingS0) :=
  .seeded _ sibling_root_minimum

theorem sibling_children : bbChildren siblingRoot 0 (spt 0 (1/2) (1/2)) siblingModel.objective=
    [siblingLeft,siblingRight] := by
  have hl : siblingRoot.node.left 0 ((spt 0 (1/2) (1/2)).2 0)=siblingLeft.node := by
    apply congrArg₂ BBNode.mk <;> funext i <;> fin_cases i <;>
      norm_num [siblingRoot,siblingLeft,bbRootNode,BBNode.left,siblingModel,timeModel,spt,tpt,Function.update_apply]
  have hr : siblingRoot.node.right 0 ((spt 0 (1/2) (1/2)).2 0)=siblingRight.node := by
    apply congrArg₂ BBNode.mk <;> funext i <;> fin_cases i <;>
      norm_num [siblingRoot,siblingRight,bbRootNode,BBNode.right,siblingModel,timeModel,spt,tpt,Function.update_apply]
  simp only [bbChildren,hl,hr,sibling_objective]
  norm_num [siblingRoot,siblingLeft,siblingRight,spt,tpt]

theorem sibling_step1 : STProcess siblingModel siblingS0 siblingS1 := by
  refine ⟨⟨siblingSeeds,oaInit none,[],some siblingRoot⟩,?_,?_⟩
  · simpa [siblingS0,stInitial,siblingSeeds,siblingRoot,sibling_objective,spt,tpt]
      using STSelect.choose siblingSeeds (oaInit none) [] [] siblingRoot
  · have hh := STResolve.branch (d:=siblingModel) (seeds:=siblingSeeds) (o:=oaInit none)
      (live:=[]) (b:=siblingRoot) 0 sibling_root_lp (by simp [oaCompetitive,oaInit])
      (show BBFractional ((spt 0 (1/2) (1/2)).2 0) by
        rintro ⟨z,hz⟩
        have h0 : (0 : ℝ)<(z : ℝ) := by rw [hz]; norm_num [spt,tpt]
        have h1 : (z : ℝ)<1 := by rw [hz]; norm_num [spt,tpt]
        have hi0 : 0<z := by exact_mod_cast h0
        have hi1 : z<1 := by exact_mod_cast h1
        omega)
    simpa only [sibling_children,List.append_nil,siblingS1] using hh

theorem sibling_step2 : STProcess siblingModel siblingS1 siblingS2 := by
  refine ⟨⟨siblingSeeds,oaInit none,[siblingLeft],some siblingRight⟩,
    STSelect.choose siblingSeeds (oaInit none) [siblingLeft] [] siblingRight,?_⟩
  have hh := STResolve.callback (d:=siblingModel) (seeds:=siblingSeeds) (o:=oaInit none)
    (live:=[siblingLeft]) (b:=siblingRight) sibling_right_lp (by simp [oaCompetitive,oaInit])
    sibling_batch_valid
    (show (spt 0 1 1).2=oaIntCast siblingBatch.integer by ext i; fin_cases i <;> norm_num [spt,tpt,siblingBatch,oaIntCast])
  have hr : stRaised siblingModel siblingRight (spt 0 1 1)=siblingRight := by
    norm_num [stRaised,siblingRight,sibling_objective,spt,tpt]
  simpa only [hr,siblingS2,siblingOA1] using hh

theorem sibling_two_process_trace : STTrace siblingModel 2 siblingS0 siblingS2 :=
  .cons sibling_step1 (.cons sibling_step2 (.nil siblingS2))

theorem sibling_global_cut_excludes_old_trial :
    spt 0 0 1∉stLP siblingModel siblingS2.seeds siblingS2.oa.history siblingLeft.node := by
  intro hp
  have hc := (sibling_cut _).mp (hp.2.2.2 siblingBatch (by simp [siblingS2,siblingOA1,oaAppend,oaInit]))
  norm_num [spt,tpt] at hc

/-- The local-only ablation keeps the waiting node's old empty history.  It
admits an old optimum that the actual shared-history process excludes. -/
theorem waiting_sibling_global_cut_local_only_ablation :
    STInitialize siblingModel none (.inr siblingS0) ∧ STTrace siblingModel 2 siblingS0 siblingS2 ∧
    siblingLeft∈siblingS1.live ∧ siblingLeft∈siblingS2.live ∧
    IsMinimizer (stLP siblingModel siblingSeeds [] siblingLeft.node) siblingModel.objective (spt 0 0 1) ∧
    spt 0 0 1∉stLP siblingModel siblingS2.seeds siblingS2.oa.history siblingLeft.node := by
  exact ⟨sibling_initialization,sibling_two_process_trace,by simp [siblingS1],by simp [siblingS2],
    sibling_waiting_old_lp,sibling_global_cut_excludes_old_trial⟩

theorem sibling_reachable_invariant : STInvariant siblingModel siblingS2 :=
  st_trace_invariant siblingModel sibling_base_compact sibling_rows_convex sibling_rows_diff
    (st_initial_invariant siblingModel _ none (by simp) sibling_root_minimum) sibling_two_process_trace


/-- A concrete guard check, separate from a legal raw process trace. -/
theorem no_zero_stop_of_stored_gap {n m l r : ℕ} (d : ModelData n m l r)
    (s : STState n m l) (v : ℝ) (hne : s.live≠[]) (hb : stGlobalBound d s=bbValue v)
    (hg : ∀u,s.oa.incumbent=some u → v<d.objective u) :
    ∀out,¬STStop d 0 s out := by
  intro out h
  cases h with
  | infeasible hr he hi => exact hne he
  | exhausted hr he hi => exact hne he
  | gap lower hr hi hbound htest =>
    rw [hb] at hbound
    have hl := bb_value_le_value.mp hbound
    have hu := hg _ hi
    linarith

theorem tie_prefix_no_zero_stop :
    (∀out,¬STStop tieModel 0 tieS0 out) ∧ (∀out,¬STStop tieModel 0 tieS1 out) ∧
    (∀out,¬STStop tieModel 0 tieS2 out) ∧ (∀out,¬STStop tieModel 0 tieS3 out) := by
  have h0 : stGlobalBound tieModel tieS0=bbValue (-3/4) := by
    norm_num [stGlobalBound,stBoundState,stFrontier,tieS0,stInitial,oaInit,bbGlobalBound,
      bbIncBound,bbLiveBound,bbValue,tie_objective,tieRootPoint,pt]
  have h1 : stGlobalBound tieModel tieS1=bbValue (-3/4) := by
    norm_num [stGlobalBound,stBoundState,stFrontier,tieS1,oaInit,bbGlobalBound,
      bbIncBound,bbLiveBound,bbValue,tieLeftRecord,tieRightRecord]
  have h2 : stGlobalBound tieModel tieS2=bbValue (-3/4) := by
    rw [←tie_repeat_start]
    exact tie_repeat_global_bound 0
  have h3 : stGlobalBound tieModel tieS3=bbValue (-3/4) := by
    norm_num [stGlobalBound,stBoundState,stFrontier,tieS3,tieOA1,oaAppend,oaInit,oaBest,tieRightBatch,
      bbGlobalBound,bbIncBound,bbLiveBound,bbValue,tieLeftRecord,tie_objective,tieRightAnchor,pt]
  exact ⟨no_zero_stop_of_stored_gap tieModel tieS0 (-3/4) (by simp [tieS0,stInitial]) h0 (by simp [tieS0,stInitial,oaInit]),
    no_zero_stop_of_stored_gap tieModel tieS1 (-3/4) (by simp [tieS1]) h1 (by simp [tieS1,oaInit]),
    no_zero_stop_of_stored_gap tieModel tieS2 (-3/4) (by simp [tieS2]) h2 (by
      intro u hu
      have he : u=tieRightAnchor := by simpa [tieS2,tieOA1,oaAppend,oaInit,tieRightBatch,oaBest] using hu.symm
      rw [he]; norm_num [tie_objective,tieRightAnchor,pt]),
    no_zero_stop_of_stored_gap tieModel tieS3 (-3/4) (by simp [tieS3]) h3 (by
      intro u hu
      have he : u=tieRightAnchor := by simpa [tieS3,tieOA1,oaAppend,oaInit,tieRightBatch,oaBest] using hu.symm
      rw [he]; norm_num [tie_objective,tieRightAnchor,pt])⟩

theorem improve_prefix_global_bounds :
    stGlobalBound improveModel improveS0=bbValue 0 ∧ stGlobalBound improveModel improveS1=bbValue 0 ∧
    stGlobalBound improveModel improveS2=bbValue 0 ∧ stGlobalBound improveModel improveS3=bbValue 0 ∧
    stGlobalBound improveModel improveS4=bbValue 0 ∧ stGlobalBound improveModel improveS5=bbValue 0 := by
  norm_num [stGlobalBound,stBoundState,stFrontier,improveS0,improveS1,improveS2,improveS3,improveS4,improveS5,
    stInitial,improveOA1,improveOA2,improveOA3,oaAppend,oaInit,oaBest,improveBatch,improveRestore,
    improve_objective,rpt,Chapter02SourceRestorationExamples.pt,improveLeft,improveRight,
    bbGlobalBound,bbIncBound,bbLiveBound,bbValue]

theorem improve_prefix_no_zero_stop :
    (∀out,¬STStop improveModel 0 improveS0 out) ∧ (∀out,¬STStop improveModel 0 improveS1 out) ∧
    (∀out,¬STStop improveModel 0 improveS2 out) ∧ (∀out,¬STStop improveModel 0 improveS3 out) ∧
    (∀out,¬STStop improveModel 0 improveS4 out) ∧ (∀out,¬STStop improveModel 0 improveS5 out) := by
  have h1 : ∀u,improveOA1.incumbent=some u → 0 < improveModel.objective u := by
    intro u hu; rw [improve_incumbents.1] at hu; cases hu
    norm_num [improve_objective,rpt,Chapter02SourceRestorationExamples.pt]
  have h2 : ∀u,improveOA2.incumbent=some u → 0 < improveModel.objective u := by
    intro u hu; rw [improve_incumbents.2.1] at hu; cases hu
    norm_num [improve_objective,rpt,Chapter02SourceRestorationExamples.pt]
  have h3 : ∀u,improveOA3.incumbent=some u → 0 < improveModel.objective u := by
    intro u hu; rw [improve_incumbents.2.2] at hu; cases hu
    norm_num [improve_objective,rpt,Chapter02SourceRestorationExamples.pt]
  exact ⟨no_zero_stop_of_stored_gap improveModel improveS0 0 (by simp [improveS0,stInitial])
      improve_prefix_global_bounds.1 (by simp [improveS0,stInitial,oaInit]),
    no_zero_stop_of_stored_gap improveModel improveS1 0 (by simp [improveS1]) improve_prefix_global_bounds.2.1 (by simp [improveS1,oaInit]),
    no_zero_stop_of_stored_gap improveModel improveS2 0 (by simp [improveS2]) improve_prefix_global_bounds.2.2.1 h1,
    no_zero_stop_of_stored_gap improveModel improveS3 0 (by simp [improveS3]) improve_prefix_global_bounds.2.2.2.1 h2,
    no_zero_stop_of_stored_gap improveModel improveS4 0 (by simp [improveS4]) improve_prefix_global_bounds.2.2.2.2.1 h2,
    no_zero_stop_of_stored_gap improveModel improveS5 0 (by simp [improveS5]) improve_prefix_global_bounds.2.2.2.2.2 h3⟩


/-- Raw exhaustion has no tolerance guard. Nonnegative tolerance is needed by
its public certificate theorem, even at the exact initialized optimum. -/
theorem negative_tolerance_initialized_control :
    STInitialize tieModel none (.inr tieS0) ∧ STTrace tieModel 5 tieS0 tieS5 ∧
    STStop tieModel (-1) tieS5 (.solution tieLeftAnchor) ∧
    ¬OAReturnCertificate tieModel (-1) (.solution tieLeftAnchor) ∧ ¬(0 : ℝ)≤-1 := by
  refine ⟨tie_initialization,tie_five_process_trace,?_,?_,by norm_num⟩
  · apply STStop.exhausted rfl rfl
    norm_num [tieS5,tieOA2,tieOA1,oaAppend,oaInit,tieRightBatch,tieLeftBatch,oaBest,
      tie_objective,tieRightAnchor,tieLeftAnchor,pt]
  · rintro ⟨hp,lb,hlb,ht⟩
    have hh := hlb _ hp
    linarith

/-- This ablation is a separately named local tolerance test. It is not a
constructor of STResolve and does not retain a retired-node bound. -/
inductive LocalTolerancePrune (d : ModelData n m l r) (eps : ℝ) :
    STState n m l → STState n m l → Prop
  | prune {seeds : List (STSeed n m l)} {o : OAState n m} {live : List (BBRecord m)}
      {b : BBRecord m} {q u : Point n m}
      (hq : IsMinimizer (stLP d seeds o.history b.node) d.objective q)
      (hu : o.incumbent=some u) (ht : d.objective u≤d.objective q+eps) :
      LocalTolerancePrune d eps ⟨seeds,o,live,some b⟩ ⟨seeds,o,live,none⟩

def tieLocalWorking : STState 2 1 1 := ⟨tieSeeds,tieOA1,[tieRightRaised],some tieLeftRecord⟩

theorem tie_local_tolerance_bad_drop :
    STSelect tieS2 tieLocalWorking ∧ LocalTolerancePrune tieModel (1/2) tieLocalWorking tieOmittedLeft ∧
    ¬STInvariant tieModel tieOmittedLeft := by
  refine ⟨STSelect.choose tieSeeds tieOA1 [tieRightRaised] [] tieLeftRecord,?_,tie_omitted_sibling_unsound⟩
  apply LocalTolerancePrune.prune
    (tie_left_lp_minimum tieOA1.history (by simp [TieHistory,tieOA1,oaAppend,oaInit]))
    (show tieOA1.incumbent=some tieRightAnchor by simp [tieOA1,oaAppend,oaInit,tieRightBatch,oaBest])
  norm_num [tie_objective,tieRightAnchor,tieLeftTrial,pt]

theorem tie_global_half_tolerance_not_stopped : ∀out,¬STStop tieModel (1/2) tieS2 out := by
  intro out h
  cases h with
  | infeasible hr he hi => simp [tieS2] at he
  | exhausted hr he hi => simp [tieS2] at he
  | @gap u lower hr hi hb ht =>
    have he : u=tieRightAnchor := by simpa [tieS2,tieOA1,oaAppend,oaInit,tieRightBatch,oaBest] using hi.symm
    rw [he,tie_objective] at ht
    norm_num [tieRightAnchor,pt] at ht
    rw [←tie_repeat_start,tie_repeat_global_bound] at hb
    have hl := bb_value_le_value.mp hb
    linarith


theorem main_control_source_hypotheses :
    (IsCompact (bbMixedBase tieModel tieModel.lo tieModel.hi) ∧
      (∀j,ConvexOn ℝ Set.univ (tieModel.g j)) ∧ (∀j,ContDiff ℝ 2 (tieModel.g j)) ∧ OAFiberSlater tieModel) ∧
    (IsCompact (bbMixedBase rootGapModel rootGapModel.lo rootGapModel.hi) ∧
      (∀j,ConvexOn ℝ Set.univ (rootGapModel.g j)) ∧ (∀j,ContDiff ℝ 2 (rootGapModel.g j)) ∧ OAFiberSlater rootGapModel) ∧
    (IsCompact (bbMixedBase improveModel improveModel.lo improveModel.hi) ∧
      (∀j,ConvexOn ℝ Set.univ (improveModel.g j)) ∧ (∀j,ContDiff ℝ 2 (improveModel.g j)) ∧ OAFiberSlater improveModel) ∧
    (IsCompact (bbMixedBase siblingModel siblingModel.lo siblingModel.hi) ∧
      (∀j,ConvexOn ℝ Set.univ (siblingModel.g j)) ∧ (∀j,ContDiff ℝ 2 (siblingModel.g j)) ∧ OAFiberSlater siblingModel) :=
  ⟨⟨tie_base_compact,tie_rows_convex,tie_rows_C2,tie_fiber_slater⟩,
    ⟨root_gap_base_compact,root_gap_rows_convex,root_gap_rows_C2,root_gap_fiber_slater_vacuous⟩,
    ⟨improve_base_compact,improve_rows_convex,improve_rows_C2,improve_fiber_slater⟩,
    ⟨sibling_base_compact,sibling_rows_convex,sibling_rows_C2,sibling_fiber_slater⟩⟩

theorem sibling_prefix_global_bounds :
    stGlobalBound siblingModel siblingS0=bbValue 0 ∧ stGlobalBound siblingModel siblingS1=bbValue 0 ∧
    stGlobalBound siblingModel siblingS2=bbValue 0 := by
  norm_num [stGlobalBound,stBoundState,stFrontier,siblingS0,siblingS1,siblingS2,stInitial,
    siblingOA1,oaAppend,oaInit,oaBest,siblingBatch,sibling_objective,spt,tpt,siblingLeft,siblingRight,
    bbGlobalBound,bbIncBound,bbLiveBound,bbValue]

theorem sibling_prefix_no_zero_stop :
    (∀out,¬STStop siblingModel 0 siblingS0 out) ∧ (∀out,¬STStop siblingModel 0 siblingS1 out) ∧
    (∀out,¬STStop siblingModel 0 siblingS2 out) := by
  exact ⟨no_zero_stop_of_stored_gap siblingModel siblingS0 0 (by simp [siblingS0,stInitial])
      sibling_prefix_global_bounds.1 (by simp [siblingS0,stInitial,oaInit]),
    no_zero_stop_of_stored_gap siblingModel siblingS1 0 (by simp [siblingS1])
      sibling_prefix_global_bounds.2.1 (by simp [siblingS1,oaInit]),
    no_zero_stop_of_stored_gap siblingModel siblingS2 0 (by simp [siblingS2])
      sibling_prefix_global_bounds.2.2 (by
        intro u hu
        have he : u=spt (5/16) 1 1 := by simpa [siblingS2,siblingOA1,oaAppend,oaInit,oaBest,siblingBatch] using hu.symm
        rw [he]; norm_num [sibling_objective,spt,tpt])⟩

/-- The concrete sibling prefix belongs to a model on which every valid
repaired selector terminates. No particular eleven-cycle continuation is asserted. -/
theorem sibling_every_selector_returns (choose : STSelector siblingModel 0) :
    ∃t out k,k≤(bbRootNode siblingModel).weight+(oaBox siblingModel).card ∧
      STTrace siblingModel k siblingS0 t ∧ STMicroTrace siblingModel (2*k) siblingS0 t ∧
      STStop siblingModel 0 t out ∧
      stRun siblingModel 0 choose siblingS0 ((bbRootNode siblingModel).weight+(oaBox siblingModel).card+1)=.stopped t out ∧
      STExactOutcome siblingModel out :=
  st_every_initialized_selector_exact_return siblingModel sibling_base_compact sibling_rows_convex
    sibling_rows_diff sibling_fiber_slater none (by simp) choose sibling_initialization


/-- Positive controls have actual original feasible points; the bound-gap
control intentionally has no feasible integer fiber and a nonempty mixed base. -/
theorem main_control_nonvacuity :
    (tieModel.feasibleOn Set.univ).Nonempty ∧
    (improveModel.feasibleOn Set.univ).Nonempty ∧
    (siblingModel.feasibleOn Set.univ).Nonempty ∧
    (bbMixedBase rootGapModel rootGapModel.lo rootGapModel.hi).Nonempty ∧
    ¬(rootGapModel.feasibleOn Set.univ).Nonempty := by
  obtain ⟨_,_,_,_,_,_,hi⟩ := restoration_then_strict_incumbent_improvement
  refine ⟨⟨_,tie_source_full_trace_optimal.2.2.1⟩,⟨_,hi.1⟩,?_,?_,gap_source_full_return.2.2⟩
  · refine ⟨siblingBatch.anchor,sibling_reachable_invariant.oa.feasible _ ?_⟩
    simp [siblingS2,siblingOA1,oaAppend,oaInit,oaBest,siblingBatch]
  · refine ⟨rpt 0 0,(root_gap_linear _).mpr (by norm_num [rpt,Chapter02SourceRestorationExamples.pt]),
      (fun _ => 0),?_,?_⟩
    · intro i; norm_num [rootGapModel,Chapter02SourceRestorationExamples.boxModel]
    · ext i; norm_num [rpt,Chapter02SourceRestorationExamples.pt]

end Chapter02STExamples


#print axioms Chapter02STExamples.tie_objective
#print axioms Chapter02STExamples.tie_linear
#print axioms Chapter02STExamples.tie_base_compact
#print axioms Chapter02STExamples.tie_rows_convex
#print axioms Chapter02STExamples.tie_rows_C2
#print axioms Chapter02STExamples.tie_rows_diff
#print axioms Chapter02STExamples.tie_derivative
#print axioms Chapter02STExamples.tie_fiber_slater
#print axioms Chapter02STExamples.tie_root_minimum
#print axioms Chapter02STExamples.tie_seed_trivial
#print axioms Chapter02STExamples.tie_right_batch_valid
#print axioms Chapter02STExamples.tie_left_batch_valid
#print axioms Chapter02STExamples.tie_batch_cuts_trivial
#print axioms Chapter02STExamples.tie_lp_iff
#print axioms Chapter02STExamples.tie_root_lp_minimum
#print axioms Chapter02STExamples.tie_right_lp_minimum
#print axioms Chapter02STExamples.tie_left_lp_minimum
#print axioms Chapter02STExamples.tie_initialization
#print axioms Chapter02STExamples.tie_children
#print axioms Chapter02STExamples.tie_raise_right
#print axioms Chapter02STExamples.tie_raise_left
#print axioms Chapter02STExamples.tie_step1
#print axioms Chapter02STExamples.tie_step2
#print axioms Chapter02STExamples.tie_step3
#print axioms Chapter02STExamples.tie_step4
#print axioms Chapter02STExamples.tie_step5
#print axioms Chapter02STExamples.tie_five_process_trace
#print axioms Chapter02STExamples.tie_final_stop
#print axioms Chapter02STExamples.tie_source_full_trace_optimal
#print axioms Chapter02STExamples.tie_repeat_start
#print axioms Chapter02STExamples.tie_repeat_append
#print axioms Chapter02STExamples.tie_raise_right_again
#print axioms Chapter02STExamples.tie_repeat_lp_minimum
#print axioms Chapter02STExamples.tie_repeat_actual_strict_callback
#print axioms Chapter02STExamples.tie_repeat_global_bound
#print axioms Chapter02STExamples.tie_repeat_trial_infeasible
#print axioms Chapter02STExamples.tie_repeat_no_global_stop
#print axioms Chapter02STExamples.tie_repeat_weak_guard_closes
#print axioms Chapter02STExamples.tie_source_initialized_strict_stall
#print axioms Chapter02STExamples.tie_prefix2
#print axioms Chapter02STExamples.tie_prefix3
#print axioms Chapter02STExamples.tie_select_working_left
#print axioms Chapter02STExamples.tie_working_reachable
#print axioms Chapter02STExamples.tie_working_bound
#print axioms Chapter02STExamples.tie_omitted_bounds
#print axioms Chapter02STExamples.tie_omitted_sibling_unsound
#print axioms Chapter02STExamples.tie_omitted_working_unsound
#print axioms Chapter02STExamples.tie_positive_tolerance_actual_stop
#print axioms Chapter02STExamples.tie_positive_tolerance_return
#print axioms Chapter02STExamples.tie_empty_frontier_incumbent_required
#print axioms Chapter02STExamples.tie_all_chosen_callback_trials_infeasible
#print axioms Chapter02STExamples.root_gap_linear
#print axioms Chapter02STExamples.root_gap_objective
#print axioms Chapter02STExamples.root_gap_base_compact
#print axioms Chapter02STExamples.root_gap_rows_convex
#print axioms Chapter02STExamples.root_gap_rows_C2
#print axioms Chapter02STExamples.root_gap_rows_diff
#print axioms Chapter02STExamples.root_gap_derivative
#print axioms Chapter02STExamples.root_gap_nlp_minimum
#print axioms Chapter02STExamples.root_gap_every_integer_fiber_empty
#print axioms Chapter02STExamples.root_gap_fiber_slater_vacuous
#print axioms Chapter02STExamples.gap_seed_trivial
#print axioms Chapter02STExamples.gap_batch_valid
#print axioms Chapter02STExamples.gap_batch_zero_cut
#print axioms Chapter02STExamples.gap_lp_minimum_of_mem
#print axioms Chapter02STExamples.gap_first_lp_minimum
#print axioms Chapter02STExamples.gap_initialization
#print axioms Chapter02STExamples.gap_raise_keeps_nlp_bound
#print axioms Chapter02STExamples.gap_first_callback
#print axioms Chapter02STExamples.root_nlp_bound_strictly_above_lp
#print axioms Chapter02STExamples.gap_batch_one_cut
#print axioms Chapter02STExamples.gap_second_lp_minimum
#print axioms Chapter02STExamples.gap_right_lp_minimum
#print axioms Chapter02STExamples.gap_children
#print axioms Chapter02STExamples.gap_step2
#print axioms Chapter02STExamples.gap_left_lp_empty
#print axioms Chapter02STExamples.gap_step3
#print axioms Chapter02STExamples.gap_step4
#print axioms Chapter02STExamples.gap_right_lp_empty
#print axioms Chapter02STExamples.gap_step5
#print axioms Chapter02STExamples.gap_five_process_trace
#print axioms Chapter02STExamples.gap_final_infeasible
#print axioms Chapter02STExamples.gap_source_full_return
#print axioms Chapter02STExamples.gap_reset_lowers_bound
#print axioms Chapter02STExamples.gap_reset_not_legal_process
#print axioms Chapter02STExamples.empty_mixed_base_unbounded_initialization
#print axioms Chapter02STExamples.time_linear
#print axioms Chapter02STExamples.time_objective
#print axioms Chapter02STExamples.time_base_compact
#print axioms Chapter02STExamples.improve_linear
#print axioms Chapter02STExamples.improve_objective
#print axioms Chapter02STExamples.improve_base_compact
#print axioms Chapter02STExamples.improve_rows_convex
#print axioms Chapter02STExamples.improve_rows_C2
#print axioms Chapter02STExamples.improve_rows_diff
#print axioms Chapter02STExamples.improve_derivative
#print axioms Chapter02STExamples.improve_root_minimum
#print axioms Chapter02STExamples.improve_zero_fiber_empty
#print axioms Chapter02STExamples.improve_fiber_slater
#print axioms Chapter02STExamples.tie_four_process_trace
#print axioms Chapter02STExamples.tie_fourth_global_bound
#print axioms Chapter02STExamples.tie_fourth_zero_gap_stop
#print axioms Chapter02STExamples.tie_state_signatures
#print axioms Chapter02STExamples.tie_selector_choices
#print axioms Chapter02STExamples.tie_gap_first_driver_return
#print axioms Chapter02STExamples.tie_gap_first_initialized_certificate
#print axioms Chapter02STExamples.improve_tangent
#print axioms Chapter02STExamples.improve_seed_iff
#print axioms Chapter02STExamples.improve_batch_valid
#print axioms Chapter02STExamples.improve_restore_valid
#print axioms Chapter02STExamples.improve_feasible_cuts
#print axioms Chapter02STExamples.improve_restore_cut
#print axioms Chapter02STExamples.improve_histories
#print axioms Chapter02STExamples.improve_incumbents
#print axioms Chapter02STExamples.improve_lp_zero_minimum
#print axioms Chapter02STExamples.improve_root_lp
#print axioms Chapter02STExamples.improve_right_first_lp
#print axioms Chapter02STExamples.improve_left_lp
#print axioms Chapter02STExamples.improve_right_second_lp
#print axioms Chapter02STExamples.improve_left_empty
#print axioms Chapter02STExamples.improve_final_lp
#print axioms Chapter02STExamples.improve_initialization
#print axioms Chapter02STExamples.improve_children
#print axioms Chapter02STExamples.improve_raise_zero
#print axioms Chapter02STExamples.improve_step1
#print axioms Chapter02STExamples.improve_step2
#print axioms Chapter02STExamples.improve_step3
#print axioms Chapter02STExamples.improve_step4
#print axioms Chapter02STExamples.improve_step5
#print axioms Chapter02STExamples.improve_step6
#print axioms Chapter02STExamples.improve_six_process_trace
#print axioms Chapter02STExamples.improve_final_stop
#print axioms Chapter02STExamples.restoration_then_strict_incumbent_improvement
#print axioms Chapter02STExamples.sibling_linear
#print axioms Chapter02STExamples.sibling_objective
#print axioms Chapter02STExamples.sibling_base_compact
#print axioms Chapter02STExamples.sibling_rows_convex
#print axioms Chapter02STExamples.sibling_rows_C2
#print axioms Chapter02STExamples.sibling_rows_diff
#print axioms Chapter02STExamples.sibling_derivative
#print axioms Chapter02STExamples.sibling_fiber_slater
#print axioms Chapter02STExamples.sibling_root_minimum
#print axioms Chapter02STExamples.sibling_seed_iff
#print axioms Chapter02STExamples.sibling_batch_valid
#print axioms Chapter02STExamples.sibling_cut
#print axioms Chapter02STExamples.sibling_empty_history_lp_iff
#print axioms Chapter02STExamples.sibling_empty_history_lp_min
#print axioms Chapter02STExamples.sibling_root_lp
#print axioms Chapter02STExamples.sibling_right_lp
#print axioms Chapter02STExamples.sibling_waiting_old_lp
#print axioms Chapter02STExamples.sibling_initialization
#print axioms Chapter02STExamples.sibling_children
#print axioms Chapter02STExamples.sibling_step1
#print axioms Chapter02STExamples.sibling_step2
#print axioms Chapter02STExamples.sibling_two_process_trace
#print axioms Chapter02STExamples.sibling_global_cut_excludes_old_trial
#print axioms Chapter02STExamples.waiting_sibling_global_cut_local_only_ablation
#print axioms Chapter02STExamples.sibling_reachable_invariant
#print axioms Chapter02STExamples.no_zero_stop_of_stored_gap
#print axioms Chapter02STExamples.tie_prefix_no_zero_stop
#print axioms Chapter02STExamples.improve_prefix_global_bounds
#print axioms Chapter02STExamples.improve_prefix_no_zero_stop
#print axioms Chapter02STExamples.negative_tolerance_initialized_control
#print axioms Chapter02STExamples.tie_local_tolerance_bad_drop
#print axioms Chapter02STExamples.tie_global_half_tolerance_not_stopped
#print axioms Chapter02STExamples.main_control_source_hypotheses
#print axioms Chapter02STExamples.sibling_prefix_global_bounds
#print axioms Chapter02STExamples.sibling_prefix_no_zero_stop
#print axioms Chapter02STExamples.sibling_every_selector_returns
#print axioms Chapter02STExamples.main_control_nonvacuity
