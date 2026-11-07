module

public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! Disabled success exclusions: a positive-cutoff trace can revisit a
successful target as a failed target. The binary domain is an explicit option,
not an assertion about the source's default mixed-binary policy. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedControls.Repeat

def data (delta : ℝ) : FPUnbounded.Data 1 1 1 where
  base := (Set.Icc (fun _ => -1) (fun _ => 1)) ×ˢ (Set.Icc (fun _ => 0) (fun _ => 1))
  f p := p.1 0+(p.2 0-3/10)^2
  g _ p := (p.1 0)^2
  Df p := xc + (2*(p.2 0-3/10)) • yc 1
  Dg _ p := (2*p.1 0) • xc
  delta := delta

def seed : Q := xy 0 (3/10)
def s0 : State 1 1 := initialState seed
def e0 : Event 1 1 := ⟨iv 0,xy 0 0,none,some (xy 0 0,xy 0 0)⟩
def s1 : State 1 1 := append s0 e0
def e1 : Event 1 1 := ⟨iv 0,xy 0 (1/10),some (1/25),none⟩
def s2 : State 1 1 := append s1 e1
def e2 : Event 1 1 := ⟨iv 1,xy 0 (1/2),some (1/25),none⟩
def s3 : State 1 1 := append s2 e2

theorem base_iff (delta : ℝ) (p : Q) :
    p ∈ (data delta).base ↔ -1 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  change ((∀ j : Fin 1, -1 ≤ p.1 j) ∧ (∀ j : Fin 1, p.1 j ≤ 1)) ∧
    ((∀ j : Fin 1, 0 ≤ p.2 j) ∧ (∀ j : Fin 1, p.2 j ≤ 1)) ↔ _
  simp only [Fin.forall_fin_one]
  tauto

theorem relaxation_iff (delta : ℝ) (p : Q) :
    p ∈ (data delta).relaxation ↔ p.1 0 = 0 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  change (p ∈ (data delta).base ∧ ∀ j : Fin 1, (p.1 0)^2 ≤ 0) ↔ _
  rw [base_iff]
  simp only [Fin.forall_fin_one]
  constructor
  · rintro ⟨⟨_,_,hy⟩,hx⟩
    exact ⟨by nlinarith [sq_nonneg (p.1 0)],hy⟩
  · rintro ⟨hx,hy⟩
    exact ⟨⟨by rw [hx]; norm_num,by rw [hx]; norm_num,hy⟩,by rw [hx]; norm_num⟩

theorem nonlinear (delta : ℝ) (j : Fin 1) : j ∈ (data delta).nonlinear := by
  intro ha
  have hd : HasFDerivAt (fun p : Q => (p.1 0)^2) (0 : Q →L[ℝ] ℝ) (xy 0 0) := by
    simpa using square_derivative xc 0 (xy 0 0)
  have hh := OAKKT.affine_tangent ha hd (xy 1 0)
  norm_num [data] at hh

theorem analytic (delta : ℝ) (hd : 0 ≤ delta) : FPUnbounded.Analytic (data delta) := by
  have hB : Convex ℝ (data delta).base := (convex_Icc _ _).prod (convex_Icc _ _)
  refine ⟨isClosed_Icc.prod isClosed_Icc,hB,?_,?_,?_,?_,?_,hd⟩
  · exact (FPTrace.linear_convex hB xc).add (square_convex hB (yc 1) (3/10))
  · intro j
    simpa [data] using square_convex hB xc 0
  · intro p _
    exact xc.hasFDerivAt.add (square_derivative (yc 1) (3/10) p)
  · intro j p _
    simpa [data] using square_derivative xc 0 p
  · apply (isCompact_Icc.prod isCompact_Icc).isBounded.subset
    exact fun _ hp => hp.1

theorem seed_minimum (delta : ℝ) :
    IsMinimizer (data delta).relaxation (data delta).f seed := by
  refine ⟨(relaxation_iff delta _).mpr (by norm_num [seed]),?_⟩
  intro p hp
  have hx := ((relaxation_iff delta p).mp hp).1
  simpa [data,seed,hx] using sq_nonneg (p.2 0-3/10)

theorem fiber_minimum (delta : ℝ) (k : ℤ) (hk : 0 ≤ (k:ℝ)) (hU : (k:ℝ) ≤ 1) :
    IsMinimizer ((data delta).fiber (iv k)) (data delta).f (xy 0 k) := by
  refine ⟨⟨(relaxation_iff delta _).mpr ⟨rfl,hk,hU⟩,rfl⟩,?_⟩
  intro p hp
  have hx := ((relaxation_iff delta p).mp hp.1).1
  have hy : p.2 0 = (k:ℝ) := congrFun hp.2 0
  simp [data,hx,hy]

theorem master_s0 (delta : ℝ) (z : Q × ℝ) :
    z ∈ FPUnbounded.master (data delta) s0 ↔
      -1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1 ∧ 0 ≤ z.1.2 0 ∧ z.1.2 0 ≤ 1 ∧
      (∃ k : ℤ, z.1.2 0 = k) ∧ z.1.1 0 ≤ z.2 := by
  rw [master_rows,base_iff,scalar_integer]
  simp [FPUnbounded.anchors,s0,initialState,seed,data,retainedNormals,
    FPUnbounded.Data.level,Allows,xc,yc,xy,Fin.forall_fin_one]
  tauto

theorem first_master (delta : ℝ) :
    IsMinimizer (FPUnbounded.master (data delta) s0) (FPUnbounded.masterCost s0) (xy 0 0,0) := by
  refine ⟨(master_s0 delta _).mpr (by norm_num [xy]; exact ⟨0,by norm_num⟩),?_⟩
  intro z hz
  obtain ⟨_,_,hl,hu,⟨k,hk⟩,_⟩ := (master_s0 delta z).mp hz
  rw [hk] at hl hu
  rcases binary_value hl hu with rfl|rfl <;>
    norm_num [FPUnbounded.masterCost,scalar_l1,State.reference,s0,initialState,seed,xy,hk,abs_of_nonneg]

theorem projection0 (delta : ℝ) :
    IsMinimizer ((data delta).region none) (distance (iv 0)) (xy 0 0) := by
  refine ⟨⟨(relaxation_iff delta _).mpr (by norm_num),trivial⟩,?_⟩
  intro p hp
  simpa [scalar_distance] using sq_nonneg (-(p.2 0))

theorem reply0 (delta : ℝ) : FPUnbounded.EventReply (data delta) s0 (xy 0 0,0) e0 := by
  refine ⟨by funext j; norm_num [e0,xy,intCast,iv],rfl,projection0 delta,?_⟩
  exact ⟨by norm_num [e0,scalar_distance],by simpa [e0] using fiber_minimum delta 0 (by norm_num) (by norm_num),rfl⟩

theorem master_s1 (delta : ℝ) (z : Q × ℝ) :
    z ∈ FPUnbounded.master (data delta) s1 ↔
      -1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1 ∧ 0 ≤ z.1.2 0 ∧ z.1.2 0 ≤ 1 ∧
      (∃ k : ℤ, z.1.2 0 = k) ∧ z.1.1 0 ≤ z.2 ∧
      z.1.1 0+9/100-(3/5)*z.1.2 0 ≤ z.2 ∧ z.2 ≤ 9/100-delta := by
  rw [master_rows,base_iff,scalar_integer]
  simp [FPUnbounded.anchors,s1,s0,append,initialState,seed,e0,data,Event.anchor,
    retainedNormals,FPUnbounded.Data.level,Allows,xc,yc,xy,Fin.forall_fin_one,
    cutoffValue, max_def, abs_of_nonneg]
  norm_num
  ring_nf
  simp only [and_assoc]
  have habs : |(3/10:ℝ)| ≤ 1 := by rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/10)]; norm_num
  constructor <;> rintro ⟨a,b,c,d,e,f,g,h⟩
  · exact ⟨a,b,c,d,e,f,by linarith,h⟩
  · exact ⟨a,b,c,d,e,f,by linarith,h⟩

theorem second_master :
    IsMinimizer (FPUnbounded.master (data (1/20)) s1) (FPUnbounded.masterCost s1)
      (xy (-1/20) 0,1/25) := by
  refine ⟨(master_s1 (1/20) _).mpr (by norm_num [xy]; exact ⟨0,by norm_num⟩),?_⟩
  intro z hz
  simpa [FPUnbounded.masterCost,scalar_l1,State.reference,s1,s0,append,initialState,
    e0,Event.anchor,xy] using abs_nonneg (z.1.2 0)

theorem region_s1_iff (p : Q) :
    p ∈ (data (1/20)).region ((data (1/20)).level s1.incumbent) ↔
      p.1 0 = 0 ∧ 1/10 ≤ p.2 0 ∧ p.2 0 ≤ 1/2 := by
  change (p ∈ (data (1/20)).relaxation ∧ _) ↔ _
  rw [relaxation_iff]
  norm_num [FPUnbounded.Data.level,s1,s0,append,initialState,e0,data,Allows,
    cutoffValue,xy,max_def,abs_of_nonneg]
  constructor
  · rintro ⟨⟨hx,hl,hu⟩,hc⟩
    refine ⟨hx,?_,?_⟩ <;> nlinarith [sq_nonneg (p.2 0-1/10),sq_nonneg (p.2 0-1/2)]
  · rintro ⟨hx,hl,hu⟩
    refine ⟨⟨hx,by linarith,by linarith⟩,?_⟩
    have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) (sub_nonpos.mpr hu)
    nlinarith

theorem projection_repeat :
    IsMinimizer ((data (1/20)).region ((data (1/20)).level s1.incumbent))
      (distance (iv 0)) (xy 0 (1/10)) := by
  refine ⟨(region_s1_iff _).mpr (by norm_num),?_⟩
  intro p hp
  have hl := ((region_s1_iff p).mp hp).2.1
  simp only [scalar_distance,iv_apply,xy_snd,Int.cast_zero]
  nlinarith [sq_nonneg (p.2 0-1/10)]

theorem reply_repeat : FPUnbounded.EventReply (data (1/20)) s1 (xy (-1/20) 0,1/25) e1 := by
  refine ⟨by funext j; norm_num [e1,xy,intCast,iv],?_,projection_repeat,?_⟩
  · norm_num [e1,FPUnbounded.Data.level,s1,s0,append,initialState,e0,data,cutoffValue,xy,max_def,abs_of_nonneg]
  · norm_num [e1,scalar_distance]

theorem third_master :
    IsMinimizer (FPUnbounded.master (data (1/20)) s2) (FPUnbounded.masterCost s2)
      (xy 0 1,0) := by
  refine ⟨?_,?_⟩
  · rw [master_rows,base_iff,scalar_integer]
    norm_num [FPUnbounded.anchors,s2,s1,s0,append,initialState,seed,e0,e1,data,
      Event.anchor,retainedNormals,scalar_normal,FPUnbounded.Data.level,Allows,
      xc,yc,xy,Fin.forall_fin_one,cutoffValue,max_def,abs_of_nonneg]
    exact ⟨1,by norm_num⟩
  · intro z hz
    obtain ⟨hb,⟨y,hy⟩,_,hn,_⟩ := (master_rows _ _ _).mp hz
    obtain ⟨_,_,hl,hu⟩ := (base_iff (1/20) z.1).mp hb
    have he : z.1.2 0 = (y 0:ℝ) := congrFun hy 0
    rw [he] at hl hu
    have hn0 := hn e1 (by simp [s2,append]) rfl
    norm_num [scalar_normal,e1,xy] at hn0
    have hk : y 0 = 1 := by
      rcases binary_value hl hu with h|h
      · rw [he,h] at hn0; norm_num at hn0
      · exact h
    simp only [FPUnbounded.masterCost,scalar_l1]
    change |(1:ℝ)-1/10| ≤ |z.1.2 0-1/10|
    rw [he,hk]; norm_num

theorem region_s2_iff (p : Q) :
    p ∈ (data (1/20)).region ((data (1/20)).level s2.incumbent) ↔
      p.1 0 = 0 ∧ 1/10 ≤ p.2 0 ∧ p.2 0 ≤ 1/2 := region_s1_iff p

theorem projection_last :
    IsMinimizer ((data (1/20)).region ((data (1/20)).level s2.incumbent))
      (distance (iv 1)) (xy 0 (1/2)) := by
  refine ⟨(region_s2_iff _).mpr (by norm_num),?_⟩
  intro p hp
  have hu := ((region_s2_iff p).mp hp).2.2
  simp only [scalar_distance,iv_apply,xy_snd,Int.cast_one]
  nlinarith [sq_nonneg (p.2 0-1/2)]

theorem reply_last : FPUnbounded.EventReply (data (1/20)) s2 (xy 0 1,0) e2 := by
  refine ⟨by funext j; norm_num [e2,xy,intCast,iv],?_,projection_last,?_⟩
  · norm_num [e2,FPUnbounded.Data.level,s2,s1,s0,append,initialState,e0,e1,data,
      cutoffValue,xy,max_def,abs_of_nonneg]
  · norm_num [e2,scalar_distance]

theorem master_final_empty : ¬(FPUnbounded.master (data (1/20)) s3).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨_,⟨y,hy⟩,_,hn,_⟩ := (master_rows _ _ _).mp hz
  have h1 := hn e1 (by simp [s3,s2,append]) rfl
  have h2 := hn e2 (by simp [s3,append]) rfl
  simp only [scalar_normal,e1,e2,iv_apply,xy_snd,Int.cast_zero,Int.cast_one] at h1 h2
  have he : z.1.2 0 = (y 0:ℝ) := congrFun hy 0
  have hl : (0:ℝ) < (y 0:ℝ) := by rw [← he]; nlinarith
  have hu : (y 0:ℝ) < 1 := by rw [← he]; nlinarith
  have hl' : 0 < y 0 := by exact_mod_cast hl
  have hu' : y 0 < 1 := by exact_mod_cast hu
  omega

theorem continue0 : FPUnbounded.Continue (data (1/20)) none s0 e0 :=
  ⟨(xy 0 0,0),first_master (1/20),by simp [BeforeCap],reply0 (1/20)⟩
theorem continue1 : FPUnbounded.Continue (data (1/20)) none s1 e1 :=
  ⟨(xy (-1/20) 0,1/25),second_master,by simp [BeforeCap],reply_repeat⟩
theorem continue2 : FPUnbounded.Continue (data (1/20)) none s2 e2 :=
  ⟨(xy 0 1,0),third_master,by simp [BeforeCap],reply_last⟩

theorem state_ne {a b : State 1 1} (h : a.history.length ≠ b.history.length) : a ≠ b :=
  fun he => h (congrArg (fun s => s.history.length) he)

theorem s01 : s0 ≠ s1 := state_ne (by norm_num [s0,s1,append,initialState])
theorem s02 : s0 ≠ s2 := state_ne (by norm_num [s0,s1,s2,append,initialState])
theorem s03 : s0 ≠ s3 := state_ne (by norm_num [s0,s1,s2,s3,append,initialState])
theorem s12 : s1 ≠ s2 := state_ne (by norm_num [s0,s1,s2,append,initialState])
theorem s13 : s1 ≠ s3 := state_ne (by norm_num [s0,s1,s2,s3,append,initialState])
theorem s23 : s2 ≠ s3 := state_ne (by norm_num [s0,s1,s2,s3,append,initialState])

def choose : FPUnbounded.Selector (data (1/20)) none :=
  patch s0 (.next e0 continue0) (patch s1 (.next e1 continue1)
    (patch s2 (.next e2 continue2) (patch s3 (.stop .emptyMaster (.emptyMaster master_final_empty))
      (Classical.choice (FPUnbounded.selector_nonempty (data (1/20)) (analytic (1/20) (by norm_num)) none)))))

def output : LoopOutput 1 1 := ⟨s3,.emptyMaster,3,3,4,1⟩

theorem run_exact (fuel : ℕ) :
    FPUnbounded.run (data (1/20)) choose (fuel+4) s0 = some output := by
  rw [FPUnbounded.run]
  simp only [choose,patch_same]
  change (FPUnbounded.run (data (1/20)) choose (fuel+3) s1).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp only [choose,patch_other _ _ _ _ s01.symm,patch_same]
  change ((FPUnbounded.run (data (1/20)) choose (fuel+2) s2).map
    (LoopOutput.bump e1)).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp only [choose,patch_other _ _ _ _ s02.symm,patch_other _ _ _ _ s12.symm,patch_same]
  change (((FPUnbounded.run (data (1/20)) choose (fuel+1) s3).map
    (LoopOutput.bump e2)).map (LoopOutput.bump e1)).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp [choose,patch,s03.symm,s13.symm,s23.symm,terminalOutput,terminalProjectionCount,
    LoopOutput.bump,polishCount,e0,e1,e2,output]

theorem seed_fractional (delta : ℝ) : seed ∉ (data delta).original := by
  rintro ⟨_,y,hy⟩
  have he : (3/10:ℝ) = (y 0:ℝ) := congrFun hy 0
  have h0 : (0:ℝ) < (y 0:ℝ) := by linarith
  have h1 : (y 0:ℝ) < 1 := by linarith
  have h0' : 0 < y 0 := by exact_mod_cast h0
  have h1' : y 0 < 1 := by exact_mod_cast h1
  omega

theorem procedure_exact (fuel : ℕ) :
    FPUnbounded.procedureWithFuel (data (1/20)) (.minimum seed (seed_minimum (1/20)))
      choose (fuel+4) = some (.loop output) := by
  simp only [FPUnbounded.procedureWithFuel,seed_fractional,if_false]
  change (FPUnbounded.run (data (1/20)) choose (fuel+4) s0).map Outcome.loop = _
  rw [run_exact]; rfl

theorem repeated_target_and_count : e0.target = e1.target ∧
    e0.success ≠ none ∧ e1.success = none ∧ output.bodies = 3 ∧ 2 < output.bodies := by
  simp [e0,e1,output]

theorem empty_projection_master :
    IsMinimizer (FPUnbounded.master (data (1/10)) s1) (FPUnbounded.masterCost s1)
      (xy (-1/10) 0,-1/100) := by
  refine ⟨(master_s1 (1/10) _).mpr (by norm_num [xy]; exact ⟨0,by norm_num⟩),?_⟩
  intro z hz
  simpa [FPUnbounded.masterCost,scalar_l1,State.reference,s1,s0,append,initialState,
    e0,Event.anchor,xy] using abs_nonneg (z.1.2 0)

theorem projection_region_empty :
    ¬((data (1/10)).region ((data (1/10)).level s1.incumbent)).Nonempty := by
  rintro ⟨p,hp,hc⟩
  have hx := ((relaxation_iff (1/10) p).mp hp).1
  norm_num [FPUnbounded.Data.level,s1,s0,append,initialState,e0,data,Allows,
    cutoffValue,xy,max_def,abs_of_nonneg,hx] at hc
  nlinarith [sq_nonneg (p.2 0-3/10)]

def emptyChoose : FPUnbounded.Selector (data (1/10)) none :=
  patch s0 (.next e0 ⟨(xy 0 0,0),first_master (1/10),by simp [BeforeCap],reply0 (1/10)⟩)
    (patch s1 (.stop (.emptyProjection (iv 0))
      (.emptyProjection empty_projection_master (by funext j; norm_num [xy,intCast,iv])
        (by simp [BeforeCap]) projection_region_empty))
      (Classical.choice (FPUnbounded.selector_nonempty (data (1/10))
        (analytic (1/10) (by norm_num)) none)))

def capChoose : FPUnbounded.Selector (data (1/10)) (some 1) :=
  patch s0 (.next e0 ⟨(xy 0 0,0),first_master (1/10),by norm_num [BeforeCap,s0,initialState],reply0 (1/10)⟩)
    (patch s1 (.stop .handoff (.handoff empty_projection_master rfl
      (by norm_num [s1,s0,append,initialState])))
      (Classical.choice (FPUnbounded.selector_nonempty (data (1/10))
        (analytic (1/10) (by norm_num)) (some 1))))

def emptyOutput : LoopOutput 1 1 := ⟨s1,.emptyProjection (iv 0),1,2,2,1⟩
def capOutput : LoopOutput 1 1 := ⟨s1,.handoff,1,1,2,1⟩

theorem empty_run (fuel : ℕ) :
    FPUnbounded.run (data (1/10)) emptyChoose (fuel+2) s0 = some emptyOutput := by
  rw [FPUnbounded.run]
  simp only [emptyChoose,patch_same]
  change (FPUnbounded.run (data (1/10)) emptyChoose (fuel+1) s1).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp [emptyChoose,patch,s01.symm,terminalOutput,terminalProjectionCount,
    LoopOutput.bump,polishCount,e0,emptyOutput]

theorem cap_run (fuel : ℕ) :
    FPUnbounded.run (data (1/10)) capChoose (fuel+2) s0 = some capOutput := by
  rw [FPUnbounded.run]
  simp only [capChoose,patch_same]
  change (FPUnbounded.run (data (1/10)) capChoose (fuel+1) s1).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp [capChoose,patch,s01.symm,terminalOutput,terminalProjectionCount,
    LoopOutput.bump,polishCount,e0,capOutput]

theorem empty_procedure (fuel : ℕ) :
    FPUnbounded.procedureWithFuel (data (1/10)) (.minimum seed (seed_minimum (1/10)))
      emptyChoose (fuel+2) = some (.loop emptyOutput) := by
  simp only [FPUnbounded.procedureWithFuel,seed_fractional,if_false]
  change (FPUnbounded.run (data (1/10)) emptyChoose (fuel+2) s0).map Outcome.loop = _
  rw [empty_run]; rfl

theorem cap_precedence_procedure (fuel : ℕ) :
    FPUnbounded.procedureWithFuel (data (1/10)) (.minimum seed (seed_minimum (1/10)))
      capChoose (fuel+2) = some (.loop capOutput) := by
  simp only [FPUnbounded.procedureWithFuel,seed_fractional,if_false]
  change (FPUnbounded.run (data (1/10)) capChoose (fuel+2) s0).map Outcome.loop = _
  rw [cap_run]; rfl

def hardTargets : Finset (IntVector 1) := {iv 0,iv 1}

theorem hardTargets_card : hardTargets.card = 2 := by
  have hn : iv 0 ≠ iv 1 := by
    intro he
    have hh := congrFun he 0
    norm_num at hh
  simp [hardTargets,hn]

theorem base_integer_targets (delta : ℝ) (y : IntVector 1) :
    (∃ p ∈ (data delta).base, p.2 = intCast y) ↔ y ∈ hardTargets := by
  constructor
  · rintro ⟨p,hp,he⟩
    obtain ⟨_,_,hl,hu⟩ := (base_iff delta p).mp hp
    have hy : p.2 0=(y 0:ℝ) := congrFun he 0
    rw [hy] at hl hu
    rcases binary_value hl hu with h|h
    · have hh : y=iv 0 := by funext j; fin_cases j; exact h
      simp [hardTargets,hh]
    · have hh : y=iv 1 := by funext j; fin_cases j; exact h
      simp [hardTargets,hh]
  · intro hy
    simp only [hardTargets,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl|rfl
    · exact ⟨xy 0 0,(base_iff delta _).mpr (by norm_num),by funext j; norm_num [xy,intCast,iv]⟩
    · exact ⟨xy 0 1,(base_iff delta _).mpr (by norm_num),by funext j; norm_num [xy,intCast,iv]⟩

theorem completed_bodies_exceed_hard_target_card : hardTargets.card < output.bodies := by
  rw [hardTargets_card]
  norm_num [output]

end Chapter03.FPUnboundedControls.Repeat
