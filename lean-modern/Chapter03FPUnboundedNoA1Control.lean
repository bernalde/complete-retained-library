module

public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! A compact nonlinear relaxation with no finite integer bound and an
actually unbounded initial master. All success exclusions are disabled. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedControls.NoA1

def data (delta : ℝ) : FPUnbounded.Data 0 1 1 where
  base := Set.univ
  f p := (p.2 0-3/10)^2
  g _ p := (p.2 0-3/10)^2-1/25
  Df p := (2*(p.2 0-3/10)) • yc 0
  Dg _ p := (2*(p.2 0-3/10)) • yc 0
  delta := delta

def seed : P := pt (3/10)
def s0 : State 0 1 := initialState seed
def e0 : Event 0 1 := ⟨iv 0, pt (1/10), none, none⟩
def s1 : State 0 1 := append s0 e0
def e1 : Event 0 1 := ⟨iv 1, pt (1/2), none, none⟩
def s2 : State 0 1 := append s1 e1

theorem nonlinear (delta : ℝ) (j : Fin 1) : j ∈ (data delta).nonlinear :=
  scalar_square_not_affine (3/10) (1/25)

theorem relaxation_iff (delta : ℝ) (p : P) :
    p ∈ (data delta).relaxation ↔ 1/10 ≤ p.2 0 ∧ p.2 0 ≤ 1/2 := by
  simp only [FPUnbounded.Data.relaxation, data, Set.mem_setOf_eq, Set.mem_univ,
    true_and, Fin.forall_fin_one]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (p.2 0-1/10), sq_nonneg (p.2 0-1/2)]
  · rintro ⟨hl, hu⟩
    have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) (sub_nonpos.mpr hu)
    nlinarith

theorem analytic (delta : ℝ) (hd : 0 ≤ delta) : FPUnbounded.Analytic (data delta) := by
  refine ⟨isClosed_univ, convex_univ, ?_, ?_, ?_, ?_, ?_, hd⟩
  · exact square_convex convex_univ (yc 0) (3/10)
  · intro j
    simpa [data,Pi.add_def,sub_eq_add_neg] using (square_convex convex_univ (yc 0) (3/10)).add_const (-(1/25))
  · intro p _; exact square_derivative (yc 0) (3/10) p
  · intro j p _; exact (square_derivative (yc 0) (3/10) p).sub_const (1/25)
  · apply (isCompact_Icc : IsCompact (Set.Icc (pt (1/10)) (pt (1/2)))).isBounded.subset
    intro p hp
    obtain ⟨hl, hu⟩ := (relaxation_iff delta p).mp hp
    constructor <;> constructor
    · intro i; exact Fin.elim0 i
    · intro i; fin_cases i; exact hl
    · intro i; exact Fin.elim0 i
    · intro i; fin_cases i; exact hu

theorem seed_minimum (delta : ℝ) :
    IsMinimizer (data delta).relaxation (data delta).f seed := by
  refine ⟨(relaxation_iff delta seed).mpr (by norm_num [seed]), ?_⟩
  intro p hp
  simpa [data, seed] using sq_nonneg (p.2 0-3/10)

theorem original_empty (delta : ℝ) : ¬(data delta).original.Nonempty := by
  rintro ⟨p, hp, y, he⟩
  have hy : p.2 0 = (y 0:ℝ) := congrFun he 0
  obtain ⟨hl, hu⟩ := (relaxation_iff delta p).mp hp
  rw [hy] at hl hu
  have hl' : (0:ℝ) < (y 0:ℝ) := by linarith
  have hu' : (y 0:ℝ) < 1 := by linarith
  have hlz : 0 < y 0 := by exact_mod_cast hl'
  have huz : y 0 < 1 := by exact_mod_cast hu'
  omega

theorem master_s0 (delta : ℝ) (z : P × ℝ) :
    z ∈ FPUnbounded.master (data delta) s0 ↔
      (∃ k : ℤ, z.1.2 0 = k) ∧ 0 ≤ z.2 := by
  rw [master_rows, scalar_integer]
  norm_num [FPUnbounded.anchors, s0, initialState, seed, data, retainedNormals,
    FPUnbounded.Data.level, Allows, yc, pt, Fin.forall_fin_one]

theorem master_unbounded (delta T : ℝ) :
    ∃ z ∈ FPUnbounded.master (data delta) s0, T < z.1.2 0 := by
  obtain ⟨k, hk⟩ := exists_int_gt T
  refine ⟨(pt k,0), (master_s0 delta _).mpr ⟨⟨k,rfl⟩,le_rfl⟩, hk⟩

theorem first_master (delta : ℝ) :
    IsMinimizer (FPUnbounded.master (data delta) s0) (FPUnbounded.masterCost s0) (pt 0,0) := by
  refine ⟨(master_s0 delta _).mpr ⟨⟨0,by norm_num⟩,le_rfl⟩, ?_⟩
  intro z hz
  obtain ⟨⟨k,hk⟩,_⟩ := (master_s0 delta z).mp hz
  simp only [FPUnbounded.masterCost,scalar_l1]
  change |(0:ℝ)-3/10| ≤ |z.1.2 0-3/10|
  rw [hk]
  by_cases h : k ≤ 0
  · have h' : (k:ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    rw [abs_of_nonpos (by norm_num), abs_of_nonneg (by linarith)]
    linarith

theorem projection0 (delta : ℝ) :
    IsMinimizer ((data delta).region none) (distance (iv 0)) (pt (1/10)) := by
  refine ⟨⟨(relaxation_iff delta _).mpr (by norm_num), trivial⟩, ?_⟩
  intro p hp
  have hl := ((relaxation_iff delta p).mp hp.1).1
  simp only [scalar_distance, iv_apply, pt_snd, Int.cast_zero]
  nlinarith [sq_nonneg (p.2 0-1/10)]

theorem reply0 (delta : ℝ) : FPUnbounded.EventReply (data delta) s0 (pt 0,0) e0 := by
  refine ⟨by funext j; norm_num [e0, pt, intCast, iv], rfl, projection0 delta, ?_⟩
  norm_num [e0, scalar_distance]

theorem master_s1 (delta : ℝ) (z : P × ℝ) :
    z ∈ FPUnbounded.master (data delta) s1 ↔
      (∃ k : ℤ, z.1.2 0 = k) ∧ 1/10 ≤ z.1.2 0 ∧
      0 ≤ z.2 ∧ 2/25-(2/5)*z.1.2 0 ≤ z.2 := by
  rw [master_rows, scalar_integer]
  simp only [FPUnbounded.anchors]
  have hnl : (data delta).nonlinear = Set.univ := Set.eq_univ_iff_forall.mpr (nonlinear delta)
  rw [hnl]
  simp [s1, s0, append, initialState, seed, e0, data,
    Event.anchor, retainedNormals, scalar_normal, FPUnbounded.Data.level,
    Allows, yc, pt, Fin.forall_fin_one, nonlinear]
  norm_num
  ring_nf
  intro k hk
  constructor
  · rintro ⟨⟨h0,h1,h2⟩,hn⟩
    exact ⟨by linarith, h0, by linarith⟩
  · rintro ⟨hl,h0,h1⟩
    exact ⟨⟨h0, by linarith, by linarith⟩,by linarith⟩

theorem second_master (delta : ℝ) :
    IsMinimizer (FPUnbounded.master (data delta) s1) (FPUnbounded.masterCost s1) (pt 1,0) := by
  refine ⟨(master_s1 delta _).mpr ⟨⟨1,by norm_num⟩,by norm_num,by norm_num,by norm_num⟩, ?_⟩
  intro z hz
  obtain ⟨⟨k,hk⟩,hl,_,_⟩ := (master_s1 delta z).mp hz
  have hpos : (0:ℝ) < (k:ℝ) := by rw [← hk]; linarith
  have hpos' : 0 < k := by exact_mod_cast hpos
  have hone : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  simp only [FPUnbounded.masterCost,scalar_l1]
  change |(1:ℝ)-1/10| ≤ |z.1.2 0-1/10|
  rw [hk, abs_of_nonneg (by norm_num), abs_of_nonneg (by linarith)]
  linarith

theorem projection1 (delta : ℝ) :
    IsMinimizer ((data delta).region none) (distance (iv 1)) (pt (1/2)) := by
  refine ⟨⟨(relaxation_iff delta _).mpr (by norm_num), trivial⟩, ?_⟩
  intro p hp
  have hu := ((relaxation_iff delta p).mp hp.1).2
  simp only [scalar_distance, iv_apply, pt_snd, Int.cast_one]
  nlinarith [sq_nonneg (p.2 0-1/2)]

theorem reply1 (delta : ℝ) : FPUnbounded.EventReply (data delta) s1 (pt 1,0) e1 := by
  refine ⟨by funext j; norm_num [e1, pt, intCast, iv], rfl, projection1 delta, ?_⟩
  norm_num [e1, scalar_distance]

theorem master_s2_empty (delta : ℝ) : ¬(FPUnbounded.master (data delta) s2).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨_,⟨k,hk⟩,_,hn,_⟩ := (master_rows _ _ _).mp hz
  have h0 := hn e0 (by simp [s2,s1,append]) rfl
  have h1 := hn e1 (by simp [s2,append]) rfl
  simp only [scalar_normal, e0, e1, iv_apply, pt_snd, Int.cast_zero, Int.cast_one] at h0 h1
  have he : z.1.2 0 = (k 0:ℝ) := congrFun hk 0
  have hl : (0:ℝ) < (k 0:ℝ) := by rw [← he]; nlinarith
  have hu : (k 0:ℝ) < 1 := by rw [← he]; nlinarith
  have hl' : 0 < k 0 := by exact_mod_cast hl
  have hu' : k 0 < 1 := by exact_mod_cast hu
  omega

theorem continue0 (delta : ℝ) : FPUnbounded.Continue (data delta) none s0 e0 :=
  ⟨(pt 0,0),first_master delta,by simp [BeforeCap],reply0 delta⟩

theorem continue1 (delta : ℝ) : FPUnbounded.Continue (data delta) none s1 e1 :=
  ⟨(pt 1,0),second_master delta,by simp [BeforeCap],reply1 delta⟩

theorem s01 : s0 ≠ s1 := by
  intro h; have hh := congrArg (fun s => s.history.length) h
  simp [s0,s1,append,initialState] at hh

theorem s02 : s0 ≠ s2 := by
  intro h; have hh := congrArg (fun s => s.history.length) h
  simp [s0,s1,s2,append,initialState] at hh

theorem s12 : s1 ≠ s2 := by
  intro h; have hh := congrArg (fun s => s.history.length) h
  simp [s0,s1,s2,append,initialState] at hh

def choose (delta : ℝ) (hd : 0 ≤ delta) : FPUnbounded.Selector (data delta) none :=
  patch s0 (.next e0 (continue0 delta))
    (patch s1 (.next e1 (continue1 delta))
      (patch s2 (.stop .emptyMaster (.emptyMaster (master_s2_empty delta)))
        (Classical.choice (FPUnbounded.selector_nonempty (data delta) (analytic delta hd) none))))

def output : LoopOutput 0 1 := ⟨s2,.emptyMaster,2,2,3,0⟩

theorem run_exact (delta : ℝ) (hd : 0 ≤ delta) (fuel : ℕ) :
    FPUnbounded.run (data delta) (choose delta hd) (fuel+3) s0 = some output := by
  rw [FPUnbounded.run]
  simp only [choose,patch_same]
  change (FPUnbounded.run (data delta) (choose delta hd) (fuel+2) s1).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp only [choose,patch_other _ _ _ _ s01.symm,patch_same]
  change ((FPUnbounded.run (data delta) (choose delta hd) (fuel+1) s2).map
    (LoopOutput.bump e1)).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp [choose,patch,s02.symm,s12.symm,terminalOutput,terminalProjectionCount,
    LoopOutput.bump,polishCount,e0,e1,output]

theorem procedure_exact (delta : ℝ) (hd : 0 ≤ delta) (fuel : ℕ) :
    FPUnbounded.procedureWithFuel (data delta) (.minimum seed (seed_minimum delta))
      (choose delta hd) (fuel+3) = some (.loop output) := by
  have hn : seed ∉ (data delta).original := fun hs => original_empty delta ⟨seed,hs⟩
  simp only [FPUnbounded.procedureWithFuel,hn,if_false]
  change (FPUnbounded.run (data delta) (choose delta hd) (fuel+3) s0).map Outcome.loop = _
  rw [run_exact]; rfl

/-- The same model has a bounded nonlinear relaxation and an unbounded initial
integer master, and its exact selected procedure completes two failed bodies. -/
theorem complete_control :
    FPUnbounded.Analytic (data (1/20)) ∧
    (∀ T : ℝ, ∃ z ∈ FPUnbounded.master (data (1/20)) s0, T < z.1.2 0) ∧
    ¬(data (1/20)).original.Nonempty ∧
    FPUnbounded.procedureWithFuel (data (1/20)) (.minimum seed (seed_minimum (1/20)))
      (choose (1/20) (by norm_num)) 3 = some (.loop output) :=
  ⟨analytic (1/20) (by norm_num), master_unbounded (1/20), original_empty (1/20),
    procedure_exact (1/20) (by norm_num) 0⟩

end Chapter03.FPUnboundedControls.NoA1
