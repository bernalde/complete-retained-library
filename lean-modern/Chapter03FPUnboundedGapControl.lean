module

public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! A regular convex polynomial on the original binary bound domain. Success
exclusions are explicitly disabled. Two positive cutoffs exhibit improvement
and an allowed nonzero relative-normalized terminal gap. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedControls.Gap

def objective (y : ℝ) : ℝ := 10+(y-9/20)^2*(1-(2/5)*y)
def slope (y : ℝ) : ℝ := 2*(y-9/20)*(1-(2/5)*y)-(2/5)*(y-9/20)^2

def data (delta : ℝ) : FPUnbounded.Data 0 1 0 where
  base := {p | 0 ≤ p.2 0 ∧ p.2 0 ≤ 1}
  f p := objective (p.2 0)
  g := Fin.elim0
  Df p := slope (p.2 0) • yc 0
  Dg := Fin.elim0
  delta := delta

def seed : P := pt (9/20)
def s0 : State 0 1 := initialState seed
def e0 : Event 0 1 := ⟨iv 0,pt 0,none,some (pt 0,pt 0)⟩
def s1 : State 0 1 := append s0 e0
def e1 : Event 0 1 := ⟨iv 1,pt 1,some (cutoffValue (1/1000) (4081/400)),some (pt 1,pt 1)⟩
def s2 : State 0 1 := append s1 e1

theorem relaxation_iff (delta : ℝ) (p : P) :
    p ∈ (data delta).relaxation ↔ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  simp [FPUnbounded.Data.relaxation,data]

theorem derivative (delta : ℝ) (p : P) :
    HasFDerivAt (data delta).f ((data delta).Df p) p := by
  have hlin := (hasFDerivAt_const (1:ℝ) p).sub ((yc 0).hasFDerivAt.const_mul (2/5))
  have hd := ((square_derivative (yc 0) (9/20) p).mul hlin).const_add 10
  exact hd.congr_fderiv (by apply ContinuousLinearMap.ext; intro q; simp [data,slope]; ring)

theorem analytic (delta : ℝ) (hd : 0 ≤ delta) : FPUnbounded.Analytic (data delta) := by
  have hB : Convex ℝ (data delta).base := by
    intro p hp q hq a b ha hb hab
    change 0 ≤ a*p.2 0+b*q.2 0 ∧ a*p.2 0+b*q.2 0 ≤ 1
    exact ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hp.2),mul_nonneg hb (sub_nonneg.mpr hq.2)]⟩
  refine ⟨?_,hB,?_,?_,?_,?_,?_,hd⟩
  · exact (isClosed_le continuous_const (yc 0).continuous).inter
      (isClosed_le (yc 0).continuous continuous_const)
  · refine ⟨hB,?_⟩
    intro p hp q hq a b ha hb hab
    change objective (a*p.2 0+b*q.2 0) ≤ a*objective (p.2 0)+b*objective (q.2 0)
    have hc : 0 ≤ 34/25-(2/5)*((a+1)*p.2 0+(b+1)*q.2 0) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ a+1) (sub_nonneg.mpr hp.2),
        mul_nonneg (by linarith : 0 ≤ b+1) (sub_nonneg.mpr hq.2)]
    have he : a*objective (p.2 0)+b*objective (q.2 0)-objective (a*p.2 0+b*q.2 0) =
        a*b*(p.2 0-q.2 0)^2*(34/25-(2/5)*((a+1)*p.2 0+(b+1)*q.2 0)) := by
      have hb' : b=1-a := by linarith
      rw [hb']; unfold objective; ring
    have hn := mul_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.2 0-q.2 0))) hc
    linarith
  · intro j; exact Fin.elim0 j
  · intro p hp; exact derivative delta p
  · intro j; exact Fin.elim0 j
  · apply (isCompact_Icc : IsCompact (Set.Icc (pt 0) (pt 1))).isBounded.subset
    intro p hp
    obtain ⟨hl,hu⟩ := (relaxation_iff delta p).mp hp
    constructor <;> constructor
    · intro i; exact Fin.elim0 i
    · intro i; fin_cases i; exact hl
    · intro i; exact Fin.elim0 i
    · intro i; fin_cases i; exact hu

theorem objective_lower (y : ℝ) (hy : y ≤ 1) : 10 ≤ objective y := by
  have h := mul_nonneg (sq_nonneg (y-9/20)) (show 0 ≤ 1-(2/5)*y by linarith)
  linarith [show objective y=10+(y-9/20)^2*(1-(2/5)*y) from rfl]

theorem seed_minimum (delta : ℝ) : IsMinimizer (data delta).relaxation (data delta).f seed := by
  refine ⟨(relaxation_iff delta _).mpr (by norm_num [seed]),?_⟩
  intro p hp
  simpa [data,seed,objective] using objective_lower (p.2 0) ((relaxation_iff delta p).mp hp).2

theorem fiber_minimum (delta : ℝ) (k : ℤ) (hk : 0 ≤ (k:ℝ)) (hU : (k:ℝ) ≤ 1) :
    IsMinimizer ((data delta).fiber (iv k)) (data delta).f (pt k) := by
  refine ⟨⟨(relaxation_iff delta _).mpr ⟨hk,hU⟩,rfl⟩,?_⟩
  intro p hp
  have hy : p.2 0=(k:ℝ) := congrFun hp.2 0
  simp [data,hy]

theorem master_s0 (delta : ℝ) (z : P × ℝ) :
    z ∈ FPUnbounded.master (data delta) s0 ↔
      0 ≤ z.1.2 0 ∧ z.1.2 0 ≤ 1 ∧ (∃ k : ℤ, z.1.2 0 = k) ∧ 10 ≤ z.2 := by
  rw [master_rows,scalar_integer]
  norm_num [FPUnbounded.anchors,s0,initialState,seed,data,retainedNormals,
    FPUnbounded.Data.level,Allows,yc,pt,objective,slope]
  tauto

theorem first_master (delta : ℝ) :
    IsMinimizer (FPUnbounded.master (data delta) s0) (FPUnbounded.masterCost s0) (pt 0,10) := by
  refine ⟨(master_s0 delta _).mpr ⟨by norm_num,by norm_num,⟨0,by norm_num⟩,le_rfl⟩,?_⟩
  intro z hz
  obtain ⟨hl,hu,⟨k,hk⟩,_⟩ := (master_s0 delta z).mp hz
  rw [hk] at hl hu
  simp only [FPUnbounded.masterCost,scalar_l1]
  change |(0:ℝ)-9/20| ≤ |z.1.2 0-9/20|
  rcases binary_value hl hu with rfl|rfl <;> rw [hk] <;>
    norm_num [abs_of_nonneg,abs_of_nonpos]

theorem projection0 (delta : ℝ) :
    IsMinimizer ((data delta).region none) (distance (iv 0)) (pt 0) := by
  refine ⟨⟨(relaxation_iff delta _).mpr (by norm_num),trivial⟩,?_⟩
  intro p hp
  simpa [scalar_distance] using sq_nonneg (-(p.2 0))

theorem reply0 (delta : ℝ) : FPUnbounded.EventReply (data delta) s0 (pt 0,10) e0 := by
  refine ⟨by funext j; norm_num [e0,pt,intCast,iv],rfl,projection0 delta,?_⟩
  exact ⟨by norm_num [e0,scalar_distance],
    by simpa [e0] using fiber_minimum delta 0 (by norm_num) (by norm_num),rfl⟩

theorem master_s1 (delta : ℝ) (z : P × ℝ) :
    z ∈ FPUnbounded.master (data delta) s1 ↔
      0 ≤ z.1.2 0 ∧ z.1.2 0 ≤ 1 ∧ (∃ k : ℤ, z.1.2 0 = k) ∧ 10 ≤ z.2 ∧
      4081/400-(981/1000)*z.1.2 0 ≤ z.2 ∧ z.2 ≤ cutoffValue delta (4081/400) := by
  rw [master_rows,scalar_integer]
  norm_num [FPUnbounded.anchors,s1,s0,append,initialState,seed,e0,data,Event.anchor,
    retainedNormals,FPUnbounded.Data.level,Allows,yc,pt,objective,slope]
  ring_nf
  simp only [and_assoc]

theorem gap_master_empty : ¬(FPUnbounded.master (data (1/40)) s1).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨_,_,_,hl,_,hu⟩ := (master_s1 (1/40) z).mp hz
  norm_num [cutoffValue,max_def,abs_of_nonneg] at hu
  linarith

theorem improving_master :
    IsMinimizer (FPUnbounded.master (data (1/1000)) s1) (FPUnbounded.masterCost s1) (pt 1,10) := by
  refine ⟨(master_s1 (1/1000) _).mpr ?_,?_⟩
  · norm_num [pt,cutoffValue,max_def,abs_of_nonneg]
    exact ⟨1,by norm_num⟩
  · intro z hz
    obtain ⟨hl,hu,⟨k,hk⟩,_,ht,hc⟩ := (master_s1 (1/1000) z).mp hz
    rw [hk] at hl hu
    have h1 : k=1 := by
      rcases binary_value hl hu with h|h
      · rw [hk,h] at ht
        norm_num [cutoffValue,max_def,abs_of_nonneg] at ht hc
        linarith
      · exact h
    simp only [FPUnbounded.masterCost,scalar_l1]
    change |(1:ℝ)-0| ≤ |z.1.2 0-0|
    rw [hk,h1]; norm_num

theorem improving_projection :
    IsMinimizer ((data (1/1000)).region ((data (1/1000)).level s1.incumbent))
      (distance (iv 1)) (pt 1) := by
  refine ⟨⟨(relaxation_iff _ _).mpr (by norm_num),?_⟩,?_⟩
  · norm_num [data,objective,FPUnbounded.Data.level,s1,s0,append,initialState,e0,
      cutoffValue,Allows,max_def,abs_of_nonneg]
  · intro p hp
    simpa [scalar_distance] using sq_nonneg (1-p.2 0)

theorem improving_reply : FPUnbounded.EventReply (data (1/1000)) s1 (pt 1,10) e1 := by
  refine ⟨by funext j; norm_num [e1,pt,intCast,iv],?_,improving_projection,?_⟩
  · norm_num [e1,data,objective,FPUnbounded.Data.level,s1,s0,append,initialState,e0]
  · refine ⟨by norm_num [e1,scalar_distance],?_,?_⟩
    · simpa [e1] using fiber_minimum (1/1000) 1 (by norm_num) (by norm_num)
    · norm_num [e1,s1,s0,append,initialState,e0,FPUnbounded.BestChoice,data,objective]

theorem master_s2 (z : P × ℝ) :
    z ∈ FPUnbounded.master (data (1/1000)) s2 ↔
      0 ≤ z.1.2 0 ∧ z.1.2 0 ≤ 1 ∧ (∃ k : ℤ, z.1.2 0 = k) ∧ 10 ≤ z.2 ∧
      4081/400-(981/1000)*z.1.2 0 ≤ z.2 ∧
      3857/400+(539/1000)*z.1.2 0 ≤ z.2 ∧
      z.2 ≤ cutoffValue (1/1000) (20363/2000) := by
  rw [master_rows,scalar_integer]
  norm_num [FPUnbounded.anchors,s2,s1,s0,append,initialState,seed,e0,e1,data,Event.anchor,
    retainedNormals,FPUnbounded.Data.level,Allows,yc,pt,objective,slope]
  ring_nf
  simp only [and_assoc]

theorem improving_master_empty : ¬(FPUnbounded.master (data (1/1000)) s2).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨hl,hu,⟨k,hk⟩,_,h0,h1,hc⟩ := (master_s2 z).mp hz
  rw [hk] at hl hu
  rcases binary_value hl hu with rfl|rfl <;>
    rw [hk] at h0 h1 <;>
    norm_num [cutoffValue,max_def,abs_of_nonneg] at h0 h1 hc <;> linarith

theorem seed_fractional (delta : ℝ) : seed ∉ (data delta).original := by
  rintro ⟨_,y,hy⟩
  have he : (9/20:ℝ) = (y 0:ℝ) := congrFun hy 0
  have h0 : (0:ℝ) < (y 0:ℝ) := by linarith
  have h1 : (y 0:ℝ) < 1 := by linarith
  have h0' : 0 < y 0 := by exact_mod_cast h0
  have h1' : y 0 < 1 := by exact_mod_cast h1
  omega

theorem s01 : s0 ≠ s1 := by
  intro h; have hh := congrArg (fun s => s.history.length) h
  simp [s0,s1,append,initialState] at hh

theorem s02 : s0 ≠ s2 := by
  intro h; have hh := congrArg (fun s => s.history.length) h
  simp [s0,s1,s2,append,initialState] at hh

theorem s12 : s1 ≠ s2 := by
  intro h; have hh := congrArg (fun s => s.history.length) h
  simp [s0,s1,s2,append,initialState] at hh

def gapChoose : FPUnbounded.Selector (data (1/40)) none :=
  patch s0 (.next e0 ⟨(pt 0,10),first_master (1/40),by simp [BeforeCap],reply0 (1/40)⟩)
    (patch s1 (.stop .emptyMaster (.emptyMaster gap_master_empty))
      (Classical.choice (FPUnbounded.selector_nonempty (data (1/40)) (analytic (1/40) (by norm_num)) none)))

def improveChoose : FPUnbounded.Selector (data (1/1000)) none :=
  patch s0 (.next e0 ⟨(pt 0,10),first_master (1/1000),by simp [BeforeCap],reply0 (1/1000)⟩)
    (patch s1 (.next e1 ⟨(pt 1,10),improving_master,by simp [BeforeCap],improving_reply⟩)
      (patch s2 (.stop .emptyMaster (.emptyMaster improving_master_empty))
        (Classical.choice (FPUnbounded.selector_nonempty (data (1/1000)) (analytic (1/1000) (by norm_num)) none))))

def gapOutput : LoopOutput 0 1 := ⟨s1,.emptyMaster,1,1,2,1⟩
def improveOutput : LoopOutput 0 1 := ⟨s2,.emptyMaster,2,2,3,2⟩

theorem gap_run (fuel : ℕ) :
    FPUnbounded.run (data (1/40)) gapChoose (fuel+2) s0 = some gapOutput := by
  rw [FPUnbounded.run]
  simp only [gapChoose,patch_same]
  change (FPUnbounded.run (data (1/40)) gapChoose (fuel+1) s1).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp [gapChoose,patch,s01.symm,terminalOutput,terminalProjectionCount,
    LoopOutput.bump,polishCount,e0,gapOutput]

theorem improve_run (fuel : ℕ) :
    FPUnbounded.run (data (1/1000)) improveChoose (fuel+3) s0 = some improveOutput := by
  rw [FPUnbounded.run]
  simp only [improveChoose,patch_same]
  change (FPUnbounded.run (data (1/1000)) improveChoose (fuel+2) s1).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp only [improveChoose,patch_other _ _ _ _ s01.symm,patch_same]
  change ((FPUnbounded.run (data (1/1000)) improveChoose (fuel+1) s2).map
    (LoopOutput.bump e1)).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp [improveChoose,patch,s02.symm,s12.symm,terminalOutput,terminalProjectionCount,
    LoopOutput.bump,polishCount,e0,e1,improveOutput]

theorem gap_procedure (fuel : ℕ) :
    FPUnbounded.procedureWithFuel (data (1/40)) (.minimum seed (seed_minimum (1/40)))
      gapChoose (fuel+2) = some (.loop gapOutput) := by
  simp only [FPUnbounded.procedureWithFuel,seed_fractional,if_false]
  change (FPUnbounded.run (data (1/40)) gapChoose (fuel+2) s0).map Outcome.loop = _
  rw [gap_run]; rfl

theorem improve_procedure (fuel : ℕ) :
    FPUnbounded.procedureWithFuel (data (1/1000)) (.minimum seed (seed_minimum (1/1000)))
      improveChoose (fuel+3) = some (.loop improveOutput) := by
  simp only [FPUnbounded.procedureWithFuel,seed_fractional,if_false]
  change (FPUnbounded.run (data (1/1000)) improveChoose (fuel+3) s0).map Outcome.loop = _
  rw [improve_run]; rfl

theorem original_minimum (delta : ℝ) :
    IsMinimizer (data delta).original (data delta).f (pt 1) := by
  refine ⟨⟨(relaxation_iff delta _).mpr (by norm_num),iv 1,by funext j; norm_num [pt,intCast,iv]⟩,?_⟩
  intro p hp
  obtain ⟨hy,y,he⟩ := hp
  obtain ⟨hl,hu⟩ := (relaxation_iff delta p).mp hy
  have hk : p.2 0=(y 0:ℝ) := congrFun he 0
  rw [hk] at hl hu
  rcases binary_value hl hu with h|h <;> norm_num [data,objective,hk,h]

theorem actual_improvement : s1.incumbent = some (pt 0) ∧ s2.incumbent = some (pt 1) ∧
    (data (1/1000)).f (pt 1) < (data (1/1000)).f (pt 0) := by
  norm_num [s1,s2,s0,append,initialState,e0,e1,data,objective]

theorem positive_relative_gap :
    (data (1/40)).f (pt 0)-(data (1/40)).f (pt 1)=21/1000 ∧
    0 < (data (1/40)).f (pt 0)-(data (1/40)).f (pt 1) ∧
    1 < |(data (1/40)).f (pt 0)| ∧
    (∀ p ∈ (data (1/40)).original,
      (data (1/40)).f (pt 0)-(data (1/40)).f p ≤
        (1/40)*max |(data (1/40)).f (pt 0)| 1) := by
  refine ⟨by norm_num [data,objective],by norm_num [data,objective],
    by norm_num [data,objective,abs_of_nonneg],?_⟩
  intro p hp
  have h := (original_minimum (1/40)).2 p hp
  norm_num [data,objective,max_def,abs_of_nonneg] at h ⊢
  linarith

theorem complete_control :
    FPUnbounded.Analytic (data (1/40)) ∧ FPUnbounded.Analytic (data (1/1000)) ∧
    (∀ fuel, FPUnbounded.procedureWithFuel (data (1/40))
      (.minimum seed (seed_minimum (1/40))) gapChoose (fuel+2) = some (.loop gapOutput)) ∧
    (∀ fuel, FPUnbounded.procedureWithFuel (data (1/1000))
      (.minimum seed (seed_minimum (1/1000))) improveChoose (fuel+3) = some (.loop improveOutput)) ∧
    IsMinimizer (data (1/40)).original (data (1/40)).f (pt 1) ∧
    (data (1/40)).f (pt 0)-(data (1/40)).f (pt 1)=21/1000 :=
  ⟨analytic (1/40) (by norm_num),analytic (1/1000) (by norm_num),
    gap_procedure,improve_procedure,original_minimum (1/40),positive_relative_gap.1⟩

end Chapter03.FPUnboundedControls.Gap
