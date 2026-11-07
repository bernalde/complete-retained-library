module

public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! Nonbinary zero-cutoff control with a total exact selector. Repeated successful
bodies are literal executions, not a finite prefix used to assert divergence. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedControls.Zero

def data : FPUnbounded.Data 0 1 0 where
  base := {p | 0 ≤ p.2 0 ∧ p.2 0 ≤ 2}
  f p := (p.2 0-1/2)^2
  g := Fin.elim0
  Df p := (2*(p.2 0-1/2)) • yc 0
  Dg := Fin.elim0
  delta := 0

def seed : P := pt (1/2)
def s0 : State 0 1 := initialState seed
def e0 : Event 0 1 := ⟨iv 0,pt 0,none,some (pt 0,pt 0)⟩
def e : Event 0 1 := ⟨iv 0,pt 0,some (1/4),some (pt 0,pt 0)⟩
def post (k : ℕ) : State 0 1 := ⟨seed,e0 :: List.replicate k e,some (pt 0),some k⟩

theorem relaxation_iff (p : P) : p ∈ data.relaxation ↔ 0 ≤ p.2 0 ∧ p.2 0 ≤ 2 := by
  simp [FPUnbounded.Data.relaxation,data]

theorem analytic : FPUnbounded.Analytic data := by
  have hB : Convex ℝ data.base := by
    intro p hp q hq a b ha hb hab
    change 0 ≤ a*p.2 0+b*q.2 0 ∧ a*p.2 0+b*q.2 0 ≤ 2
    exact ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hp.2), mul_nonneg hb (sub_nonneg.mpr hq.2)]⟩
  refine ⟨?_,hB,square_convex hB (yc 0) (1/2),?_,?_,?_,?_,le_rfl⟩
  · exact (isClosed_le continuous_const (yc 0).continuous).inter
      (isClosed_le (yc 0).continuous continuous_const)
  · intro j; exact Fin.elim0 j
  · intro p hp; exact square_derivative (yc 0) (1/2) p
  · intro j; exact Fin.elim0 j
  · apply (isCompact_Icc : IsCompact (Set.Icc (pt 0) (pt 2))).isBounded.subset
    intro p hp
    obtain ⟨hl,hu⟩ := (relaxation_iff p).mp hp
    constructor <;> constructor
    · intro i; exact Fin.elim0 i
    · intro i; fin_cases i; exact hl
    · intro i; exact Fin.elim0 i
    · intro i; fin_cases i; exact hu

theorem seed_minimum : IsMinimizer data.relaxation data.f seed := by
  refine ⟨(relaxation_iff seed).mpr (by norm_num [seed]),?_⟩
  intro p hp
  simpa [data,seed] using sq_nonneg (p.2 0-1/2)

theorem fractional_seed : seed ∉ data.original := by
  rintro ⟨_,y,hy⟩
  have he : (1/2:ℝ) = (y 0:ℝ) := congrFun hy 0
  have h0 : (0:ℝ) < (y 0:ℝ) := by linarith
  have h1 : (y 0:ℝ) < 1 := by linarith
  have h0' : 0 < y 0 := by exact_mod_cast h0
  have h1' : y 0 < 1 := by exact_mod_cast h1
  omega

theorem original_two : pt 2 ∈ data.original := by
  refine ⟨(relaxation_iff _).mpr (by norm_num),iv 2,?_⟩
  funext j; norm_num [pt,intCast,iv]

theorem master_s0 (z : P × ℝ) : z ∈ FPUnbounded.master data s0 ↔
    0 ≤ z.1.2 0 ∧ z.1.2 0 ≤ 2 ∧ (∃ k : ℤ, z.1.2 0 = k) ∧ 0 ≤ z.2 := by
  rw [master_rows,scalar_integer]
  simp [FPUnbounded.anchors,s0,initialState,seed,data,retainedNormals,
    FPUnbounded.Data.level,Allows,yc,pt]
  tauto

theorem first_master :
    IsMinimizer (FPUnbounded.master data s0) (FPUnbounded.masterCost s0) (pt 0,0) := by
  refine ⟨(master_s0 _).mpr ⟨by norm_num,by norm_num,⟨0,by norm_num⟩,le_rfl⟩,?_⟩
  intro z hz
  obtain ⟨_,_,⟨k,hk⟩,_⟩ := (master_s0 z).mp hz
  simp only [FPUnbounded.masterCost,scalar_l1]
  change |(0:ℝ)-1/2| ≤ |z.1.2 0-1/2|
  rw [hk]
  by_cases h : k ≤ 0
  · have h' : (k:ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonpos (by norm_num),abs_of_nonpos (by linarith)]; linarith
  · have h' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    rw [abs_of_nonpos (by norm_num),abs_of_nonneg (by linarith)]; linarith

theorem projection0 : IsMinimizer (data.region none) (distance (iv 0)) (pt 0) := by
  refine ⟨⟨(relaxation_iff _).mpr (by norm_num),trivial⟩,?_⟩
  intro p hp
  simpa [scalar_distance] using sq_nonneg (-(p.2 0))

theorem fiber0 : IsMinimizer (data.fiber (iv 0)) data.f (pt 0) := by
  refine ⟨⟨(relaxation_iff _).mpr (by norm_num),by funext j; norm_num [pt,intCast,iv]⟩,?_⟩
  intro p hp
  have hy : p.2 0 = 0 := by simpa [intCast,iv] using congrFun hp.2 0
  simp [data,hy]

theorem reply0 : FPUnbounded.EventReply data s0 (pt 0,0) e0 := by
  refine ⟨by funext j; norm_num [e0,pt,intCast,iv],rfl,projection0,?_⟩
  exact ⟨by norm_num [e0,scalar_distance],fiber0,rfl⟩

theorem append_first : append s0 e0 = post 0 := rfl

theorem append_post (k : ℕ) : append (post k) e = post (k+1) := by
  have hl : (e0 :: List.replicate k e) ++ [e] = e0 :: List.replicate (k+1) e := by
    rw [List.cons_append,List.replicate_succ']
  simp only [append,post]
  rw [hl]
  simp [e]

theorem reference_post (k : ℕ) : (post k).reference = pt 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [← append_post k]
    simp [State.reference,append,List.getLast?_append_cons,Event.anchor,e]

theorem post_ne_initial (k : ℕ) : post k ≠ s0 := by
  intro he
  have hh := congrArg (fun s => s.history.length) he
  simp [post,s0,initialState] at hh

theorem master_post (k : ℕ) (z : P × ℝ) : z ∈ FPUnbounded.master data (post k) ↔
    0 ≤ z.1.2 0 ∧ z.1.2 0 ≤ 2 ∧ (∃ j : ℤ, z.1.2 0 = j) ∧
      0 ≤ z.2 ∧ 1/4-z.1.2 0 ≤ z.2 ∧ z.2 ≤ 1/4 := by
  rw [master_rows,scalar_integer]
  simp [FPUnbounded.anchors,post,seed,data,e0,e,Event.anchor,retainedNormals,
    FPUnbounded.Data.level,Allows,yc,pt,cutoffValue,List.mem_replicate]
  ring_nf
  tauto

theorem post_master (k : ℕ) :
    IsMinimizer (FPUnbounded.master data (post k)) (FPUnbounded.masterCost (post k)) (pt 0,1/4) := by
  refine ⟨(master_post k _).mpr ⟨by norm_num,by norm_num,⟨0,by norm_num⟩,
    by norm_num,by norm_num,by norm_num⟩,?_⟩
  intro z hz
  simpa [FPUnbounded.masterCost,scalar_l1,reference_post] using abs_nonneg (z.1.2 0)

theorem post_projection (k : ℕ) :
    IsMinimizer (data.region (data.level (post k).incumbent)) (distance (iv 0)) (pt 0) := by
  refine ⟨⟨(relaxation_iff _).mpr (by norm_num),?_⟩,?_⟩
  · norm_num [data,FPUnbounded.Data.level,post,Allows,cutoffValue]
  · intro p hp
    simpa [scalar_distance] using sq_nonneg (-(p.2 0))

theorem post_reply (k : ℕ) : FPUnbounded.EventReply data (post k) (pt 0,1/4) e := by
  refine ⟨by funext j; norm_num [e,pt,intCast,iv],?_,post_projection k,?_⟩
  · norm_num [e,data,FPUnbounded.Data.level,post,cutoffValue]
  · refine ⟨by norm_num [e,scalar_distance],fiber0,?_⟩
    simp [FPUnbounded.BestChoice,post,e]

theorem continue0 : FPUnbounded.Continue data none s0 e0 :=
  ⟨(pt 0,0),first_master,by simp [BeforeCap],reply0⟩

theorem post_continue (k : ℕ) : FPUnbounded.Continue data none (post k) e :=
  ⟨(pt 0,1/4),post_master k,by simp [BeforeCap],post_reply k⟩

def choose : FPUnbounded.Selector data none := by
  classical
  exact patch s0 (.next e0 continue0) (fun s =>
    if h : ∃ k, s = post k then
      (Classical.choose_spec h).symm ▸ (.next e (post_continue (Classical.choose h)))
    else Classical.choice (FPUnbounded.decision_nonempty data analytic none s))

theorem next_transport {s t : State 0 1} (he : s=t)
    (ht : FPUnbounded.Continue data none t e) (hs : FPUnbounded.Continue data none s e) :
    he.symm ▸ FPUnbounded.Decision.next e ht = FPUnbounded.Decision.next e hs := by
  cases he
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem choose_post (k : ℕ) : choose (post k) = .next e (post_continue k) := by
  classical
  simp only [choose,patch_other _ _ _ _ (post_ne_initial k)]
  have h : ∃ j, post k = post j := ⟨k,rfl⟩
  rw [dif_pos h]
  exact next_transport (Classical.choose_spec h) _ _

theorem post_nonreturn (fuel k : ℕ) : FPUnbounded.run data choose fuel (post k) = none := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    rw [FPUnbounded.run,choose_post]
    simp [append_post,ih]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem run_nonreturn (fuel : ℕ) : FPUnbounded.run data choose fuel s0 = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [FPUnbounded.run]
    simp only [choose,patch_same]
    change (FPUnbounded.run data choose fuel (post 0)).map (LoopOutput.bump e0) = none
    rw [post_nonreturn]; rfl

theorem procedure_nonreturn (fuel : ℕ) :
    FPUnbounded.procedureWithFuel data (.minimum seed seed_minimum) choose fuel = none := by
  simp only [FPUnbounded.procedureWithFuel,fractional_seed,if_false]
  change (FPUnbounded.run data choose fuel s0).map Outcome.loop = none
  rw [run_nonreturn]; rfl

theorem post_ne_post {a b : ℕ} (h : a ≠ b) : post a ≠ post b := by
  intro he
  have hh := congrArg (fun s => s.history.length) he
  exact h (by simpa [post] using hh)

def capChoose : FPUnbounded.Selector data (some 3) :=
  patch s0 (.next e0 ⟨(pt 0,0),first_master,by norm_num [BeforeCap,s0,initialState],reply0⟩)
    (patch (post 0) (.next e ⟨(pt 0,1/4),post_master 0,by norm_num [BeforeCap,post],post_reply 0⟩)
      (patch (post 1) (.next e ⟨(pt 0,1/4),post_master 1,by norm_num [BeforeCap,post],post_reply 1⟩)
        (patch (post 2) (.stop .handoff (.handoff (post_master 2) rfl (by norm_num [post])))
          (Classical.choice (FPUnbounded.selector_nonempty data analytic (some 3))))))

def capOutput : LoopOutput 0 1 := ⟨post 2,.handoff,3,3,4,3⟩

theorem cap_run (fuel : ℕ) : FPUnbounded.run data capChoose (fuel+4) s0 = some capOutput := by
  rw [FPUnbounded.run]
  simp only [capChoose,patch_same]
  change (FPUnbounded.run data capChoose (fuel+3) (post 0)).map (LoopOutput.bump e0) = _
  rw [FPUnbounded.run]
  simp only [capChoose,patch_other _ _ _ _ (post_ne_initial 0),patch_same]
  rw [append_post]
  rw [FPUnbounded.run]
  simp only [capChoose,patch_other _ _ _ _ (post_ne_initial 1),
    patch_other _ _ _ _ (post_ne_post (by decide : 1 ≠ 0)),patch_same]
  rw [append_post]
  rw [FPUnbounded.run]
  simp [capChoose,patch,post_ne_initial,post_ne_post (by decide : 2 ≠ 0),
    post_ne_post (by decide : 2 ≠ 1),terminalOutput,terminalProjectionCount,
    LoopOutput.bump,polishCount,e0,e,capOutput]

theorem cap_procedure (fuel : ℕ) :
    FPUnbounded.procedureWithFuel data (.minimum seed seed_minimum) capChoose (fuel+4) =
      some (.loop capOutput) := by
  simp only [FPUnbounded.procedureWithFuel,fractional_seed,if_false]
  change (FPUnbounded.run data capChoose (fuel+4) s0).map Outcome.loop = _
  rw [cap_run]; rfl

def cap0Choose : FPUnbounded.Selector data (some 0) :=
  patch s0 (.stop .handoff (.handoff first_master rfl (by norm_num [s0,initialState])))
    (Classical.choice (FPUnbounded.selector_nonempty data analytic (some 0)))

def cap0Output : LoopOutput 0 1 := ⟨s0,.handoff,0,0,1,0⟩

theorem cap0_procedure (fuel : ℕ) :
    FPUnbounded.procedureWithFuel data (.minimum seed seed_minimum) cap0Choose (fuel+1) =
      some (.loop cap0Output) := by
  simp only [FPUnbounded.procedureWithFuel,fractional_seed,if_false]
  change (FPUnbounded.run data cap0Choose (fuel+1) s0).map Outcome.loop = _
  rw [FPUnbounded.run]
  simp [cap0Choose,terminalOutput,terminalProjectionCount,cap0Output]

theorem complete_control : FPUnbounded.Analytic data ∧ pt 2 ∈ data.original ∧
    (∀ fuel, FPUnbounded.procedureWithFuel data (.minimum seed seed_minimum) choose fuel = none) ∧
    (∀ fuel, FPUnbounded.procedureWithFuel data (.minimum seed seed_minimum)
      capChoose (fuel+4) = some (.loop capOutput)) ∧
    (∀ fuel, FPUnbounded.procedureWithFuel data (.minimum seed seed_minimum)
      cap0Choose (fuel+1) = some (.loop cap0Output)) :=
  ⟨analytic,original_two,procedure_nonreturn,cap_procedure,cap0_procedure⟩

end Chapter03.FPUnboundedControls.Zero
