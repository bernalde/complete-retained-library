module

public import Chapter03FPSearchBonamiMaster
public import Chapter03FPSearchProcedure
public import Chapter03FPSearchAffineCQ

@[expose] public section

/-! Actual every-finite-fuel basic cycling and a two-projection enhanced return
for the held degenerate example. The source never asserts basic convergence
without its projection CQ; this control illustrates that qualification. -/
noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch.Bonami

def fallback (mode : Mode) : Selector data mode :=
  Classical.choice (selector_nonempty data analytic mode)

def repeatingStep (k : ℕ) : Step data .basic (repeated k) where
  point := masterOne
  target := integer 1
  projection := seed
  master_min := repeated_master_one k
  target_eq := by funext j; fin_cases j; norm_num [masterOne,point,integer,intCast]
  projection_min := projection_one

def repeatingSelector : Selector data .basic := by
  classical
  exact fun s hs => if h : s=repeated s.history.length then
    Decision.project {
      point := masterOne
      target := integer 1
      projection := seed
      master_min := h.symm ▸ repeated_master_one s.history.length
      target_eq := by funext j; fin_cases j; norm_num [masterOne,point,integer,intCast]
      projection_min := projection_one }
    else fallback .basic s hs

theorem repeatingSelector_at (k : ℕ) (hs : (repeated k).seed ∈ data.relaxation) :
    repeatingSelector (repeated k) hs = .project (repeatingStep k) := by
  simp [repeatingSelector,repeated,repeatingStep]

theorem repeated_append (k : ℕ) :
    append (repeated k) (repeatingStep k).event = repeated (k+1) := by
  simp [append,repeated,repeatingStep,Step.event,failed,List.replicate_succ']

theorem basic_run_none (fuel k : ℕ) (hs : (repeated k).seed ∈ data.relaxation) :
    run data .basic repeatingSelector fuel (repeated k) hs = none := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    rw [run_fractional data .basic repeatingSelector fuel (repeated k) hs
      (repeatingStep k) (repeatingSelector_at k hs) seed_fractional]
    simp only [repeated_append]
    rw [ih]
    rfl

theorem basic_procedure_none (fuel : ℕ) :
    procedureWithFuel data .basic (.minimum seed seed_minimum) repeatingSelector fuel = none := by
  have hf : ¬Integral seed := seed_fractional
  simp only [procedureWithFuel,hf,if_false]
  have h := basic_run_none fuel 0 seed_feasible
  simpa only [repeated,List.replicate_zero,initialState,h,Option.map_none] using congrArg
    (Option.map Outcome.loop) h

theorem initial_enhanced_master : master data .enhanced (repeated 0) =
    master data .basic (repeated 0) := by
  ext p
  simp [master,repeated]

def enhancedFirst : Step data .enhanced (repeated 0) where
  point := masterOne
  target := integer 1
  projection := seed
  master_min := by rw [initial_enhanced_master]; exact repeated_master_one 0
  target_eq := by funext j; fin_cases j; norm_num [masterOne,point,integer,intCast]
  projection_min := projection_one

/-- The displayed source chooses continuous coordinates (0,0) in the second
master; its projection has different continuous coordinates (1/2,0). -/
theorem enhanced_source_master_minimum :
    IsMinimizer (master data .enhanced (repeated 1)) (masterCost (repeated 1)) (point 0 0 0) := by
  refine ⟨(first_enhanced_master_iff _).mpr (by norm_num [point]),?_⟩
  intro p hp
  have ht := ((first_enhanced_master_iff p).mp hp).1
  simp only [masterCost,repeated_reference,FPUnboundedControls.scalar_l1]
  simp [point,ht]

def enhancedSecond : Step data .enhanced (repeated 1) where
  point := point 0 0 0
  target := integer 0
  projection := projectedZero
  master_min := enhanced_source_master_minimum
  target_eq := by funext j; fin_cases j; norm_num [projectedZero,point,integer,intCast]
  projection_min := projection_zero

def patch {mode : Mode} (s₀ : State 2 1) (dec : Decision data mode s₀)
    (rest : Selector data mode) : Selector data mode := by
  classical
  exact fun s hs => if h : s=s₀ then h.symm ▸ dec else rest s hs

theorem patch_at {mode : Mode} (s₀ : State 2 1) (dec : Decision data mode s₀)
    (rest : Selector data mode) (hs : s₀.seed ∈ data.relaxation) :
    patch s₀ dec rest s₀ hs=dec := by simp [patch]

def enhancedSelector : Selector data .enhanced :=
  patch (repeated 0) (.project enhancedFirst)
    (patch (repeated 1) (.project enhancedSecond) (fallback .enhanced))

theorem enhanced_at_zero (hs : (repeated 0).seed ∈ data.relaxation) :
    enhancedSelector (repeated 0) hs=.project enhancedFirst :=
  patch_at _ _ _ hs

theorem enhanced_at_one (hs : (repeated 1).seed ∈ data.relaxation) :
    enhancedSelector (repeated 1) hs=.project enhancedSecond := by
  have hn : repeated 1≠repeated 0 := by
    intro h
    have hh := congrArg (fun s : State 2 1 => s.history.length) h
    simp [repeated] at hh
  simp [enhancedSelector,patch,hn]

theorem zero_integral : Integral projectedZero := by
  refine ⟨integer 0,?_⟩
  funext j
  fin_cases j
  norm_num [projectedZero,point,integer,intCast]

def enhancedOutput : LoopOutput 2 1 :=
  (terminalOutput (repeated 1) (.found projectedZero)).bump

theorem enhanced_run : run data .enhanced enhancedSelector 2 (repeated 0)
    seed_feasible = some enhancedOutput := by
  rw [run_fractional data .enhanced enhancedSelector 1 (repeated 0) seed_feasible
    enhancedFirst (enhanced_at_zero _) seed_fractional]
  have ha : append (repeated 0) enhancedFirst.event=repeated 1 := rfl
  simp only [ha]
  rw [run_integral data .enhanced enhancedSelector 0 (repeated 1) seed_feasible
    enhancedSecond (enhanced_at_one _) zero_integral]
  rfl

theorem enhanced_procedure :
    procedureWithFuel data .enhanced (.minimum seed seed_minimum) enhancedSelector 2 =
      some (.loop enhancedOutput) := by
  have hf : ¬Integral seed := seed_fractional
  simp only [procedureWithFuel,hf,if_false]
  exact congrArg (Option.map Outcome.loop) enhanced_run

theorem enhanced_counts : enhancedOutput.masters=2 ∧ enhancedOutput.projections=2 ∧
    enhancedOutput.failures=1 := ⟨rfl,rfl,rfl⟩

theorem enhanced_feasible : projectedZero ∈ data.original := ⟨zero_feasible,zero_integral⟩

theorem no_strict_active_direction : ¬∃ w : P, ∀ j, row j seed=0 → rowD j seed w<0 := by
  rintro ⟨w,hw⟩
  have h0 := hw 0 (by norm_num [row,seed,point])
  have h2 := hw 2 (by change seed.1 1=0; rfl)
  change w.1 1<0 at h2
  norm_num [rowD,seed,point] at h0
  linarith

theorem full_projection_licq_fails {r : ℕ} (b : BaseRows data r) :
    ¬JointLICQ (jointRows data b) (jointRowD data b seed) seed := by
  intro h
  obtain ⟨w,hw⟩ := joint_mfcq_of_licq (jointRows data b) (jointRowD data b seed) seed h
  apply no_strict_active_direction
  exact ⟨w,fun j hj => hw (.inr j) hj⟩

end Chapter03.FPSearch.Bonami
