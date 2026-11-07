module

public import Chapter03FPC1Execution

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPControls

def unboundedData : Data 1 1 1 2 := data false 1 0 1 0 0
theorem unbounded_analytic : Analytic unboundedData :=
  analytic false 1 0 1 0 (by norm_num) (by norm_num)
theorem unbounded_seed : IsMinimizer unboundedData.relaxation unboundedData.f seed :=
  relaxation_seed false 1 0 1 0 (by norm_num) (by norm_num)

theorem unbounded_master_witness (height : ℝ) :
    (pt (-height) 0,height) ∈ master unboundedData s0 := by
  apply (master_s0 false 1 0 1 0 _).mpr
  refine ⟨by simp,⟨0,by norm_num,by norm_num,by norm_num [pt]⟩,?_⟩
  simp [pt]

theorem unbounded_master_minimum (height : ℝ) :
    IsMinimizer (master unboundedData s0) (masterCost s0) (pt (-height) 0,height) := by
  refine ⟨unbounded_master_witness height,?_⟩
  intro z hz
  obtain ⟨_,⟨k,h0,h1,he⟩,_⟩ := (master_s0 false 1 0 1 0 z).mp hz
  rcases binary_value h0 h1 with rfl|rfl <;>
    norm_num [masterCost,l1_formula,State.reference,s0,initialState,seed,pt,he]

theorem handoff_initial_eq_master {n m l r : ℕ} (d : Data n m l r) (p : Point n m) :
    handoff d (initialState p) = master d (initialState p) := by
  ext z
  simp [handoff,master,handoffNormals,retainedNormals,noGoods,initialState,Data.level,Allows]

theorem unbounded_handoff_witness (height : ℝ) :
    (pt (-height) 0,height) ∈ handoff unboundedData s0 := by
  rw [show s0=initialState seed from rfl,handoff_initial_eq_master]
  exact unbounded_master_witness height

theorem unbounded_handoff_height :
    ¬ ∃ L : ℝ, IsLowerBound (handoff unboundedData s0) Prod.snd L := by
  rintro ⟨L,hL⟩
  have h := hL _ (unbounded_handoff_witness (L-1))
  change L ≤ L-1 at h
  linarith

theorem unbounded_continuous_master :
    ∀ x : ℝ, ∃ z ∈ master unboundedData s0, z.1.1 0 = x := by
  intro x
  exact ⟨(pt x 0,-x),by simpa using unbounded_master_witness (-x),rfl⟩

def cap0Selector : Selector unboundedData (some 0) :=
  patch s0 (.stop .handoff (.handoff (unbounded_master_minimum 0) rfl (by simp)))
    (Classical.choice (selector_nonempty unboundedData unbounded_analytic (some 0)))
def cap0Output : LoopOutput 1 1 := ⟨s0,.handoff,0,0,1,0⟩

theorem cap0_run (fuel : ℕ) : run unboundedData cap0Selector (fuel+1) s0 = some cap0Output := by
  rw [run]
  simp [cap0Selector,terminalOutput,terminalProjectionCount,cap0Output]

theorem cap0_procedure :
    procedure unboundedData (.minimum seed unbounded_seed) cap0Selector = some (.loop cap0Output) := by
  rw [procedure_fractional_eq unboundedData seed unbounded_seed cap0Selector
    (fractional_seed false 1 0 1 0 0)]
  change (run unboundedData cap0Selector (_+1) s0).map Outcome.loop = _
  rw [cap0_run]; rfl

theorem unbounded_integral_minimum :
    IsMinimizer unboundedData.relaxation unboundedData.f (pt 0 0) := by
  refine ⟨(relaxation_iff false 1 0 1 0 _).mpr ⟨rfl,by norm_num,by norm_num⟩,?_⟩
  intro p hp
  have hx := ((relaxation_iff false 1 0 1 0 p).mp hp).1
  simp [unboundedData,data,pt,hx]

theorem unbounded_integral_original : pt 0 0 ∈ unboundedData.original := by
  apply fiber_original unboundedData (iv 0)
  refine ⟨unbounded_integral_minimum.1,?_⟩
  funext j; norm_num [pt,intCast,iv]

/-- The same nonempty relaxation admits fractional and integral minimizing
initial choices; the actual selected integral point takes the early branch. -/
theorem integral_initialization {cap : Option ℕ} (choose : Selector unboundedData cap) :
    procedure unboundedData (.minimum (pt 0 0) unbounded_integral_minimum) choose =
      some (.initialOptimal (pt 0 0)) :=
  procedure_integral_eq unboundedData _ unbounded_integral_minimum choose unbounded_integral_original

def emptyData : Data 1 1 1 2 := data true 1 1 1 1 1
theorem empty_relaxation : ¬emptyData.relaxation.Nonempty := by
  rintro ⟨p,hp⟩
  have hg := ((relaxation_mem_iff emptyData p).mp hp).2 0
  change (p.1 0)^2+1 ≤ 0 at hg
  nlinarith [sq_nonneg (p.1 0)]

theorem empty_analytic : Analytic emptyData := by
  refine ⟨?_,?_,?_,?_,?_,by norm_num [emptyData,data]⟩
  · exact (affine_convex (base_convex emptyData) xc (-1)).add
      ((square_convex (base_convex emptyData) yc (1/2)).smul (by norm_num : (0:ℝ)≤1))
  · intro j
    simpa [emptyData,data,model,Pi.add_def] using (square_convex (base_convex emptyData) xc 0).add_const 1
  · intro p _; exact f_deriv true 1 1 1 1 1 p
  · intro j p _; exact g_deriv true 1 1 1 1 1 j p
  · have he : emptyData.relaxation = ∅ := Set.not_nonempty_iff_eq_empty.mp empty_relaxation
    rw [he]
    exact isCompact_empty.isBounded

def emptySelector : Selector emptyData none :=
  Classical.choice (selector_nonempty emptyData empty_analytic none)
theorem empty_initialization : procedure emptyData (.empty empty_relaxation) emptySelector =
    some .initialInfeasible := rfl

def zeroData : Data 0 0 0 0 where
  model := {
    g := Fin.elim0
    A := Fin.elim0
    B := Fin.elim0
    rhs := Fin.elim0
    c1 := 0
    c2 := 0
    lo := 0
    hi := 0 }
  f _ := 0
  Df _ := 0
  Dg := Fin.elim0
  nonlinear := ∅
  delta := 0

theorem zero_analytic : Analytic zeroData := by
  refine ⟨convexOn_const (0:ℝ) (base_convex zeroData),?_,?_,?_,?_,le_rfl⟩
  · intro j; exact Fin.elim0 j
  · intro p _; exact hasFDerivAt_const 0 p
  · intro j; exact Fin.elim0 j
  · have hs : zeroData.relaxation.Subsingleton := fun _ _ _ _ => Subsingleton.elim _ _
    exact hs.finite.isCompact.isBounded

theorem zero_minimum : IsMinimizer zeroData.relaxation zeroData.f (0,0) := by
  refine ⟨?_,fun _ _ => le_rfl⟩
  simp [zeroData,Data.relaxation,ModelData.relaxationOn,ContinuousRelaxation,
    ModelData.nonlinearRegion,ModelData.linearRegion]

theorem zero_original : (0,0) ∈ zeroData.original := by
  apply fiber_original zeroData 0
  exact ⟨zero_minimum.1,Subsingleton.elim _ _⟩

def zeroSelector : Selector zeroData none :=
  Classical.choice (selector_nonempty zeroData zero_analytic none)
theorem zero_initialization : procedure zeroData (.minimum (0,0) zero_minimum) zeroSelector =
    some (.initialOptimal (0,0)) :=
  procedure_integral_eq zeroData _ zero_minimum zeroSelector zero_original

end Chapter03.FPControls
