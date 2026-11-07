module

public import Chapter02PenaltyRestoration
public import Chapter02CPExamples
public import Chapter02OAExamples
public import Chapter02STGeometry

@[expose] public section

/-! Complete source-model restoration controls. These are mathematical controls
for distinct restoration objectives; they do not certify the damaged original
Quesada–Grossmann microstep process. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter02SourceRestorationExamples

def pt (x y : ℝ) : Point 1 1 := (fun _ => x,fun _ => y)
def cx : Point 1 1 →L[ℝ] ℝ := Chapter02Examples.coordX
def cy : Point 1 1 →L[ℝ] ℝ := Chapter02KKTExamples.coordY

def boxModel (l : ℕ) (G : Fin l → Point 1 1 → ℝ) (B U c d : ℝ) : ModelData 1 1 l 2 where
  g := G
  A := fun row _ => if row=0 then 1 else -1
  B := fun _ _ => 0
  rhs := fun _ => B
  c1 := fun _ => c
  c2 := fun _ => d
  lo := fun _ => 0
  hi := fun _ => U

theorem box_linear (l : ℕ) (G : Fin l → Point 1 1 → ℝ) (B U c d : ℝ) (p : Point 1 1) :
    p∈(boxModel l G B U c d).linearRegion ↔ -B≤p.1 0 ∧ p.1 0≤B := by
  simp [boxModel,ModelData.linearRegion,LinearForm,Fin.forall_fin_succ]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem box_objective (l : ℕ) (G : Fin l → Point 1 1 → ℝ) (B U c d : ℝ) (p : Point 1 1) :
    (boxModel l G B U c d).objective p=c*p.1 0+d*p.2 0 := by
  simp [boxModel,ModelData.objective,LinearForm]

theorem box_base_compact (l : ℕ) (G : Fin l → Point 1 1 → ℝ) (B U c d : ℝ) :
    IsCompact ((boxModel l G B U c d).linearRegion ∩
      IntegerCylinder (n:=1) (boxModel l G B U c d).lo (boxModel l G B U c d).hi) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (pt (-B) 0) (pt B U))).of_isClosed_subset
    (Chapter02CPExamples.base_closed _)
  rintro p ⟨hp,y,hy,heq⟩
  have hx := (box_linear l G B U c d p).mp hp
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i; exact hx.1
  · intro i; rw [heq]; exact (hy i).1
  · intro i; fin_cases i; exact hx.2
  · intro i; rw [heq]; exact (hy i).2

def f2 : ModelData 1 1 1 2 :=
  boxModel 1 (fun _ p => (p.1 0)^2+1-2*p.2 0) 10 1 (-2) 5

theorem f2_linear (p : Point 1 1) : p∈f2.linearRegion ↔ -10≤p.1 0 ∧ p.1 0≤10 :=
  box_linear _ _ _ _ _ _ _

theorem f2_objective (p : Point 1 1) : f2.objective p = -2*p.1 0+5*p.2 0 :=
  box_objective _ _ _ _ _ _ _

theorem f2_base_compact : IsCompact (f2.linearRegion ∩ IntegerCylinder (n:=1) f2.lo f2.hi) :=
  box_base_compact _ _ _ _ _ _

theorem f2_rows_convex : ∀ j,ConvexOn ℝ Set.univ (f2.g j) :=
  Chapter02OAExamples.trace_convex

theorem f2_rows_C2 : ∀ j,ContDiff ℝ 2 (f2.g j) := by
  intro j
  exact ((((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).add
    contDiff_const).sub (contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd))

theorem f2_derivative (p : Point 1 1) (j : Fin 1) :
    HasFDerivAt (f2.g j) ((2*p.1 0) • cx-(2 : ℝ) • cy) p := by
  have h := (((hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p cx.hasFDerivAt).add_const 1).fun_sub
    (cy.hasFDerivAt.const_mul 2)
  simpa [f2,boxModel,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY,
    Function.comp_def] using h

theorem f2_global_strict : pt 0 (3/4)∈f2.linearRegion ∧
    (∀ j,f2.g j (pt 0 (3/4))<0) ∧ (∀ i,f2.lo i<(pt 0 (3/4)).2 i ∧
      (pt 0 (3/4)).2 i<f2.hi i) := by
  refine ⟨(f2_linear _).mpr (by norm_num [pt]),?_,?_⟩ <;>
    intro j <;> norm_num [f2,boxModel,pt]

theorem f2_zero_fiber_empty : f2.fixedNonlinearFiber (fun _ => 0)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hy : p.2 0=0 := congrFun hp.1.2 0
  have hg := hp.2 (0 : Fin 1)
  change (p.1 0)^2+1-2*p.2 0≤0 at hg
  rw [hy] at hg
  nlinarith [sq_nonneg (p.1 0)]

theorem f2_root_relaxed_minimum :
    IsMinimizer (f2.relaxationOn Set.univ) f2.objective (pt (2/5) (29/50)) := by
  refine ⟨⟨⟨Set.mem_univ _,fun _ => by norm_num [f2,boxModel,pt]⟩,
    (f2_linear _).mpr (by norm_num [pt]),?_⟩,?_⟩
  · intro i; norm_num [f2,boxModel,pt]
  · intro p hp
    have hg := hp.1.2 (0 : Fin 1)
    change (p.1 0)^2+1-2*p.2 0≤0 at hg
    rw [f2_objective,f2_objective]
    norm_num [pt]
    nlinarith [sq_nonneg (p.1 0-2/5)]

theorem f2_original_minimum : IsMinimizer (f2.feasibleOn Set.univ) f2.objective (pt 1 1) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact ⟨⟨Set.mem_univ _,fun _ => by norm_num [f2,boxModel,pt]⟩,(f2_linear _).mpr (by norm_num [pt])⟩
  · exact ⟨fun _ => 1,fun _ => by norm_num [f2,boxModel],by ext i; norm_num [pt]⟩
  · intro p hp
    obtain ⟨y,hy,heq⟩ := hp.2
    have hi0 := (hy 0).1
    have hi1 := (hy 0).2
    change (0 : ℝ)≤(y 0 : ℝ) at hi0
    change (y 0 : ℝ)≤1 at hi1
    have hiz0 : 0≤y 0 := by exact_mod_cast hi0
    have hiz1 : y 0≤1 := by exact_mod_cast hi1
    have hg := hp.1.1.2 (0 : Fin 1)
    change (p.1 0)^2+1-2*p.2 0≤0 at hg
    have hpy : p.2 0=(y 0 : ℝ) := congrFun heq 0
    have hy1 : y 0=1 := by
      by_contra hh
      have hz : y 0=0 := by omega
      rw [hpy,hz] at hg
      norm_num at hg
      nlinarith [sq_nonneg (p.1 0)]
    have hpy1 : p.2 0=1 := by simpa [hy1] using hpy
    rw [hpy1] at hg
    have hx : p.1 0≤1 := by nlinarith [sq_nonneg (p.1 0-1)]
    rw [f2_objective,f2_objective,hpy1]
    norm_num [pt]
    linarith

/-- The actual nonnegative-slack problem at y=0, with M=1. -/
theorem f2_penalty_one_actual_minimum :
    IsMinimizer (penaltyPairs (f2.fixedLinearFiber (fun _ => 0)) f2.g)
      (fun q => f2.objective q.1+1*q.2) (pt 1 0,2) := by
  refine ⟨⟨⟨(f2_linear _).mpr (by norm_num [pt]),rfl⟩,
    by norm_num,fun _ => by norm_num [f2,boxModel,pt]⟩,?_⟩
  intro q hq
  have hy : q.1.2 0=0 := congrFun hq.1.2 0
  have hg := hq.2.2 (0 : Fin 1)
  change (q.1.1 0)^2+1-2*q.1.2 0≤q.2 at hg
  simp only [f2_objective,pt,hy]
  nlinarith [sq_nonneg (q.1.1 0-1)]

theorem f2_penalty_hundred_actual_minimum :
    IsMinimizer (penaltyPairs (f2.fixedLinearFiber (fun _ => 0)) f2.g)
      (fun q => f2.objective q.1+100*q.2) (pt (1/100) 0,10001/10000) := by
  refine ⟨⟨⟨(f2_linear _).mpr (by norm_num [pt]),rfl⟩,
    by norm_num,fun _ => by norm_num [f2,boxModel,pt]⟩,?_⟩
  intro q hq
  have hy : q.1.2 0=0 := congrFun hq.1.2 0
  have hg := hq.2.2 (0 : Fin 1)
  change (q.1.1 0)^2+1-2*q.1.2 0≤q.2 at hg
  simp only [f2_objective,pt,hy]
  nlinarith [sq_nonneg (q.1.1 0-1/100)]

theorem f2_penalized_zero_is_not_original_value :
    f2.objective (pt 1 0)+1*2=0 ∧ f2.objective (pt 1 1)=3 ∧
      ¬∃p∈(f2.feasibleOn Set.univ),f2.objective p≤0 := by
  refine ⟨by norm_num [f2_objective,pt],by norm_num [f2_objective,pt],?_⟩
  rintro ⟨p,hp,hv⟩
  have hm := f2_original_minimum.2 p hp
  norm_num [f2_objective,pt] at hm
  rw [f2_objective] at hv
  linarith


def f2Root : BBNode 1 := ⟨fun _ => 0,fun _ => 1⟩
def f2Seed : STSeed 1 1 1 := ⟨pt (2/5) (29/50),Set.univ⟩
def f2PenaltySeed (M : ℝ) : STSeed 1 1 1 := ⟨pt (1/M) 0,Set.univ⟩
def f2RepeatedSeeds (k : ℕ) : List (STSeed 1 1 1) :=
  f2Seed :: List.replicate k (f2PenaltySeed 1)

theorem f2_seed_cut (q : Point 1 1) :
    stSeedCuts f2 f2Seed q ↔ 21/50+(2/5)*q.1 0≤q.2 0 := by
  unfold stSeedCuts
  simp only [f2Seed,Set.mem_univ,forall_true_left]
  constructor
  · intro h
    have hh := h (0 : Fin 1)
    rw [(f2_derivative _ _).fderiv] at hh
    norm_num [f2,boxModel,pt,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY] at hh
    linarith
  · intro h j
    rw [(f2_derivative _ _).fderiv]
    norm_num [f2,boxModel,pt,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY]
    linarith

theorem f2_penalty_one_cut (q : Point 1 1) :
    stSeedCuts f2 (f2PenaltySeed 1) q ↔ q.1 0≤q.2 0 := by
  unfold stSeedCuts
  simp only [f2PenaltySeed,Set.mem_univ,forall_true_left]
  constructor
  · intro h
    have hh := h (0 : Fin 1)
    rw [(f2_derivative _ _).fderiv] at hh
    norm_num [f2,boxModel,pt,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY] at hh
    linarith
  · intro h j
    rw [(f2_derivative _ _).fderiv]
    norm_num [f2,boxModel,pt,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY]
    linarith

theorem f2_repeated_history_append (k : ℕ) :
    f2RepeatedSeeds (k+1)=f2RepeatedSeeds k++[f2PenaltySeed 1] := by
  simp [f2RepeatedSeeds,List.replicate_succ',List.cons_append]

/-- Every retained cut is present in this exact LP minimum. This is the
mathematical repeated re-solve control; a QG microstep-loop theorem requires
the separately reviewed original-process adapter. -/
theorem f2_every_repeated_lp_minimum (k : ℕ) :
    IsMinimizer (stLP f2 (f2RepeatedSeeds k) [] f2Root) f2.objective (pt (-21/20) 0) := by
  refine ⟨⟨(f2_linear _).mpr (by norm_num [pt]),?_,?_,by simp⟩,?_⟩
  · intro i; norm_num [f2Root,pt]
  · intro a ha
    simp only [f2RepeatedSeeds,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact (f2_seed_cut _).mpr (by norm_num [pt])
    · have he : a=f2PenaltySeed 1 := List.eq_of_mem_replicate ha
      rw [he]
      exact (f2_penalty_one_cut _).mpr (by norm_num [pt])
  · intro p hp
    have hs := (f2_seed_cut p).mp (hp.2.2.1 f2Seed (by simp [f2RepeatedSeeds]))
    rw [f2_objective,f2_objective]
    norm_num [pt]
    linarith

theorem f2_repeated_lp_value_and_integer_trial :
    f2.objective (pt (-21/20) 0)=21/10 ∧
    (pt (-21/20) 0)∈IntegerCylinder (n:=1) f2.lo f2.hi ∧
    (pt (-21/20) 0)∉f2.nonlinearRegion := by
  refine ⟨by norm_num [f2_objective,pt],?_,?_⟩
  · exact ⟨fun _ => 0,fun _ => by norm_num [f2,boxModel],by ext i; norm_num [pt]⟩
  · intro h; have hh := h (0 : Fin 1); norm_num [f2,boxModel,pt] at hh

theorem f2_penalty_hundred_cut (q : Point 1 1) :
    stSeedCuts f2 (f2PenaltySeed 100) q ↔ 9999/10000+(1/50)*q.1 0-2*q.2 0≤0 := by
  unfold stSeedCuts
  simp only [f2PenaltySeed,Set.mem_univ,forall_true_left]
  constructor
  · intro h
    have hh := h (0 : Fin 1)
    rw [(f2_derivative _ _).fderiv] at hh
    norm_num [f2,boxModel,pt,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY] at hh
    linarith
  · intro h j
    rw [(f2_derivative _ _).fderiv]
    norm_num [f2,boxModel,pt,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY]
    linarith

theorem f2_penalty_hundred_excludes_zero_fiber :
    ¬∃q∈f2.fixedLinearFiber (fun _ => 0),stSeedCuts f2 (f2PenaltySeed 100) q := by
  rintro ⟨q,hq,hcut⟩
  have hy : q.2 0=0 := congrFun hq.2 0
  have hb := (f2_linear q).mp hq.1
  have hc := (f2_penalty_hundred_cut q).mp hcut
  rw [hy] at hc
  linarith

theorem f2_penalty_hundred_exact_boundary {q : Point 1 1}
    (hy : q.2 0=0) (hc : stSeedCuts f2 (f2PenaltySeed 100) q) : q.1 0≤-9999/200 := by
  have hh := (f2_penalty_hundred_cut q).mp hc
  rw [hy] at hh
  linarith


theorem quad_derivative (a b : ℝ) (p : Point 1 1) :
    HasFDerivAt (fun q : Point 1 1 => (q.1 0)^2+a-b*q.2 0)
      ((2*p.1 0) • cx-b • cy) p := by
  have hh := (((hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p cx.hasFDerivAt).add_const a).fun_sub
    (cy.hasFDerivAt.const_mul b)
  simpa [cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY,Function.comp_def] using hh

theorem quad_convex (a b : ℝ) :
    ConvexOn ℝ Set.univ (fun q : Point 1 1 => (q.1 0)^2+a-b*q.2 0) := by
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have hh := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.1 0-q.1 0))
  simp only [Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have ht : t=1-s := by linarith
  rw [ht] at hh ⊢
  nlinarith

def hardModel (t : ℝ) : ModelData 1 1 2 2 :=
  boxModel 2 (fun j p => if j=0 then (p.1 0)^2-t*p.2 0 else p.1 0+1-2*t*p.2 0) 1 t 0 0

def hardRow (t : ℝ) : Fin 1 → Point 1 1 → ℝ := fun _ => (hardModel t).g 0
def softRow (t : ℝ) : Fin 1 → Point 1 1 → ℝ := fun _ => (hardModel t).g 1

theorem hard_base_compact (t : ℝ) : IsCompact ((hardModel t).linearRegion ∩
    IntegerCylinder (n:=1) (hardModel t).lo (hardModel t).hi) := box_base_compact _ _ _ _ _ _

theorem hard_rows_convex (t : ℝ) : ∀j,ConvexOn ℝ Set.univ ((hardModel t).g j) := by
  intro j
  fin_cases j
  · simpa [hardModel,boxModel] using quad_convex 0 t
  · refine ⟨convex_univ,?_⟩
    intro p _ q _ s u hs hu hsu
    simp [hardModel,boxModel,smul_eq_mul]
    nlinarith

theorem hard_rows_C2 (t : ℝ) : ∀j,ContDiff ℝ 2 ((hardModel t).g j) := by
  intro j
  fin_cases j
  · exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).sub
      (contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd))
  · exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).add contDiff_const).sub
      (contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd))

theorem hard_fiber_actual_minimum (t : ℝ) :
    IsMinimizer (weightedHardRegion ((hardModel t).fixedLinearFiber (fun _ => 0)) (hardRow t))
      (weightedPositive (fun _ : Fin 1 => 1) (softRow t)) (pt 0 0) := by
  refine ⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    fun _ => by norm_num [hardRow,hardModel,boxModel,pt]⟩,?_⟩
  intro q hq
  have hy : q.2 0=0 := congrFun hq.1.2 0
  have hh := hq.2 (0 : Fin 1)
  change (q.1 0)^2-t*q.2 0≤0 at hh
  rw [hy] at hh
  have hx : q.1 0=0 := by nlinarith [sq_nonneg (q.1 0)]
  simp [weightedPositive,softRow,hardModel,boxModel,pt,hx,hy]

theorem hard_fiber_value_one (t : ℝ) :
    weightedPositive (fun _ : Fin 1 => 1) (softRow t) (pt 0 0)=1 := by
  norm_num [weightedPositive,softRow,hardModel,boxModel,pt]

theorem hard_fiber_original_empty (t : ℝ) :
    ¬∃q∈weightedHardRegion ((hardModel t).fixedLinearFiber (fun _ => 0)) (hardRow t),
      ∀j,softRow t j q≤0 := by
  exact (weighted_hard_value_pos_iff_empty _ _ _ _ (fun _ => by norm_num)
    (hard_fiber_actual_minimum t)).mp (by rw [hard_fiber_value_one]; norm_num)

theorem hard_fiber_slater_impossible (t : ℝ) :
    ¬∃q∈(hardModel t).fixedLinearFiber (fun _ => 0),∀j,hardRow t j q<0 := by
  rintro ⟨q,hq,hh⟩
  have hy : q.2 0=0 := congrFun hq.2 0
  have hg := hh (0 : Fin 1)
  change (q.1 0)^2-t*q.2 0<0 at hg
  rw [hy] at hg
  nlinarith [sq_nonneg (q.1 0)]

theorem hard_zero_anchor_derivative (t : ℝ) (j : Fin 2) :
    HasFDerivAt ((hardModel t).g j)
      (if j=0 then -(t • cy) else cx-(2*t) • cy) (pt 0 0) := by
  fin_cases j
  · simpa [hardModel,boxModel,pt,neg_smul] using quad_derivative 0 t (pt 0 0)
  · have hh := ((cx.hasFDerivAt (x:=pt 0 0)).add_const 1).fun_sub (cy.hasFDerivAt.const_mul (2*t))
    simpa [hardModel,boxModel,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY] using hh

theorem hard_actual_minimum_tangents_fail_exclusion (t : ℝ) :
    pt (-1) 0∈(hardModel t).fixedLinearFiber (fun _ => 0) ∧
    ∀j,(hardModel t).g j (pt 0 0)+
      (fderiv ℝ ((hardModel t).g j) (pt 0 0)) (pt (-1) 0-pt 0 0)≤0 := by
  refine ⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,?_⟩
  intro j
  rw [(hard_zero_anchor_derivative t j).fderiv]
  fin_cases j <;>
    norm_num [hardModel,boxModel,pt,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY]

theorem hard_h1_original_empty : (hardModel 0).feasibleOn Set.univ=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hh := hp.1.1.2 (0 : Fin 2)
  have hs := hp.1.1.2 (1 : Fin 2)
  norm_num [hardModel,boxModel] at hh hs
  have hx : p.1 0=0 := by nlinarith [sq_nonneg (p.1 0)]
  linarith

theorem hard_h1_global_feasible_CQ_vacuous (P : Point 1 1 → Prop) :
    ∀p∈(hardModel 0).feasibleOn Set.univ,P p := by
  rw [hard_h1_original_empty]
  simp

theorem hard_h2_global_strict_and_original_nonempty :
    (pt 0 (3/4)∈(hardModel 1).linearRegion ∧
      ∀j,(hardModel 1).g j (pt 0 (3/4))<0) ∧
    pt 0 1∈(hardModel 1).feasibleOn Set.univ := by
  refine ⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),?_⟩,
    ⟨⟨⟨Set.mem_univ _,?_⟩,(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt])⟩,?_⟩⟩
  · intro j; fin_cases j <;> norm_num [hardModel,boxModel,pt]
  · intro j; fin_cases j <;> norm_num [hardModel,boxModel,pt]
  · exact ⟨fun _ => 1,fun _ => by norm_num [hardModel,boxModel],by ext i; norm_num [pt]⟩


def h3 : ModelData 1 1 1 2 :=
  { Chapter02CPExamples.scalarModel 1 1 (fun _ x => x+1) 0 with hi := fun _ => 0 }

theorem h3_linear (p : Point 1 1) : p∈h3.linearRegion ↔ 0≤p.1 0 ∧ p.1 0≤1 :=
  Chapter02CPExamples.scalar_linear_iff 1 1 (fun _ x => x+1) 0 p

theorem h3_base_compact : IsCompact (h3.linearRegion ∩ IntegerCylinder (n:=1) h3.lo h3.hi) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (pt 0 0) (pt 1 0))).of_isClosed_subset
    (Chapter02CPExamples.base_closed _)
  rintro p ⟨hp,y,hy,heq⟩
  have hx := (h3_linear p).mp hp
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i; exact hx.1
  · intro i; rw [heq]; exact (hy i).1
  · intro i; fin_cases i; exact hx.2
  · intro i; rw [heq]; exact (hy i).2

theorem h3_actual_minimum :
    IsMinimizer (h3.fixedLinearFiber (fun _ => 0))
      (weightedPositive (fun _ : Fin 1 => 1) h3.g) (pt 0 0) := by
  refine ⟨⟨(h3_linear _).mpr (by norm_num [pt]),rfl⟩,?_⟩
  intro q hq
  have hx := ((h3_linear q).mp hq.1).1
  simp only [weightedPositive,Fin.sum_univ_one,one_mul]
  change max ((0 : ℝ)+1) 0 ≤ max (q.1 0+1) 0
  rw [zero_add,max_eq_left (by norm_num : (0 : ℝ)≤1)]
  exact (show (1 : ℝ)≤q.1 0+1 by linarith).trans (le_max_left _ _)

theorem h3_full_domain_normal_and_exclusion :
    (∀q∈h3.fixedLinearFiber (fun _ => 0),(-cx) (q-pt 0 0)≤0) ∧
    cx+(-cx)=0 ∧ cx≠0 ∧
    (∀q∈h3.fixedLinearFiber (fun _ => 0),0<h3.g 0 (pt 0 0)+cx (q-pt 0 0)) := by
  refine ⟨?_,by abel,?_,?_⟩
  · intro q hq
    have hx := ((h3_linear q).mp hq.1).1
    simpa [cx,Chapter02Examples.coordX,pt] using neg_nonpos.mpr hx
  · intro hh
    have he := congrArg (fun D : Point 1 1 →L[ℝ] ℝ => D (pt 1 0)) hh
    norm_num [cx,Chapter02Examples.coordX,pt] at he
  · intro q hq
    have hx := ((h3_linear q).mp hq.1).1
    norm_num [h3,Chapter02CPExamples.scalarModel,cx,Chapter02Examples.coordX,pt]
    linarith

def h4 : ModelData 1 1 1 2 := boxModel 1 (fun _ _ => 1) 1 0 0 0

theorem h4_empty_hard_region : weightedHardRegion (h4.fixedLinearFiber (fun _ => 0)) h4.g=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := hq.2 (0 : Fin 1)
  norm_num [h4,boxModel] at hh

theorem h4_no_hard_restoration_minimum :
    ¬∃p,IsMinimizer (weightedHardRegion (h4.fixedLinearFiber (fun _ => 0)) h4.g)
      (fun _ => (0 : ℝ)) p := by
  rw [h4_empty_hard_region]
  rintro ⟨p,hp⟩
  exact hp.1

theorem h4_zero_weight_actual_minimum_and_empty_original :
    IsMinimizer (h4.fixedLinearFiber (fun _ => 0))
      (weightedPositive (fun _ : Fin 1 => 0) h4.g) (pt 0 0) ∧
    weightedPositive (fun _ : Fin 1 => 0) h4.g (pt 0 0)=0 ∧
    h4.fixedNonlinearFiber (fun _ => 0)=∅ := by
  refine ⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,?_⟩,
    by simp [weightedPositive],?_⟩
  · intro q hq; simp [weightedPositive]
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hh := hq.2 (0 : Fin 1)
    norm_num [h4,boxModel] at hh

def p1 : ModelData 1 1 1 2 := boxModel 1 (fun _ p => p.1 0) 1 0 (-1) 0

theorem p1_half_actual_minimum :
    IsMinimizer (penaltyPairs (p1.fixedLinearFiber (fun _ => 0)) p1.g)
      (fun q => p1.objective q.1+(1/2)*q.2) (pt 1 0,1) := by
  refine ⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    by norm_num,fun _ => by norm_num [p1,boxModel,pt]⟩,?_⟩
  intro q hq
  have hx := ((box_linear _ _ _ _ _ _ _).mp hq.1.1).2
  have hg := hq.2.2 (0 : Fin 1)
  change q.1.1 0≤q.2 at hg
  change q.1.1 0≤1 at hx
  simp [p1,box_objective,pt]
  linarith

theorem p1_unit_tied_actual_minimum {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) :
    IsMinimizer (penaltyPairs (p1.fixedLinearFiber (fun _ => 0)) p1.g)
      (fun q => p1.objective q.1+1*q.2) (pt t 0,t) := by
  refine ⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by simp [pt]; constructor <;> linarith),rfl⟩,
    ht0,fun _ => by simp [p1,boxModel,pt]⟩,?_⟩
  intro q hq
  have hg := hq.2.2 (0 : Fin 1)
  change q.1.1 0≤q.2 at hg
  simp [p1,box_objective,pt]
  linarith

theorem p1_large_actual_minimum {M : ℝ} (hM : 1<M) :
    IsMinimizer (penaltyPairs (p1.fixedLinearFiber (fun _ => 0)) p1.g)
      (fun q => p1.objective q.1+M*q.2) (pt 0 0,0) := by
  refine ⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    le_rfl,fun _ => by simp [p1,boxModel,pt]⟩,?_⟩
  intro q hq
  have hg := hq.2.2 (0 : Fin 1)
  change q.1.1 0≤q.2 at hg
  have hu := hq.2.1
  simp [p1,box_objective,pt]
  nlinarith

theorem p1_original_minimum_and_strict :
    IsMinimizer (p1.fixedNonlinearFiber (fun _ => 0)) p1.objective (pt 0 0) ∧
    pt (-1) 0∈p1.fixedLinearFiber (fun _ => 0) ∧ ∀j,p1.g j (pt (-1) 0)<0 := by
  refine ⟨⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    fun _ => by norm_num [p1,boxModel,pt]⟩,?_⟩,
    ⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    fun _ => by norm_num [p1,boxModel,pt]⟩
  intro q hq
  have hg := hq.2 (0 : Fin 1)
  change q.1 0≤0 at hg
  simpa [p1,box_objective,pt] using neg_nonneg.mpr hg

def p2 : ModelData 1 1 1 2 := boxModel 1 (fun _ p => (p.1 0)^2+1) 1 0 (-1) 0

theorem p2_actual_minimum :
    IsMinimizer (penaltyPairs (p2.fixedLinearFiber (fun _ => 0)) p2.g)
      (fun q => p2.objective q.1+1*q.2) (pt (1/2) 0,5/4) := by
  refine ⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    by norm_num,fun _ => by norm_num [p2,boxModel,pt]⟩,?_⟩
  intro q hq
  have hg := hq.2.2 (0 : Fin 1)
  change (q.1.1 0)^2+1≤q.2 at hg
  simp [p2,box_objective,pt]
  nlinarith [sq_nonneg (q.1.1 0-1/2)]

theorem p2_original_empty : p2.fixedNonlinearFiber (fun _ => 0)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hh := hq.2 (0 : Fin 1)
  change (q.1 0)^2+1≤0 at hh
  nlinarith [sq_nonneg (q.1 0)]

theorem p2_actual_derivative_and_admitted_tangent :
    (∀j,HasFDerivAt (p2.g j) cx (pt (1/2) 0)) ∧
    pt (-1) 0∈p2.fixedLinearFiber (fun _ => 0) ∧
    ∀j,p2.g j (pt (1/2) 0)+cx (pt (-1) 0-pt (1/2) 0)≤0 := by
  refine ⟨?_,⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,?_⟩
  · intro j
    simpa [p2,boxModel,pt] using quad_derivative 1 0 (pt (1/2) 0)
  · intro j
    norm_num [p2,boxModel,pt,cx,Chapter02Examples.coordX]

def feasibleQuadratic : ModelData 1 1 1 2 :=
  boxModel 1 (fun _ p => (p.1 0)^2-1) 10 0 (-2) 0

theorem feasible_quadratic_small_penalty_actual_minimum :
    IsMinimizer (penaltyPairs (feasibleQuadratic.fixedLinearFiber (fun _ => 0)) feasibleQuadratic.g)
      (fun q => feasibleQuadratic.objective q.1+(1/2)*q.2) (pt 2 0,3) := by
  refine ⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    by norm_num,fun _ => by norm_num [feasibleQuadratic,boxModel,pt]⟩,?_⟩
  intro q hq
  have hg := hq.2.2 (0 : Fin 1)
  change (q.1.1 0)^2-1≤q.2 at hg
  simp [feasibleQuadratic,box_objective,pt]
  nlinarith [sq_nonneg (q.1.1 0-2)]

theorem feasible_quadratic_original_minimum_and_strict :
    IsMinimizer (feasibleQuadratic.fixedNonlinearFiber (fun _ => 0))
      feasibleQuadratic.objective (pt 1 0) ∧
    ∀j,feasibleQuadratic.g j (pt 0 0)<0 := by
  refine ⟨⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    fun _ => by norm_num [feasibleQuadratic,boxModel,pt]⟩,?_⟩,
    fun _ => by norm_num [feasibleQuadratic,boxModel,pt]⟩
  intro q hq
  have hg := hq.2 (0 : Fin 1)
  change (q.1 0)^2-1≤0 at hg
  simp [feasibleQuadratic,box_objective,pt]
  nlinarith [sq_nonneg (q.1 0-1)]


theorem h3_rows_regular : ∀j,ConvexOn ℝ Set.univ (h3.g j) ∧
    ContDiff ℝ 2 (h3.g j) ∧ HasFDerivAt (h3.g j) cx (pt 0 0) := by
  intro j
  refine ⟨?_,?_,?_⟩
  · exact (cx.toLinearMap.convexOn convex_univ).add (convexOn_const 1 convex_univ)
  · exact ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).add contDiff_const
  · exact cx.hasFDerivAt.add_const 1

theorem h4_regular : IsCompact (h4.linearRegion ∩ IntegerCylinder (n:=1) h4.lo h4.hi) ∧
    ∀j,ConvexOn ℝ Set.univ (h4.g j) ∧ ContDiff ℝ 2 (h4.g j) := by
  refine ⟨box_base_compact _ _ _ _ _ _,fun _ => ⟨convexOn_const 1 convex_univ,contDiff_const⟩⟩

theorem p1_regular : IsCompact (p1.linearRegion ∩ IntegerCylinder (n:=1) p1.lo p1.hi) ∧
    ∀j,ConvexOn ℝ Set.univ (p1.g j) ∧ ContDiff ℝ 2 (p1.g j) := by
  refine ⟨box_base_compact _ _ _ _ _ _,fun _ => ⟨cx.toLinearMap.convexOn convex_univ,?_⟩⟩
  exact (contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst

theorem p2_regular : IsCompact (p2.linearRegion ∩ IntegerCylinder (n:=1) p2.lo p2.hi) ∧
    ∀j,ConvexOn ℝ Set.univ (p2.g j) ∧ ContDiff ℝ 2 (p2.g j) := by
  refine ⟨box_base_compact _ _ _ _ _ _,?_⟩
  intro j
  refine ⟨?_,?_⟩
  · simpa [p2,boxModel] using quad_convex 1 0
  · exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).add contDiff_const

theorem feasible_quadratic_regular :
    IsCompact (feasibleQuadratic.linearRegion ∩ IntegerCylinder (n:=1)
      feasibleQuadratic.lo feasibleQuadratic.hi) ∧
    ∀j,ConvexOn ℝ Set.univ (feasibleQuadratic.g j) ∧ ContDiff ℝ 2 (feasibleQuadratic.g j) := by
  refine ⟨box_base_compact _ _ _ _ _ _,?_⟩
  intro j
  refine ⟨?_,?_⟩
  · simpa [feasibleQuadratic,boxModel,sub_eq_add_neg] using quad_convex (-1) 0
  · exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).sub contDiff_const

theorem f2_explicit_penalty_margin_and_oscillation :
    (∀p∈f2.fixedLinearFiber (fun _ => 0),(1 : ℝ)≤penaltyViolation f2.g p) ∧
    (∀p∈f2.fixedLinearFiber (fun _ => 0),∀q∈f2.fixedLinearFiber (fun _ => 0),
      f2.objective p-f2.objective q≤40) ∧ (40 : ℝ)<100*1 := by
  refine ⟨?_,?_,by norm_num⟩
  · intro p hp
    have hy : p.2 0=0 := congrFun hp.2 0
    have hh := penaltyViolation_row_le f2.g p (0 : Fin 1)
    change (p.1 0)^2+1-2*p.2 0≤penaltyViolation f2.g p at hh
    rw [hy] at hh
    nlinarith [sq_nonneg (p.1 0)]
  · intro p hp q hq
    have hpy : p.2 0=0 := congrFun hp.2 0
    have hqy : q.2 0=0 := congrFun hq.2 0
    have hx := (f2_linear p).mp hp.1
    have hqx := (f2_linear q).mp hq.1
    rw [f2_objective,f2_objective,hpy,hqy]
    linarith

def p3 : ModelData 1 1 0 2 := boxModel 0 Fin.elim0 1 0 0 0

theorem p3_base_compact_nonempty :
    IsCompact (p3.linearRegion ∩ IntegerCylinder (n:=1) p3.lo p3.hi) ∧
      (p3.fixedLinearFiber (fun _ => 0)).Nonempty := by
  exact ⟨box_base_compact _ _ _ _ _ _,
    ⟨pt 0 0,(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩⟩

theorem p3_positive_actual_minimum {M : ℝ} (hM : 0<M) :
    IsMinimizer (penaltyPairs (p3.fixedLinearFiber (fun _ => 0)) p3.g)
      (fun q => p3.objective q.1+M*q.2) (pt 0 0,0) := by
  apply (penalty_zero_rows_positive_iff _ _ _ hM _).mpr
  refine ⟨⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,?_⟩,rfl⟩
  intro q hq
  simp [p3,box_objective]

theorem p3_zero_coefficient_positive_slack_minimum :
    IsMinimizer (penaltyPairs (p3.fixedLinearFiber (fun _ => 0)) p3.g)
      (fun q => p3.objective q.1+0*q.2) (pt 0 0,7) := by
  apply penalty_zero_coefficient_any_height
  · refine ⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,?_⟩
    intro q hq; simp [p3,box_objective]
  · norm_num
  · intro j; exact Fin.elim0 j

theorem p3_negative_no_minimum :
    ¬∃q,IsMinimizer (penaltyPairs (p3.fixedLinearFiber (fun _ => 0)) p3.g)
      (fun q => p3.objective q.1+(-1)*q.2) q :=
  penalty_negative_no_minimum _ _ _ (by norm_num)

theorem p3_signed_free_slack_unbounded : ∀b : ℝ,
    ∃q∈RestorationPairs (p3.fixedLinearFiber (fun _ => 0)) p3.g,q.2<b := by
  intro b
  exact ⟨(pt 0 0,b-1),⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,
    (fun j => Fin.elim0 j)⟩,by dsimp; linarith⟩

def emptyBase : ModelData 1 1 0 2 := boxModel 0 Fin.elim0 (-1) 0 0 0

theorem empty_base_fixed_fiber : emptyBase.fixedLinearFiber (fun _ => 0)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hx := (box_linear _ _ _ _ _ _ _).mp hp.1
  change -(-1 : ℝ)≤p.1 0 ∧ p.1 0≤-1 at hx
  linarith [hx.1,hx.2]

theorem empty_base_no_penalty_reply (M : ℝ) :
    ¬∃q,IsMinimizer (penaltyPairs (emptyBase.fixedLinearFiber (fun _ => 0)) emptyBase.g)
      (fun q => emptyBase.objective q.1+M*q.2) q := by
  rw [empty_base_fixed_fiber]
  exact penalty_empty_domain_no_minimum _ _ _


theorem hard_h2_full_strict_base :
    (∀k,LinearForm ((hardModel 1).A k) ((hardModel 1).B k) (pt 0 (3/4))<
      (hardModel 1).rhs k) ∧
    (∀i,(hardModel 1).lo i<(pt 0 (3/4)).2 i ∧ (pt 0 (3/4)).2 i<(hardModel 1).hi i) := by
  constructor
  · intro k; fin_cases k <;> norm_num [hardModel,boxModel,LinearForm,pt]
  · intro i; norm_num [hardModel,boxModel,pt]

theorem p1_small_penalty_false_infeasibility :
    (p1.fixedNonlinearFiber (fun _ => 0)).Nonempty ∧
    (pt 1 0)∉p1.fixedNonlinearFiber (fun _ => 0) ∧ (0 : ℝ)<1 := by
  refine ⟨⟨pt 0 0,p1_original_minimum_and_strict.1.1⟩,?_,by norm_num⟩
  intro h
  have hh := h.2 (0 : Fin 1)
  norm_num [p1,boxModel,pt] at hh

theorem feasible_quadratic_small_penalty_false_infeasibility :
    (feasibleQuadratic.fixedNonlinearFiber (fun _ => 0)).Nonempty ∧
    (pt 2 0)∉feasibleQuadratic.fixedNonlinearFiber (fun _ => 0) ∧ (0 : ℝ)<3 := by
  refine ⟨⟨pt 1 0,feasible_quadratic_original_minimum_and_strict.1.1⟩,?_,by norm_num⟩
  intro h
  have hh := h.2 (0 : Fin 1)
  norm_num [feasibleQuadratic,boxModel,pt] at hh

theorem zero_rows_weighted_actual_minimum :
    IsMinimizer (p3.fixedLinearFiber (fun _ => 0))
      (weightedPositive (fun j : Fin 0 => Fin.elim0 j) p3.g) (pt 0 0) := by
  refine ⟨⟨(box_linear _ _ _ _ _ _ _).mpr (by norm_num [pt]),rfl⟩,?_⟩
  intro q hq
  simp [weightedPositive]

theorem hard_h1_convex_hull_CQ_vacuous (P : Point 1 1 → Prop) :
    ∀p∈convexHull ℝ ((hardModel 0).feasibleOn Set.univ),P p := by
  rw [hard_h1_original_empty]
  simp

theorem hard_derivative (t : ℝ) (p : Point 1 1) (j : Fin 2) :
    HasFDerivAt ((hardModel t).g j)
      (if j=0 then (2*p.1 0) • cx-t • cy else cx-(2*t) • cy) p := by
  fin_cases j
  · simpa [hardModel,boxModel] using quad_derivative 0 t p
  · have hh := ((cx.hasFDerivAt (x:=p)).add_const 1).fun_sub (cy.hasFDerivAt.const_mul (2*t))
    simpa [hardModel,boxModel,cx,cy,Chapter02Examples.coordX,Chapter02KKTExamples.coordY] using hh

/-- Full-space MFCQ holds even though the selected y=0 hard fiber has no strict
hard-feasible point and its actual restoration tangent family fails exclusion. -/
theorem hard_h2_full_space_MFCQ (p : Point 1 1) :
    ∃v : Point 1 1,
      (∀j,(hardModel 1).g j p=0 → (fderiv ℝ ((hardModel 1).g j) p) v<0) ∧
      (∀k,LinearForm ((hardModel 1).A k) ((hardModel 1).B k) p=(hardModel 1).rhs k →
        LinearForm ((hardModel 1).A k) ((hardModel 1).B k) v<0) ∧
      (∀i,p.2 i=(hardModel 1).lo i → 0<v.2 i) ∧
      (∀i,p.2 i=(hardModel 1).hi i → v.2 i<0) := by
  refine ⟨pt 0 (3/4)-p,?_,?_,?_,?_⟩
  · intro j hj
    rw [(hard_derivative 1 p j).fderiv]
    fin_cases j <;>
      norm_num [hardModel,boxModel,pt,cx,cy,Chapter02Examples.coordX,
        Chapter02KKTExamples.coordY] at hj ⊢ <;>
      nlinarith [sq_nonneg (p.1 0)]
  · intro k hk
    fin_cases k <;>
      norm_num [hardModel,boxModel,pt,LinearForm] at hk ⊢ <;> linarith
  · intro i hi
    simp only [hardModel,boxModel] at hi
    norm_num [pt,hi]
  · intro i hi
    simp only [hardModel,boxModel] at hi
    norm_num [pt,hi]

end Chapter02SourceRestorationExamples

#print axioms Chapter02SourceRestorationExamples.box_linear
#print axioms Chapter02SourceRestorationExamples.box_objective
#print axioms Chapter02SourceRestorationExamples.box_base_compact
#print axioms Chapter02SourceRestorationExamples.f2_linear
#print axioms Chapter02SourceRestorationExamples.f2_objective
#print axioms Chapter02SourceRestorationExamples.f2_base_compact
#print axioms Chapter02SourceRestorationExamples.f2_rows_convex
#print axioms Chapter02SourceRestorationExamples.f2_rows_C2
#print axioms Chapter02SourceRestorationExamples.f2_derivative
#print axioms Chapter02SourceRestorationExamples.f2_global_strict
#print axioms Chapter02SourceRestorationExamples.f2_zero_fiber_empty
#print axioms Chapter02SourceRestorationExamples.f2_root_relaxed_minimum
#print axioms Chapter02SourceRestorationExamples.f2_original_minimum
#print axioms Chapter02SourceRestorationExamples.f2_penalty_one_actual_minimum
#print axioms Chapter02SourceRestorationExamples.f2_penalty_hundred_actual_minimum
#print axioms Chapter02SourceRestorationExamples.f2_penalized_zero_is_not_original_value
#print axioms Chapter02SourceRestorationExamples.f2_seed_cut
#print axioms Chapter02SourceRestorationExamples.f2_penalty_one_cut
#print axioms Chapter02SourceRestorationExamples.f2_repeated_history_append
#print axioms Chapter02SourceRestorationExamples.f2_every_repeated_lp_minimum
#print axioms Chapter02SourceRestorationExamples.f2_repeated_lp_value_and_integer_trial
#print axioms Chapter02SourceRestorationExamples.f2_penalty_hundred_cut
#print axioms Chapter02SourceRestorationExamples.f2_penalty_hundred_excludes_zero_fiber
#print axioms Chapter02SourceRestorationExamples.f2_penalty_hundred_exact_boundary
#print axioms Chapter02SourceRestorationExamples.quad_derivative
#print axioms Chapter02SourceRestorationExamples.quad_convex
#print axioms Chapter02SourceRestorationExamples.hard_base_compact
#print axioms Chapter02SourceRestorationExamples.hard_rows_convex
#print axioms Chapter02SourceRestorationExamples.hard_rows_C2
#print axioms Chapter02SourceRestorationExamples.hard_fiber_actual_minimum
#print axioms Chapter02SourceRestorationExamples.hard_fiber_value_one
#print axioms Chapter02SourceRestorationExamples.hard_fiber_original_empty
#print axioms Chapter02SourceRestorationExamples.hard_fiber_slater_impossible
#print axioms Chapter02SourceRestorationExamples.hard_zero_anchor_derivative
#print axioms Chapter02SourceRestorationExamples.hard_actual_minimum_tangents_fail_exclusion
#print axioms Chapter02SourceRestorationExamples.hard_h1_original_empty
#print axioms Chapter02SourceRestorationExamples.hard_h1_global_feasible_CQ_vacuous
#print axioms Chapter02SourceRestorationExamples.hard_h2_global_strict_and_original_nonempty
#print axioms Chapter02SourceRestorationExamples.h3_linear
#print axioms Chapter02SourceRestorationExamples.h3_base_compact
#print axioms Chapter02SourceRestorationExamples.h3_actual_minimum
#print axioms Chapter02SourceRestorationExamples.h3_full_domain_normal_and_exclusion
#print axioms Chapter02SourceRestorationExamples.h4_empty_hard_region
#print axioms Chapter02SourceRestorationExamples.h4_no_hard_restoration_minimum
#print axioms Chapter02SourceRestorationExamples.h4_zero_weight_actual_minimum_and_empty_original
#print axioms Chapter02SourceRestorationExamples.p1_half_actual_minimum
#print axioms Chapter02SourceRestorationExamples.p1_unit_tied_actual_minimum
#print axioms Chapter02SourceRestorationExamples.p1_large_actual_minimum
#print axioms Chapter02SourceRestorationExamples.p1_original_minimum_and_strict
#print axioms Chapter02SourceRestorationExamples.p2_actual_minimum
#print axioms Chapter02SourceRestorationExamples.p2_original_empty
#print axioms Chapter02SourceRestorationExamples.p2_actual_derivative_and_admitted_tangent
#print axioms Chapter02SourceRestorationExamples.feasible_quadratic_small_penalty_actual_minimum
#print axioms Chapter02SourceRestorationExamples.feasible_quadratic_original_minimum_and_strict
#print axioms Chapter02SourceRestorationExamples.h3_rows_regular
#print axioms Chapter02SourceRestorationExamples.h4_regular
#print axioms Chapter02SourceRestorationExamples.p1_regular
#print axioms Chapter02SourceRestorationExamples.p2_regular
#print axioms Chapter02SourceRestorationExamples.feasible_quadratic_regular
#print axioms Chapter02SourceRestorationExamples.f2_explicit_penalty_margin_and_oscillation
#print axioms Chapter02SourceRestorationExamples.p3_base_compact_nonempty
#print axioms Chapter02SourceRestorationExamples.p3_positive_actual_minimum
#print axioms Chapter02SourceRestorationExamples.p3_zero_coefficient_positive_slack_minimum
#print axioms Chapter02SourceRestorationExamples.p3_negative_no_minimum
#print axioms Chapter02SourceRestorationExamples.p3_signed_free_slack_unbounded
#print axioms Chapter02SourceRestorationExamples.empty_base_fixed_fiber
#print axioms Chapter02SourceRestorationExamples.empty_base_no_penalty_reply
#print axioms Chapter02SourceRestorationExamples.hard_h2_full_strict_base
#print axioms Chapter02SourceRestorationExamples.p1_small_penalty_false_infeasibility
#print axioms Chapter02SourceRestorationExamples.feasible_quadratic_small_penalty_false_infeasibility
#print axioms Chapter02SourceRestorationExamples.zero_rows_weighted_actual_minimum
#print axioms Chapter02SourceRestorationExamples.hard_h1_convex_hull_CQ_vacuous
#print axioms Chapter02SourceRestorationExamples.hard_derivative
#print axioms Chapter02SourceRestorationExamples.hard_h2_full_space_MFCQ
