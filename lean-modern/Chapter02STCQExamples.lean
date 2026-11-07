module

public import Chapter02OAExamples
public import Chapter02STDriver

@[expose] public section

/-! Source-CQ controls F1a/F1b. Global strict feasibility and even the explicit
full-space MFCQ below do not imply fixed-integer-fiber Slater/KKT. Algorithmic
traces are added against the actual single-tree interfaces separately. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02Examples
namespace Chapter02STCQExamples

def pt (x y : ℝ) : Point 1 1 := (fun _ => x, fun _ => y)
def coordY : Point 1 1 →L[ℝ] ℝ := Chapter02KKTExamples.coordY

def model (delta : ℝ) : ModelData 1 1 1 2 :=
  { Chapter02OAExamples.traceModel with
    g := fun _ p => (p.1 0)^2-p.2 0
    c1 := fun _ => -1
    c2 := fun _ => delta }

theorem objective (delta : ℝ) (p : Point 1 1) :
    (model delta).objective p = -p.1 0 + delta*p.2 0 := by
  simp [model,ModelData.objective,LinearForm,Fin.sum_univ_one]

theorem linear_iff (delta : ℝ) (p : Point 1 1) :
    p ∈ (model delta).linearRegion ↔ -2 ≤ p.1 0 ∧ p.1 0 ≤ 2 :=
  Chapter02OAExamples.trace_linear_iff p

theorem base_compact (delta : ℝ) : IsCompact
    ((model delta).linearRegion ∩ IntegerCylinder (n := 1) (model delta).lo (model delta).hi) :=
  Chapter02OAExamples.trace_base_compact

theorem rows_convex (delta : ℝ) :
    ∀ j, ConvexOn ℝ Set.univ ((model delta).g j) :=
  Chapter02KKTExamples.zeroMargin_convex

theorem rows_C2 (delta : ℝ) : ∀ j, ContDiff ℝ 2 ((model delta).g j) := by
  intro j
  exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).sub
    ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd)

theorem rows_diff (delta : ℝ) : ∀ j, Differentiable ℝ ((model delta).g j) :=
  fun j => (rows_C2 delta j).differentiable (by norm_num)

theorem row_derivative (delta : ℝ) (a : Point 1 1) (j : Fin 1) :
    HasFDerivAt ((model delta).g j) ((2*a.1 0) • coordX-coordY) a := by
  have h := ((hasDerivAt_pow 2 (a.1 0)).comp_hasFDerivAt a coordX.hasFDerivAt).fun_sub
    coordY.hasFDerivAt
  simpa [model,coordX,coordY,Chapter02KKTExamples.coordY,Function.comp_def] using h

theorem fixed_zero_minimum (delta : ℝ) :
    IsMinimizer ((model delta).fixedNonlinearFiber (fun _ => 0))
      (model delta).objective (pt 0 0) := by
  refine ⟨⟨⟨(linear_iff delta _).mpr (by norm_num [pt]),rfl⟩,
    fun _ => by norm_num [model,pt]⟩,?_⟩
  intro p hp
  have hy : p.2 0 = 0 := congrFun hp.1.2 0
  have hg := hp.2 (0 : Fin 1)
  change (p.1 0)^2-p.2 0 ≤ 0 at hg
  have hx : p.1 0 = 0 := by nlinarith [sq_nonneg (p.1 0)]
  simp [objective,pt,hx,hy]

def zeroBatch : OABatch 1 1 := ⟨fun _ => 0,pt 0 0,none⟩

theorem zero_batch_valid (delta : ℝ) : oaBatchValid (model delta) zeroBatch := by
  refine ⟨?_,by ext i; simp [zeroBatch,Chapter02.oaIntCast,pt],?_⟩
  · intro i
    norm_num [model,Chapter02OAExamples.traceModel,zeroBatch]
  · change IsMinimizer ((model delta).fixedNonlinearFiber
      (Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)))) (model delta).objective (pt 0 0)
    have he : Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)) = (fun _ => 0) := by
      ext i
      norm_num [Chapter02.oaIntCast]
    rw [he]
    exact fixed_zero_minimum delta

theorem zero_batch_cuts (delta : ℝ) (q : Point 1 1) :
    oaBatchCuts (model delta) zeroBatch q ↔ -q.2 0 ≤ 0 := by
  have hd : oaBatchDerivative (model delta) zeroBatch = fun _ => -coordY := by
    funext j
    simpa [zeroBatch,pt,oaBatchDerivative] using (row_derivative delta (pt 0 0) j).fderiv
  unfold oaBatchCuts SelectedOARows tangentRow
  rw [hd]
  simp [oaBatchRows,zeroBatch,model,pt,coordY,Chapter02KKTExamples.coordY]

theorem global_strict_point (delta : ℝ) :
    pt 0 (1/2) ∈ (model delta).relaxationOn Set.univ ∧
    (∀ j, (model delta).g j (pt 0 (1/2)) < 0) ∧
    (∀ k, LinearForm ((model delta).A k) ((model delta).B k) (pt 0 (1/2)) <
      (model delta).rhs k) ∧
    (∀ i, (model delta).lo i < (pt 0 (1/2)).2 i ∧
      (pt 0 (1/2)).2 i < (model delta).hi i) := by
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨⟨Set.mem_univ _,fun _ => by norm_num [model,pt]⟩,
      (linear_iff delta _).mpr (by norm_num [pt]),?_⟩
    intro i
    norm_num [model,Chapter02OAExamples.traceModel,pt]
  · intro j; norm_num [model,pt]
  · intro k
    norm_num [model,Chapter02OAExamples.traceModel,LinearForm,pt]
  · intro i; norm_num [model,Chapter02OAExamples.traceModel,pt]

/-- Full-space MFCQ for the nonlinear and affine rows, including the two
continuous integer-coordinate bounds. It does not freeze the integer fiber. -/
def FullMFCQ (delta : ℝ) (p : Point 1 1) : Prop :=
  ∃ v : Point 1 1,
    (∀ j, (model delta).g j p = 0 → (fderiv ℝ ((model delta).g j) p) v < 0) ∧
    (∀ k, LinearForm ((model delta).A k) ((model delta).B k) p = (model delta).rhs k →
      LinearForm ((model delta).A k) ((model delta).B k) v < 0) ∧
    (∀ i, p.2 i = (model delta).lo i → 0 < v.2 i) ∧
    (∀ i, p.2 i = (model delta).hi i → v.2 i < 0)

theorem full_mfcq_everywhere (delta : ℝ) (p : Point 1 1) : FullMFCQ delta p := by
  refine ⟨pt 0 (1/2)-p,?_,?_,?_,?_⟩
  · intro j hj
    rw [(row_derivative delta p j).fderiv]
    change (p.1 0)^2-p.2 0=0 at hj
    simp [coordX,coordY,Chapter02KKTExamples.coordY,pt]
    nlinarith [sq_nonneg (p.1 0)]
  · intro k hk
    fin_cases k <;>
      norm_num [model,Chapter02OAExamples.traceModel,LinearForm,Fin.sum_univ_one,pt] at hk ⊢ <;>
      linarith
  · intro i hi
    simp [model,Chapter02OAExamples.traceModel] at hi
    norm_num [pt,hi]
  · intro i hi
    simp [model,Chapter02OAExamples.traceModel] at hi
    norm_num [pt,hi]

theorem fiber_slater_fails (delta : ℝ) : ¬ OAFiberSlater (model delta) := by
  intro h
  have hy : (fun _ : Fin 1 => (0 : ℤ)) ∈ IntegerBox (model delta).lo (model delta).hi := by
    intro i; norm_num [model,Chapter02OAExamples.traceModel]
  have hn : ((model delta).fixedNonlinearFiber (Chapter02.oaIntCast (fun _ => (0 : ℤ)))).Nonempty := by
    have he : Chapter02.oaIntCast (fun _ : Fin 1 => (0 : ℤ)) = (fun _ => 0) := by
      ext i
      norm_num [Chapter02.oaIntCast]
    rw [he]
    exact ⟨pt 0 0,(fixed_zero_minimum delta).1⟩
  obtain ⟨p,hp,hg⟩ := h _ hy hn
  have hpy : p.2 0=0 := by simpa [Chapter02.oaIntCast] using congrFun hp.2 0
  have hh := hg (0 : Fin 1)
  change (p.1 0)^2-p.2 0<0 at hh
  rw [hpy] at hh
  nlinarith [sq_nonneg (p.1 0)]

theorem zero_fiber_stationarity_impossible :
    ¬ ∃ lambda : ℝ, -1+lambda*(2*(pt 0 0).1 0)=0 := by
  norm_num [pt]

theorem f1b_root_minimum :
    IsMinimizer ((model 2).relaxationOn Set.univ) (model 2).objective (pt (1/4) (1/16)) := by
  refine ⟨⟨⟨Set.mem_univ _,fun _ => by norm_num [model,pt]⟩,
    (linear_iff 2 _).mpr (by norm_num [pt]),?_⟩,?_⟩
  · intro i; norm_num [model,Chapter02OAExamples.traceModel,pt]
  · intro p hp
    have hg := hp.1.2 (0 : Fin 1)
    change (p.1 0)^2-p.2 0≤0 at hg
    simp only [objective,pt]
    nlinarith [sq_nonneg (p.1 0-1/4)]

theorem objective_C2 (delta : ℝ) : ContDiff ℝ 2 (model delta).objective :=
  (linearFormCLM (model delta).c1 (model delta).c2).contDiff

theorem fixed_zero_fiber_iff (delta : ℝ) (p : Point 1 1) :
    p ∈ (model delta).fixedNonlinearFiber (fun _ => 0) ↔ p = pt 0 0 := by
  constructor
  · intro hp
    have hy := congrFun hp.1.2 0
    have hg := hp.2 (0 : Fin 1)
    change (p.1 0)^2-p.2 0 ≤ 0 at hg
    have hx : p.1 0 = 0 := by nlinarith [sq_nonneg (p.1 0)]
    apply Prod.ext
    · funext i; fin_cases i; exact hx
    · exact hp.1.2
  · rintro rfl
    exact (fixed_zero_minimum delta).1

theorem zero_fiber_no_kkt (delta : ℝ) :
    ¬ ∃ (D : Fin 1 → Point 1 1 →L[ℝ] ℝ) (lambda : Fin 1 → ℝ) (mu : Fin 2 → ℝ),
      FixedNLPKKT (model delta) (pt 0 0) D lambda mu := by
  rintro ⟨D,lambda,mu,h⟩
  have hD : D 0 = -coordY := by
    have hc : HasFDerivAt ((model delta).g 0) (-coordY) (pt 0 0) := by
      simpa [pt] using row_derivative delta (pt 0 0) 0
    exact (h.derivatives 0).unique hc
  have hm0 : mu 0 = 0 := by
    have hh := h.linear_complementarity 0
    norm_num [linearResidual,model,Chapter02OAExamples.traceModel,pt,LinearForm] at hh
    linarith
  have hm1 : mu 1 = 0 := by
    have hh := h.linear_complementarity 1
    norm_num [linearResidual,model,Chapter02OAExamples.traceModel,pt,LinearForm] at hh
    linarith
  have hh := h.stationarity (fun _ => 1)
  norm_num [ModelData.objective,model,Chapter02OAExamples.traceModel,LinearForm,
    Fin.sum_univ_one,Fin.sum_univ_succ,hD,hm0,hm1,coordY,Chapter02KKTExamples.coordY] at hh

theorem no_kkt_any_zero_fiber_point (delta : ℝ) (p : Point 1 1)
    (hp : p ∈ (model delta).fixedNonlinearFiber (fun _ => 0)) :
    ¬ ∃ (D : Fin 1 → Point 1 1 →L[ℝ] ℝ) (lambda : Fin 1 → ℝ) (mu : Fin 2 → ℝ),
      FixedNLPKKT (model delta) p D lambda mu := by
  rw [(fixed_zero_fiber_iff delta p).mp hp]
  exact zero_fiber_no_kkt delta

theorem global_cq_on_convex_hull (delta : ℝ) :
    ∀ p ∈ convexHull ℝ ((model delta).feasibleOn Set.univ), FullMFCQ delta p :=
  fun p _ => full_mfcq_everywhere delta p

theorem objective_tangent (delta : ℝ) (a q : Point 1 1) :
    (model delta).objective a + (fderiv ℝ (model delta).objective a) (q-a) =
      (model delta).objective q := by
  rw [(objective_hasFDerivAt (model delta) a).fderiv]
  simp [linearFormCLM_apply,ModelData.objective,model,LinearForm,Fin.sum_univ_one]
  ring

/-- The actual source epigraph LP on its root polyhedron, with objective and
constraint tangents and a closed cutoff. No original nonlinear constraint is
inserted into this set. Full source-loop transport awaits the cutoff engine. -/
def cutoffLP (delta epsilon upper : ℝ) (H : List (OABatch 1 1)) : Set (Point 1 1 × ℝ) :=
  {q | q.1 ∈ (model delta).linearRegion ∧
    (∀ i, (model delta).lo i ≤ q.1.2 i ∧ q.1.2 i ≤ (model delta).hi i) ∧
    (∀ b ∈ H, (model delta).objective b.anchor +
      (fderiv ℝ (model delta).objective b.anchor) (q.1-b.anchor) ≤ q.2 ∧
      oaBatchCuts (model delta) b q.1) ∧ q.2 ≤ upper-epsilon}

def f1aHistory (k : ℕ) : List (OABatch 1 1) := List.replicate (k+1) zeroBatch

theorem f1a_history_succ (k : ℕ) : f1aHistory (k+1) = f1aHistory k ++ [zeroBatch] := by
  simp only [f1aHistory,List.replicate_add,List.replicate_one]

theorem f1a_history_valid (delta : ℝ) (k : ℕ) :
    ∀ b ∈ f1aHistory k, oaBatchValid (model delta) b := by
  intro b hb
  have hb' : b = zeroBatch := (List.mem_replicate.mp hb).2
  rw [hb']
  exact zero_batch_valid delta

theorem f1a_lp_iff (delta epsilon : ℝ) (k : ℕ) (q : Point 1 1 × ℝ) :
    q ∈ cutoffLP delta epsilon 0 (f1aHistory k) ↔
      (-2 ≤ q.1.1 0 ∧ q.1.1 0 ≤ 2) ∧ (0 ≤ q.1.2 0 ∧ q.1.2 0 ≤ 1) ∧
      -q.1.1 0+delta*q.1.2 0 ≤ q.2 ∧ q.2 ≤ -epsilon := by
  constructor
  · rintro ⟨hl,hy,hH,hcut⟩
    have hb : zeroBatch ∈ f1aHistory k := by simp [f1aHistory]
    have ht := (hH zeroBatch hb).1
    rw [objective_tangent,objective] at ht
    exact ⟨(linear_iff delta _).mp hl,by simpa [model,Chapter02OAExamples.traceModel] using hy 0,
      ht,by simpa using hcut⟩
  · rintro ⟨hx,hy,ho,hcut⟩
    refine ⟨(linear_iff delta _).mpr hx,?_,?_,by simpa using hcut⟩
    · intro i; fin_cases i
      simpa [model,Chapter02OAExamples.traceModel] using hy
    · intro b hb
      have hb' : b=zeroBatch := (List.mem_replicate.mp hb).2
      rw [hb']
      exact ⟨by rw [objective_tangent,objective]; exact ho,
        (zero_batch_cuts delta q.1).mpr (by linarith [hy.1])⟩

theorem f1a_lp_minimum (delta epsilon : ℝ) (hd : 0 ≤ delta) (he : epsilon ≤ 2) (k : ℕ) :
    IsMinimizer (cutoffLP delta epsilon 0 (f1aHistory k)) Prod.snd (pt 2 0,-2) := by
  refine ⟨(f1a_lp_iff delta epsilon k _).mpr ?_,?_⟩
  · norm_num [pt]
    linarith
  · intro q hq
    obtain ⟨hx,hy,ho,_⟩ := (f1a_lp_iff delta epsilon k q).mp hq
    have hh := mul_nonneg hd hy.1
    change -2 ≤ q.2
    linarith [hx.2]

theorem f1a_lp_unique (delta epsilon : ℝ) (hd : 0 < delta) (he : epsilon ≤ 2) (k : ℕ)
    (q : Point 1 1 × ℝ)
    (hq : IsMinimizer (cutoffLP delta epsilon 0 (f1aHistory k)) Prod.snd q) :
    q = (pt 2 0,-2) := by
  have hm := f1a_lp_minimum delta epsilon hd.le he k
  have hl := hq.2 _ hm.1
  have hr := hm.2 _ hq.1
  have hv : q.2 = -2 := by change q.2 ≤ -2 at hl; change -2 ≤ q.2 at hr; linarith
  obtain ⟨hx,hy,ho,_⟩ := (f1a_lp_iff delta epsilon k q).mp hq.1
  have hprod := mul_nonneg hd.le hy.1
  have hyp : q.1.2 0 = 0 := by
    by_contra hn
    have hp := mul_pos hd (lt_of_le_of_ne hy.1 (Ne.symm hn))
    linarith [hx.2]
  have hxp : q.1.1 0 = 2 := by rw [hyp,hv] at ho; nlinarith [hx.2]
  apply Prod.ext
  · apply Prod.ext
    · funext i; fin_cases i; exact hxp
    · funext i; fin_cases i; exact hyp
  · exact hv

theorem f1a_original_optimum (delta : ℝ) (hd : delta ≤ 1) :
    IsMinimizer ((model delta).feasibleOn Set.univ) (model delta).objective (pt 1 1) := by
  refine ⟨?_,?_⟩
  · rw [source_feasible_iff]
    refine ⟨Set.mem_univ _,fun _ => by norm_num [model,pt],
      (linear_iff delta _).mpr (by norm_num [pt]),fun _ => (1 : ℤ),?_,?_⟩
    · intro i; norm_num [model,Chapter02OAExamples.traceModel]
    · ext i; norm_num [pt]
  · intro p hp
    obtain ⟨_,hg,_,y,hy,hpy⟩ := (source_feasible_iff (model delta) Set.univ p).mp hp
    have hlo : (0 : ℤ) ≤ y 0 := by
      have hh : (0 : ℝ) ≤ (y 0 : ℝ) := by
        simpa [model,Chapter02OAExamples.traceModel] using (hy 0).1
      exact_mod_cast hh
    have hhi : y 0 ≤ (1 : ℤ) := by
      have hh : (y 0 : ℝ) ≤ 1 := by
        simpa [model,Chapter02OAExamples.traceModel] using (hy 0).2
      exact_mod_cast hh
    have hc := hg (0 : Fin 1)
    change (p.1 0)^2-p.2 0 ≤ 0 at hc
    have hy0 : y 0=0 ∨ y 0=1 := by omega
    have hpy0 := congrFun hpy 0
    rcases hy0 with hy0 | hy0
    · have hp0 : p.2 0=0 := by simpa [hy0] using hpy0
      have hx0 : p.1 0=0 := by nlinarith [sq_nonneg (p.1 0)]
      simp only [objective,pt,hp0,hx0]
      linarith
    · have hp1 : p.2 0=1 := by simpa [hy0] using hpy0
      have hx1 : p.1 0≤1 := by nlinarith [sq_nonneg (p.1 0-1)]
      simp only [objective,pt,hp1]
      linarith

def f1bSeed : STSeed 1 1 1 := ⟨pt (1/4) (1/16),Set.univ⟩

theorem f1b_seed_iff (q : Point 1 1) :
    stSeedCuts (model 2) f1bSeed q ↔ q.1 0/2-q.2 0 ≤ 1/16 := by
  constructor
  · intro h
    have hh := h (0 : Fin 1) (Set.mem_univ _)
    change (model 2).g 0 (pt (1/4) (1/16)) +
      (fderiv ℝ ((model 2).g 0) (pt (1/4) (1/16))) (q-pt (1/4) (1/16)) ≤ 0 at hh
    rw [(row_derivative 2 (pt (1/4) (1/16)) 0).fderiv] at hh
    norm_num [model,pt,coordX,coordY,Chapter02KKTExamples.coordY] at hh
    linarith
  · intro h j _
    change (model 2).g j (pt (1/4) (1/16)) +
      (fderiv ℝ ((model 2).g j) (pt (1/4) (1/16))) (q-pt (1/4) (1/16)) ≤ 0
    rw [(row_derivative 2 (pt (1/4) (1/16)) j).fderiv]
    norm_num [model,pt,coordX,coordY,Chapter02KKTExamples.coordY]
    linarith

def f1bOA : ℕ → OAState 1 1
  | 0 => oaInit none
  | k+1 => oaAppend (model 2) (f1bOA k) zeroBatch

theorem f1b_history (k : ℕ) : ∀ b ∈ (f1bOA k).history, b=zeroBatch := by
  induction k with
  | zero => simp [f1bOA,oaInit]
  | succ k ih =>
    intro b hb
    simp only [f1bOA,oaAppend,List.mem_append,List.mem_singleton] at hb
    exact hb.elim (ih b) id

theorem f1b_history_length (k : ℕ) : (f1bOA k).history.length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [f1bOA,oaAppend] using congrArg Nat.succ ih

theorem f1b_incumbent (k : ℕ) :
    (f1bOA k).incumbent=none ∨ (f1bOA k).incumbent=some (pt 0 0) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    right
    rcases ih with h | h <;> simp [f1bOA,oaAppend,zeroBatch,oaBest,h]

theorem f1b_oa_invariant (k : ℕ) : OAInvariant (model 2) (f1bOA k) := by
  induction k with
  | zero => exact oa_init_invariant _ none (by simp)
  | succ k ih => exact oa_append_invariant _ ih _ (zero_batch_valid 2)

def f1bRecord : BBRecord 1 := ⟨bbRootNode (model 2),((-1/8 : ℝ) : WithBot ℝ)⟩

def f1bState (k : ℕ) : STState 1 1 1 := ⟨[f1bSeed],f1bOA k,[f1bRecord],none⟩

theorem f1b_actual_initialization : STInitialize (model 2) none (.inr (f1bState 0)) := by
  have he : f1bState 0 = stInitial (model 2) (pt (1/4) (1/16)) none := by
    norm_num [f1bState,f1bSeed,f1bRecord,f1bOA,stInitial,objective,pt]
  rw [he]
  exact .seeded _ f1b_root_minimum

theorem f1b_lp_minimum (k : ℕ) :
    IsMinimizer (stLP (model 2) [f1bSeed] (f1bOA k).history f1bRecord.node)
      (model 2).objective (pt (1/8) 0) := by
  refine ⟨⟨(linear_iff 2 _).mpr (by norm_num [pt]),?_,?_,?_⟩,?_⟩
  · intro i
    norm_num [f1bRecord,bbRootNode,model,Chapter02OAExamples.traceModel,pt]
  · intro a ha
    have he : a=f1bSeed := List.mem_singleton.mp ha
    rw [he]
    exact (f1b_seed_iff _).mpr (by norm_num [pt])
  · intro b hb
    rw [f1b_history k b hb]
    exact (zero_batch_cuts 2 _).mpr (by norm_num [pt])
  · intro q hq
    have hh := (f1b_seed_iff q).mp (hq.2.2.1 f1bSeed (by simp))
    simp only [objective,pt]
    linarith

theorem f1b_competitive (k : ℕ) :
    oaCompetitive (model 2) 0 (f1bOA k) (pt (1/8) 0) := by
  intro u hu
  rcases f1b_incumbent k with h | h
  · rw [h] at hu; cases hu
  · rw [h] at hu
    cases Option.some.inj hu
    norm_num [objective,pt]

theorem f1b_raised_record : stRaised (model 2) f1bRecord (pt (1/8) 0) = f1bRecord := by
  norm_num [stRaised,f1bRecord,objective,pt]

theorem f1b_actual_process (k : ℕ) : STProcess (model 2) (f1bState k) (f1bState (k+1)) := by
  refine ⟨⟨[f1bSeed],f1bOA k,[],some f1bRecord⟩,
    STSelect.choose [f1bSeed] (f1bOA k) [] [] f1bRecord,?_⟩
  have h : STResolve (model 2) ⟨[f1bSeed],f1bOA k,[],some f1bRecord⟩
      ⟨[f1bSeed],oaAppend (model 2) (f1bOA k) zeroBatch,
        [stRaised (model 2) f1bRecord (pt (1/8) 0)],none⟩ :=
    .callback (f1b_lp_minimum k) (f1b_competitive k) (zero_batch_valid 2)
      (by ext i; norm_num [pt,zeroBatch,Chapter02.oaIntCast])
  simpa only [f1bState,f1bOA,f1b_raised_record] using h

theorem f1b_actual_trace (k : ℕ) : STTrace (model 2) k (f1bState 0) (f1bState k) := by
  induction k with
  | zero => exact .nil _
  | succ k ih => exact st_trace_append_step _ ih (f1b_actual_process k)

theorem f1b_actual_microtrace (k : ℕ) :
    STMicroTrace (model 2) (2*k) (f1bState 0) (f1bState k) :=
  st_trace_micro _ (f1b_actual_trace k)

theorem f1b_global_bound (k : ℕ) :
    stGlobalBound (model 2) (f1bState k) = bbValue (-1/8) := by
  rcases f1b_incumbent k with h | h <;>
    norm_num [stGlobalBound,stBoundState,stFrontier,f1bState,bbGlobalBound,bbLiveBound,
      bbIncBound,h,f1bRecord,objective,pt,bbValue]

theorem f1b_no_stop (epsilon : ℝ) (he : epsilon<1/8) (k : ℕ) :
    ¬ ∃ out, STStop (model 2) epsilon (f1bState k) out := by
  rintro ⟨out,h⟩
  cases h with
  | infeasible hr hl hi => simp [f1bState] at hl
  | exhausted hr hl hi => simp [f1bState] at hl
  | @gap u lower hr hi hb ht =>
    have hu : u=pt 0 0 := by
      rcases f1b_incumbent k with h | h
      · change (f1bOA k).incumbent=some u at hi
        rw [h] at hi; cases hi
      · exact Option.some.inj (hi.symm.trans h)
    rw [f1b_global_bound] at hb
    have hlow := bb_value_le_value.mp hb
    rw [hu,objective] at ht
    norm_num [pt] at ht
    linarith

theorem f1b_source_cq_actual_nontermination (epsilon : ℝ) (_he0 : 0 ≤ epsilon)
    (he : epsilon<1/8) :
    IsCompact ((model 2).linearRegion ∩ IntegerCylinder (n := 1) (model 2).lo (model 2).hi) ∧
    (∀ j, ConvexOn ℝ Set.univ ((model 2).g j)) ∧
    (∀ j, ContDiff ℝ 2 ((model 2).g j)) ∧
    (∀ p ∈ convexHull ℝ ((model 2).feasibleOn Set.univ), FullMFCQ 2 p) ∧
    ¬ OAFiberSlater (model 2) ∧
    STInitialize (model 2) none (.inr (f1bState 0)) ∧
    (∀ k, STProcess (model 2) (f1bState k) (f1bState (k+1))) ∧
    (∀ k, ¬ ∃ out, STStop (model 2) epsilon (f1bState k) out) :=
  ⟨base_compact 2,rows_convex 2,rows_C2 2,global_cq_on_convex_hull 2,
    fiber_slater_fails 2,f1b_actual_initialization,f1b_actual_process,f1b_no_stop epsilon he⟩

end Chapter02STCQExamples



#print axioms Chapter02STCQExamples.objective
#print axioms Chapter02STCQExamples.linear_iff
#print axioms Chapter02STCQExamples.base_compact
#print axioms Chapter02STCQExamples.rows_convex
#print axioms Chapter02STCQExamples.rows_C2
#print axioms Chapter02STCQExamples.rows_diff
#print axioms Chapter02STCQExamples.row_derivative
#print axioms Chapter02STCQExamples.fixed_zero_minimum
#print axioms Chapter02STCQExamples.zero_batch_valid
#print axioms Chapter02STCQExamples.zero_batch_cuts
#print axioms Chapter02STCQExamples.global_strict_point
#print axioms Chapter02STCQExamples.full_mfcq_everywhere
#print axioms Chapter02STCQExamples.fiber_slater_fails
#print axioms Chapter02STCQExamples.zero_fiber_stationarity_impossible
#print axioms Chapter02STCQExamples.f1b_root_minimum
#print axioms Chapter02STCQExamples.objective_C2
#print axioms Chapter02STCQExamples.fixed_zero_fiber_iff
#print axioms Chapter02STCQExamples.zero_fiber_no_kkt
#print axioms Chapter02STCQExamples.no_kkt_any_zero_fiber_point
#print axioms Chapter02STCQExamples.global_cq_on_convex_hull
#print axioms Chapter02STCQExamples.objective_tangent
#print axioms Chapter02STCQExamples.f1a_history_succ
#print axioms Chapter02STCQExamples.f1a_history_valid
#print axioms Chapter02STCQExamples.f1a_lp_iff
#print axioms Chapter02STCQExamples.f1a_lp_minimum
#print axioms Chapter02STCQExamples.f1a_lp_unique
#print axioms Chapter02STCQExamples.f1a_original_optimum
#print axioms Chapter02STCQExamples.f1b_seed_iff
#print axioms Chapter02STCQExamples.f1b_history
#print axioms Chapter02STCQExamples.f1b_history_length
#print axioms Chapter02STCQExamples.f1b_incumbent
#print axioms Chapter02STCQExamples.f1b_oa_invariant
#print axioms Chapter02STCQExamples.f1b_actual_initialization
#print axioms Chapter02STCQExamples.f1b_lp_minimum
#print axioms Chapter02STCQExamples.f1b_competitive
#print axioms Chapter02STCQExamples.f1b_raised_record
#print axioms Chapter02STCQExamples.f1b_actual_process
#print axioms Chapter02STCQExamples.f1b_actual_trace
#print axioms Chapter02STCQExamples.f1b_actual_microtrace
#print axioms Chapter02STCQExamples.f1b_global_bound
#print axioms Chapter02STCQExamples.f1b_no_stop
#print axioms Chapter02STCQExamples.f1b_source_cq_actual_nontermination
