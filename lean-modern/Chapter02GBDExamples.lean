module

public import Chapter02OAExamples
public import Chapter02GBDState
public import Chapter02GBDDriver

@[expose] public section

/-! Concrete controls for the literal projected GBD procedure. Source-derived
multiplier existence is separate from explicitly selected multiplier controls.
These are candidates until the independent frozen review records acceptance. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02Examples
namespace Chapter02GBDExamples

def pt (x y : ℝ) : Point 1 1 := (fun _ => x, fun _ => y)
def iy (y : ℤ) : IntVector 1 := fun _ => y

def eqModel : ModelData 1 1 0 2 where
  g := Fin.elim0
  A := fun row _ => if row = 0 then 1 else -1
  B := fun row _ => if row = 0 then -1 else 1
  rhs := fun _ => 0
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

theorem eq_objective (p : Point 1 1) : eqModel.objective p = p.1 0 := by
  simp [eqModel, ModelData.objective, LinearForm, Fin.sum_univ_one]

theorem eq_linear_iff (p : Point 1 1) : p ∈ eqModel.linearRegion ↔ p.1 0 = p.2 0 := by
  simp [eqModel, ModelData.linearRegion, LinearForm, Fin.sum_univ_one, Fin.forall_fin_succ]
  constructor
  · intro h
    linarith [h.1,h.2]
  · intro h
    constructor <;> linarith

theorem binary_box_cases (y : IntVector 1)
    (hy : y ∈ IntegerBox eqModel.lo eqModel.hi) : y = iy 0 ∨ y = iy 1 := by
  have hb : (0 : ℝ) ≤ (y 0 : ℝ) ∧ (y 0 : ℝ) ≤ 1 := hy 0
  have h0 : (0 : ℤ) ≤ y 0 := by exact_mod_cast hb.1
  have h1 : y 0 ≤ (1 : ℤ) := by exact_mod_cast hb.2
  have he : y 0 = 0 ∨ y 0 = 1 := by omega
  rcases he with h | h
  · left
    funext i
    fin_cases i
    exact h
  · right
    funext i
    fin_cases i
    exact h

theorem binary_zero_mem : iy 0 ∈ IntegerBox eqModel.lo eqModel.hi := by
  intro i
  norm_num [eqModel,iy]

theorem binary_one_mem : iy 1 ∈ IntegerBox eqModel.lo eqModel.hi := by
  intro i
  norm_num [eqModel,iy]

theorem cast_iy (z : ℤ) : Chapter02.oaIntCast (iy z) = fun _ => (z : ℝ) := rfl

theorem eq_base_compact :
    IsCompact (eqModel.linearRegion ∩ IntegerCylinder (n := 1) eqModel.lo eqModel.hi) := by
  have hs : eqModel.linearRegion ∩ IntegerCylinder (n := 1) eqModel.lo eqModel.hi ⊆
      ({pt 0 0,pt 1 1} : Set (Point 1 1)) := by
    rintro p ⟨hL,y,hy,hpy⟩
    have hx := (eq_linear_iff p).mp hL
    rcases binary_box_cases y hy with rfl | rfl
    · have hp : p = pt 0 0 := by
        apply Prod.ext <;> funext i <;> fin_cases i
        · have hh := congrFun hpy 0
          norm_num [iy] at hh
          simpa [pt,hh] using hx
        · simpa [pt,iy] using congrFun hpy 0
      simp [hp]
    · have hp : p = pt 1 1 := by
        apply Prod.ext <;> funext i <;> fin_cases i
        · have hh := congrFun hpy 0
          norm_num [iy] at hh
          simpa [pt,hh] using hx
        · simpa [pt,iy] using congrFun hpy 0
      simp [hp]
  exact ((Set.finite_singleton (pt 1 1)).insert (pt 0 0)).subset hs |>.isCompact

theorem eq_convex : ∀j, ConvexOn ℝ Set.univ (eqModel.g j) := fun j => Fin.elim0 j
theorem eq_diff : ∀j, Differentiable ℝ (eqModel.g j) := fun j => Fin.elim0 j

theorem eq_fixed_minimum (y : ℝ) :
    IsMinimizer (eqModel.fixedNonlinearFiber (fun _ => y)) eqModel.objective (pt y y) := by
  refine ⟨⟨⟨(eq_linear_iff _).mpr rfl,rfl⟩,fun j => Fin.elim0 j⟩,?_⟩
  intro q hq
  have hx := (eq_linear_iff q).mp hq.1.1
  have hy := congrFun hq.1.2 0
  rw [eq_objective,eq_objective]
  change y ≤ q.1 0
  linarith

theorem eq_slater : OAFiberSlater eqModel := by
  intro y hy hn
  exact ⟨(Chapter02.oaIntCast y,Chapter02.oaIntCast y),
    ⟨(eq_linear_iff _).mpr rfl,rfl⟩,fun j => Fin.elim0 j⟩

theorem eq_floor : IsLowerBound (eqModel.feasibleOn Set.univ) eqModel.objective 0 := by
  intro p hp
  have hf := (source_feasible_iff _ _ _).mp hp
  have hx := (eq_linear_iff p).mp hf.2.2.1
  obtain ⟨y,hy,hpy⟩ := hf.2.2.2
  rw [eq_objective,hx,hpy]
  exact (hy 0).1

theorem eq_multipliers_exist (y : ℝ) :
    ∃lambda mu, FixedNLPKKT eqModel (pt y y)
      (fun j => fderiv ℝ (eqModel.g j) (pt y y)) lambda mu := by
  exact exists_fixedNLPKKT eqModel (pt y y) _ eq_convex (fun j => Fin.elim0 j) (eq_fixed_minimum y)
    ⟨pt y y,⟨(eq_linear_iff _).mpr rfl,rfl⟩,fun j => Fin.elim0 j⟩

theorem eq_cut_identity (a : ℝ) {D : Fin 0 → Point 1 1 →L[ℝ] ℝ}
    {lambda : Fin 0 → ℝ} {mu : Fin 2 → ℝ}
    (h : FixedNLPKKT eqModel (pt a a) D lambda mu) (y : RealVector 1) :
    anchoredOptimalityCut eqModel (pt a a) D lambda mu y = y 0 := by
  have hs := h.stationarity (fun _ => 1)
  norm_num [eqModel,ModelData.objective,LinearForm,Fin.sum_univ_two,Fin.sum_univ_one] at hs
  simp [anchoredOptimalityCut,eqModel,ModelData.objective,LinearForm,pt,
    Fin.sum_univ_two,Fin.sum_univ_one]
  have he : mu 1 = 1+mu 0 := by linarith
  rw [he]
  ring

abbrev linkedModel := Chapter02KKTExamples.linkedModel (1/2)

theorem linked_diff : ∀j, Differentiable ℝ (linkedModel.g j) :=
  fun j => (Chapter02KKTExamples.linked_smooth (1/2) j).differentiable (by norm_num)

theorem linked_zero_fixed :
    IsMinimizer (linkedModel.fixedNonlinearFiber (fun _ => 0)) linkedModel.objective (pt 0 0) := by
  refine ⟨⟨⟨(Chapter02KKTExamples.linked_linear_iff (1/2) _).mpr (by norm_num [pt]),rfl⟩,
    fun _ => by norm_num [linkedModel,Chapter02KKTExamples.linkedModel,pt]⟩,?_⟩
  intro q hq
  have hx := ((Chapter02KKTExamples.linked_linear_iff (1/2) q).mp hq.1.1).1
  simpa only [Chapter02KKTExamples.linked_objective,pt] using hx

theorem linked_one_infeasible : ¬ (linkedModel.fixedNonlinearFiber (fun _ => 1)).Nonempty := by
  rintro ⟨p,hp⟩
  have hx := ((Chapter02KKTExamples.linked_linear_iff (1/2) p).mp hp.1.1).2.2
  have hy : p.2 0 = 1 := congrFun hp.1.2 0
  have hg := hp.2 (0 : Fin 1)
  change (p.1 0)^2-1/2≤0 at hg
  rw [hy] at hx
  nlinarith

theorem linked_slater : OAFiberSlater linkedModel := by
  intro y hy hn
  rcases binary_box_cases y hy with rfl | rfl
  · refine ⟨pt 0 0,⟨(Chapter02KKTExamples.linked_linear_iff (1/2) _).mpr (by norm_num [pt]),?_⟩,?_⟩
    · ext i
      norm_num [Chapter02.oaIntCast,iy,pt]
    · intro j
      norm_num [linkedModel,Chapter02KKTExamples.linkedModel,pt]
  · have he : Chapter02.oaIntCast (iy 1) = (fun _ => 1) := by
      ext i
      norm_num [Chapter02.oaIntCast,iy]
    rw [he] at hn
    exact False.elim (linked_one_infeasible hn)

theorem linked_restoration_minimum :
    IsMinimizer (RestorationPairs (linkedModel.fixedLinearFiber (fun _ => 1)) linkedModel.g)
      Prod.snd (pt 1 1,1/2) := by
  refine ⟨⟨⟨(Chapter02KKTExamples.linked_linear_iff (1/2) _).mpr (by norm_num [pt]),rfl⟩,
    fun _ => by norm_num [linkedModel,Chapter02KKTExamples.linkedModel,pt]⟩,?_⟩
  intro q hq
  have hx := ((Chapter02KKTExamples.linked_linear_iff (1/2) q.1).mp hq.1.1).2.2
  have hy : q.1.2 0 = 1 := congrFun hq.1.2 0
  have hg := hq.2 (0 : Fin 1)
  change (q.1.1 0)^2-1/2≤q.2 at hg
  rw [hy] at hx
  change 1/2≤q.2
  nlinarith

theorem linked_source_multipliers :
    (∃lambda mu, FixedNLPKKT linkedModel (pt 0 0)
      (fun j => fderiv ℝ (linkedModel.g j) (pt 0 0)) lambda mu) ∧
    (∃lambda mu, RestorationKKT linkedModel (pt 1 1) (1/2)
      (fun j => fderiv ℝ (linkedModel.g j) (pt 1 1)) lambda mu) := by
  constructor
  · apply exists_fixedNLPKKT linkedModel (pt 0 0) _
      (Chapter02KKTExamples.linked_convex (1/2))
      (fun j => (linked_diff j _).hasFDerivAt) linked_zero_fixed
    exact ⟨pt 0 0,⟨(Chapter02KKTExamples.linked_linear_iff (1/2) _).mpr (by norm_num [pt]),rfl⟩,
      fun _ => by norm_num [linkedModel,Chapter02KKTExamples.linkedModel,pt]⟩
  · exact exists_restorationKKT linkedModel (pt 1 1) (1/2) _
      (Chapter02KKTExamples.linked_convex (1/2))
      (fun j => (linked_diff j _).hasFDerivAt) linked_restoration_minimum

theorem linked_floor : IsLowerBound (linkedModel.feasibleOn Set.univ) linkedModel.objective 0 := by
  intro p hp
  have hx := ((Chapter02KKTExamples.linked_linear_iff (1/2) p).mp
    ((source_feasible_iff _ _ _).mp hp).2.2.1).1
  simpa only [Chapter02KKTExamples.linked_objective] using hx

def routePoint (y : ℝ) : Point 0 1 := (0,fun _ => y)

def routeModel (bound : ℝ) : ModelData 0 1 1 1 where
  g := fun _ _ => -1
  A := fun _ _ => 0
  B := fun _ _ => 1
  rhs := fun _ => bound
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

theorem route_objective (bound : ℝ) (p : Point 0 1) : (routeModel bound).objective p = 0 := by
  simp [routeModel,ModelData.objective,LinearForm]

theorem route_linear_iff (bound : ℝ) (p : Point 0 1) :
    p ∈ (routeModel bound).linearRegion ↔ p.2 0 ≤ bound := by
  simp [routeModel,ModelData.linearRegion,LinearForm,Fin.sum_univ_one]

theorem route_base_compact (bound : ℝ) :
    IsCompact ((routeModel bound).linearRegion ∩ IntegerCylinder (n := 0)
      (routeModel bound).lo (routeModel bound).hi) := by
  have hs : (routeModel bound).linearRegion ∩ IntegerCylinder (n := 0)
      (routeModel bound).lo (routeModel bound).hi ⊆
      ({routePoint 0,routePoint 1} : Set (Point 0 1)) := by
    rintro p ⟨hL,y,hy,hpy⟩
    rcases binary_box_cases y hy with rfl | rfl
    · have hp : p = routePoint 0 := by
        apply Prod.ext
        · funext i
          exact Fin.elim0 i
        · funext i
          simpa [routePoint,iy] using congrFun hpy i
      simp [hp]
    · have hp : p = routePoint 1 := by
        apply Prod.ext
        · funext i
          exact Fin.elim0 i
        · funext i
          simpa [routePoint,iy] using congrFun hpy i
      simp [hp]
  exact ((Set.finite_singleton (routePoint 1)).insert (routePoint 0)).subset hs |>.isCompact

theorem route_convex (bound : ℝ) : ∀j,ConvexOn ℝ Set.univ ((routeModel bound).g j) :=
  fun _ => convexOn_const _ convex_univ

theorem route_diff (bound : ℝ) : ∀j,Differentiable ℝ ((routeModel bound).g j) :=
  fun _ => differentiable_const _

theorem route_slater (bound : ℝ) : OAFiberSlater (routeModel bound) := by
  intro y hy ⟨p,hp⟩
  exact ⟨p,hp.1,fun _ => by norm_num [routeModel]⟩

theorem route_fixed_minimum (bound y : ℝ) (hy : y ≤ bound) :
    IsMinimizer ((routeModel bound).fixedNonlinearFiber (fun _ => y))
      (routeModel bound).objective (routePoint y) := by
  refine ⟨⟨⟨(route_linear_iff _ _).mpr hy,rfl⟩,
    fun _ => by norm_num [routeModel]⟩,?_⟩
  intro q hq
  simp [route_objective]

theorem route_empty_linear (bound y : ℝ) (hy : bound < y) :
    ¬ ((routeModel bound).fixedLinearFiber (fun _ => y)).Nonempty := by
  rintro ⟨p,hp⟩
  have hl := (route_linear_iff bound p).mp hp.1
  have hpy : p.2 0 = y := congrFun hp.2 0
  linarith

theorem route_floor (bound : ℝ) :
    IsLowerBound ((routeModel bound).feasibleOn Set.univ) (routeModel bound).objective 0 := by
  intro p hp
  simp [route_objective]

theorem route_source_multipliers (bound y : ℝ) (hy : y ≤ bound) :
    ∃lambda mu,FixedNLPKKT (routeModel bound) (routePoint y)
      (fun j => fderiv ℝ ((routeModel bound).g j) (routePoint y)) lambda mu := by
  apply exists_fixedNLPKKT (routeModel bound) (routePoint y) _ (route_convex bound)
    (fun j => (route_diff bound j _).hasFDerivAt) (route_fixed_minimum bound y hy)
  exact ⟨routePoint y,⟨(route_linear_iff _ _).mpr hy,rfl⟩,
    fun _ => by norm_num [routeModel]⟩

theorem linked_canonical_derivative (p : Point 1 1) (j : Fin 1) :
    fderiv ℝ (linkedModel.g j) p = (2*p.1 0) • coordX :=
  (Chapter02KKTExamples.linked_derivative (1/2) p j).fderiv

theorem linked_restoration_cut_identity {lambda : Fin 1 → ℝ} {mu : Fin 3 → ℝ}
    (h : RestorationKKT linkedModel (pt 1 1) (1/2)
      (fun j => fderiv ℝ (linkedModel.g j) (pt 1 1)) lambda mu) (y : RealVector 1) :
    anchoredFeasibilityCut linkedModel (pt 1 1)
      (fun j => fderiv ℝ (linkedModel.g j) (pt 1 1)) lambda mu y = 2*y 0-3/2 := by
  have hlam : lambda 0 = 1 := by simpa [Fin.sum_univ_one] using h.normalization
  have hm0 : mu 0 = 0 := by
    have hc := h.linear_complementarity 0
    norm_num [linearResidual,linkedModel,Chapter02KKTExamples.linkedModel,pt,LinearForm,
      Fin.sum_univ_one,Fin.ext_iff] at hc
    exact hc
  have hm1 : mu 1 = 0 := by
    have hc := h.linear_complementarity 1
    norm_num [linearResidual,linkedModel,Chapter02KKTExamples.linkedModel,pt,LinearForm,
      Fin.sum_univ_one,Fin.ext_iff] at hc
    exact hc
  have hs := h.stationarity (fun _ => 1)
  have hD : (fun j => fderiv ℝ (linkedModel.g j) (pt 1 1)) = fun _ => (2 : ℝ) • coordX := by
    funext j
    simpa [pt] using linked_canonical_derivative (pt 1 1) j
  change (∑ j, lambda j * ((fun j => fderiv ℝ (linkedModel.g j) (pt 1 1)) j) ((fun _ => 1),0)) +
    ∑ row,mu row*LinearForm (linkedModel.A row) (linkedModel.B row) ((fun _ => 1),0) = 0 at hs
  rw [hD] at hs
  simp only [Fin.sum_univ_one,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
  norm_num [linkedModel,Chapter02KKTExamples.linkedModel,LinearForm,Fin.sum_univ_one,
    coordX,smul_eq_mul,Fin.ext_iff,hlam,hm0,hm1] at hs
  have hm2 : mu 2 = 2 := by linarith
  unfold anchoredFeasibilityCut
  rw [hD]
  simp only [Fin.sum_univ_one,Fin.sum_univ_three]
  simp [linkedModel,Chapter02KKTExamples.linkedModel,hlam,hm0,hm1,hm2,pt,LinearForm,
    coordX,Fin.sum_univ_one,Fin.ext_iff]
  ring

theorem linked_optimal_cut_identity {lambda : Fin 1 → ℝ} {mu : Fin 3 → ℝ}
    (h : FixedNLPKKT linkedModel (pt 0 0)
      (fun j => fderiv ℝ (linkedModel.g j) (pt 0 0)) lambda mu) (y : RealVector 1) :
    anchoredOptimalityCut linkedModel (pt 0 0)
      (fun j => fderiv ℝ (linkedModel.g j) (pt 0 0)) lambda mu y = mu 2 * y 0 := by
  have hm1 : mu 1 = 0 := by
    have hc := h.linear_complementarity 1
    norm_num [linearResidual,linkedModel,Chapter02KKTExamples.linkedModel,pt,LinearForm,
      Fin.sum_univ_one,Fin.ext_iff] at hc
    linarith
  unfold anchoredOptimalityCut
  have hD : (fun j => fderiv ℝ (linkedModel.g j) (pt 0 0)) = fun _ => (0 : Point 1 1 →L[ℝ] ℝ) := by
    funext j
    simpa [pt] using linked_canonical_derivative (pt 0 0) j
  rw [hD]
  simp [linkedModel,
    Chapter02KKTExamples.linkedModel,hm1,pt,ModelData.objective,LinearForm,coordX,Fin.sum_univ_succ]

def linkedMu (t : ℝ) (row : Fin 3) : ℝ :=
  if row = 0 then 1-t else if row = 2 then t else 0

/-- An explicitly selected family supplements, rather than replaces, the
source-derived multiplier existence theorem. -/
theorem linked_selected_kkt (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    FixedNLPKKT linkedModel (pt 0 0)
      (fun j => fderiv ℝ (linkedModel.g j) (pt 0 0)) (fun _ => 0) (linkedMu t) := by
  refine ⟨(Chapter02KKTExamples.linked_linear_iff (1/2) _).mpr (by norm_num [pt]),
    fun _ => by norm_num [linkedModel,Chapter02KKTExamples.linkedModel,pt],
    fun j => (linked_diff j _).hasFDerivAt,fun _ => le_rfl,?_,?_,?_,?_⟩
  · intro row
    fin_cases row <;> simp [linkedMu] <;> linarith
  · intro j
    simp
  · intro row
    fin_cases row <;> norm_num [linkedMu,linearResidual,linkedModel,
      Chapter02KKTExamples.linkedModel,pt,LinearForm,Fin.sum_univ_one,Fin.ext_iff]
  · intro dx
    simp [linkedMu,linkedModel,Chapter02KKTExamples.linkedModel,ModelData.objective,
      LinearForm,Fin.sum_univ_succ]
    ring

def eqLambda (a : ℝ) : Fin 0 → ℝ := Classical.choose (eq_multipliers_exist a)
def eqMu (a : ℝ) : Fin 2 → ℝ := Classical.choose (Classical.choose_spec (eq_multipliers_exist a))
theorem eq_chosen_kkt (a : ℝ) : FixedNLPKKT eqModel (pt a a)
    (fun j => fderiv ℝ (eqModel.g j) (pt a a)) (eqLambda a) (eqMu a) :=
  Classical.choose_spec (Classical.choose_spec (eq_multipliers_exist a))

def eqBatch (a : ℤ) : GBDBatch 1 1 0 2 :=
  ⟨iy a,.optimal (pt (a:ℝ) (a:ℝ)) (eqLambda (a:ℝ)) (eqMu (a:ℝ))⟩

theorem eq_batch_valid (a : ℤ) (ha : iy a ∈ IntegerBox eqModel.lo eqModel.hi) :
    gbdBatchValid eqModel (eqBatch a) := by
  refine ⟨ha,?_,?_,eq_chosen_kkt (a:ℝ)⟩
  · rfl
  · change IsMinimizer (eqModel.fixedNonlinearFiber (Chapter02.oaIntCast (iy a)))
      eqModel.objective (pt (a:ℝ) (a:ℝ))
    rw [cast_iy]
    exact eq_fixed_minimum (a:ℝ)

theorem eq_batch_constraint (a : ℤ) (z : IntVector 1 × ℝ) :
    gbdBatchConstraint eqModel (eqBatch a) z ↔ (z.1 0 : ℝ) ≤ z.2 := by
  change anchoredOptimalityCut eqModel (pt (a:ℝ) (a:ℝ)) _ _ _ (Chapter02.oaIntCast z.1) ≤ z.2 ↔ _
  unfold gbdBatchDerivative
  rw [eq_cut_identity (a:ℝ) (eq_chosen_kkt (a:ℝ))]
  rfl

theorem eq_initial_master (a : ℤ) (ha : iy a ∈ IntegerBox eqModel.lo eqModel.hi) (floor : ℝ) :
    IsMinimizer (gbdMaster eqModel floor []) Prod.snd (iy a,floor) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨ha,le_rfl,by simp⟩,?_⟩
  intro q hq
  exact ((gbd_master_mem_iff _ _ _ _).mp hq).2.1

theorem eq_later_master (H : List (GBDBatch 1 1 0 2))
    (hH : ∀b∈H, ∃a,b=eqBatch a) :
    IsMinimizer (gbdMaster eqModel 0 H) Prod.snd (iy 0,0) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨binary_zero_mem,le_rfl,?_⟩,?_⟩
  · intro b hb
    obtain ⟨a,rfl⟩ := hH b hb
    exact (eq_batch_constraint a _).mpr (by norm_num [iy])
  · intro q hq
    exact ((gbd_master_mem_iff _ _ _ _).mp hq).2.1

def eqS0 : GBDState 1 1 0 2 := gbdInit none
def eqS1 : GBDState 1 1 0 2 := gbdAppend eqModel eqS0 (eqBatch 1)
def eqS2 : GBDState 1 1 0 2 := gbdAppend eqModel eqS1 (eqBatch 0)
def eqShort : GBDState 1 1 0 2 := gbdAppend eqModel eqS0 (eqBatch 0)

theorem eq_first_continue (epsilon : ℝ) : GBDContinue eqModel 0 epsilon eqS0 eqS1 := by
  exact GBDContinue.step (eq_initial_master 1 binary_one_mem 0)
    (by simp [gbdCompetitive,eqS0,gbdInit]) (eq_batch_valid 1 binary_one_mem) rfl

theorem eq_second_continue : GBDContinue eqModel 0 0 eqS1 eqS2 := by
  apply GBDContinue.step (z := (iy 0,0)) (b := eqBatch 0)
  · exact eq_later_master [eqBatch 1] (by simp)
  · intro u hu
    have he : u = pt 1 1 := by
      simpa [eqS1,eqS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,eqBatch,oaBest] using
        (Option.some.inj hu).symm
    rw [he]
    norm_num [eq_objective,pt]
  · exact eq_batch_valid 0 binary_zero_mem
  · rfl

theorem eq_final_stop : GBDStop eqModel 0 0 eqS2 (.solution (pt 0 0)) := by
  apply GBDStop.gap (z := (iy 0,0))
  · exact eq_later_master [eqBatch 1,eqBatch 0] (by simp)
  · norm_num [eqS2,eqS1,eqS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,eqBatch,oaBest,eq_objective,pt]
  · norm_num [eq_objective,pt]

theorem eq_short_continue : GBDContinue eqModel 0 0 eqS0 eqShort :=
  GBDContinue.step (eq_initial_master 0 binary_zero_mem 0)
    (by simp [gbdCompetitive,eqS0,gbdInit]) (eq_batch_valid 0 binary_zero_mem) rfl

theorem eq_short_stop : GBDStop eqModel 0 0 eqShort (.solution (pt 0 0)) := by
  apply GBDStop.gap (z := (iy 0,0))
  · exact eq_later_master [eqBatch 0] (by simp)
  · norm_num [eqShort,eqS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,eqBatch,oaBest,pt]
  · norm_num [eq_objective,pt]

theorem eq_feasible (a : ℤ) (ha : iy a ∈ IntegerBox eqModel.lo eqModel.hi) :
    pt (a:ℝ) (a:ℝ) ∈ eqModel.feasibleOn Set.univ := by
  apply (source_feasible_iff _ _ _).mpr
  exact ⟨Set.mem_univ _,fun j => Fin.elim0 j,(eq_linear_iff _).mpr rfl,iy a,ha,rfl⟩

theorem zero_rows_two_distinct_traces :
    IsCompact (eqModel.linearRegion ∩ IntegerCylinder (n := 1) eqModel.lo eqModel.hi) ∧
    (∀j,ConvexOn ℝ Set.univ (eqModel.g j)) ∧
    (∀j,Differentiable ℝ (eqModel.g j)) ∧ OAFiberSlater eqModel ∧ GBDFloorValid eqModel 0 ∧
    GBDInvariant eqModel eqS0 ∧
    GBDContinue eqModel 0 0 eqS0 eqS1 ∧ GBDContinue eqModel 0 0 eqS1 eqS2 ∧
    GBDStop eqModel 0 0 eqS2 (.solution (pt 0 0)) ∧
    GBDContinue eqModel 0 0 eqS0 eqShort ∧ GBDStop eqModel 0 0 eqShort (.solution (pt 0 0)) ∧
    eqS2.history.length=2 ∧ eqShort.history.length=1 := by
  exact ⟨eq_base_compact,eq_convex,eq_diff,eq_slater,eq_floor,
    gbd_init_invariant _ none (by simp),eq_first_continue 0,eq_second_continue,eq_final_stop,
    eq_short_continue,eq_short_stop,rfl,rfl⟩

theorem eq_positive_tolerance_nonoptimal :
    GBDContinue eqModel 0 1 eqS0 eqS1 ∧ GBDStop eqModel 0 1 eqS1 (.solution (pt 1 1)) ∧
    ¬ IsMinimizer (eqModel.feasibleOn Set.univ) eqModel.objective (pt 1 1) := by
  refine ⟨eq_first_continue 1,?_,?_⟩
  · apply GBDStop.gap (z := (iy 0,0))
    · exact eq_later_master [eqBatch 1] (by simp)
    · norm_num [eqS1,eqS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,eqBatch,oaBest,pt]
    · norm_num [eq_objective,pt]
  · intro hm
    have hf : pt 0 0 ∈ eqModel.feasibleOn Set.univ := by simpa using eq_feasible 0 binary_zero_mem
    have hh := hm.2 _ hf
    norm_num [eq_objective,pt] at hh

def eqWarm : GBDState 1 1 0 2 := gbdInit (some (pt 1 1))

theorem invalid_floor_false_return :
    GBDInvariant eqModel eqWarm ∧ ¬ GBDFloorValid eqModel 1 ∧
    (iy 0,0) ∉ gbdMaster eqModel 1 [] ∧
    GBDStop eqModel 1 0 eqWarm (.solution (pt 1 1)) ∧
    ¬ GBDReturnCertificate eqModel 0 (.solution (pt 1 1)) := by
  have hf0 : pt 0 0 ∈ eqModel.feasibleOn Set.univ := by simpa using eq_feasible 0 binary_zero_mem
  have hf1 : pt 1 1 ∈ eqModel.feasibleOn Set.univ := by simpa using eq_feasible 1 binary_one_mem
  refine ⟨gbd_init_invariant _ _ ?_,?_,?_,?_,?_⟩
  · intro u hu
    cases Option.some.inj hu
    exact hf1
  · intro h
    have hh := h _ hf0
    norm_num [eq_objective,pt] at hh
  · simp [gbd_master_mem_iff]
  · exact GBDStop.gap (eq_initial_master 0 binary_zero_mem 1) rfl (by norm_num [eq_objective,pt])
  · intro h
    have ho := gbd_certificate_zero_optimal eqModel h
    have hh := ho.2 _ hf0
    norm_num [eq_objective,pt] at hh

#print axioms zero_rows_two_distinct_traces
#print axioms eq_positive_tolerance_nonoptimal
#print axioms invalid_floor_false_return

def eqRepeatState : ℕ → GBDState 1 1 0 2
  | 0 => gbdInit (some (pt 0 0))
  | k+1 => gbdAppend eqModel (eqRepeatState k) (eqBatch 0)

theorem eq_repeat_history (k : ℕ) : ∀b∈(eqRepeatState k).history,∃a,b=eqBatch a := by
  induction k with
  | zero => simp [eqRepeatState,gbdInit]
  | succ k ih =>
    intro b hb
    simp only [eqRepeatState,gbdAppend,List.mem_append,List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact ih b hb
    · exact ⟨0,rfl⟩

theorem eq_repeat_incumbent (k : ℕ) : (eqRepeatState k).incumbent = some (pt 0 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [eqRepeatState,gbdAppend,gbdBatchOptimalAnchor,eqBatch,oaBest,ih,eq_objective,pt]

theorem eq_repeat_invariant (k : ℕ) : GBDInvariant eqModel (eqRepeatState k) := by
  induction k with
  | zero =>
    apply gbd_init_invariant
    intro u hu
    cases Option.some.inj hu
    simpa using eq_feasible 0 binary_zero_mem
  | succ k ih => exact gbd_append_invariant _ ih _ (eq_batch_valid 0 binary_zero_mem)

theorem negative_epsilon_repeat (k : ℕ) :
    GBDContinue eqModel 0 (-1) (eqRepeatState k) (eqRepeatState (k+1)) := by
  apply GBDContinue.step (eq_later_master _ (eq_repeat_history k))
  · intro u hu
    rw [eq_repeat_incumbent] at hu
    cases Option.some.inj hu
    norm_num [eq_objective,pt]
  · exact eq_batch_valid 0 binary_zero_mem
  · rfl

def StrictGBDContinue {n m l r : ℕ} (d : ModelData n m l r) (floor : ℝ)
    (s t : GBDState n m l r) : Prop :=
  ∃z b, IsMinimizer (gbdMaster d floor s.history) Prod.snd z ∧
    (∀u,s.incumbent=some u → ¬d.objective u<z.2) ∧
    gbdBatchValid d b ∧ z.1=b.integer ∧ t=gbdAppend d s b

theorem strict_guard_repeat (k : ℕ) : StrictGBDContinue eqModel 0 (eqRepeatState k) (eqRepeatState (k+1)) := by
  refine ⟨(iy 0,0),eqBatch 0,eq_later_master _ (eq_repeat_history k),?_,
    eq_batch_valid 0 binary_zero_mem,rfl,rfl⟩
  intro u hu
  rw [eq_repeat_incumbent] at hu
  cases Option.some.inj hu
  norm_num [eq_objective,pt]

theorem correct_guard_stops_repeat (k : ℕ) :
    GBDStop eqModel 0 0 (eqRepeatState k) (.solution (pt 0 0)) :=
  GBDStop.gap (eq_later_master _ (eq_repeat_history k)) (eq_repeat_incumbent k)
    (by norm_num [eq_objective,pt])

theorem guard_and_negative_tolerance_controls :
    IsCompact (eqModel.linearRegion ∩ IntegerCylinder (n := 1) eqModel.lo eqModel.hi) ∧
    (∀j,ConvexOn ℝ Set.univ (eqModel.g j)) ∧
    (∀j,Differentiable ℝ (eqModel.g j)) ∧ OAFiberSlater eqModel ∧ GBDFloorValid eqModel 0 ∧
    (∀k,GBDInvariant eqModel (eqRepeatState k)) ∧
    (∀k,GBDContinue eqModel 0 (-1) (eqRepeatState k) (eqRepeatState (k+1))) ∧
    (∀k,StrictGBDContinue eqModel 0 (eqRepeatState k) (eqRepeatState (k+1))) ∧
    (∀k,GBDStop eqModel 0 0 (eqRepeatState k) (.solution (pt 0 0))) :=
  ⟨eq_base_compact,eq_convex,eq_diff,eq_slater,eq_floor,eq_repeat_invariant,
    negative_epsilon_repeat,strict_guard_repeat,correct_guard_stops_repeat⟩

def eqDeleted : GBDState 1 1 0 2 := ⟨[],some (pt 1 1)⟩

theorem deleted_optimality_history_repeats :
    (iy 1,0) ∉ gbdMaster eqModel 0 eqS1.history ∧
    GBDContinue eqModel 0 0 eqDeleted (gbdAppend eqModel eqDeleted (eqBatch 1)) ∧
    eqDeleted.incumbent=eqS1.incumbent := by
  refine ⟨?_,?_,by norm_num [eqDeleted,eqS1,eqS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,eqBatch,oaBest,pt]⟩
  · intro h
    have hc := ((gbd_master_mem_iff _ _ _ _).mp h).2.2 (eqBatch 1) (by simp [eqS1,eqS0,gbdAppend,gbdInit])
    have hh := (eq_batch_constraint 1 _).mp hc
    norm_num [iy] at hh
  · apply GBDContinue.step (eq_initial_master 1 binary_one_mem 0)
    · intro u hu
      cases Option.some.inj hu
      norm_num [eq_objective,pt]
    · exact eq_batch_valid 1 binary_one_mem
    · rfl

def linkedRestLambda : Fin 1 → ℝ := Classical.choose linked_source_multipliers.2
def linkedRestMu : Fin 3 → ℝ := Classical.choose (Classical.choose_spec linked_source_multipliers.2)
theorem linked_chosen_restoration : RestorationKKT linkedModel (pt 1 1) (1/2)
    (fun j => fderiv ℝ (linkedModel.g j) (pt 1 1)) linkedRestLambda linkedRestMu :=
  Classical.choose_spec (Classical.choose_spec linked_source_multipliers.2)
def linkedOptLambda : Fin 1 → ℝ := Classical.choose linked_source_multipliers.1
def linkedOptMu : Fin 3 → ℝ := Classical.choose (Classical.choose_spec linked_source_multipliers.1)
theorem linked_chosen_optimal : FixedNLPKKT linkedModel (pt 0 0)
    (fun j => fderiv ℝ (linkedModel.g j) (pt 0 0)) linkedOptLambda linkedOptMu :=
  Classical.choose_spec (Classical.choose_spec linked_source_multipliers.1)

def linkedRest : GBDBatch 1 1 1 3 :=
  ⟨iy 1,.restoration (pt 1 1) (1/2) linkedRestLambda linkedRestMu⟩
def linkedOpt : GBDBatch 1 1 1 3 :=
  ⟨iy 0,.optimal (pt 0 0) linkedOptLambda linkedOptMu⟩
def linkedSelected (t : ℝ) : GBDBatch 1 1 1 3 :=
  ⟨iy 0,.optimal (pt 0 0) (fun _ => 0) (linkedMu t)⟩

theorem linked_rest_valid : gbdBatchValid linkedModel linkedRest := by
  have hc : Chapter02.oaIntCast (iy 1) = (fun _ => 1) := by ext i; norm_num [Chapter02.oaIntCast,iy]
  refine ⟨binary_one_mem,?_,?_,?_,linked_chosen_restoration⟩
  · ext i
    norm_num [linkedRest,Chapter02.oaIntCast,iy,pt]
  · change ¬ (linkedModel.fixedNonlinearFiber (Chapter02.oaIntCast (iy 1))).Nonempty
    rw [hc]
    exact linked_one_infeasible
  · change IsMinimizer (RestorationPairs (linkedModel.fixedLinearFiber (Chapter02.oaIntCast (iy 1))) linkedModel.g)
      Prod.snd (pt 1 1,1/2)
    rw [hc]
    exact linked_restoration_minimum

theorem linked_opt_valid : gbdBatchValid linkedModel linkedOpt := by
  have hc : Chapter02.oaIntCast (iy 0) = (fun _ => 0) := by ext i; norm_num [Chapter02.oaIntCast,iy]
  refine ⟨binary_zero_mem,?_,?_,linked_chosen_optimal⟩
  · ext i
    norm_num [linkedOpt,Chapter02.oaIntCast,iy,pt]
  · change IsMinimizer (linkedModel.fixedNonlinearFiber (Chapter02.oaIntCast (iy 0))) linkedModel.objective (pt 0 0)
    rw [hc]
    exact linked_zero_fixed

theorem linked_selected_valid (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    gbdBatchValid linkedModel (linkedSelected t) := by
  have hc : Chapter02.oaIntCast (iy 0) = (fun _ => 0) := by ext i; norm_num [Chapter02.oaIntCast,iy]
  refine ⟨binary_zero_mem,?_,?_,linked_selected_kkt t ht0 ht1⟩
  · ext i
    norm_num [linkedSelected,Chapter02.oaIntCast,iy,pt]
  · change IsMinimizer (linkedModel.fixedNonlinearFiber (Chapter02.oaIntCast (iy 0))) linkedModel.objective (pt 0 0)
    rw [hc]
    exact linked_zero_fixed

theorem linked_rest_constraint (z : IntVector 1 × ℝ) :
    gbdBatchConstraint linkedModel linkedRest z ↔ 2*(z.1 0 : ℝ)-3/2≤0 := by
  change anchoredFeasibilityCut linkedModel (pt 1 1) _ _ _ (Chapter02.oaIntCast z.1)≤0 ↔ _
  unfold gbdBatchDerivative
  rw [linked_restoration_cut_identity linked_chosen_restoration]
  rfl

theorem linked_opt_constraint (z : IntVector 1 × ℝ) :
    gbdBatchConstraint linkedModel linkedOpt z ↔ linkedOptMu 2*(z.1 0 : ℝ)≤z.2 := by
  change anchoredOptimalityCut linkedModel (pt 0 0) _ _ _ (Chapter02.oaIntCast z.1)≤z.2 ↔ _
  unfold gbdBatchDerivative
  rw [linked_optimal_cut_identity linked_chosen_optimal]
  rfl

theorem linked_selected_constraint (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) (z : IntVector 1 × ℝ) :
    gbdBatchConstraint linkedModel (linkedSelected t) z ↔ t*(z.1 0 : ℝ)≤z.2 := by
  change anchoredOptimalityCut linkedModel (pt 0 0) _ _ _ (Chapter02.oaIntCast z.1)≤z.2 ↔ _
  unfold gbdBatchDerivative
  rw [linked_optimal_cut_identity (linked_selected_kkt t ht0 ht1)]
  norm_num [linkedMu,Fin.ext_iff,Chapter02.oaIntCast]

#print axioms guard_and_negative_tolerance_controls
#print axioms deleted_optimality_history_repeats

theorem linked_initial_master (a : ℤ) (ha : iy a ∈ IntegerBox linkedModel.lo linkedModel.hi) :
    IsMinimizer (gbdMaster linkedModel 0 []) Prod.snd (iy a,0) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨ha,le_rfl,by simp⟩,?_⟩
  intro q hq
  exact ((gbd_master_mem_iff _ _ _ _).mp hq).2.1

theorem linked_later_master (H : List (GBDBatch 1 1 1 3))
    (hH : ∀b∈H,b=linkedRest ∨ b=linkedOpt) :
    IsMinimizer (gbdMaster linkedModel 0 H) Prod.snd (iy 0,0) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨binary_zero_mem,le_rfl,?_⟩,?_⟩
  · intro b hb
    rcases hH b hb with rfl | rfl
    · exact (linked_rest_constraint _).mpr (by norm_num [iy])
    · exact (linked_opt_constraint _).mpr (by norm_num [iy])
  · intro q hq
    exact ((gbd_master_mem_iff _ _ _ _).mp hq).2.1

def linkedS0 : GBDState 1 1 1 3 := gbdInit none
def linkedS1 : GBDState 1 1 1 3 := gbdAppend linkedModel linkedS0 linkedRest
def linkedS2 : GBDState 1 1 1 3 := gbdAppend linkedModel linkedS1 linkedOpt

theorem linked_first_continue : GBDContinue linkedModel 0 0 linkedS0 linkedS1 :=
  GBDContinue.step (linked_initial_master 1 binary_one_mem)
    (by simp [gbdCompetitive,linkedS0,gbdInit]) linked_rest_valid rfl

theorem linked_second_continue : GBDContinue linkedModel 0 0 linkedS1 linkedS2 := by
  apply GBDContinue.step (z := (iy 0,0))
  · exact linked_later_master [linkedRest] (by simp)
  · simp [gbdCompetitive,linkedS1,linkedS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,linkedRest]
  · exact linked_opt_valid
  · rfl

theorem linked_final_stop : GBDStop linkedModel 0 0 linkedS2 (.solution (pt 0 0)) := by
  apply GBDStop.gap (z := (iy 0,0))
  · exact linked_later_master [linkedRest,linkedOpt] (by simp)
  · simp [linkedS2,linkedS1,linkedS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,linkedRest,linkedOpt,oaBest]
  · norm_num [Chapter02KKTExamples.linked_objective,pt]

theorem linked_counted : GBDCountedCompleted linkedModel 0 0 linkedS0 ⟨1,1,0⟩ (.solution (pt 0 0)) :=
  ⟨linkedS2,[linkedRest,linkedOpt],GBDTrace.cons linked_first_continue
    (GBDTrace.cons linked_second_continue (GBDTrace.nil linkedS2)),linked_final_stop,rfl⟩

theorem linked_restoration_complete_control :
    IsCompact (linkedModel.linearRegion ∩ IntegerCylinder (n := 1) linkedModel.lo linkedModel.hi) ∧
    (∀j,ConvexOn ℝ Set.univ (linkedModel.g j)) ∧
    (∀j,Differentiable ℝ (linkedModel.g j)) ∧ OAFiberSlater linkedModel ∧ GBDFloorValid linkedModel 0 ∧
    GBDInvariant linkedModel linkedS0 ∧
    GBDCountedCompleted linkedModel 0 0 linkedS0 ⟨1,1,0⟩ (.solution (pt 0 0)) ∧
    GBDReturnCertificate linkedModel 0 (.solution (pt 0 0)) := by
  have hi : GBDInvariant linkedModel linkedS0 := gbd_init_invariant _ none (by simp)
  refine ⟨Chapter02KKTExamples.linked_base_compact (1/2),Chapter02KKTExamples.linked_convex (1/2),
    linked_diff,linked_slater,linked_floor,hi,linked_counted,?_⟩
  exact gbd_stop_sound linkedModel linked_floor (Chapter02KKTExamples.linked_convex (1/2))
    (gbd_continue_invariant _ (gbd_continue_invariant _ hi linked_first_continue) linked_second_continue)
    linked_final_stop

theorem unfloored_empty_and_restoration_nonattainment :
    (gbdMasterUnfloored eqModel []).Nonempty ∧
    (¬∃z,IsMinimizer (gbdMasterUnfloored eqModel []) Prod.snd z) ∧
    gbdBatchValid linkedModel linkedRest ∧
    (gbdMasterUnfloored linkedModel [linkedRest]).Nonempty ∧
    (¬∃z,IsMinimizer (gbdMasterUnfloored linkedModel [linkedRest]) Prod.snd z) := by
  refine ⟨⟨(iy 0,0),binary_zero_mem,by simp⟩,
    gbd_unfloored_no_minimum _ [] (by simp),linked_rest_valid,?_,?_⟩
  · refine ⟨(iy 0,0),binary_zero_mem,?_⟩
    intro b hb
    have hb' : b=linkedRest := by simpa using hb
    subst b
    exact (linked_rest_constraint _).mpr (by norm_num [iy])
  · apply gbd_unfloored_no_minimum
    intro b hb
    have hb' : b=linkedRest := by simpa using hb
    subst b
    rfl

theorem floor_attained_master_noncompact :
    IsMinimizer (gbdMaster linkedModel 0 [linkedRest]) Prod.snd (iy 0,0) ∧
    ¬IsCompact (gbdMaster linkedModel 0 [linkedRest]) ∧
    ∀t : ℝ,0≤t → (iy 0,t)∈gbdMaster linkedModel 0 [linkedRest] := by
  have hm := linked_later_master [linkedRest] (by simp)
  refine ⟨hm,gbd_master_not_compact _ _ _ ⟨_,hm.1⟩,?_⟩
  intro t ht
  apply (gbd_master_mem_iff _ _ _ _).mpr
  refine ⟨binary_zero_mem,ht,?_⟩
  intro b hb
  have hb' : b=linkedRest := by simpa using hb
  subst b
  exact (linked_rest_constraint _).mpr (by norm_num [iy])

def linkedSelectedState (t : ℝ) : GBDState 1 1 1 3 := gbdAppend linkedModel linkedS0 (linkedSelected t)

theorem linked_selected_first (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    GBDContinue linkedModel 0 0 linkedS0 (linkedSelectedState t) :=
  GBDContinue.step (linked_initial_master 0 binary_zero_mem)
    (by simp [gbdCompetitive,linkedS0,gbdInit]) (linked_selected_valid t ht0 ht1) rfl

theorem linked_selected_zero_master (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    IsMinimizer (gbdMaster linkedModel 0 [linkedSelected t]) Prod.snd (iy 0,0) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨binary_zero_mem,le_rfl,?_⟩,?_⟩
  · intro b hb
    have hb' : b=linkedSelected t := by simpa using hb
    subst b
    exact (linked_selected_constraint t ht0 ht1 _).mpr (by norm_num [iy])
  · intro q hq
    exact ((gbd_master_mem_iff _ _ _ _).mp hq).2.1

theorem linked_selected_tie_master :
    IsMinimizer (gbdMaster linkedModel 0 [linkedSelected 0]) Prod.snd (iy 1,0) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨binary_one_mem,le_rfl,?_⟩,?_⟩
  · intro b hb
    have hb' : b=linkedSelected 0 := by simpa using hb
    subst b
    exact (linked_selected_constraint 0 le_rfl (by norm_num) _).mpr (by norm_num [iy])
  · intro q hq
    exact ((gbd_master_mem_iff _ _ _ _).mp hq).2.1

theorem linked_selected_tie_stop :
    GBDStop linkedModel 0 0 (linkedSelectedState 0) (.solution (pt 0 0)) := by
  apply GBDStop.gap linked_selected_tie_master
  · simp [linkedSelectedState,linkedS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,linkedSelected,oaBest]
  · norm_num [Chapter02KKTExamples.linked_objective,pt]

theorem linked_selected_positive_master_integer (t : ℝ) (ht0 : 0<t) (ht1 : t≤1)
    (z : IntVector 1 × ℝ) (hm : IsMinimizer (gbdMaster linkedModel 0 [linkedSelected t]) Prod.snd z) :
    z.1 = iy 0 := by
  have hlow := ((gbd_master_mem_iff _ _ _ _).mp hm.1).2.1
  have hupp := hm.2 _ (linked_selected_zero_master t ht0.le ht1).1
  have he : z.2 = 0 := le_antisymm hupp hlow
  have hmem := (gbd_master_mem_iff _ _ _ _).mp hm.1
  have hc := (linked_selected_constraint t ht0.le ht1 z).mp (hmem.2.2 _ (by simp))
  rcases binary_box_cases z.1 hmem.1 with hh | hh
  · exact hh
  · rw [hh,he] at hc
    norm_num [iy] at hc
    linarith

theorem linked_selected_positive_stop (t : ℝ) (ht0 : 0<t) (ht1 : t≤1) :
    GBDStop linkedModel 0 0 (linkedSelectedState t) (.solution (pt 0 0)) := by
  apply GBDStop.gap (linked_selected_zero_master t ht0.le ht1)
  · simp [linkedSelectedState,linkedS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,linkedSelected,oaBest]
  · norm_num [Chapter02KKTExamples.linked_objective,pt]

theorem linked_multiplier_master_tie_control :
    GBDContinue linkedModel 0 0 linkedS0 (linkedSelectedState 0) ∧
    IsMinimizer (gbdMaster linkedModel 0 [linkedSelected 0]) Prod.snd (iy 1,0) ∧
    GBDStop linkedModel 0 0 (linkedSelectedState 0) (.solution (pt 0 0)) ∧
    (iy 1) ∉ gbdSeen (linkedSelectedState 0) ∧
    ∀t : ℝ,0<t → t≤1 →
      GBDContinue linkedModel 0 0 linkedS0 (linkedSelectedState t) ∧
      GBDStop linkedModel 0 0 (linkedSelectedState t) (.solution (pt 0 0)) ∧
      ∀z,IsMinimizer (gbdMaster linkedModel 0 [linkedSelected t]) Prod.snd z → z.1=iy 0 := by
  refine ⟨linked_selected_first 0 le_rfl (by norm_num),linked_selected_tie_master,
    linked_selected_tie_stop,?_,?_⟩
  · simp [gbdSeen,linkedSelectedState,gbdAppend,linkedS0,gbdInit,linkedSelected]
    intro h
    have hh := congrFun h 0
    norm_num [iy] at hh
  · intro t ht0 ht1
    exact ⟨linked_selected_first t ht0.le ht1,linked_selected_positive_stop t ht0 ht1,
      linked_selected_positive_master_integer t ht0 ht1⟩

#print axioms linked_restoration_complete_control
#print axioms unfloored_empty_and_restoration_nonattainment
#print axioms floor_attained_master_noncompact
#print axioms linked_multiplier_master_tie_control

def routeNoGood (a : ℤ) : GBDBatch 0 1 1 1 := ⟨iy a,.emptyLinear⟩
def routeLambda : Fin 1 → ℝ := Classical.choose (route_source_multipliers 0 0 le_rfl)
def routeMu : Fin 1 → ℝ := Classical.choose (Classical.choose_spec (route_source_multipliers 0 0 le_rfl))
theorem route_chosen_kkt : FixedNLPKKT (routeModel 0) (routePoint 0)
    (fun j => fderiv ℝ ((routeModel 0).g j) (routePoint 0)) routeLambda routeMu :=
  Classical.choose_spec (Classical.choose_spec (route_source_multipliers 0 0 le_rfl))
def routeGood : GBDBatch 0 1 1 1 := ⟨iy 0,.optimal (routePoint 0) routeLambda routeMu⟩

theorem route_nogood_valid (bound : ℝ) (a : ℤ)
    (ha : iy a ∈ IntegerBox (routeModel bound).lo (routeModel bound).hi) (hlt : bound < (a:ℝ)) :
    gbdBatchValid (routeModel bound) (routeNoGood a) := by
  refine ⟨ha,?_⟩
  change ¬ ((routeModel bound).fixedLinearFiber (Chapter02.oaIntCast (iy a))).Nonempty
  rw [cast_iy]
  exact route_empty_linear bound (a:ℝ) hlt

theorem route_good_valid : gbdBatchValid (routeModel 0) routeGood := by
  have hc : Chapter02.oaIntCast (iy 0) = (fun _ => 0) := by ext i; norm_num [Chapter02.oaIntCast,iy]
  refine ⟨binary_zero_mem,?_,?_,route_chosen_kkt⟩
  · ext i
    norm_num [routeGood,routePoint,Chapter02.oaIntCast,iy]
  · change IsMinimizer ((routeModel 0).fixedNonlinearFiber (Chapter02.oaIntCast (iy 0)))
      (routeModel 0).objective (routePoint 0)
    rw [hc]
    exact route_fixed_minimum 0 0 le_rfl

theorem route_good_constraint_zero (bound eta : ℝ) :
    gbdBatchConstraint (routeModel bound) routeGood (iy 0,eta) ↔ 0≤eta := by
  have hc : Chapter02.oaIntCast (iy 0) = (routePoint 0).2 := by
    ext i
    norm_num [Chapter02.oaIntCast,iy,routePoint]
  change anchoredOptimalityCut (routeModel bound) (routePoint 0) _ _ _ (Chapter02.oaIntCast (iy 0))≤eta ↔ _
  rw [hc,optimality_cut_at_anchor,route_objective]

theorem binary_zero_ne_one : iy 0 ≠ iy 1 := by
  intro h
  have hh := congrFun h 0
  norm_num [iy] at hh

theorem route_initial_master (bound : ℝ) (a : ℤ)
    (ha : iy a ∈ IntegerBox (routeModel bound).lo (routeModel bound).hi) :
    IsMinimizer (gbdMaster (routeModel bound) 0 []) Prod.snd (iy a,0) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨ha,le_rfl,by simp⟩,?_⟩
  intro q hq
  exact ((gbd_master_mem_iff _ _ _ _).mp hq).2.1

theorem route_later_master (bound : ℝ) (H : List (GBDBatch 0 1 1 1))
    (hH : ∀b∈H,b=routeNoGood 1 ∨ b=routeGood) :
    IsMinimizer (gbdMaster (routeModel bound) 0 H) Prod.snd (iy 0,0) := by
  refine ⟨(gbd_master_mem_iff _ _ _ _).mpr ⟨binary_zero_mem,le_rfl,?_⟩,?_⟩
  · intro b hb
    rcases hH b hb with rfl | rfl
    · exact binary_zero_ne_one
    · exact (route_good_constraint_zero bound 0).mpr le_rfl
  · intro q hq
    exact ((gbd_master_mem_iff _ _ _ _).mp hq).2.1

def routeS0 : GBDState 0 1 1 1 := gbdInit none
def routeS1 : GBDState 0 1 1 1 := gbdAppend (routeModel 0) routeS0 (routeNoGood 1)
def routeS2 : GBDState 0 1 1 1 := gbdAppend (routeModel 0) routeS1 routeGood

theorem route_first_continue : GBDContinue (routeModel 0) 0 0 routeS0 routeS1 :=
  GBDContinue.step (route_initial_master 0 1 binary_one_mem)
    (by simp [gbdCompetitive,routeS0,gbdInit]) (route_nogood_valid 0 1 binary_one_mem (by norm_num)) rfl

theorem route_second_continue : GBDContinue (routeModel 0) 0 0 routeS1 routeS2 := by
  apply GBDContinue.step (z := (iy 0,0))
  · exact route_later_master 0 [routeNoGood 1] (by simp)
  · simp [gbdCompetitive,routeS1,routeS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,routeNoGood]
  · exact route_good_valid
  · rfl

theorem route_final_stop : GBDStop (routeModel 0) 0 0 routeS2 (.solution (routePoint 0)) := by
  apply GBDStop.gap (z := (iy 0,0))
  · exact route_later_master 0 [routeNoGood 1,routeGood] (by simp)
  · simp [routeS2,routeS1,routeS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,routeNoGood,routeGood,oaBest]
  · norm_num [route_objective]

theorem route_counted : GBDCountedCompleted (routeModel 0) 0 0 routeS0 ⟨1,0,1⟩ (.solution (routePoint 0)) :=
  ⟨routeS2,[routeNoGood 1,routeGood],GBDTrace.cons route_first_continue
    (GBDTrace.cons route_second_continue (GBDTrace.nil routeS2)),route_final_stop,rfl⟩

theorem route_restoration_also_empty :
    ¬ (RestorationPairs ((routeModel 0).fixedLinearFiber (fun _ => 1)) (routeModel 0).g).Nonempty := by
  rintro ⟨p,hp⟩
  exact route_empty_linear 0 1 (by norm_num) ⟨p.1,hp.1⟩

theorem empty_affine_then_feasible_complete_control :
    IsCompact ((routeModel 0).linearRegion ∩ IntegerCylinder (n := 0) (routeModel 0).lo (routeModel 0).hi) ∧
    (∀j,ConvexOn ℝ Set.univ ((routeModel 0).g j)) ∧
    (∀j,Differentiable ℝ ((routeModel 0).g j)) ∧ OAFiberSlater (routeModel 0) ∧ GBDFloorValid (routeModel 0) 0 ∧
    GBDInvariant (routeModel 0) routeS0 ∧
    GBDCountedCompleted (routeModel 0) 0 0 routeS0 ⟨1,0,1⟩ (.solution (routePoint 0)) ∧
    GBDReturnCertificate (routeModel 0) 0 (.solution (routePoint 0)) ∧
    ¬ (RestorationPairs ((routeModel 0).fixedLinearFiber (fun _ => 1)) (routeModel 0).g).Nonempty := by
  have hi : GBDInvariant (routeModel 0) routeS0 := gbd_init_invariant _ none (by simp)
  refine ⟨route_base_compact 0,route_convex 0,route_diff 0,route_slater 0,route_floor 0,
    hi,route_counted,?_,route_restoration_also_empty⟩
  exact gbd_stop_sound (routeModel 0) (route_floor 0) (route_convex 0)
    (gbd_continue_invariant _ (gbd_continue_invariant _ hi route_first_continue) route_second_continue)
    route_final_stop

def emptyS1 : GBDState 0 1 1 1 := gbdAppend (routeModel (-1)) routeS0 (routeNoGood 1)
def emptyS2 : GBDState 0 1 1 1 := gbdAppend (routeModel (-1)) emptyS1 (routeNoGood 0)

theorem all_empty_first_continue : GBDContinue (routeModel (-1)) 0 0 routeS0 emptyS1 :=
  GBDContinue.step (route_initial_master (-1) 1 binary_one_mem)
    (by simp [gbdCompetitive,routeS0,gbdInit])
    (route_nogood_valid (-1) 1 binary_one_mem (by norm_num)) rfl

theorem all_empty_second_continue : GBDContinue (routeModel (-1)) 0 0 emptyS1 emptyS2 := by
  apply GBDContinue.step (z := (iy 0,0))
  · exact route_later_master (-1) [routeNoGood 1] (by simp)
  · simp [gbdCompetitive,emptyS1,routeS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,routeNoGood]
  · exact route_nogood_valid (-1) 0 binary_zero_mem (by norm_num)
  · rfl

theorem all_empty_master : gbdMaster (routeModel (-1)) 0 emptyS2.history = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hm := (gbd_master_mem_iff _ _ _ _).mp hz
  have h1 : z.1 ≠ iy 1 := hm.2.2 (routeNoGood 1) (by simp [emptyS2,emptyS1,routeS0,gbdAppend,gbdInit])
  have h0 : z.1 ≠ iy 0 := hm.2.2 (routeNoGood 0) (by simp [emptyS2,emptyS1,routeS0,gbdAppend,gbdInit])
  exact (binary_box_cases z.1 hm.1).elim h0 h1

theorem all_empty_counted : GBDCountedCompleted (routeModel (-1)) 0 0 routeS0 ⟨0,0,2⟩ .infeasible :=
  ⟨emptyS2,[routeNoGood 1,routeNoGood 0],GBDTrace.cons all_empty_first_continue
    (GBDTrace.cons all_empty_second_continue (GBDTrace.nil emptyS2)),GBDStop.empty all_empty_master,rfl⟩

theorem all_affine_empty_complete_control :
    IsCompact ((routeModel (-1)).linearRegion ∩ IntegerCylinder (n := 0) (routeModel (-1)).lo (routeModel (-1)).hi) ∧
    (∀j,ConvexOn ℝ Set.univ ((routeModel (-1)).g j)) ∧
    (∀j,Differentiable ℝ ((routeModel (-1)).g j)) ∧ OAFiberSlater (routeModel (-1)) ∧ GBDFloorValid (routeModel (-1)) 0 ∧
    GBDInvariant (routeModel (-1)) routeS0 ∧
    GBDCountedCompleted (routeModel (-1)) 0 0 routeS0 ⟨0,0,2⟩ .infeasible ∧
    GBDReturnCertificate (routeModel (-1)) 0 .infeasible := by
  have hi : GBDInvariant (routeModel (-1)) routeS0 := gbd_init_invariant _ none (by simp)
  refine ⟨route_base_compact (-1),route_convex (-1),route_diff (-1),route_slater (-1),route_floor (-1),
    hi,all_empty_counted,?_⟩
  exact gbd_stop_sound (routeModel (-1)) (route_floor (-1)) (route_convex (-1))
    (gbd_continue_invariant _ (gbd_continue_invariant _ hi all_empty_first_continue) all_empty_second_continue)
    (GBDStop.empty all_empty_master)

theorem deleted_no_good_reopens_empty_fiber :
    (iy 1,0) ∉ gbdMaster (routeModel 0) 0 routeS1.history ∧
    routeS0.incumbent=routeS1.incumbent ∧
    GBDContinue (routeModel 0) 0 0 routeS0 routeS1 := by
  refine ⟨?_,rfl,route_first_continue⟩
  intro h
  have hn : iy 1 ≠ iy 1 := ((gbd_master_mem_iff _ _ _ _).mp h).2.2 (routeNoGood 1)
    (by simp [routeS1,routeS0,gbdAppend,gbdInit])
  exact hn rfl

theorem eq_counted_long : GBDCountedCompleted eqModel 0 0 eqS0 ⟨2,0,0⟩ (.solution (pt 0 0)) :=
  ⟨eqS2,[eqBatch 1,eqBatch 0],GBDTrace.cons (eq_first_continue 0)
    (GBDTrace.cons eq_second_continue (GBDTrace.nil eqS2)),eq_final_stop,rfl⟩

theorem eq_counted_short : GBDCountedCompleted eqModel 0 0 eqS0 ⟨1,0,0⟩ (.solution (pt 0 0)) :=
  ⟨eqShort,[eqBatch 0],GBDTrace.cons eq_short_continue (GBDTrace.nil eqShort),eq_short_stop,rfl⟩

theorem zero_rows_complete_counts_and_certificates :
    IsCompact (eqModel.linearRegion ∩ IntegerCylinder (n := 1) eqModel.lo eqModel.hi) ∧
    (∀j,ConvexOn ℝ Set.univ (eqModel.g j)) ∧
    (∀j,Differentiable ℝ (eqModel.g j)) ∧ OAFiberSlater eqModel ∧ GBDFloorValid eqModel 0 ∧
    GBDInvariant eqModel eqS0 ∧ (oaBox eqModel).card=2 ∧
    GBDCountedCompleted eqModel 0 0 eqS0 ⟨2,0,0⟩ (.solution (pt 0 0)) ∧
    GBDCountedCompleted eqModel 0 0 eqS0 ⟨1,0,0⟩ (.solution (pt 0 0)) ∧
    GBDReturnCertificate eqModel 0 (.solution (pt 0 0)) := by
  have hi : GBDInvariant eqModel eqS0 := gbd_init_invariant _ none (by simp)
  refine ⟨eq_base_compact,eq_convex,eq_diff,eq_slater,eq_floor,hi,
    Chapter02OAExamples.trace_box_card,eq_counted_long,eq_counted_short,?_⟩
  exact gbd_stop_sound eqModel eq_floor eq_convex
    (gbd_continue_invariant _ (gbd_continue_invariant _ hi (eq_first_continue 0)) eq_second_continue) eq_final_stop

#print axioms empty_affine_then_feasible_complete_control
#print axioms all_affine_empty_complete_control
#print axioms deleted_no_good_reopens_empty_fiber
#print axioms zero_rows_complete_counts_and_certificates

theorem linked_selected_final_stop (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    GBDStop linkedModel 0 0 (linkedSelectedState t) (.solution (pt 0 0)) := by
  apply GBDStop.gap (linked_selected_zero_master t ht0 ht1)
  · simp [linkedSelectedState,linkedS0,gbdAppend,gbdInit,gbdBatchOptimalAnchor,linkedSelected,oaBest]
  · norm_num [Chapter02KKTExamples.linked_objective,pt]

theorem linked_selected_counted (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    GBDCountedCompleted linkedModel 0 0 linkedS0 ⟨1,0,0⟩ (.solution (pt 0 0)) :=
  ⟨linkedSelectedState t,[linkedSelected t],GBDTrace.cons (linked_selected_first t ht0 ht1)
    (GBDTrace.nil (linkedSelectedState t)),linked_selected_final_stop t ht0 ht1,rfl⟩

theorem linked_feasible_first_complete_control :
    IsCompact (linkedModel.linearRegion ∩ IntegerCylinder (n := 1) linkedModel.lo linkedModel.hi) ∧
    (∀j,ConvexOn ℝ Set.univ (linkedModel.g j)) ∧
    (∀j,Differentiable ℝ (linkedModel.g j)) ∧ OAFiberSlater linkedModel ∧ GBDFloorValid linkedModel 0 ∧
    GBDInvariant linkedModel linkedS0 ∧
    (∀t : ℝ,0≤t → t≤1 → GBDCountedCompleted linkedModel 0 0 linkedS0 ⟨1,0,0⟩ (.solution (pt 0 0))) ∧
    GBDReturnCertificate linkedModel 0 (.solution (pt 0 0)) := by
  have hi : GBDInvariant linkedModel linkedS0 := gbd_init_invariant _ none (by simp)
  refine ⟨Chapter02KKTExamples.linked_base_compact (1/2),Chapter02KKTExamples.linked_convex (1/2),
    linked_diff,linked_slater,linked_floor,hi,linked_selected_counted,?_⟩
  exact gbd_stop_sound linkedModel linked_floor (Chapter02KKTExamples.linked_convex (1/2))
    (gbd_continue_invariant _ hi (linked_selected_first 0 le_rfl (by norm_num)))
    linked_selected_tie_stop

theorem eq_tolerance_counted : GBDCountedCompleted eqModel 0 1 eqS0 ⟨1,0,0⟩ (.solution (pt 1 1)) :=
  ⟨eqS1,[eqBatch 1],GBDTrace.cons (eq_first_continue 1) (GBDTrace.nil eqS1),
    eq_positive_tolerance_nonoptimal.2.1,rfl⟩

theorem positive_tolerance_complete_certificate :
    IsCompact (eqModel.linearRegion ∩ IntegerCylinder (n := 1) eqModel.lo eqModel.hi) ∧
    (∀j,ConvexOn ℝ Set.univ (eqModel.g j)) ∧
    (∀j,Differentiable ℝ (eqModel.g j)) ∧ OAFiberSlater eqModel ∧ GBDFloorValid eqModel 0 ∧
    GBDInvariant eqModel eqS0 ∧
    GBDCountedCompleted eqModel 0 1 eqS0 ⟨1,0,0⟩ (.solution (pt 1 1)) ∧
    GBDReturnCertificate eqModel 1 (.solution (pt 1 1)) ∧
    ¬IsMinimizer (eqModel.feasibleOn Set.univ) eqModel.objective (pt 1 1) := by
  have hi : GBDInvariant eqModel eqS0 := gbd_init_invariant _ none (by simp)
  exact ⟨eq_base_compact,eq_convex,eq_diff,eq_slater,eq_floor,hi,eq_tolerance_counted,
    gbd_stop_sound eqModel eq_floor eq_convex (gbd_continue_invariant _ hi (eq_first_continue 1))
      eq_positive_tolerance_nonoptimal.2.1,eq_positive_tolerance_nonoptimal.2.2⟩

#print axioms linked_feasible_first_complete_control
#print axioms positive_tolerance_complete_certificate

end Chapter02GBDExamples
