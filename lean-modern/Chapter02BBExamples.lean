module

public import Chapter02BBNodes
public import Chapter02BBDriver
public import Chapter02BBAffine
public import Chapter02CPExamples
public import Chapter02OAEdgeExamples
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-! Concrete exact BB controls. Model premises, exact minimizers and actual
transition traces are separate proof obligations. Literal real bounds are used
throughout; an empty child is retained until its own processing step. -/
noncomputable section
open Chapter02
open scoped BigOperators Topology
namespace Chapter02BBExamples

def region {n m l r : ℕ} (d : ModelData n m l r) (N : BBNode m) :=
  ContinuousRelaxation d.nonlinearRegion d.linearRegion N.lower N.upper

def rootNode {n m l r : ℕ} (d : ModelData n m l r) : BBNode m := ⟨d.lo,d.hi⟩
def intervalNode (a b : ℝ) : BBNode 1 := ⟨fun _ => a,fun _ => b⟩
def point (x y : ℝ) : Point 1 1 := (fun _ => x,fun _ => y)
def purePoint (y : ℝ) : Point 0 1 := (Fin.elim0,fun _ => y)

theorem root_region_eq {n m l r : ℕ} (d : ModelData n m l r) :
    region d (rootNode d) = d.relaxationOn Set.univ := by
  ext p; simp [region,rootNode,ModelData.relaxationOn,ContinuousRelaxation]

/-- A bounded continuous epigraph coordinate and actual binary coordinates. -/
def boundedModel (m l : ℕ) (g : Fin l → Point 1 m → ℝ) (K : ℝ) :
    ModelData 1 m l 2 where
  g := g
  A := fun row _ => if row = 0 then -1 else 1
  B := fun _ _ => 0
  rhs := fun row => if row = 0 then 0 else K
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

theorem bounded_linear_iff (m l : ℕ) (g : Fin l → Point 1 m → ℝ) (K : ℝ)
    (p : Point 1 m) : p ∈ (boundedModel m l g K).linearRegion ↔
      0 ≤ p.1 0 ∧ p.1 0 ≤ K := by
  simp [ModelData.linearRegion,boundedModel,LinearForm,Fin.forall_fin_succ]

theorem bounded_objective (m l : ℕ) (g : Fin l → Point 1 m → ℝ) (K : ℝ)
    (p : Point 1 m) : (boundedModel m l g K).objective p = p.1 0 := by
  simp [ModelData.objective,boundedModel,LinearForm]

theorem bounded_base_compact (m l : ℕ) (g : Fin l → Point 1 m → ℝ) (K : ℝ) :
    IsCompact ((boundedModel m l g K).linearRegion ∩ IntegerCylinder (n := 1)
      (boundedModel m l g K).lo (boundedModel m l g K).hi) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Point 1 m)
    ((fun _ => K),1))).of_isClosed_subset (Chapter02CPExamples.base_closed _)
  rintro p ⟨hp,y,hy,heq⟩
  have hx := (bounded_linear_iff m l g K p).mp hp
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i; exact hx.1
  · intro i; rw [heq]; exact (hy i).1
  · intro i; fin_cases i; exact hx.2
  · intro i; rw [heq]; exact (hy i).2

def quadModel (a : ℝ) : ModelData 1 1 1 2 :=
  boundedModel 1 1 (fun _ p => (p.2 0-a)^2-p.1 0) 1

theorem quad_region_iff (a L U : ℝ) (p : Point 1 1) :
    p ∈ region (quadModel a) (intervalNode L U) ↔
      (p.2 0-a)^2 ≤ p.1 0 ∧ 0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧
        L ≤ p.2 0 ∧ p.2 0 ≤ U := by
  simp [region,ContinuousRelaxation,ModelData.nonlinearRegion,
    quadModel,ModelData.linearRegion,LinearForm,boundedModel,intervalNode,Fin.forall_fin_succ,
    sub_nonpos,and_assoc]

theorem quad_objective (a : ℝ) (p : Point 1 1) :
    (quadModel a).objective p = p.1 0 := bounded_objective _ _ _ _ _

theorem quad_convex (a : ℝ) : ∀ j, ConvexOn ℝ Set.univ ((quadModel a).g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.2 0-q.2 0))
  simp only [quadModel,boundedModel,Prod.fst_add,Prod.snd_add,Prod.smul_fst,
    Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have heq : s * p.2 0 + t * q.2 0 - a =
      s * (p.2 0-a) + t * (q.2 0-a) := by
    calc
      _ = s * p.2 0 + t * q.2 0 - (s+t)*a := by rw [hst]; ring
      _ = _ := by ring
  rw [heq]
  have hid : s * (p.2 0-a)^2 + t * (q.2 0-a)^2 -
      (s * (p.2 0-a) + t * (q.2 0-a))^2 =
      s*t*(p.2 0-q.2 0)^2 := by
    have hstp := congrArg (fun z : ℝ => z * (s*(p.2 0-a)^2+t*(q.2 0-a)^2)) hst
    nlinarith
  nlinarith

theorem quad_smooth (a : ℝ) : ∀ j, ContDiff ℝ 2 ((quadModel a).g j) := by
  intro j; dsimp [quadModel,boundedModel]; fun_prop

theorem quad_base_compact (a : ℝ) :
    IsCompact ((quadModel a).linearRegion ∩ IntegerCylinder (n := 1)
      (quadModel a).lo (quadModel a).hi) := bounded_base_compact _ _ _ _

theorem quad_root_minimum (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1) :
    IsMinimizer (region (quadModel a) (intervalNode 0 1))
      (quadModel a).objective (point 0 a) := by
  refine ⟨(quad_region_iff _ _ _ _).2 ?_,?_⟩
  · simpa [point] using And.intro ha hb
  · intro p hp; simpa [quad_objective,point] using
      ((quad_region_iff _ _ _ _).1 hp).2.1

theorem quad_fixed_minimum (a y : ℝ) (h : (y-a)^2 ≤ 1) :
    IsMinimizer (region (quadModel a) (intervalNode y y))
      (quadModel a).objective (point ((y-a)^2) y) := by
  refine ⟨(quad_region_iff _ _ _ _).2 ?_,?_⟩
  · exact ⟨le_rfl,sq_nonneg _,h,le_rfl,le_rfl⟩
  · intro p hp
    rcases (quad_region_iff _ _ _ _).1 hp with ⟨hg,_,_,hl,hu⟩
    have hy : p.2 0 = y := le_antisymm hu hl
    simpa [quad_objective,point,hy] using hg

theorem quad_two_fifths_minima :
    IsMinimizer (region (quadModel (2/5)) (intervalNode 0 1))
      (quadModel (2/5)).objective (point 0 (2/5)) ∧
    IsMinimizer (region (quadModel (2/5)) (intervalNode 0 0))
      (quadModel (2/5)).objective (point (4/25) 0) ∧
    IsMinimizer (region (quadModel (2/5)) (intervalNode 1 1))
      (quadModel (2/5)).objective (point (9/25) 1) := by
  refine ⟨quad_root_minimum _ (by norm_num) (by norm_num),?_,?_⟩
  · convert quad_fixed_minimum (2/5) 0 (by norm_num) using 1; norm_num
  · convert quad_fixed_minimum (2/5) 1 (by norm_num) using 1; norm_num

theorem quad_half_minima :
    IsMinimizer (region (quadModel (1/2)) (intervalNode 0 1))
      (quadModel (1/2)).objective (point 0 (1/2)) ∧
    IsMinimizer (region (quadModel (1/2)) (intervalNode 0 0))
      (quadModel (1/2)).objective (point (1/4) 0) ∧
    IsMinimizer (region (quadModel (1/2)) (intervalNode 1 1))
      (quadModel (1/2)).objective (point (1/4) 1) := by
  refine ⟨quad_root_minimum _ (by norm_num) (by norm_num),?_,?_⟩
  · convert quad_fixed_minimum (1/2) 0 (by norm_num) using 1; norm_num
  · convert quad_fixed_minimum (1/2) 1 (by norm_num) using 1; norm_num

theorem interval_children (L U v : ℝ) :
    (intervalNode L U).left 0 v = intervalNode L (Int.floor v) ∧
    (intervalNode L U).right 0 v = intervalNode (Int.ceil v) U := by
  constructor
  · unfold BBNode.left intervalNode
    congr 1
    funext i; fin_cases i; simp
  · unfold BBNode.right intervalNode
    congr 1
    funext i; fin_cases i; simp

theorem fractional_between_integers (v : ℝ) (z : ℤ)
    (hl : (z:ℝ) < v) (hu : v < (z+1:ℤ)) : BBFractional v := by
  rintro ⟨k,hk⟩
  rw [← hk] at hl hu
  have h1 : z < k := by exact_mod_cast hl
  have h2 : k < z+1 := by exact_mod_cast hu
  omega

def boxModel (L U : ℝ) : ModelData 0 1 0 0 where
  g := Fin.elim0
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := Fin.elim0
  c2 := fun _ => 0
  lo := fun _ => L
  hi := fun _ => U

theorem box_region_iff (L U a b : ℝ) (p : Point 0 1) :
    p ∈ region (boxModel L U) (intervalNode a b) ↔ a ≤ p.2 0 ∧ p.2 0 ≤ b := by
  simp [region,ContinuousRelaxation,ModelData.nonlinearRegion,
    ModelData.linearRegion,boxModel,intervalNode,Fin.forall_fin_succ]

theorem box_objective (L U : ℝ) (p : Point 0 1) :
    (boxModel L U).objective p = 0 := by simp [ModelData.objective,LinearForm,boxModel]

theorem box_minimum (L U a b y : ℝ) (hl : a ≤ y) (hu : y ≤ b) :
    IsMinimizer (region (boxModel L U) (intervalNode a b))
      (boxModel L U).objective (purePoint y) :=
  ⟨(box_region_iff _ _ _ _ _).2 ⟨hl,hu⟩,fun _ _ => by simp [box_objective]⟩

theorem box_empty (L U a b : ℝ) (h : b < a) :
    region (boxModel L U) (intervalNode a b) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro p hp
  have hx := (box_region_iff _ _ _ _ _).1 hp
  exact (not_le_of_gt h) (hx.1.trans hx.2)

theorem box_base_compact (L U : ℝ) :
    IsCompact ((boxModel L U).linearRegion ∩ IntegerCylinder (n := 0)
      (boxModel L U).lo (boxModel L U).hi) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (purePoint L) (purePoint U))).of_isClosed_subset
    (Chapter02CPExamples.base_closed _)
  rintro p ⟨_,y,hy,heq⟩
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; exact Fin.elim0 i
  · intro i; rw [heq]; exact (hy i).1
  · intro i; exact Fin.elim0 i
  · intro i; rw [heq]; exact (hy i).2

theorem literal_fractional_ranks :
    (intervalNode (1/5) (14/5)).rank = 3 ∧
    ((intervalNode (1/5) (14/5)).left 0 (1/5)).rank = 0 ∧
    ((intervalNode (1/5) (14/5)).right 0 (1/5)).rank = 2 ∧
    (intervalNode (-14/5) (-1/5)).rank = 3 ∧
    ((intervalNode (-14/5) (-1/5)).left 0 (-1/5)).rank = 2 ∧
    ((intervalNode (-14/5) (-1/5)).right 0 (-1/5)).rank = 0 ∧
    (intervalNode (1/4) (3/4)).rank = 1 ∧
    (intervalNode 2 1).rank = 0 := by
  norm_num [BBNode.rank,BBNode.span,BBNode.left,BBNode.right,intervalNode,
    Fin.sum_univ_one]

/-- Affine infeasibility can arise in both children even with consistent bounds. -/
def bandModel : ModelData 0 1 0 2 where
  g := Fin.elim0
  A := fun _ => Fin.elim0
  B := fun row _ => if row = 0 then -1 else 1
  rhs := fun row => if row = 0 then -1/4 else 3/4
  c1 := Fin.elim0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

theorem band_region_iff (a b : ℝ) (p : Point 0 1) :
    p ∈ region bandModel (intervalNode a b) ↔
      1/4 ≤ p.2 0 ∧ p.2 0 ≤ 3/4 ∧ a ≤ p.2 0 ∧ p.2 0 ≤ b := by
  simp [region,ContinuousRelaxation,ModelData.nonlinearRegion,ModelData.linearRegion,
    bandModel,LinearForm,intervalNode,Fin.forall_fin_succ]
  constructor
  · rintro ⟨⟨h0,h1⟩,h2,h3⟩; exact ⟨by linarith,h1,h2,h3⟩
  · rintro ⟨h0,h1,h2,h3⟩; exact ⟨⟨by linarith,h1⟩,h2,h3⟩

theorem band_objective (p : Point 0 1) : bandModel.objective p = 0 := by
  simp [ModelData.objective,LinearForm,bandModel]

theorem band_root_minimum : IsMinimizer (region bandModel (intervalNode 0 1))
    bandModel.objective (purePoint (1/2)) := by
  refine ⟨(band_region_iff _ _ _).2 ?_,fun _ _ => by simp [band_objective]⟩
  norm_num [purePoint]

theorem band_children_empty : region bandModel (intervalNode 0 0) = ∅ ∧
    region bandModel (intervalNode 1 1) = ∅ := by
  constructor <;> apply Set.eq_empty_iff_forall_notMem.2 <;> intro p hp
  · have h := (band_region_iff _ _ _).1 hp; linarith [h.1,h.2.2.2]
  · have h := (band_region_iff _ _ _).1 hp; linarith [h.2.1,h.2.2.1]

theorem band_base_empty : bandModel.linearRegion ∩
    IntegerCylinder (n := 0) bandModel.lo bandModel.hi = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  rintro p ⟨hp,y,hy,heq⟩
  have h0 := hp (0:Fin 2)
  have h1 := hp (1:Fin 2)
  simp only [LinearForm,bandModel,Fin.sum_univ_one,Fin.sum_univ_zero,
    heq] at h0 h1
  norm_num at h0 h1
  have hL : (0:ℤ) < y 0 := by exact_mod_cast (by linarith : (0:ℝ) < (y 0:ℝ))
  have hU : y 0 < (1:ℤ) := by exact_mod_cast (by linarith : (y 0:ℝ) < 1)
  omega

theorem band_base_compact : IsCompact (bandModel.linearRegion ∩
    IntegerCylinder (n := 0) bandModel.lo bandModel.hi) := by
  rw [band_base_empty]; exact isCompact_empty

theorem accepted_unbounded_reply :
    ∀ M : ℝ, ∃ p ∈ region OAEdgeExamples.badRelaxationModel
      (rootNode OAEdgeExamples.badRelaxationModel),
      OAEdgeExamples.badRelaxationModel.objective p < M := by
  intro M
  refine ⟨point (M-1) (1/2),?_,?_⟩
  · rw [root_region_eq]
    exact OAEdgeExamples.badRelaxation_feasible_line _
  · rw [OAEdgeExamples.badRelaxation_objective]
    dsimp [point]; linarith

/-- Without compactness, a bad reply need not mean that the original is empty. -/
def noncompactModel : ModelData 1 1 0 0 where
  g := Fin.elim0
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0

theorem noncompact_feasible_line (x : ℝ) :
    point x 0 ∈ noncompactModel.feasibleOn Set.univ := by
  apply (source_feasible_iff _ _ _).2
  refine ⟨Set.mem_univ _,(fun j => Fin.elim0 j),(fun row => Fin.elim0 row),fun _ => 0,?_,by simp [point]⟩
  intro i; norm_num [noncompactModel]

theorem noncompact_objective (p : Point 1 1) : noncompactModel.objective p = p.1 0 := by
  simp [ModelData.objective,LinearForm,noncompactModel]

theorem noncompact_base_not_compact : ¬ IsCompact (noncompactModel.linearRegion ∩
    IntegerCylinder (n := 1) noncompactModel.lo noncompactModel.hi) := by
  intro hc
  obtain ⟨M,hM⟩ := hc.bddAbove_image (f := fun p : Point 1 1 => p.1 0)
    (by fun_prop : Continuous (fun p : Point 1 1 => p.1 0)).continuousOn
  have hp : point (M+1) 0 ∈ noncompactModel.linearRegion ∩
      IntegerCylinder (n := 1) noncompactModel.lo noncompactModel.hi := by
    refine ⟨by intro i; exact Fin.elim0 i,fun _ => 0,?_,by simp [point]⟩
    intro i; norm_num [noncompactModel]
  have hh := hM ⟨point (M+1) 0,hp,rfl⟩
  dsimp [point] at hh; linarith

theorem noncompact_original_unbounded :
    ∀ M : ℝ, ∃ p ∈ noncompactModel.feasibleOn Set.univ,
      noncompactModel.objective p < M := by
  intro M
  refine ⟨point (M-1) 0,noncompact_feasible_line _,?_⟩
  simp only [noncompact_objective,point]; linarith

theorem noncompact_relaxation_unbounded :
    ∀ M : ℝ, ∃ p ∈ region noncompactModel (rootNode noncompactModel),
      noncompactModel.objective p < M := by
  intro M
  obtain ⟨p,hp,hM⟩ := noncompact_original_unbounded M
  refine ⟨p,?_,hM⟩
  rw [root_region_eq]
  exact source_mixed_subset_relaxation _ _ hp

/-- A finite unattained infimum differs from an unbounded-below reply. -/
def unattainedModel : ModelData 2 1 1 2 where
  g := fun _ p => Real.exp (-p.1 0)-p.1 1
  A := fun _ _ => 0
  B := fun row _ => if row = 0 then 1 else -1
  rhs := fun row => if row = 0 then 1/2 else -1/2
  c1 := ![0,1]
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

def expPoint (s t : ℝ) : Point 2 1 := (![s,t],fun _ => 1/2)

theorem unattained_linear_iff (p : Point 2 1) :
    p ∈ unattainedModel.linearRegion ↔ p.2 0 = 1/2 := by
  simp [ModelData.linearRegion,LinearForm,unattainedModel,Fin.forall_fin_succ]
  constructor
  · intro h; linarith [h.1,h.2]
  · intro h; constructor <;> linarith

theorem unattained_region_iff (p : Point 2 1) :
    p ∈ region unattainedModel (rootNode unattainedModel) ↔
      Real.exp (-p.1 0) ≤ p.1 1 ∧ p.2 0 = 1/2 := by
  simp only [region,ContinuousRelaxation,Set.mem_setOf_eq,unattained_linear_iff]
  simp [ModelData.nonlinearRegion,unattainedModel,rootNode,Fin.forall_fin_succ]
  intro h hy
  rw [hy]; norm_num

theorem unattained_objective (p : Point 2 1) : unattainedModel.objective p = p.1 1 := by
  simp [ModelData.objective,LinearForm,unattainedModel,Fin.sum_univ_two]

theorem unattained_base_empty : unattainedModel.linearRegion ∩
    IntegerCylinder (n := 2) unattainedModel.lo unattainedModel.hi = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  rintro p ⟨hp,y,_,heq⟩
  have h := (unattained_linear_iff p).1 hp
  rw [heq] at h
  have h0 : (0:ℤ) < y 0 := by exact_mod_cast (by linarith : (0:ℝ) < (y 0:ℝ))
  have h1 : y 0 < (1:ℤ) := by exact_mod_cast (by linarith : (y 0:ℝ) < 1)
  omega

theorem unattained_base_compact : IsCompact (unattainedModel.linearRegion ∩
    IntegerCylinder (n := 2) unattainedModel.lo unattainedModel.hi) := by
  rw [unattained_base_empty]; exact isCompact_empty

theorem unattained_convex : ∀ j, ConvexOn ℝ Set.univ (unattainedModel.g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have h := convexOn_exp.2 (Set.mem_univ (-p.1 0))
    (Set.mem_univ (-q.1 0)) hs ht hst
  simp only [unattainedModel,Prod.fst_add,Prod.smul_fst,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul]
  simp only [smul_eq_mul] at h
  have heq : -(s*p.1 0+t*q.1 0) = s*(-p.1 0)+t*(-q.1 0) := by ring
  rw [heq]
  nlinarith

theorem unattained_smooth : ∀ j, ContDiff ℝ 2 (unattainedModel.g j) := by
  intro j; dsimp [unattainedModel]; fun_prop

theorem unattained_objective_pos (p : Point 2 1)
    (hp : p ∈ region unattainedModel (rootNode unattainedModel)) :
    0 < unattainedModel.objective p := by
  rw [unattained_objective]
  exact (Real.exp_pos _).trans_le ((unattained_region_iff _).1 hp).1

theorem unattained_small (ε : ℝ) (he : 0 < ε) :
    ∃ p ∈ region unattainedModel (rootNode unattainedModel),
      unattainedModel.objective p < ε := by
  refine ⟨expPoint (-Real.log (ε/2)) (ε/2),?_,?_⟩
  · apply (unattained_region_iff _).2
    simp [expPoint,Real.exp_log (by positivity : 0 < ε/2)]
  · simp only [unattained_objective,expPoint,Matrix.cons_val_one,Matrix.cons_val_zero]
    linarith

theorem unattained_no_minimum : ¬ ∃ p,
    IsMinimizer (region unattainedModel (rootNode unattainedModel))
      unattainedModel.objective p := by
  rintro ⟨p,hp⟩
  obtain ⟨q,hq,hlt⟩ := unattained_small _ (unattained_objective_pos p hp.1)
  exact (not_le_of_gt hlt) (hp.2 q hq)

theorem unattained_finite_infimum :
    IsGLB (unattainedModel.objective '' region unattainedModel
      (rootNode unattainedModel)) 0 := by
  refine ⟨?_,?_⟩
  · rintro _ ⟨p,hp,rfl⟩; exact (unattained_objective_pos p hp).le
  · intro b hb
    by_contra h
    have hpos : 0 < b := lt_of_not_ge h
    obtain ⟨p,hp,hlt⟩ := unattained_small b hpos
    exact (not_le_of_gt hlt) (hb ⟨p,hp,rfl⟩)

theorem unattained_not_unbounded : ¬ (∀ M : ℝ,
    ∃ p ∈ region unattainedModel (rootNode unattainedModel),
      unattainedModel.objective p < M) := by
  intro h
  obtain ⟨p,hp,hneg⟩ := h 0
  exact (not_le_of_gt hneg) (unattained_objective_pos p hp).le

/-- Irrational affine coefficients are permitted in the compactness bridge. -/
def stripModel (α : ℝ) : ModelData 1 1 0 2 where
  g := Fin.elim0
  A := fun row _ => if row = 0 then -1 else 1
  B := fun row _ => if row = 0 then α else -α
  rhs := fun row => if row = 0 then 0 else 1
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => -1/5
  hi := fun _ => 6/5

theorem strip_linear_iff (α : ℝ) (p : Point 1 1) :
    p ∈ (stripModel α).linearRegion ↔ α*p.2 0 ≤ p.1 0 ∧ p.1 0 ≤ α*p.2 0+1 := by
  simp [ModelData.linearRegion,LinearForm,stripModel,Fin.forall_fin_succ]
  simp [add_comm]

theorem strip_region_iff (α a b : ℝ) (p : Point 1 1) :
    p ∈ region (stripModel α) (intervalNode a b) ↔
      α*p.2 0 ≤ p.1 0 ∧ p.1 0 ≤ α*p.2 0+1 ∧ a ≤ p.2 0 ∧ p.2 0 ≤ b := by
  simp only [region,ContinuousRelaxation,Set.mem_setOf_eq,strip_linear_iff]
  simp [ModelData.nonlinearRegion,stripModel,intervalNode,Fin.forall_fin_succ,and_assoc]

theorem strip_objective (α : ℝ) (p : Point 1 1) :
    (stripModel α).objective p = p.1 0 := by
  simp [ModelData.objective,LinearForm,stripModel]

theorem strip_base_compact (α : ℝ) (ha : 0 ≤ α) :
    IsCompact ((stripModel α).linearRegion ∩ IntegerCylinder (n := 1)
      (stripModel α).lo (stripModel α).hi) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (point (-α-1) (-1))
    (point (2*α+2) 2))).of_isClosed_subset (Chapter02CPExamples.base_closed _)
  rintro p ⟨hp,y,hy,heq⟩
  have hx := (strip_linear_iff α p).1 hp
  have hb := hy 0
  change -1/5 ≤ (y 0:ℝ) ∧ (y 0:ℝ) ≤ 6/5 at hb
  have hpy : p.2 0 = (y 0:ℝ) := congrFun heq 0
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i; dsimp [point]; nlinarith
  · intro i; fin_cases i; dsimp [point]; linarith
  · intro i; fin_cases i; dsimp [point]; nlinarith
  · intro i; fin_cases i; dsimp [point]; linarith

theorem strip_base_nonempty (α : ℝ) :
    ((stripModel α).linearRegion ∩ IntegerCylinder (n := 1)
      (stripModel α).lo (stripModel α).hi).Nonempty := by
  refine ⟨point 0 0,(strip_linear_iff _ _).2 ?_,fun _ => 0,?_,by simp [point]⟩
  · norm_num [point]
  · intro i; norm_num [stripModel]

theorem strip_root_minimum (α : ℝ) (ha : 0 ≤ α) :
    IsMinimizer (region (stripModel α) (intervalNode (-1/5) (6/5)))
      (stripModel α).objective (point ((-α/5 : ℝ)) (-1/5)) := by
  refine ⟨(strip_region_iff _ _ _ _).2 ?_,?_⟩
  · dsimp [point]; constructor <;> first | constructor | nlinarith
    all_goals norm_num <;> nlinarith
  · intro p hp
    have h := (strip_region_iff _ _ _ _).1 hp
    simp only [strip_objective,point]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr h.2.2.1)]

theorem strip_right_minimum (α : ℝ) (ha : 0 ≤ α) :
    IsMinimizer (region (stripModel α) (intervalNode 0 (6/5)))
      (stripModel α).objective (point 0 0) := by
  refine ⟨(strip_region_iff _ _ _ _).2 ?_,?_⟩
  · norm_num [point]
  · intro p hp
    have h := (strip_region_iff _ _ _ _).1 hp
    simp only [strip_objective,point]
    nlinarith [mul_nonneg ha h.2.2.1]

theorem strip_left_empty (α : ℝ) :
    region (stripModel α) (intervalNode (-1/5) (-1)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro p hp
  have h := (strip_region_iff _ _ _ _).1 hp
  linarith [h.2.2.1,h.2.2.2]

theorem sqrt_two_strip_premises :
    IsCompact ((stripModel (Real.sqrt 2)).linearRegion ∩ IntegerCylinder (n := 1)
      (stripModel (Real.sqrt 2)).lo (stripModel (Real.sqrt 2)).hi) ∧
    ((stripModel (Real.sqrt 2)).linearRegion ∩ IntegerCylinder (n := 1)
      (stripModel (Real.sqrt 2)).lo (stripModel (Real.sqrt 2)).hi).Nonempty ∧
    IsMinimizer (region (stripModel (Real.sqrt 2)) (intervalNode (-1/5) (6/5)))
      (stripModel (Real.sqrt 2)).objective (point (-Real.sqrt 2/5) (-1/5)) :=
  ⟨strip_base_compact _ (Real.sqrt_nonneg _),strip_base_nonempty _,
    strip_root_minimum _ (Real.sqrt_nonneg _)⟩

def bookkeepingModel : ModelData 1 2 1 2 :=
  boundedModel 2 1 (fun _ p => (p.2 0-2/5)^2+(p.2 1-p.2 0/2)^2-p.1 0) 2

def bookPoint (x y z : ℝ) : Point 1 2 := (fun _ => x,![y,z])
def bookNode (a b c d : ℝ) : BBNode 2 := ⟨![a,c],![b,d]⟩

theorem bookkeeping_region_iff (a b c d : ℝ) (p : Point 1 2) :
    p ∈ region bookkeepingModel (bookNode a b c d) ↔
      (p.2 0-2/5)^2+(p.2 1-p.2 0/2)^2 ≤ p.1 0 ∧
      0 ≤ p.1 0 ∧ p.1 0 ≤ 2 ∧ a ≤ p.2 0 ∧ p.2 0 ≤ b ∧
        c ≤ p.2 1 ∧ p.2 1 ≤ d := by
  simp [region,ContinuousRelaxation,ModelData.nonlinearRegion,ModelData.linearRegion,
    bookkeepingModel,boundedModel,LinearForm,bookNode,Fin.forall_fin_succ,
    sub_nonpos,and_assoc]

theorem bookkeeping_objective (p : Point 1 2) : bookkeepingModel.objective p = p.1 0 :=
  bounded_objective _ _ _ _ _

theorem square_combination_le (u v s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s+t = 1) : (s*u+t*v)^2 ≤ s*u^2+t*v^2 := by
  have hc : ConvexOn ℝ Set.univ (fun z : ℝ => z^2) :=
    (show Even (2:ℕ) from ⟨1,rfl⟩).convexOn_pow
  simpa only [smul_eq_mul] using hc.2 (Set.mem_univ u) (Set.mem_univ v) hs ht hst

theorem bookkeeping_convex : ∀ j, ConvexOn ℝ Set.univ (bookkeepingModel.g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have h1 := square_combination_le (p.2 0-2/5) (q.2 0-2/5) s t hs ht hst
  have h2 := square_combination_le (p.2 1-p.2 0/2) (q.2 1-q.2 0/2) s t hs ht hst
  have heq1 : s*p.2 0+t*q.2 0-2/5 = s*(p.2 0-2/5)+t*(q.2 0-2/5) := by
    nlinarith
  have heq2 : s*p.2 1+t*q.2 1-(s*p.2 0+t*q.2 0)/2 =
      s*(p.2 1-p.2 0/2)+t*(q.2 1-q.2 0/2) := by ring
  simp only [bookkeepingModel,boundedModel,Prod.fst_add,Prod.snd_add,Prod.smul_fst,
    Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [heq1,heq2]
  nlinarith

theorem bookkeeping_smooth : ∀ j, ContDiff ℝ 2 (bookkeepingModel.g j) := by
  intro j; dsimp [bookkeepingModel,boundedModel]; simp only [div_eq_mul_inv]; fun_prop

theorem bookkeeping_base_compact : IsCompact (bookkeepingModel.linearRegion ∩
    IntegerCylinder (n := 1) bookkeepingModel.lo bookkeepingModel.hi) :=
  bounded_base_compact _ _ _ _

theorem bookkeeping_root_minimum :
    IsMinimizer (region bookkeepingModel (bookNode 0 1 0 1))
      bookkeepingModel.objective (bookPoint 0 (2/5) (1/5)) := by
  refine ⟨(bookkeeping_region_iff _ _ _ _ _).2 ?_,?_⟩
  · norm_num [bookPoint]
  · intro p hp
    simpa only [bookkeeping_objective,bookPoint] using
      ((bookkeeping_region_iff _ _ _ _ _).1 hp).2.1

theorem bookkeeping_y_fixed_minimum (y : ℝ) (hy : 0 ≤ y) (hu : y ≤ 1)
    (hv : (y-2/5)^2 ≤ 2) :
    IsMinimizer (region bookkeepingModel (bookNode y y 0 1))
      bookkeepingModel.objective (bookPoint ((y-2/5)^2) y (y/2)) := by
  refine ⟨(bookkeeping_region_iff _ _ _ _ _).2 ?_,?_⟩
  · simp only [bookPoint,Matrix.cons_val_zero,Matrix.cons_val_one]
    refine ⟨?_,sq_nonneg _,hv,le_rfl,le_rfl,by linarith,by linarith⟩
    norm_num
  · intro p hp
    rcases (bookkeeping_region_iff _ _ _ _ _).1 hp with ⟨hg,_,_,hl,hu',_⟩
    have heq : p.2 0 = y := le_antisymm hu' hl
    simp only [bookkeeping_objective,bookPoint]
    rw [heq] at hg
    nlinarith [sq_nonneg (p.2 1-y/2)]

theorem bookkeeping_children_minima :
    IsMinimizer (region bookkeepingModel (bookNode 0 0 0 1))
      bookkeepingModel.objective (bookPoint (4/25) 0 0) ∧
    IsMinimizer (region bookkeepingModel (bookNode 1 1 0 1))
      bookkeepingModel.objective (bookPoint (9/25) 1 (1/2)) := by
  constructor
  · convert bookkeeping_y_fixed_minimum 0 (by norm_num) (by norm_num) (by norm_num) using 1; norm_num
  · convert bookkeeping_y_fixed_minimum 1 (by norm_num) (by norm_num) (by norm_num) using 1; norm_num

theorem bookkeeping_grandchild_minimum (z : ℝ) (hz : z = 0 ∨ z = 1) :
    IsMinimizer (region bookkeepingModel (bookNode 1 1 z z))
      bookkeepingModel.objective (bookPoint (61/100) 1 z) := by
  refine ⟨(bookkeeping_region_iff _ _ _ _ _).2 ?_,?_⟩
  · rcases hz with rfl | rfl <;> norm_num [bookPoint]
  · intro p hp
    rcases (bookkeeping_region_iff _ _ _ _ _).1 hp with ⟨hg,_,_,hy,hy',hz0,hz1⟩
    have hey : p.2 0 = 1 := le_antisymm hy' hy
    have hez : p.2 1 = z := le_antisymm hz1 hz0
    simp only [bookkeeping_objective,bookPoint]
    rcases hz with rfl | rfl <;> rw [hey,hez] at hg <;> norm_num at hg ⊢ <;> linarith

/-- This objective is genuinely nonlinear; it is not `d.objective`. -/
def boxSquareObjective (a : ℝ) (p : Point 0 1) : ℝ := (p.2 0-a)^2

theorem box_square_smooth (a : ℝ) : ContDiff ℝ 2 (boxSquareObjective a) := by
  unfold boxSquareObjective; fun_prop

theorem box_square_convex (a : ℝ) : ConvexOn ℝ Set.univ (boxSquareObjective a) := by
  refine ⟨convex_univ,?_⟩
  intro p _ q _ s t hs ht hst
  have h := square_combination_le (p.2 0-a) (q.2 0-a) s t hs ht hst
  have heq : s*p.2 0+t*q.2 0-a = s*(p.2 0-a)+t*(q.2 0-a) := by
    calc
      _ = s*p.2 0+t*q.2 0-(s+t)*a := by rw [hst]; ring
      _ = _ := by ring
  simpa only [boxSquareObjective,Prod.snd_add,Prod.smul_snd,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,heq] using h

theorem box_square_root_minimum (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1) :
    IsMinimizer (region (boxModel 0 1) (intervalNode 0 1))
      (boxSquareObjective a) (purePoint a) := by
  refine ⟨(box_region_iff _ _ _ _ _).2 ⟨ha,hb⟩,?_⟩
  intro p _; simpa [boxSquareObjective,purePoint] using sq_nonneg (p.2 0-a)

theorem box_square_fixed_minimum (a y : ℝ) :
    IsMinimizer (region (boxModel 0 1) (intervalNode y y))
      (boxSquareObjective a) (purePoint y) := by
  refine ⟨(box_region_iff _ _ _ _ _).2 ⟨le_rfl,le_rfl⟩,?_⟩
  intro p hp
  have heq : p.2 0 = y := le_antisymm ((box_region_iff _ _ _ _ _).1 hp).2
    ((box_region_iff _ _ _ _ _).1 hp).1
  simp [boxSquareObjective,purePoint,heq]

def zeroModel (l r : ℕ) (g : Fin l → ℝ) (b : Fin r → ℝ) : ModelData 0 0 l r where
  g := fun j _ => g j
  A := fun _ => Fin.elim0
  B := fun _ => Fin.elim0
  rhs := b
  c1 := Fin.elim0
  c2 := Fin.elim0
  lo := Fin.elim0
  hi := Fin.elim0

def zeroPoint : Point 0 0 := (Fin.elim0,Fin.elim0)
def emptyModel := zeroModel 0 0 Fin.elim0 Fin.elim0
def constantRowModel (c : ℝ) := zeroModel 1 0 (fun _ => c) Fin.elim0
def impossibleAffineModel := zeroModel 0 1 Fin.elim0 (fun _ => -1)
def continuousBoxModel := boundedModel 0 0 Fin.elim0 1
def continuousPoint (x : ℝ) : Point 1 0 := (fun _ => x,Fin.elim0)

theorem zero_objective (l r : ℕ) (g : Fin l → ℝ) (b : Fin r → ℝ) (p : Point 0 0) :
    (zeroModel l r g b).objective p = 0 := by
  simp [ModelData.objective,LinearForm,zeroModel]

theorem zero_base_compact (l r : ℕ) (g : Fin l → ℝ) (b : Fin r → ℝ) :
    IsCompact ((zeroModel l r g b).linearRegion ∩ IntegerCylinder (n := 0)
      (zeroModel l r g b).lo (zeroModel l r g b).hi) := by
  exact Set.toFinite _ |>.isCompact

theorem zero_rows_smooth (l r : ℕ) (g : Fin l → ℝ) (b : Fin r → ℝ) :
    ∀ j, ContDiff ℝ 2 ((zeroModel l r g b).g j) := by
  intro j; exact contDiff_const

theorem zero_rows_convex (l r : ℕ) (g : Fin l → ℝ) (b : Fin r → ℝ) :
    ∀ j, ConvexOn ℝ Set.univ ((zeroModel l r g b).g j) := by
  intro j; exact convexOn_const _ convex_univ

theorem empty_model_minimum : IsMinimizer (region emptyModel (rootNode emptyModel))
    emptyModel.objective zeroPoint := by
  refine ⟨?_,fun _ _ => by simp [emptyModel,zero_objective]⟩
  simp [region,ContinuousRelaxation,ModelData.nonlinearRegion,ModelData.linearRegion,
    emptyModel,zeroModel,rootNode]

theorem constant_zero_minimum :
    IsMinimizer (region (constantRowModel 0) (rootNode (constantRowModel 0)))
      (constantRowModel 0).objective zeroPoint := by
  refine ⟨?_,fun _ _ => by simp [constantRowModel,zero_objective]⟩
  simp [region,ContinuousRelaxation,ModelData.nonlinearRegion,ModelData.linearRegion,
    constantRowModel,zeroModel,rootNode]

theorem constant_one_relaxation_empty :
    region (constantRowModel 1) (rootNode (constantRowModel 1)) = ∅ := by
  ext p
  simp [region,ContinuousRelaxation,ModelData.nonlinearRegion,constantRowModel,zeroModel]

theorem constant_one_base_nonempty : ((constantRowModel 1).linearRegion ∩
    IntegerCylinder (n := 0) (constantRowModel 1).lo (constantRowModel 1).hi).Nonempty := by
  refine ⟨zeroPoint,?_,Fin.elim0,?_,by funext i; exact Fin.elim0 i⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

theorem impossible_affine_relaxation_empty :
    region impossibleAffineModel (rootNode impossibleAffineModel) = ∅ := by
  ext p
  simp [region,ContinuousRelaxation,ModelData.linearRegion,LinearForm,
    impossibleAffineModel,zeroModel]

theorem continuous_box_region_iff (p : Point 1 0) :
    p ∈ region continuousBoxModel (rootNode continuousBoxModel) ↔
      0 ≤ p.1 0 ∧ p.1 0 ≤ 1 := by
  simp only [region,ContinuousRelaxation,Set.mem_setOf_eq]
  simp [continuousBoxModel,ModelData.nonlinearRegion,ModelData.linearRegion,
    LinearForm,boundedModel,rootNode,Fin.forall_fin_succ]

theorem continuous_box_minimum :
    IsMinimizer (region continuousBoxModel (rootNode continuousBoxModel))
      continuousBoxModel.objective (continuousPoint 0) := by
  refine ⟨(continuous_box_region_iff _).2 (by norm_num [continuousPoint]),?_⟩
  intro p hp
  simpa [continuousBoxModel,bounded_objective,continuousPoint] using
    ((continuous_box_region_iff _).1 hp).1

theorem feasible_nonoptimal_not_lower_bound :
    continuousPoint 1 ∈ region continuousBoxModel (rootNode continuousBoxModel) ∧
    ¬ IsMinimizer (region continuousBoxModel (rootNode continuousBoxModel))
      continuousBoxModel.objective (continuousPoint 1) ∧
    ¬ IsLowerBound (region continuousBoxModel (rootNode continuousBoxModel))
      continuousBoxModel.objective (continuousBoxModel.objective (continuousPoint 1)) := by
  refine ⟨(continuous_box_region_iff _).2 (by norm_num [continuousPoint]),?_,?_⟩
  · intro h
    have hh := h.2 _ continuous_box_minimum.1
    norm_num [continuousBoxModel,bounded_objective,continuousPoint] at hh

  · intro h
    have hh := h _ continuous_box_minimum.1
    norm_num [continuousBoxModel,bounded_objective,continuousPoint] at hh

theorem region_is_node_region {n m l r : ℕ} (d : ModelData n m l r) (N : BBNode m) :
    region d N = N.region d := rfl

theorem point_integer (x : ℝ) (z : ℤ) : BBIntegerPoint (point x (z:ℝ)) :=
  ⟨fun _ => z,rfl⟩

theorem pure_point_integer (z : ℤ) : BBIntegerPoint (purePoint (z:ℝ)) :=
  ⟨fun _ => z,rfl⟩

theorem no_integer_coordinates (n : ℕ) (p : Point n 0) : BBIntegerPoint p := by
  exact ⟨Fin.elim0,by funext i; exact Fin.elim0 i⟩

theorem quad_integer_point_feasible (a x : ℝ) (z : ℤ)
    (hq : point x (z:ℝ) ∈ region (quadModel a) (intervalNode 0 1)) :
    point x (z:ℝ) ∈ (quadModel a).feasibleOn Set.univ := by
  rw [← bb_root_feasible]
  exact (bb_feasible_mem_iff _ _ _).2 ⟨hq,point_integer x z⟩

theorem quad_binary (a : ℝ) (p : Point 1 1)
    (hp : p ∈ (quadModel a).feasibleOn Set.univ) : p.2 0 = 0 ∨ p.2 0 = 1 := by
  obtain ⟨_,_,_,y,hy,heq⟩ := (source_feasible_iff _ _ _).1 hp
  have hb := hy 0
  change 0 ≤ (y 0:ℝ) ∧ (y 0:ℝ) ≤ 1 at hb
  have h0 : (0:ℤ) ≤ y 0 := by exact_mod_cast hb.1
  have h1 : y 0 ≤ (1:ℤ) := by exact_mod_cast hb.2
  have he : y 0 = 0 ∨ y 0 = 1 := by omega
  rw [heq]
  rcases he with h | h <;> simp [h]

theorem quad_two_fifths_feasible :
    point (4/25) 0 ∈ (quadModel (2/5)).feasibleOn Set.univ ∧
    point (9/25) 1 ∈ (quadModel (2/5)).feasibleOn Set.univ := by
  constructor
  · simpa using quad_integer_point_feasible (2/5) (4/25) 0 ((quad_region_iff _ _ _ _).2 (by norm_num [point]))
  · simpa using quad_integer_point_feasible (2/5) (9/25) 1 ((quad_region_iff _ _ _ _).2 (by norm_num [point]))

theorem quad_two_fifths_global_minimum :
    IsMinimizer ((quadModel (2/5)).feasibleOn Set.univ) (quadModel (2/5)).objective
      (point (4/25) 0) := by
  refine ⟨quad_two_fifths_feasible.1,?_⟩
  intro p hp
  have hg := ((source_feasible_iff _ _ _).1 hp).2.1 (0:Fin 1)
  change (p.2 0-2/5)^2-p.1 0 ≤ 0 at hg
  simp only [quad_objective,point]
  rcases quad_binary _ p hp with h | h <;> rw [h] at hg <;> nlinarith

theorem integral_inferior_child_not_global_minimum :
    ¬ IsMinimizer ((quadModel (2/5)).feasibleOn Set.univ) (quadModel (2/5)).objective
      (point (9/25) 1) := by
  intro h
  have hh := h.2 _ quad_two_fifths_feasible.1
  norm_num [quad_objective,point] at hh

theorem quad_half_two_global_minima :
    IsMinimizer ((quadModel (1/2)).feasibleOn Set.univ) (quadModel (1/2)).objective
      (point (1/4) 0) ∧
    IsMinimizer ((quadModel (1/2)).feasibleOn Set.univ) (quadModel (1/2)).objective
      (point (1/4) 1) := by
  have hm (z : ℤ) (hz : z = 0 ∨ z = 1) :
      IsMinimizer ((quadModel (1/2)).feasibleOn Set.univ) (quadModel (1/2)).objective
        (point (1/4) (z:ℝ)) := by
    refine ⟨quad_integer_point_feasible _ _ z ?_,?_⟩
    · apply (quad_region_iff _ _ _ _).2
      rcases hz with rfl | rfl <;> norm_num [point]
    · intro p hp
      have hg := ((source_feasible_iff _ _ _).1 hp).2.1 (0:Fin 1)
      change (p.2 0-1/2)^2-p.1 0 ≤ 0 at hg
      simp only [quad_objective,point]
      rcases quad_binary _ p hp with h | h <;> rw [h] at hg <;> nlinarith
  simpa using And.intro (hm 0 (Or.inl rfl)) (hm 1 (Or.inr rfl))

theorem fake_warm_incumbent_rejected :
    point 0 0 ∉ (quadModel (2/5)).feasibleOn Set.univ ∧
    (quadModel (2/5)).objective (point 0 0) <
      (quadModel (2/5)).objective (point (4/25) 0) := by
  constructor
  · intro h
    have hg := ((source_feasible_iff _ _ _).1 h).2.1 (0:Fin 1)
    norm_num [quadModel,boundedModel,point] at hg
  · norm_num [quad_objective,point]

/-- These are the source hypotheses, including the unused convex C1 premises. -/
def SourcePremises {n m l r : ℕ} (d : ModelData n m l r) : Prop :=
  IsCompact (bbMixedBase d d.lo d.hi) ∧
  (∀ j, ConvexOn ℝ Set.univ (d.g j)) ∧ (∀ j, ContDiff ℝ 1 (d.g j))

theorem quad_source_premises (a : ℝ) : SourcePremises (quadModel a) :=
  ⟨quad_base_compact a,quad_convex a,fun j => (quad_smooth a j).of_le (by norm_num)⟩

theorem bookkeeping_source_premises : SourcePremises bookkeepingModel :=
  ⟨bookkeeping_base_compact,bookkeeping_convex,
    fun j => (bookkeeping_smooth j).of_le (by norm_num)⟩

theorem unattained_source_premises : SourcePremises unattainedModel :=
  ⟨unattained_base_compact,unattained_convex,
    fun j => (unattained_smooth j).of_le (by norm_num)⟩

theorem no_rows_source_premises {n m r : ℕ} (d : ModelData n m 0 r)
    (hc : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi)) :
    SourcePremises d := ⟨hc,(fun j => Fin.elim0 j),(fun j => Fin.elim0 j)⟩

theorem box_source_premises (L U : ℝ) : SourcePremises (boxModel L U) :=
  no_rows_source_premises _ (box_base_compact L U)

theorem band_source_premises : SourcePremises bandModel :=
  no_rows_source_premises _ band_base_compact

theorem accepted_unbounded_source_premises : SourcePremises OAEdgeExamples.badRelaxationModel :=
  no_rows_source_premises _ OAEdgeExamples.badRelaxation_compact

theorem strip_source_premises (α : ℝ) (ha : 0 ≤ α) : SourcePremises (stripModel α) :=
  no_rows_source_premises _ (strip_base_compact α ha)

theorem zero_source_premises (l r : ℕ) (g : Fin l → ℝ) (b : Fin r → ℝ) :
    SourcePremises (zeroModel l r g b) :=
  ⟨zero_base_compact l r g b,zero_rows_convex l r g b,
    fun j => (zero_rows_smooth l r g b j).of_le (by norm_num)⟩

theorem continuous_box_source_premises : SourcePremises continuousBoxModel :=
  no_rows_source_premises _ (bounded_base_compact _ _ _ _)

def intervalRecord (L U : ℝ) (v : WithBot ℝ) : BBRecord 1 :=
  ⟨intervalNode L U,v⟩

def splitState {n : ℕ} (v : ℝ) (inc : Option (Point n 1)) : BBState n 1 :=
  ⟨[intervalRecord 0 0 v,intervalRecord 1 1 v],inc⟩

def leftState {n : ℕ} (v : ℝ) (inc : Point n 1) : BBState n 1 :=
  ⟨[intervalRecord 0 0 v],some inc⟩

def doneState {n m : ℕ} (inc : Option (Point n m)) : BBState n m := ⟨[],inc⟩

theorem literal_interval_branch {n l r : ℕ} (d : ModelData n 1 l r)
    (f : Point n 1 → ℝ) (policy : BBPolicy) (pre post : List (BBRecord 1))
    (inc : Option (Point n 1)) (L U : ℝ) (v : WithBot ℝ) (q : Point n 1)
    (hq : IsMinimizer (region d (intervalNode L U)) f q)
    (hk : ¬ bbPrunable policy f inc (f q)) (hf : BBFractional (q.2 0)) :
    BBProcess d f policy ⟨pre ++ intervalRecord L U v :: post,inc⟩
      ⟨pre ++ [intervalRecord L (Int.floor (q.2 0)) (max v (f q)),
        intervalRecord (Int.ceil (q.2 0)) U (max v (f q))] ++ post,inc⟩ := by
  simpa only [bbChildren,intervalRecord,(interval_children L U (q.2 0)).1,
    (interval_children L U (q.2 0)).2] using
      (BBProcess.branch (d := d) (f := f) (policy := policy) (pre := pre) (post := post)
        (b := intervalRecord L U v) (inc := inc) 0 hq hk hf)

theorem quad_two_fifths_step1 (policy : BBPolicy) :
    BBProcess (quadModel (2/5)) (quadModel (2/5)).objective policy
      (bbInitial (quadModel (2/5)) none) (splitState 0 none) := by
  have h := literal_interval_branch (quadModel (2/5)) (quadModel (2/5)).objective
    policy [] [] none 0 1 ⊥ (point 0 (2/5)) quad_two_fifths_minima.1
      (by simp [bbPrunable])
      (fractional_between_integers (2/5) 0 (by norm_num) (by norm_num))
  norm_num [quad_objective,point] at h
  simpa [bbInitial,bbRootNode,quadModel,boundedModel,intervalNode,
    intervalRecord,splitState,point] using h

theorem quad_two_fifths_step2 (policy : BBPolicy) :
    BBProcess (quadModel (2/5)) (quadModel (2/5)).objective policy
      (splitState 0 none) (leftState 0 (point (9/25) 1)) := by
  have h := BBProcess.integral (d := quadModel (2/5)) (f := (quadModel (2/5)).objective)
    (policy := policy) (pre := [intervalRecord 0 0 0]) (post := [])
    (b := intervalRecord 1 1 0) (inc := none) quad_two_fifths_minima.2.2
    (by simp [bbPrunable]) (by simpa using point_integer (9/25) 1)
  simpa [splitState,leftState,bbUpdate] using h

theorem quad_two_fifths_step3 (policy : BBPolicy) :
    BBProcess (quadModel (2/5)) (quadModel (2/5)).objective policy
      (leftState 0 (point (9/25) 1)) (doneState (some (point (4/25) 0))) := by
  have hk : ¬ bbPrunable policy (quadModel (2/5)).objective
      (some (point (9/25) 1)) ((quadModel (2/5)).objective (point (4/25) 0)) := by
    cases policy <;> norm_num [bbPrunable,quad_objective,point]
  have h := BBProcess.integral (d := quadModel (2/5)) (f := (quadModel (2/5)).objective)
    (policy := policy) (pre := []) (post := []) (b := intervalRecord 0 0 0)
    (inc := some (point (9/25) 1)) quad_two_fifths_minima.2.1 hk
    (by simpa using point_integer (4/25) 0)
  have hu : bbUpdate policy (quadModel (2/5)).objective (some (point (9/25) 1))
      (point (4/25) 0) = some (point (4/25) 0) := by
    cases policy <;> norm_num [bbUpdate,quad_objective,point]
  simpa [leftState,doneState,hu] using h

theorem quad_half_step1 (policy : BBPolicy) :
    BBProcess (quadModel (1/2)) (quadModel (1/2)).objective policy
      (bbInitial (quadModel (1/2)) none) (splitState 0 none) := by
  have h := literal_interval_branch (quadModel (1/2)) (quadModel (1/2)).objective
    policy [] [] none 0 1 ⊥ (point 0 (1/2)) quad_half_minima.1
      (by simp [bbPrunable])
      (fractional_between_integers (1/2) 0 (by norm_num) (by norm_num))
  norm_num [quad_objective,point] at h
  simpa [bbInitial,bbRootNode,quadModel,boundedModel,intervalNode,
    intervalRecord,splitState,point] using h

theorem quad_half_step2 (policy : BBPolicy) :
    BBProcess (quadModel (1/2)) (quadModel (1/2)).objective policy
      (splitState 0 none) (leftState 0 (point (1/4) 1)) := by
  have h := BBProcess.integral (d := quadModel (1/2)) (f := (quadModel (1/2)).objective)
    (policy := policy) (pre := [intervalRecord 0 0 0]) (post := [])
    (b := intervalRecord 1 1 0) (inc := none) quad_half_minima.2.2
    (by simp [bbPrunable]) (by simpa using point_integer (1/4) 1)
  simpa [splitState,leftState,bbUpdate] using h

theorem tie_source_keeps_first :
    BBProcess (quadModel (1/2)) (quadModel (1/2)).objective .source
      (leftState 0 (point (1/4) 1)) (doneState (some (point (1/4) 1))) := by
  have h := BBProcess.integral (d := quadModel (1/2)) (f := (quadModel (1/2)).objective)
    (policy := .source) (pre := []) (post := []) (b := intervalRecord 0 0 0)
    (inc := some (point (1/4) 1)) quad_half_minima.2.1
    (by norm_num [bbPrunable,quad_objective,point]) (by simpa using point_integer (1/4) 0)
  simpa [leftState,doneState,bbUpdate,quad_objective,point] using h

theorem tie_algorithm_replaces_first :
    BBProcess (quadModel (1/2)) (quadModel (1/2)).objective .belottiAlgorithm
      (leftState 0 (point (1/4) 1)) (doneState (some (point (1/4) 0))) := by
  have h := BBProcess.integral (d := quadModel (1/2)) (f := (quadModel (1/2)).objective)
    (policy := .belottiAlgorithm) (pre := []) (post := []) (b := intervalRecord 0 0 0)
    (inc := some (point (1/4) 1)) quad_half_minima.2.1
    (by norm_num [bbPrunable,quad_objective,point]) (by simpa using point_integer (1/4) 0)
  simpa [leftState,doneState,bbUpdate,quad_objective,point] using h

theorem tie_weak_prunes_other_optimizer :
    BBProcess (quadModel (1/2)) (quadModel (1/2)).objective .weak
      (leftState 0 (point (1/4) 1)) (doneState (some (point (1/4) 1))) ∧
    IsMinimizer ((quadModel (1/2)).feasibleOn Set.univ) (quadModel (1/2)).objective
      (point (1/4) 0) := by
  refine ⟨?_,quad_half_two_global_minima.1⟩
  have h := BBProcess.prune (d := quadModel (1/2)) (f := (quadModel (1/2)).objective)
    (policy := .weak) (pre := []) (post := []) (b := intervalRecord 0 0 0)
    (inc := some (point (1/4) 1)) quad_half_minima.2.1
    (by norm_num [bbPrunable,quad_objective,point])
  simpa [leftState,doneState] using h

theorem quad_exact_potentials :
    bbPotential (bbInitial (quadModel (2/5)) none) = 3 ∧
    bbPotential (splitState (n := 1) 0 none) = 2 ∧
    bbPotential (leftState 0 (point (9/25) 1)) = 1 ∧
    bbPotential (doneState (some (point (4/25) 0))) = 0 := by
  norm_num [bbPotential,bbInitial,bbRootNode,quadModel,boundedModel,splitState,
    leftState,doneState,intervalRecord,intervalNode,BBNode.weight,BBNode.rank,BBNode.span]

theorem quad_exact_global_bounds :
    bbGlobalBound (quadModel (2/5)).objective (bbInitial (quadModel (2/5)) none) =
      ((⊥ : WithBot ℝ) : BBGlobalBound) ∧
    bbGlobalBound (quadModel (2/5)).objective (splitState 0 none) = bbValue 0 ∧
    bbGlobalBound (quadModel (2/5)).objective (leftState 0 (point (9/25) 1)) = bbValue 0 ∧
    bbGlobalBound (quadModel (2/5)).objective (doneState (some (point (4/25) 0))) =
      bbValue (4/25) := by
  norm_num [bbGlobalBound,bbIncBound,bbLiveBound,bbInitial,splitState,leftState,
    doneState,intervalRecord,bbValue,quad_objective,point]

theorem omitted_sibling_bound_false :
    ¬ IsLowerBound ((quadModel (2/5)).feasibleOn Set.univ) (quadModel (2/5)).objective (9/25) := by
  intro h
  have hh := h _ quad_two_fifths_feasible.1
  norm_num [quad_objective,point] at hh

theorem box_branch (L U y : ℝ) (hl : L ≤ y) (hu : y ≤ U) (hf : BBFractional y)
    (policy : BBPolicy) :
    BBProcess (boxModel L U) (boxModel L U).objective policy
      (bbInitial (boxModel L U) none)
      ⟨[intervalRecord L (Int.floor y) 0,intervalRecord (Int.ceil y) U 0],none⟩ := by
  have h := literal_interval_branch (boxModel L U) (boxModel L U).objective
    policy [] [] none L U ⊥ (purePoint y) (box_minimum L U L U y hl hu)
      (by simp [bbPrunable]) hf
  simpa [bbInitial,bbRootNode,boxModel,intervalRecord,intervalNode,purePoint,
    ModelData.objective,LinearForm] using h

theorem box_positive_step1 (policy : BBPolicy) :
    BBProcess (boxModel (1/5) (14/5)) (boxModel (1/5) (14/5)).objective policy
      (bbInitial (boxModel (1/5) (14/5)) none)
      ⟨[intervalRecord (1/5) 0 0,intervalRecord 1 (14/5) 0],none⟩ := by
  have h := box_branch (1/5) (14/5) (1/5) le_rfl (by norm_num)
    (fractional_between_integers (1/5) 0 (by norm_num) (by norm_num)) policy
  norm_num at h ⊢; exact h

theorem box_positive_step2 (policy : BBPolicy) :
    BBProcess (boxModel (1/5) (14/5)) (boxModel (1/5) (14/5)).objective policy
      ⟨[intervalRecord (1/5) 0 0,intervalRecord 1 (14/5) 0],none⟩
      ⟨[intervalRecord 1 (14/5) 0],none⟩ := by
  exact BBProcess.empty (pre := []) (post := [intervalRecord 1 (14/5) 0])
    (box_empty _ _ _ _ (by norm_num))

theorem box_positive_step3 (policy : BBPolicy) :
    BBProcess (boxModel (1/5) (14/5)) (boxModel (1/5) (14/5)).objective policy
      ⟨[intervalRecord 1 (14/5) 0],none⟩ (doneState (some (purePoint 1))) := by
  have h := BBProcess.integral (d := boxModel (1/5) (14/5))
    (f := (boxModel (1/5) (14/5)).objective) (policy := policy)
    (pre := []) (post := []) (b := intervalRecord 1 (14/5) 0) (inc := none)
    (box_minimum _ _ _ _ 1 le_rfl (by norm_num)) (by simp [bbPrunable])
    (by simpa using pure_point_integer 1)
  simpa [doneState,bbUpdate] using h

theorem box_negative_step1 (policy : BBPolicy) :
    BBProcess (boxModel (-14/5) (-1/5)) (boxModel (-14/5) (-1/5)).objective policy
      (bbInitial (boxModel (-14/5) (-1/5)) none)
      ⟨[intervalRecord (-14/5) (-1) 0,intervalRecord 0 (-1/5) 0],none⟩ := by
  have h := box_branch (-14/5) (-1/5) (-1/5) (by norm_num) le_rfl
    (fractional_between_integers (-1/5) (-1) (by norm_num) (by norm_num)) policy
  norm_num at h ⊢; exact h

theorem box_negative_step2 (policy : BBPolicy) :
    BBProcess (boxModel (-14/5) (-1/5)) (boxModel (-14/5) (-1/5)).objective policy
      ⟨[intervalRecord (-14/5) (-1) 0,intervalRecord 0 (-1/5) 0],none⟩
      ⟨[intervalRecord (-14/5) (-1) 0],none⟩ := by
  have h := BBProcess.empty (d := boxModel (-14/5) (-1/5))
    (f := (boxModel (-14/5) (-1/5)).objective) (policy := policy)
    (pre := [intervalRecord (-14/5) (-1) 0]) (post := [])
    (b := intervalRecord 0 (-1/5) 0) (inc := none)
    (box_empty _ _ _ _ (by norm_num))
  simpa using h

theorem box_negative_step3 (policy : BBPolicy) :
    BBProcess (boxModel (-14/5) (-1/5)) (boxModel (-14/5) (-1/5)).objective policy
      ⟨[intervalRecord (-14/5) (-1) 0],none⟩ (doneState (some (purePoint (-1)))) := by
  have h := BBProcess.integral (d := boxModel (-14/5) (-1/5))
    (f := (boxModel (-14/5) (-1/5)).objective) (policy := policy)
    (pre := []) (post := []) (b := intervalRecord (-14/5) (-1) 0) (inc := none)
    (box_minimum _ _ _ _ (-1) (by norm_num) le_rfl) (by simp [bbPrunable])
    (by simpa using pure_point_integer (-1))
  simpa [doneState,bbUpdate] using h

theorem band_step1 (policy : BBPolicy) :
    BBProcess bandModel bandModel.objective policy (bbInitial bandModel none) (splitState 0 none) := by
  have h := literal_interval_branch bandModel bandModel.objective policy [] [] none
    0 1 ⊥ (purePoint (1/2)) band_root_minimum (by simp [bbPrunable])
    (fractional_between_integers (1/2) 0 (by norm_num) (by norm_num))
  norm_num [band_objective,purePoint] at h
  simpa [bbInitial,bbRootNode,bandModel,intervalRecord,intervalNode,splitState,purePoint] using h

theorem band_step2 (policy : BBPolicy) :
    BBProcess bandModel bandModel.objective policy (splitState 0 none)
      ⟨[intervalRecord 1 1 0],none⟩ := by
  exact BBProcess.empty (pre := []) (post := [intervalRecord 1 1 0]) band_children_empty.1

theorem band_step3 (policy : BBPolicy) :
    BBProcess bandModel bandModel.objective policy ⟨[intervalRecord 1 1 0],none⟩
      (doneState none) := BBProcess.empty (pre := []) (post := []) band_children_empty.2

theorem fractional_empty_box_step1 (policy : BBPolicy) :
    BBProcess (boxModel (1/4) (3/4)) (boxModel (1/4) (3/4)).objective policy
      (bbInitial (boxModel (1/4) (3/4)) none)
      ⟨[intervalRecord (1/4) 0 0,intervalRecord 1 (3/4) 0],none⟩ := by
  have h := box_branch (1/4) (3/4) (1/2) (by norm_num) (by norm_num)
    (fractional_between_integers (1/2) 0 (by norm_num) (by norm_num)) policy
  norm_num at h ⊢; exact h

theorem fractional_empty_box_step2 (policy : BBPolicy) :
    BBProcess (boxModel (1/4) (3/4)) (boxModel (1/4) (3/4)).objective policy
      ⟨[intervalRecord (1/4) 0 0,intervalRecord 1 (3/4) 0],none⟩
      ⟨[intervalRecord 1 (3/4) 0],none⟩ :=
  BBProcess.empty (pre := []) (post := [intervalRecord 1 (3/4) 0])
    (box_empty _ _ _ _ (by norm_num))

theorem fractional_empty_box_step3 (policy : BBPolicy) :
    BBProcess (boxModel (1/4) (3/4)) (boxModel (1/4) (3/4)).objective policy
      ⟨[intervalRecord 1 (3/4) 0],none⟩ (doneState none) :=
  BBProcess.empty (pre := []) (post := []) (box_empty _ _ _ _ (by norm_num))

theorem contradictory_root_step (policy : BBPolicy) :
    BBProcess (boxModel 2 1) (boxModel 2 1).objective policy
      (bbInitial (boxModel 2 1) none) (doneState none) :=
  BBProcess.empty (pre := []) (post := []) (box_empty 2 1 2 1 (by norm_num))

theorem accepted_unbounded_step (policy : BBPolicy) :
    BBProcess OAEdgeExamples.badRelaxationModel OAEdgeExamples.badRelaxationModel.objective policy
      (bbInitial OAEdgeExamples.badRelaxationModel none) (doneState none) :=
  BBProcess.unbounded (pre := []) (post := []) accepted_unbounded_reply

theorem unattained_step (policy : BBPolicy) :
    BBProcess unattainedModel unattainedModel.objective policy
      (bbInitial unattainedModel none) (doneState none) := by
  obtain ⟨p,hp,_⟩ := unattained_small 1 (by norm_num)
  exact BBProcess.unattained (pre := []) (post := []) ⟨p,hp⟩
    ⟨0,unattained_finite_infimum.1⟩ unattained_no_minimum

theorem noncompact_false_infeasibility_step (policy : BBPolicy) :
    BBProcess noncompactModel noncompactModel.objective policy
      (bbInitial noncompactModel none) (doneState none) ∧
    (noncompactModel.feasibleOn Set.univ).Nonempty ∧
    ¬ IsCompact (bbMixedBase noncompactModel noncompactModel.lo noncompactModel.hi) :=
  ⟨BBProcess.unbounded (pre := []) (post := []) noncompact_relaxation_unbounded,
    ⟨point 0 0,noncompact_feasible_line 0⟩,noncompact_base_not_compact⟩

theorem strip_step1 (α : ℝ) (ha : 0 ≤ α) (policy : BBPolicy) :
    BBProcess (stripModel α) (stripModel α).objective policy (bbInitial (stripModel α) none)
      ⟨[intervalRecord (-1/5) (-1) ((-α/5 : ℝ)),intervalRecord 0 (6/5) ((-α/5 : ℝ))],none⟩ := by
  have h := literal_interval_branch (stripModel α) (stripModel α).objective policy [] [] none
    (-1/5) (6/5) ⊥ (point ((-α/5 : ℝ)) (-1/5)) (strip_root_minimum α ha)
    (by simp [bbPrunable])
    (fractional_between_integers (-1/5) (-1) (by norm_num) (by norm_num))
  norm_num [strip_objective,point] at h
  convert h using 1 <;> norm_num [bbInitial,bbRootNode,stripModel,intervalRecord,intervalNode]

theorem strip_step2 (α : ℝ) (policy : BBPolicy) :
    BBProcess (stripModel α) (stripModel α).objective policy
      ⟨[intervalRecord (-1/5) (-1) ((-α/5 : ℝ)),intervalRecord 0 (6/5) ((-α/5 : ℝ))],none⟩
      ⟨[intervalRecord 0 (6/5) ((-α/5 : ℝ))],none⟩ :=
  BBProcess.empty (pre := []) (post := [intervalRecord 0 (6/5) ((-α/5 : ℝ))]) (strip_left_empty α)

theorem strip_step3 (α : ℝ) (ha : 0 ≤ α) (policy : BBPolicy) :
    BBProcess (stripModel α) (stripModel α).objective policy
      ⟨[intervalRecord 0 (6/5) ((-α/5 : ℝ))],none⟩ (doneState (some (point 0 0))) := by
  have h := BBProcess.integral (d := stripModel α) (f := (stripModel α).objective)
    (policy := policy) (pre := []) (post := []) (b := intervalRecord 0 (6/5) ((-α/5 : ℝ)))
    (inc := none) (strip_right_minimum α ha) (by simp [bbPrunable])
    (by simpa using point_integer 0 0)
  simpa [doneState,bbUpdate] using h

theorem root_integral_step {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (policy : BBPolicy) (q : Point n m)
    (hq : IsMinimizer (region d (rootNode d)) f q) (hi : BBIntegerPoint q) :
    BBProcess d f policy (bbInitial d none) (doneState (some q)) := by
  have h := BBProcess.integral (d := d) (f := f) (policy := policy)
    (pre := []) (post := []) (b := ⟨bbRootNode d,⊥⟩) (inc := none) hq
    (by simp [bbPrunable]) hi
  simpa [bbInitial,doneState,bbUpdate] using h

theorem root_empty_step {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (policy : BBPolicy) (h : region d (rootNode d) = ∅) :
    BBProcess d f policy (bbInitial d none) (doneState none) :=
  BBProcess.empty (pre := []) (post := []) h

theorem all_zero_dimensions_step (policy : BBPolicy) :
    BBProcess emptyModel emptyModel.objective policy (bbInitial emptyModel none)
      (doneState (some zeroPoint)) :=
  root_integral_step _ _ _ _ empty_model_minimum (no_integer_coordinates _ _)

theorem present_zero_row_step (policy : BBPolicy) :
    BBProcess (constantRowModel 0) (constantRowModel 0).objective policy
      (bbInitial (constantRowModel 0) none) (doneState (some zeroPoint)) :=
  root_integral_step _ _ _ _ constant_zero_minimum (no_integer_coordinates _ _)

theorem constant_one_empty_step (policy : BBPolicy) :
    BBProcess (constantRowModel 1) (constantRowModel 1).objective policy
      (bbInitial (constantRowModel 1) none) (doneState none) :=
  root_empty_step _ _ _ constant_one_relaxation_empty

theorem impossible_affine_empty_step (policy : BBPolicy) :
    BBProcess impossibleAffineModel impossibleAffineModel.objective policy
      (bbInitial impossibleAffineModel none) (doneState none) :=
  root_empty_step _ _ _ impossible_affine_relaxation_empty

theorem continuous_box_step (policy : BBPolicy) :
    BBProcess continuousBoxModel continuousBoxModel.objective policy
      (bbInitial continuousBoxModel none) (doneState (some (continuousPoint 0))) :=
  root_integral_step _ _ _ _ continuous_box_minimum (no_integer_coordinates _ _)

theorem negative_fixed_integer_step (policy : BBPolicy) :
    BBProcess (boxModel (-2) (-2)) (boxModel (-2) (-2)).objective policy
      (bbInitial (boxModel (-2) (-2)) none) (doneState (some (purePoint (-2)))) :=
  root_integral_step _ _ _ _ (box_minimum _ _ _ _ (-2) le_rfl le_rfl)
    (by simpa using pure_point_integer (-2))

theorem quad_three_process_trace (policy : BBPolicy) :
    BBTrace (quadModel (2/5)) (quadModel (2/5)).objective policy 3
      (bbInitial (quadModel (2/5)) none) (doneState (some (point (4/25) 0))) :=
  .cons (quad_two_fifths_step1 policy) (.cons (quad_two_fifths_step2 policy)
    (.cons (quad_two_fifths_step3 policy) (.nil _)))

theorem tie_three_policy_traces :
    BBTrace (quadModel (1/2)) (quadModel (1/2)).objective .source 3
      (bbInitial (quadModel (1/2)) none) (doneState (some (point (1/4) 1))) ∧
    BBTrace (quadModel (1/2)) (quadModel (1/2)).objective .belottiAlgorithm 3
      (bbInitial (quadModel (1/2)) none) (doneState (some (point (1/4) 0))) ∧
    BBTrace (quadModel (1/2)) (quadModel (1/2)).objective .weak 3
      (bbInitial (quadModel (1/2)) none) (doneState (some (point (1/4) 1))) :=
  ⟨.cons (quad_half_step1 _) (.cons (quad_half_step2 _) (.cons tie_source_keeps_first (.nil _))),
    .cons (quad_half_step1 _) (.cons (quad_half_step2 _) (.cons tie_algorithm_replaces_first (.nil _))),
    .cons (quad_half_step1 _) (.cons (quad_half_step2 _) (.cons tie_weak_prunes_other_optimizer.1 (.nil _)))⟩

theorem positive_literal_box_trace (policy : BBPolicy) :
    BBTrace (boxModel (1/5) (14/5)) (boxModel (1/5) (14/5)).objective policy 3
      (bbInitial (boxModel (1/5) (14/5)) none) (doneState (some (purePoint 1))) :=
  .cons (box_positive_step1 _) (.cons (box_positive_step2 _) (.cons (box_positive_step3 _) (.nil _)))

theorem negative_literal_box_trace (policy : BBPolicy) :
    BBTrace (boxModel (-14/5) (-1/5)) (boxModel (-14/5) (-1/5)).objective policy 3
      (bbInitial (boxModel (-14/5) (-1/5)) none) (doneState (some (purePoint (-1)))) :=
  .cons (box_negative_step1 _) (.cons (box_negative_step2 _) (.cons (box_negative_step3 _) (.nil _)))

theorem affine_empty_children_trace (policy : BBPolicy) :
    BBTrace bandModel bandModel.objective policy 3
      (bbInitial bandModel none) (doneState none) :=
  .cons (band_step1 _) (.cons (band_step2 _) (.cons (band_step3 _) (.nil _)))

theorem contradictory_children_trace (policy : BBPolicy) :
    BBTrace (boxModel (1/4) (3/4)) (boxModel (1/4) (3/4)).objective policy 3
      (bbInitial (boxModel (1/4) (3/4)) none) (doneState none) :=
  .cons (fractional_empty_box_step1 _)
    (.cons (fractional_empty_box_step2 _) (.cons (fractional_empty_box_step3 _) (.nil _)))

theorem irrational_strip_trace (policy : BBPolicy) :
    BBTrace (stripModel (Real.sqrt 2)) (stripModel (Real.sqrt 2)).objective policy 3
      (bbInitial (stripModel (Real.sqrt 2)) none) (doneState (some (point 0 0))) :=
  .cons (strip_step1 _ (Real.sqrt_nonneg _) _)
    (.cons (strip_step2 _ _) (.cons (strip_step3 _ (Real.sqrt_nonneg _) _) (.nil _)))

/-- This uses the same full model with a separate nonlinear objective. -/
theorem nonlinear_objective_three_process_trace (policy : BBPolicy) :
    BBTrace (boxModel 0 1) (boxSquareObjective (2/5)) policy 3
      (bbInitial (boxModel 0 1) none) (doneState (some (purePoint 0))) := by
  have h1 : BBProcess (boxModel 0 1) (boxSquareObjective (2/5)) policy
      (bbInitial (boxModel 0 1) none) (splitState 0 none) := by
    have h := literal_interval_branch (boxModel 0 1) (boxSquareObjective (2/5))
      policy [] [] none 0 1 ⊥ (purePoint (2/5))
      (box_square_root_minimum _ (by norm_num) (by norm_num)) (by simp [bbPrunable])
      (fractional_between_integers (2/5) 0 (by norm_num) (by norm_num))
    norm_num [boxSquareObjective,purePoint] at h
    simpa [bbInitial,bbRootNode,boxModel,intervalRecord,intervalNode,splitState,purePoint] using h
  have h2 : BBProcess (boxModel 0 1) (boxSquareObjective (2/5)) policy
      (splitState 0 none) (leftState 0 (purePoint 1)) := by
    have h := BBProcess.integral (d := boxModel 0 1) (f := boxSquareObjective (2/5))
      (policy := policy) (pre := [intervalRecord 0 0 0]) (post := [])
      (b := intervalRecord 1 1 0) (inc := none) (box_square_fixed_minimum (2/5) 1)
      (by simp [bbPrunable]) (by simpa using pure_point_integer 1)
    simpa [splitState,leftState,bbUpdate] using h
  have h3 : BBProcess (boxModel 0 1) (boxSquareObjective (2/5)) policy
      (leftState 0 (purePoint 1)) (doneState (some (purePoint 0))) := by
    have hk : ¬ bbPrunable policy (boxSquareObjective (2/5)) (some (purePoint 1))
        (boxSquareObjective (2/5) (purePoint 0)) := by
      cases policy <;> norm_num [bbPrunable,boxSquareObjective,purePoint]
    have h := BBProcess.integral (d := boxModel 0 1) (f := boxSquareObjective (2/5))
      (policy := policy) (pre := []) (post := []) (b := intervalRecord 0 0 0)
      (inc := some (purePoint 1)) (box_square_fixed_minimum (2/5) 0) hk
      (by simpa using pure_point_integer 0)
    have hu : bbUpdate policy (boxSquareObjective (2/5)) (some (purePoint 1))
        (purePoint 0) = some (purePoint 0) := by
      cases policy <;> norm_num [bbUpdate,boxSquareObjective,purePoint]
    simpa [leftState,doneState,hu] using h
  exact .cons h1 (.cons h2 (.cons h3 (.nil _)))

def bookRecord (a b c d : ℝ) (v : ℝ) : BBRecord 2 := ⟨bookNode a b c d,v⟩
def bookS1 : BBState 1 2 := ⟨[bookRecord 0 0 0 1 0,bookRecord 1 1 0 1 0],none⟩
def bookS2 : BBState 1 2 :=
  ⟨[bookRecord 0 0 0 1 0,bookRecord 1 1 0 0 (9/25),bookRecord 1 1 1 1 (9/25)],none⟩
def bookS3 : BBState 1 2 :=
  ⟨[bookRecord 1 1 0 0 (9/25),bookRecord 1 1 1 1 (9/25)],some (bookPoint (4/25) 0 0)⟩
def bookS4 : BBState 1 2 :=
  ⟨[bookRecord 1 1 1 1 (9/25)],some (bookPoint (4/25) 0 0)⟩
def bookReset : BBState 1 2 :=
  ⟨[bookRecord 0 0 0 1 0,⟨bookNode 1 1 0 0,⊥⟩,⟨bookNode 1 1 1 1,⊥⟩],none⟩

theorem book_node_updates (a b c d v : ℝ) :
    (bookNode a b c d).left 0 v = bookNode a (Int.floor v) c d ∧
    (bookNode a b c d).right 0 v = bookNode (Int.ceil v) b c d ∧
    (bookNode a b c d).left 1 v = bookNode a b c (Int.floor v) ∧
    (bookNode a b c d).right 1 v = bookNode a b (Int.ceil v) d := by
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp only [BBNode.left,BBNode.right,bookNode] <;>
    congr 1 <;> funext i <;> fin_cases i <;> simp

theorem book_root_node : bbRootNode bookkeepingModel = bookNode 0 1 0 1 := by
  unfold bbRootNode bookkeepingModel boundedModel bookNode
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem book_point_integer (x : ℝ) (y z : ℤ) :
    BBIntegerPoint (bookPoint x (y:ℝ) (z:ℝ)) := by
  refine ⟨![y,z],?_⟩
  funext i; fin_cases i <;> rfl

theorem bookkeeping_step1 (policy : BBPolicy) :
    BBProcess bookkeepingModel bookkeepingModel.objective policy
      (bbInitial bookkeepingModel none) bookS1 := by
  have h := BBProcess.branch (d := bookkeepingModel) (f := bookkeepingModel.objective)
    (policy := policy) (pre := []) (post := []) (b := ⟨bookNode 0 1 0 1,⊥⟩)
    (inc := none) 0 bookkeeping_root_minimum (by simp [bbPrunable])
    (fractional_between_integers (2/5) 0 (by norm_num) (by norm_num))
  simp only [bbChildren,bookPoint,Matrix.cons_val_zero,bookkeeping_objective] at h
  rw [(book_node_updates 0 1 0 1 (2/5)).1,(book_node_updates 0 1 0 1 (2/5)).2.1] at h
  norm_num at h
  simpa [bbInitial,book_root_node,bookS1,bookRecord] using h

theorem bookkeeping_step2 (policy : BBPolicy) :
    BBProcess bookkeepingModel bookkeepingModel.objective policy bookS1 bookS2 := by
  have h := BBProcess.branch (d := bookkeepingModel) (f := bookkeepingModel.objective)
    (policy := policy) (pre := [bookRecord 0 0 0 1 0]) (post := [])
    (b := bookRecord 1 1 0 1 0) (inc := none) 1 bookkeeping_children_minima.2
    (by simp [bbPrunable])
    (fractional_between_integers (1/2) 0 (by norm_num) (by norm_num))
  simp only [bbChildren,bookRecord,bookPoint,Matrix.cons_val_one,Matrix.cons_val_zero,
    bookkeeping_objective] at h
  rw [(book_node_updates 1 1 0 1 (1/2)).2.2.1,(book_node_updates 1 1 0 1 (1/2)).2.2.2] at h
  norm_num at h
  simpa [bookS1,bookS2,bookRecord] using h

theorem bookkeeping_step3 (policy : BBPolicy) :
    BBProcess bookkeepingModel bookkeepingModel.objective policy bookS2 bookS3 := by
  have h := BBProcess.integral (d := bookkeepingModel) (f := bookkeepingModel.objective)
    (policy := policy) (pre := [])
    (post := [bookRecord 1 1 0 0 (9/25),bookRecord 1 1 1 1 (9/25)])
    (b := bookRecord 0 0 0 1 0) (inc := none) bookkeeping_children_minima.1
    (by simp [bbPrunable]) (by simpa using book_point_integer (4/25) 0 0)
  simpa [bookS2,bookS3,bbUpdate] using h

theorem bookkeeping_step4 (policy : BBPolicy) :
    BBProcess bookkeepingModel bookkeepingModel.objective policy bookS3 bookS4 := by
  have hp : bbPrunable policy bookkeepingModel.objective (some (bookPoint (4/25) 0 0))
      (bookkeepingModel.objective (bookPoint (61/100) 1 0)) := by
    cases policy <;> norm_num [bbPrunable,bookkeeping_objective,bookPoint]
  have h := BBProcess.prune (d := bookkeepingModel) (f := bookkeepingModel.objective)
    (policy := policy) (pre := []) (post := [bookRecord 1 1 1 1 (9/25)])
    (b := bookRecord 1 1 0 0 (9/25)) (inc := some (bookPoint (4/25) 0 0))
    (bookkeeping_grandchild_minimum 0 (Or.inl rfl)) hp
  simpa [bookS3,bookS4] using h

theorem bookkeeping_step5 (policy : BBPolicy) :
    BBProcess bookkeepingModel bookkeepingModel.objective policy bookS4
      (doneState (some (bookPoint (4/25) 0 0))) := by
  have hp : bbPrunable policy bookkeepingModel.objective (some (bookPoint (4/25) 0 0))
      (bookkeepingModel.objective (bookPoint (61/100) 1 1)) := by
    cases policy <;> norm_num [bbPrunable,bookkeeping_objective,bookPoint]
  have h := BBProcess.prune (d := bookkeepingModel) (f := bookkeepingModel.objective)
    (policy := policy) (pre := []) (post := []) (b := bookRecord 1 1 1 1 (9/25))
    (inc := some (bookPoint (4/25) 0 0))
    (bookkeeping_grandchild_minimum 1 (Or.inr rfl)) hp
  simpa [bookS4,doneState] using h

theorem bookkeeping_five_process_trace (policy : BBPolicy) :
    BBTrace bookkeepingModel bookkeepingModel.objective policy 5
      (bbInitial bookkeepingModel none) (doneState (some (bookPoint (4/25) 0 0))) :=
  .cons (bookkeeping_step1 _) (.cons (bookkeeping_step2 _) (.cons (bookkeeping_step3 _)
    (.cons (bookkeeping_step4 _) (.cons (bookkeeping_step5 _) (.nil _)))))

theorem bookkeeping_exact_potentials :
    bbPotential (bbInitial bookkeepingModel none) = 7 ∧
    bbPotential bookS1 = 6 ∧ bbPotential bookS2 = 5 ∧ bbPotential bookS3 = 2 ∧
    bbPotential bookS4 = 1 ∧ bbPotential (doneState (some (bookPoint (4/25) 0 0))) = 0 := by
  norm_num [bbPotential,bbInitial,book_root_node,bookS1,bookS2,bookS3,bookS4,
    doneState,bookRecord,bookNode,BBNode.weight,BBNode.rank,BBNode.span,Fin.sum_univ_two]

theorem bookkeeping_exact_global_bounds :
    bbGlobalBound bookkeepingModel.objective bookS1 = bbValue 0 ∧
    bbGlobalBound bookkeepingModel.objective bookS2 = bbValue 0 ∧
    bbGlobalBound bookkeepingModel.objective bookS3 = bbValue (4/25) ∧
    bbGlobalBound bookkeepingModel.objective bookS4 = bbValue (4/25) ∧
    bbGlobalBound bookkeepingModel.objective (doneState (some (bookPoint (4/25) 0 0))) =
      bbValue (4/25) := by
  norm_num [bbGlobalBound,bbIncBound,bbLiveBound,bookS1,bookS2,bookS3,bookS4,
    doneState,bookRecord,bbValue,bookkeeping_objective,bookPoint]

theorem bookkeeping_incumbent_feasible :
    bookPoint (4/25) 0 0 ∈ bookkeepingModel.feasibleOn Set.univ := by
  rw [← bb_root_feasible]
  apply (bb_feasible_mem_iff _ _ _).2
  refine ⟨?_,by simpa using book_point_integer (4/25) 0 0⟩
  rw [book_root_node]
  apply (bookkeeping_region_iff _ _ _ _ _).2
  norm_num [bookPoint]

theorem omitted_incumbent_bound_false :
    bbLiveBound bookS3.live = bbValue (9/25) ∧
    ¬ IsLowerBound (bookkeepingModel.feasibleOn Set.univ) bookkeepingModel.objective (9/25) := by
  constructor
  · norm_num [bbLiveBound,bookS3,bookRecord,bbValue]
  · intro h
    have hh := h _ bookkeeping_incumbent_feasible
    norm_num [bookkeeping_objective,bookPoint] at hh

/-- Resetting both children to unknown changes the process and can lower G. -/
theorem reset_bound_decreases :
    bbGlobalBound bookkeepingModel.objective bookReset <
      bbGlobalBound bookkeepingModel.objective bookS1 ∧
    bbGlobalBound bookkeepingModel.objective bookS1 ≤
      bbGlobalBound bookkeepingModel.objective bookS2 := by
  rw [bookkeeping_exact_global_bounds.1,bookkeeping_exact_global_bounds.2.1]
  norm_num [bbGlobalBound,bbIncBound,bbLiveBound,bookReset,bookRecord,bbValue]
  exact (WithTop.coe_lt_coe).2 (WithBot.bot_lt_coe (0:ℝ))

theorem constant_tie_warm_feasible :
    purePoint 0 ∈ (boxModel 0 1).feasibleOn Set.univ := by
  rw [← bb_root_feasible]
  exact (bb_feasible_mem_iff _ _ _).2
    ⟨(box_minimum 0 1 0 1 0 le_rfl (by norm_num)).1,by simpa using pure_point_integer 0⟩

theorem constant_fractional_tie_three_steps :
    BBTrace (boxModel 0 1) (boxModel 0 1).objective .source 3
      (bbInitial (boxModel 0 1) (some (purePoint 0))) (doneState (some (purePoint 0))) := by
  have h1 : BBProcess (boxModel 0 1) (boxModel 0 1).objective .source
      (bbInitial (boxModel 0 1) (some (purePoint 0))) (splitState 0 (some (purePoint 0))) := by
    have h := literal_interval_branch (boxModel 0 1) (boxModel 0 1).objective
      .source [] [] (some (purePoint 0)) 0 1 ⊥ (purePoint (1/2))
      (box_minimum 0 1 0 1 (1/2) (by norm_num) (by norm_num))
      (by simp [bbPrunable,box_objective])
      (fractional_between_integers (1/2) 0 (by norm_num) (by norm_num))
    norm_num [box_objective,purePoint] at h
    simpa [bbInitial,bbRootNode,boxModel,intervalRecord,intervalNode,splitState,purePoint] using h
  have h2 : BBProcess (boxModel 0 1) (boxModel 0 1).objective .source
      (splitState 0 (some (purePoint 0))) (leftState 0 (purePoint 0)) := by
    have h := BBProcess.integral (d := boxModel 0 1) (f := (boxModel 0 1).objective)
      (policy := .source) (pre := [intervalRecord 0 0 0]) (post := [])
      (b := intervalRecord 1 1 0) (inc := some (purePoint 0))
      (box_minimum 0 1 1 1 1 le_rfl le_rfl) (by simp [bbPrunable,box_objective])
      (by simpa using pure_point_integer 1)
    simpa [splitState,leftState,bbUpdate,box_objective] using h
  have h3 : BBProcess (boxModel 0 1) (boxModel 0 1).objective .source
      (leftState 0 (purePoint 0)) (doneState (some (purePoint 0))) := by
    have h := BBProcess.integral (d := boxModel 0 1) (f := (boxModel 0 1).objective)
      (policy := .source) (pre := []) (post := []) (b := intervalRecord 0 0 0)
      (inc := some (purePoint 0)) (box_minimum 0 1 0 0 0 le_rfl le_rfl)
      (by simp [bbPrunable,box_objective]) (by simpa using pure_point_integer 0)
    simpa [leftState,doneState,bbUpdate,box_objective] using h
  exact .cons h1 (.cons h2 (.cons h3 (.nil _)))

theorem constant_tie_weak_one_step :
    BBTrace (boxModel 0 1) (boxModel 0 1).objective .weak 1
      (bbInitial (boxModel 0 1) (some (purePoint 0))) (doneState (some (purePoint 0))) := by
  have h := BBProcess.prune (d := boxModel 0 1) (f := (boxModel 0 1).objective)
    (policy := .weak) (pre := []) (post := []) (b := ⟨bbRootNode (boxModel 0 1),⊥⟩)
    (inc := some (purePoint 0)) (box_minimum 0 1 0 1 (1/2) (by norm_num) (by norm_num))
    (by simp [bbPrunable,box_objective])
  exact .cons h (.nil _)

theorem constant_tie_integral_choice_one_step :
    BBTrace (boxModel 0 1) (boxModel 0 1).objective .source 1
      (bbInitial (boxModel 0 1) none) (doneState (some (purePoint 0))) :=
  .cons (root_integral_step _ _ _ _ (box_minimum 0 1 0 1 0 le_rfl (by norm_num))
    (by simpa using pure_point_integer 0)) (.nil _)

/-- The duplicate start is a separate raw-state test, not the standard initializer. -/
theorem duplicate_occurrences_two_steps :
    BBTrace emptyModel emptyModel.objective .source 2
      ⟨[⟨bbRootNode emptyModel,⊥⟩,⟨bbRootNode emptyModel,⊥⟩],none⟩
      (doneState (some zeroPoint)) := by
  have h1 := BBProcess.integral (d := emptyModel) (f := emptyModel.objective)
    (policy := .source) (pre := []) (post := [⟨bbRootNode emptyModel,⊥⟩])
    (b := ⟨bbRootNode emptyModel,⊥⟩) (inc := none) empty_model_minimum
    (by simp [bbPrunable]) (no_integer_coordinates _ _)
  have h2 := BBProcess.integral (d := emptyModel) (f := emptyModel.objective)
    (policy := .source) (pre := []) (post := []) (b := ⟨bbRootNode emptyModel,⊥⟩)
    (inc := some zeroPoint) empty_model_minimum
    (by simp [bbPrunable]) (no_integer_coordinates _ _)
  have hu : bbUpdate .source emptyModel.objective (some zeroPoint) zeroPoint = some zeroPoint := by
    simp [bbUpdate]
  simpa [bbUpdate,hu,doneState] using BBTrace.cons h1 (BBTrace.cons h2 (.nil _))

theorem source_trace_minimum {n m l r : ℕ} (d : ModelData n m l r) (policy : BBPolicy)
    (hp : SourcePremises d) {k : ℕ} {q : Point n m}
    (ht : BBTrace d d.objective policy k (bbInitial d none) (doneState (some q))) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective q := by
  exact bb_reachable_empty_live_optimal d d.objective policy none (by simp) hp.1
    (fun j => (hp.2.2 j).continuous) (linearForm_continuous _ _).continuousOn
    (bb_trace_reachable d d.objective policy none .initial ht) rfl q rfl

theorem source_trace_infeasible {n m l r : ℕ} (d : ModelData n m l r) (policy : BBPolicy)
    (hp : SourcePremises d) {k : ℕ}
    (ht : BBTrace d d.objective policy k (bbInitial d none) (doneState none)) :
    d.feasibleOn Set.univ = ∅ := by
  exact bb_reachable_empty_live_infeasible d d.objective policy none (by simp) hp.1
    (fun j => (hp.2.2 j).continuous) (linearForm_continuous _ _).continuousOn
    (bb_trace_reachable d d.objective policy none .initial ht) rfl rfl

theorem quad_full_model_trace_return (policy : BBPolicy) :
    SourcePremises (quadModel (2/5)) ∧
    BBTrace (quadModel (2/5)) (quadModel (2/5)).objective policy 3
      (bbInitial (quadModel (2/5)) none) (doneState (some (point (4/25) 0))) ∧
    IsMinimizer ((quadModel (2/5)).feasibleOn Set.univ) (quadModel (2/5)).objective
      (point (4/25) 0) :=
  ⟨quad_source_premises _,quad_three_process_trace _,
    source_trace_minimum _ policy (quad_source_premises _) (quad_three_process_trace policy)⟩

theorem literal_boxes_full_trace_returns (policy : BBPolicy) :
    IsMinimizer ((boxModel (1/5) (14/5)).feasibleOn Set.univ)
      (boxModel (1/5) (14/5)).objective (purePoint 1) ∧
    IsMinimizer ((boxModel (-14/5) (-1/5)).feasibleOn Set.univ)
      (boxModel (-14/5) (-1/5)).objective (purePoint (-1)) :=
  ⟨source_trace_minimum _ policy (box_source_premises _ _) (positive_literal_box_trace _),
    source_trace_minimum _ policy (box_source_premises _ _) (negative_literal_box_trace _)⟩

theorem two_empty_routes_full_trace_returns (policy : BBPolicy) :
    bandModel.feasibleOn Set.univ = ∅ ∧ (boxModel (1/4) (3/4)).feasibleOn Set.univ = ∅ ∧
    (boxModel 2 1).feasibleOn Set.univ = ∅ :=
  ⟨source_trace_infeasible _ policy band_source_premises (affine_empty_children_trace _),
    source_trace_infeasible _ policy (box_source_premises _ _) (contradictory_children_trace _),
    source_trace_infeasible _ policy (box_source_premises _ _) (.cons (contradictory_root_step _) (.nil _))⟩

theorem bad_status_full_trace_returns (policy : BBPolicy) :
    SourcePremises OAEdgeExamples.badRelaxationModel ∧ SourcePremises unattainedModel ∧
    BBTrace OAEdgeExamples.badRelaxationModel OAEdgeExamples.badRelaxationModel.objective policy 1
      (bbInitial OAEdgeExamples.badRelaxationModel none) (doneState none) ∧
    BBTrace unattainedModel unattainedModel.objective policy 1
      (bbInitial unattainedModel none) (doneState none) ∧
    OAEdgeExamples.badRelaxationModel.feasibleOn Set.univ = ∅ ∧
    unattainedModel.feasibleOn Set.univ = ∅ :=
  ⟨accepted_unbounded_source_premises,unattained_source_premises,
    .cons (accepted_unbounded_step _) (.nil _),.cons (unattained_step _) (.nil _),
    source_trace_infeasible _ policy accepted_unbounded_source_premises
      (.cons (accepted_unbounded_step _) (.nil _)),
    source_trace_infeasible _ policy unattained_source_premises (.cons (unattained_step _) (.nil _))⟩

theorem irrational_strip_full_trace_return (policy : BBPolicy) :
    SourcePremises (stripModel (Real.sqrt 2)) ∧
    IsMinimizer ((stripModel (Real.sqrt 2)).feasibleOn Set.univ)
      (stripModel (Real.sqrt 2)).objective (point 0 0) :=
  ⟨strip_source_premises _ (Real.sqrt_nonneg _),source_trace_minimum _ policy
    (strip_source_premises _ (Real.sqrt_nonneg _)) (irrational_strip_trace _)⟩

theorem bookkeeping_full_model_trace_return (policy : BBPolicy) :
    SourcePremises bookkeepingModel ∧
    IsMinimizer (bookkeepingModel.feasibleOn Set.univ) bookkeepingModel.objective
      (bookPoint (4/25) 0 0) :=
  ⟨bookkeeping_source_premises,source_trace_minimum _ policy bookkeeping_source_premises
    (bookkeeping_five_process_trace _)⟩

theorem nonlinear_objective_full_trace_return (policy : BBPolicy) :
    IsMinimizer ((boxModel 0 1).feasibleOn Set.univ) (boxSquareObjective (2/5)) (purePoint 0) :=
  bb_reachable_empty_live_optimal (boxModel 0 1) (boxSquareObjective (2/5)) policy none (by simp)
    (box_source_premises 0 1).1 (fun j => Fin.elim0 j) (box_square_smooth _).continuous.continuousOn
    (bb_trace_reachable _ _ _ none .initial (nonlinear_objective_three_process_trace policy))
    rfl _ rfl

theorem all_zero_edge_counted_traces (policy : BBPolicy) :
    BBTrace emptyModel emptyModel.objective policy 1
      (bbInitial emptyModel none) (doneState (some zeroPoint)) ∧
    BBTrace (constantRowModel 0) (constantRowModel 0).objective policy 1
      (bbInitial (constantRowModel 0) none) (doneState (some zeroPoint)) ∧
    BBTrace (constantRowModel 1) (constantRowModel 1).objective policy 1
      (bbInitial (constantRowModel 1) none) (doneState none) ∧
    BBTrace impossibleAffineModel impossibleAffineModel.objective policy 1
      (bbInitial impossibleAffineModel none) (doneState none) ∧
    BBTrace continuousBoxModel continuousBoxModel.objective policy 1
      (bbInitial continuousBoxModel none) (doneState (some (continuousPoint 0))) ∧
    BBTrace (boxModel (-2) (-2)) (boxModel (-2) (-2)).objective policy 1
      (bbInitial (boxModel (-2) (-2)) none) (doneState (some (purePoint (-2)))) :=
  ⟨.cons (all_zero_dimensions_step _) (.nil _),.cons (present_zero_row_step _) (.nil _),
    .cons (constant_one_empty_step _) (.nil _),.cons (impossible_affine_empty_step _) (.nil _),
    .cons (continuous_box_step _) (.nil _),.cons (negative_fixed_integer_step _) (.nil _)⟩

theorem all_zero_edge_source_returns (policy : BBPolicy) :
    IsMinimizer (emptyModel.feasibleOn Set.univ) emptyModel.objective zeroPoint ∧
    IsMinimizer ((constantRowModel 0).feasibleOn Set.univ) (constantRowModel 0).objective zeroPoint ∧
    (constantRowModel 1).feasibleOn Set.univ = ∅ ∧
    impossibleAffineModel.feasibleOn Set.univ = ∅ ∧
    IsMinimizer (continuousBoxModel.feasibleOn Set.univ) continuousBoxModel.objective (continuousPoint 0) ∧
    IsMinimizer ((boxModel (-2) (-2)).feasibleOn Set.univ) (boxModel (-2) (-2)).objective (purePoint (-2)) :=
  ⟨source_trace_minimum _ policy (zero_source_premises _ _ _ _)
      (all_zero_edge_counted_traces policy).1,
    source_trace_minimum _ policy (zero_source_premises _ _ _ _)
      (all_zero_edge_counted_traces policy).2.1,
    source_trace_infeasible _ policy (zero_source_premises _ _ _ _)
      (all_zero_edge_counted_traces policy).2.2.1,
    source_trace_infeasible _ policy (zero_source_premises _ _ _ _)
      (all_zero_edge_counted_traces policy).2.2.2.1,
    source_trace_minimum _ policy continuous_box_source_premises
      (all_zero_edge_counted_traces policy).2.2.2.2.1,
    source_trace_minimum _ policy (box_source_premises _ _)
      (all_zero_edge_counted_traces policy).2.2.2.2.2⟩

theorem literal_box_integer_contents (z : ℤ) :
    ((1/5:ℝ) ≤ (z:ℝ) ∧ (z:ℝ) ≤ 14/5 ↔ z = 1 ∨ z = 2) ∧
    ((1:ℝ) ≤ (z:ℝ) ∧ (z:ℝ) ≤ 14/5 ↔ z = 1 ∨ z = 2) ∧
    ((-14/5:ℝ) ≤ (z:ℝ) ∧ (z:ℝ) ≤ -1/5 ↔ z = -2 ∨ z = -1) ∧
    ((-14/5:ℝ) ≤ (z:ℝ) ∧ (z:ℝ) ≤ -1 ↔ z = -2 ∨ z = -1) := by
  have pos (L : ℝ) (hL : 0 < L) (h1 : L ≤ 1) :
      (L ≤ (z:ℝ) ∧ (z:ℝ) ≤ 14/5 ↔ z = 1 ∨ z = 2) := by
    constructor
    · rintro ⟨hl,hu⟩
      have hh0 : (0:ℤ) < z := by exact_mod_cast hL.trans_le hl
      have hh3 : z < (3:ℤ) := by exact_mod_cast (by linarith : (z:ℝ) < 3)
      omega
    · rintro (rfl | rfl) <;> norm_num <;> linarith
  have neg (U : ℝ) (hU : U < 0) (hm1 : -1 ≤ U) :
      ((-14/5:ℝ) ≤ (z:ℝ) ∧ (z:ℝ) ≤ U ↔ z = -2 ∨ z = -1) := by
    constructor
    · rintro ⟨hl,hu⟩
      have hh0 : z < (0:ℤ) := by exact_mod_cast hu.trans_lt hU
      have hh3 : (-3:ℤ) < z := by exact_mod_cast (by linarith : (-3:ℝ) < (z:ℝ))
      omega
    · rintro (rfl | rfl) <;> norm_num <;> linarith
  exact ⟨pos _ (by norm_num) (by norm_num),pos _ (by norm_num) le_rfl,
    neg _ (by norm_num) (by norm_num),neg _ (by norm_num) le_rfl⟩

theorem literal_bound_counts_are_not_integer_cardinality :
    (intervalNode (1/5) (14/5)).weight = 15 ∧
    (intervalNode (1/5) 0).weight = 1 ∧ (intervalNode 1 (14/5)).weight = 7 ∧
    (intervalNode (-14/5) (-1/5)).weight = 15 ∧
    (intervalNode (-14/5) (-1)).weight = 7 ∧ (intervalNode 0 (-1/5)).weight = 1 := by
  norm_num [BBNode.weight,BBNode.rank,BBNode.span,intervalNode,Fin.sum_univ_one]

theorem empty_dimension_potentials :
    bbPotential (bbInitial emptyModel none) = 1 ∧
    bbPotential (bbInitial continuousBoxModel none) = 1 ∧
    bbPotential (bbInitial (constantRowModel 0) none) = 1 ∧
    bbPotential (bbInitial (constantRowModel 1) none) = 1 ∧
    bbPotential (bbInitial impossibleAffineModel none) = 1 ∧
    bbPotential (bbInitial (boxModel (-2) (-2)) none) = 1 := by
  norm_num [bbPotential,bbInitial,bbRootNode,emptyModel,continuousBoxModel,
    constantRowModel,impossibleAffineModel,zeroModel,boundedModel,boxModel,
    BBNode.weight,BBNode.rank,BBNode.span,Fin.sum_univ_one]

theorem bookkeeping_prefix_reachable (policy : BBPolicy) :
    BBReachable bookkeepingModel bookkeepingModel.objective policy none bookS1 ∧
    BBReachable bookkeepingModel bookkeepingModel.objective policy none bookS2 ∧
    BBReachable bookkeepingModel bookkeepingModel.objective policy none bookS3 :=
  ⟨.next .initial (bookkeeping_step1 policy),
    .next (.next .initial (bookkeeping_step1 policy)) (bookkeeping_step2 policy),
    .next (.next (.next .initial (bookkeeping_step1 policy)) (bookkeeping_step2 policy))
      (bookkeeping_step3 policy)⟩

theorem reset_is_not_a_legal_process (policy : BBPolicy) :
    ¬ BBProcess bookkeepingModel bookkeepingModel.objective policy bookS1 bookReset := by
  intro h
  have hinv := bb_reachable_invariant bookkeepingModel bookkeepingModel.objective policy none
    (by simp) bookkeeping_source_premises.1
    (fun j => (bookkeeping_source_premises.2.2 j).continuous)
    (linearForm_continuous _ _).continuousOn (bookkeeping_prefix_reachable policy).1
  exact (not_le_of_gt reset_bound_decreases.1)
    (bb_process_global_bound_mono _ _ _ hinv h)

/-- Atomic selection retains this occurrence until its exact reply is processed. -/
theorem selected_working_node_omission_false (policy : BBPolicy) :
    BBReachable (quadModel (2/5)) (quadModel (2/5)).objective policy none
      (leftState 0 (point (9/25) 1)) ∧
    (leftState 0 (point (9/25) 1)).live = [intervalRecord 0 0 0] ∧
    bbGlobalBound (quadModel (2/5)).objective (doneState (some (point (9/25) 1))) = bbValue (9/25) ∧
    ¬ IsLowerBound ((quadModel (2/5)).feasibleOn Set.univ) (quadModel (2/5)).objective (9/25) := by
  refine ⟨.next (.next .initial (quad_two_fifths_step1 policy)) (quad_two_fifths_step2 policy),
    rfl,?_,omitted_sibling_bound_false⟩
  simp [bbGlobalBound,bbIncBound,bbLiveBound,doneState,quad_objective,point]

theorem nonoptimal_point_cannot_supply_exact_reply :
    BBIntegerPoint (continuousPoint 1) ∧
    continuousPoint 1 ∈ (bbRootNode continuousBoxModel).region continuousBoxModel ∧
    ¬ IsMinimizer ((bbRootNode continuousBoxModel).region continuousBoxModel)
      continuousBoxModel.objective (continuousPoint 1) :=
  ⟨no_integer_coordinates _ _,feasible_nonoptimal_not_lower_bound.1,
    feasible_nonoptimal_not_lower_bound.2.1⟩

theorem strip_derived_continuous_compact (α : ℝ) (ha : 0 ≤ α) :
    IsCompact (bbAffineRelaxation (stripModel α) (stripModel α).lo (stripModel α).hi) :=
  bb_affine_relaxation_compact _ _ _ (strip_base_compact α ha) (strip_base_nonempty α)

theorem quad_warm_incumbent_three_steps :
    BBTrace (quadModel (2/5)) (quadModel (2/5)).objective .source 3
      (bbInitial (quadModel (2/5)) (some (point (9/25) 1)))
      (doneState (some (point (4/25) 0))) := by
  have h1 : BBProcess (quadModel (2/5)) (quadModel (2/5)).objective .source
      (bbInitial (quadModel (2/5)) (some (point (9/25) 1)))
      (splitState 0 (some (point (9/25) 1))) := by
    have h := literal_interval_branch (quadModel (2/5)) (quadModel (2/5)).objective
      .source [] [] (some (point (9/25) 1)) 0 1 ⊥ (point 0 (2/5)) quad_two_fifths_minima.1
      (by norm_num [bbPrunable,quad_objective,point])
      (fractional_between_integers (2/5) 0 (by norm_num) (by norm_num))
    norm_num [quad_objective,point] at h
    simpa [bbInitial,bbRootNode,quadModel,boundedModel,intervalNode,intervalRecord,splitState,point] using h
  have h2 : BBProcess (quadModel (2/5)) (quadModel (2/5)).objective .source
      (splitState 0 (some (point (9/25) 1))) (leftState 0 (point (9/25) 1)) := by
    have h := BBProcess.integral (d := quadModel (2/5)) (f := (quadModel (2/5)).objective)
      (policy := .source) (pre := [intervalRecord 0 0 0]) (post := [])
      (b := intervalRecord 1 1 0) (inc := some (point (9/25) 1)) quad_two_fifths_minima.2.2
      (by simp [bbPrunable]) (by simpa using point_integer (9/25) 1)
    simpa [splitState,leftState,bbUpdate] using h
  exact .cons h1 (.cons h2 (.cons (quad_two_fifths_step3 .source) (.nil _)))

theorem quad_warm_trace_return :
    IsMinimizer ((quadModel (2/5)).feasibleOn Set.univ) (quadModel (2/5)).objective
      (point (4/25) 0) := by
  have hw : ∀ p, some (point (9/25) 1) = some p → p ∈ (quadModel (2/5)).feasibleOn Set.univ := by
    intro p hp
    cases Option.some.inj hp
    exact quad_two_fifths_feasible.2
  exact bb_reachable_empty_live_optimal _ _ .source (some (point (9/25) 1)) hw
    (quad_source_premises (2/5)).1 (fun j => ((quad_source_premises (2/5)).2.2 j).continuous)
    (linearForm_continuous _ _).continuousOn
    (bb_trace_reachable _ _ .source _ .initial quad_warm_incumbent_three_steps) rfl _ rfl

theorem fractional_box_potentials :
    bbPotential (bbInitial (boxModel (1/5) (14/5)) none) = 15 ∧
    bbPotential (⟨[intervalRecord (1/5) 0 0,intervalRecord 1 (14/5) 0],none⟩ : BBState 0 1) = 8 ∧
    bbPotential (⟨[intervalRecord 1 (14/5) 0],none⟩ : BBState 0 1) = 7 ∧
    bbPotential (bbInitial (boxModel (-14/5) (-1/5)) none) = 15 ∧
    bbPotential (⟨[intervalRecord (-14/5) (-1) 0,intervalRecord 0 (-1/5) 0],none⟩ : BBState 0 1) = 8 ∧
    bbPotential (⟨[intervalRecord (-14/5) (-1) 0],none⟩ : BBState 0 1) = 7 ∧
    bbPotential (bbInitial (boxModel (1/4) (3/4)) none) = 3 ∧
    bbPotential (⟨[intervalRecord (1/4) 0 0,intervalRecord 1 (3/4) 0],none⟩ : BBState 0 1) = 2 := by
  norm_num [bbPotential,bbInitial,bbRootNode,boxModel,intervalRecord,intervalNode,
    BBNode.weight,BBNode.rank,BBNode.span,Fin.sum_univ_one]

/-- Source wrapper instantiation: every selector returns, not only the displayed one. -/
theorem quad_every_selector_exact_return (policy : BBPolicy)
    (choose : BBSelector (quadModel (2/5)) (quadModel (2/5)).objective policy) :
    ∃ s out j, j ≤ 3 ∧
      BBTrace (quadModel (2/5)) (quadModel (2/5)).objective policy j
        (bbInitial (quadModel (2/5)) none) s ∧ s.live = [] ∧ out = s.incumbent ∧
      bbRun (quadModel (2/5)) (quadModel (2/5)).objective policy choose
        (bbInitial (quadModel (2/5)) none) 4 = .stopped s out ∧
      BBOutcome (quadModel (2/5)) (quadModel (2/5)).objective out := by
  have hp := quad_source_premises (2/5)
  have h := bb_source_every_selector_exact_return (quadModel (2/5)) policy none (by simp)
    hp.1 hp.2.1 hp.2.2 choose
  have hw : (bbRootNode (quadModel (2/5))).weight = 3 := by
    norm_num [bbRootNode,quadModel,boundedModel,BBNode.weight,BBNode.rank,BBNode.span]
  simpa [hw] using h

theorem noncompact_full_bad_route_ablation (policy : BBPolicy) :
    (∀ j, ConvexOn ℝ Set.univ (noncompactModel.g j)) ∧
    (∀ j, ContDiff ℝ 1 (noncompactModel.g j)) ∧
    ¬ IsCompact (bbMixedBase noncompactModel noncompactModel.lo noncompactModel.hi) ∧
    BBTrace noncompactModel noncompactModel.objective policy 1
      (bbInitial noncompactModel none) (doneState none) ∧
    (noncompactModel.feasibleOn Set.univ).Nonempty ∧
    (∀ M : ℝ, ∃ p ∈ noncompactModel.feasibleOn Set.univ, noncompactModel.objective p < M) :=
  ⟨(fun j => Fin.elim0 j),(fun j => Fin.elim0 j),noncompact_base_not_compact,
    .cons (noncompact_false_infeasibility_step policy).1 (.nil _),
    ⟨point 0 0,noncompact_feasible_line 0⟩,noncompact_original_unbounded⟩

theorem nonempty_affine_base_empty_nonlinear_control (policy : BBPolicy) :
    SourcePremises (constantRowModel 1) ∧
    (bbMixedBase (constantRowModel 1) (constantRowModel 1).lo (constantRowModel 1).hi).Nonempty ∧
    (¬ ∃ p, IsMinimizer (region (constantRowModel 1) (rootNode (constantRowModel 1)))
      (constantRowModel 1).objective p) ∧
    BBTrace (constantRowModel 1) (constantRowModel 1).objective policy 1
      (bbInitial (constantRowModel 1) none) (doneState none) := by
  refine ⟨zero_source_premises _ _ _ _,constant_one_base_nonempty,?_,
    .cons (constant_one_empty_step policy) (.nil _)⟩
  rintro ⟨p,hp⟩
  have hmem := hp.1
  rw [constant_one_relaxation_empty] at hmem
  exact hmem

end Chapter02BBExamples













#print axioms Chapter02BBExamples.root_region_eq
#print axioms Chapter02BBExamples.bounded_linear_iff
#print axioms Chapter02BBExamples.bounded_objective
#print axioms Chapter02BBExamples.bounded_base_compact
#print axioms Chapter02BBExamples.quad_region_iff
#print axioms Chapter02BBExamples.quad_objective
#print axioms Chapter02BBExamples.quad_convex
#print axioms Chapter02BBExamples.quad_smooth
#print axioms Chapter02BBExamples.quad_base_compact
#print axioms Chapter02BBExamples.quad_root_minimum
#print axioms Chapter02BBExamples.quad_fixed_minimum
#print axioms Chapter02BBExamples.quad_two_fifths_minima
#print axioms Chapter02BBExamples.quad_half_minima
#print axioms Chapter02BBExamples.interval_children
#print axioms Chapter02BBExamples.fractional_between_integers
#print axioms Chapter02BBExamples.box_region_iff
#print axioms Chapter02BBExamples.box_objective
#print axioms Chapter02BBExamples.box_minimum
#print axioms Chapter02BBExamples.box_empty
#print axioms Chapter02BBExamples.box_base_compact
#print axioms Chapter02BBExamples.literal_fractional_ranks
#print axioms Chapter02BBExamples.band_region_iff
#print axioms Chapter02BBExamples.band_objective
#print axioms Chapter02BBExamples.band_root_minimum
#print axioms Chapter02BBExamples.band_children_empty
#print axioms Chapter02BBExamples.band_base_empty
#print axioms Chapter02BBExamples.band_base_compact
#print axioms Chapter02BBExamples.accepted_unbounded_reply
#print axioms Chapter02BBExamples.noncompact_feasible_line
#print axioms Chapter02BBExamples.noncompact_objective
#print axioms Chapter02BBExamples.noncompact_base_not_compact
#print axioms Chapter02BBExamples.noncompact_original_unbounded
#print axioms Chapter02BBExamples.noncompact_relaxation_unbounded
#print axioms Chapter02BBExamples.unattained_linear_iff
#print axioms Chapter02BBExamples.unattained_region_iff
#print axioms Chapter02BBExamples.unattained_objective
#print axioms Chapter02BBExamples.unattained_base_empty
#print axioms Chapter02BBExamples.unattained_base_compact
#print axioms Chapter02BBExamples.unattained_convex
#print axioms Chapter02BBExamples.unattained_smooth
#print axioms Chapter02BBExamples.unattained_objective_pos
#print axioms Chapter02BBExamples.unattained_small
#print axioms Chapter02BBExamples.unattained_no_minimum
#print axioms Chapter02BBExamples.unattained_finite_infimum
#print axioms Chapter02BBExamples.unattained_not_unbounded
#print axioms Chapter02BBExamples.strip_linear_iff
#print axioms Chapter02BBExamples.strip_region_iff
#print axioms Chapter02BBExamples.strip_objective
#print axioms Chapter02BBExamples.strip_base_compact
#print axioms Chapter02BBExamples.strip_base_nonempty
#print axioms Chapter02BBExamples.strip_root_minimum
#print axioms Chapter02BBExamples.strip_right_minimum
#print axioms Chapter02BBExamples.strip_left_empty
#print axioms Chapter02BBExamples.sqrt_two_strip_premises
#print axioms Chapter02BBExamples.bookkeeping_region_iff
#print axioms Chapter02BBExamples.bookkeeping_objective
#print axioms Chapter02BBExamples.square_combination_le
#print axioms Chapter02BBExamples.bookkeeping_convex
#print axioms Chapter02BBExamples.bookkeeping_smooth
#print axioms Chapter02BBExamples.bookkeeping_base_compact
#print axioms Chapter02BBExamples.bookkeeping_root_minimum
#print axioms Chapter02BBExamples.bookkeeping_y_fixed_minimum
#print axioms Chapter02BBExamples.bookkeeping_children_minima
#print axioms Chapter02BBExamples.bookkeeping_grandchild_minimum
#print axioms Chapter02BBExamples.box_square_smooth
#print axioms Chapter02BBExamples.box_square_convex
#print axioms Chapter02BBExamples.box_square_root_minimum
#print axioms Chapter02BBExamples.box_square_fixed_minimum
#print axioms Chapter02BBExamples.zero_objective
#print axioms Chapter02BBExamples.zero_base_compact
#print axioms Chapter02BBExamples.zero_rows_smooth
#print axioms Chapter02BBExamples.zero_rows_convex
#print axioms Chapter02BBExamples.empty_model_minimum
#print axioms Chapter02BBExamples.constant_zero_minimum
#print axioms Chapter02BBExamples.constant_one_relaxation_empty
#print axioms Chapter02BBExamples.constant_one_base_nonempty
#print axioms Chapter02BBExamples.impossible_affine_relaxation_empty
#print axioms Chapter02BBExamples.continuous_box_region_iff
#print axioms Chapter02BBExamples.continuous_box_minimum
#print axioms Chapter02BBExamples.feasible_nonoptimal_not_lower_bound
#print axioms Chapter02BBExamples.region_is_node_region
#print axioms Chapter02BBExamples.point_integer
#print axioms Chapter02BBExamples.pure_point_integer
#print axioms Chapter02BBExamples.no_integer_coordinates
#print axioms Chapter02BBExamples.quad_integer_point_feasible
#print axioms Chapter02BBExamples.quad_binary
#print axioms Chapter02BBExamples.quad_two_fifths_feasible
#print axioms Chapter02BBExamples.quad_two_fifths_global_minimum
#print axioms Chapter02BBExamples.integral_inferior_child_not_global_minimum
#print axioms Chapter02BBExamples.quad_half_two_global_minima
#print axioms Chapter02BBExamples.fake_warm_incumbent_rejected
#print axioms Chapter02BBExamples.quad_source_premises
#print axioms Chapter02BBExamples.bookkeeping_source_premises
#print axioms Chapter02BBExamples.unattained_source_premises
#print axioms Chapter02BBExamples.no_rows_source_premises
#print axioms Chapter02BBExamples.box_source_premises
#print axioms Chapter02BBExamples.band_source_premises
#print axioms Chapter02BBExamples.accepted_unbounded_source_premises
#print axioms Chapter02BBExamples.strip_source_premises
#print axioms Chapter02BBExamples.zero_source_premises
#print axioms Chapter02BBExamples.continuous_box_source_premises
#print axioms Chapter02BBExamples.literal_interval_branch
#print axioms Chapter02BBExamples.quad_two_fifths_step1
#print axioms Chapter02BBExamples.quad_two_fifths_step2
#print axioms Chapter02BBExamples.quad_two_fifths_step3
#print axioms Chapter02BBExamples.quad_half_step1
#print axioms Chapter02BBExamples.quad_half_step2
#print axioms Chapter02BBExamples.tie_source_keeps_first
#print axioms Chapter02BBExamples.tie_algorithm_replaces_first
#print axioms Chapter02BBExamples.tie_weak_prunes_other_optimizer
#print axioms Chapter02BBExamples.quad_exact_potentials
#print axioms Chapter02BBExamples.quad_exact_global_bounds
#print axioms Chapter02BBExamples.omitted_sibling_bound_false
#print axioms Chapter02BBExamples.box_branch
#print axioms Chapter02BBExamples.box_positive_step1
#print axioms Chapter02BBExamples.box_positive_step2
#print axioms Chapter02BBExamples.box_positive_step3
#print axioms Chapter02BBExamples.box_negative_step1
#print axioms Chapter02BBExamples.box_negative_step2
#print axioms Chapter02BBExamples.box_negative_step3
#print axioms Chapter02BBExamples.band_step1
#print axioms Chapter02BBExamples.band_step2
#print axioms Chapter02BBExamples.band_step3
#print axioms Chapter02BBExamples.fractional_empty_box_step1
#print axioms Chapter02BBExamples.fractional_empty_box_step2
#print axioms Chapter02BBExamples.fractional_empty_box_step3
#print axioms Chapter02BBExamples.contradictory_root_step
#print axioms Chapter02BBExamples.accepted_unbounded_step
#print axioms Chapter02BBExamples.unattained_step
#print axioms Chapter02BBExamples.noncompact_false_infeasibility_step
#print axioms Chapter02BBExamples.strip_step1
#print axioms Chapter02BBExamples.strip_step2
#print axioms Chapter02BBExamples.strip_step3
#print axioms Chapter02BBExamples.root_integral_step
#print axioms Chapter02BBExamples.root_empty_step
#print axioms Chapter02BBExamples.all_zero_dimensions_step
#print axioms Chapter02BBExamples.present_zero_row_step
#print axioms Chapter02BBExamples.constant_one_empty_step
#print axioms Chapter02BBExamples.impossible_affine_empty_step
#print axioms Chapter02BBExamples.continuous_box_step
#print axioms Chapter02BBExamples.negative_fixed_integer_step
#print axioms Chapter02BBExamples.quad_three_process_trace
#print axioms Chapter02BBExamples.tie_three_policy_traces
#print axioms Chapter02BBExamples.positive_literal_box_trace
#print axioms Chapter02BBExamples.negative_literal_box_trace
#print axioms Chapter02BBExamples.affine_empty_children_trace
#print axioms Chapter02BBExamples.contradictory_children_trace
#print axioms Chapter02BBExamples.irrational_strip_trace
#print axioms Chapter02BBExamples.nonlinear_objective_three_process_trace
#print axioms Chapter02BBExamples.book_node_updates
#print axioms Chapter02BBExamples.book_root_node
#print axioms Chapter02BBExamples.book_point_integer
#print axioms Chapter02BBExamples.bookkeeping_step1
#print axioms Chapter02BBExamples.bookkeeping_step2
#print axioms Chapter02BBExamples.bookkeeping_step3
#print axioms Chapter02BBExamples.bookkeeping_step4
#print axioms Chapter02BBExamples.bookkeeping_step5
#print axioms Chapter02BBExamples.bookkeeping_five_process_trace
#print axioms Chapter02BBExamples.bookkeeping_exact_potentials
#print axioms Chapter02BBExamples.bookkeeping_exact_global_bounds
#print axioms Chapter02BBExamples.bookkeeping_incumbent_feasible
#print axioms Chapter02BBExamples.omitted_incumbent_bound_false
#print axioms Chapter02BBExamples.reset_bound_decreases
#print axioms Chapter02BBExamples.constant_tie_warm_feasible
#print axioms Chapter02BBExamples.constant_fractional_tie_three_steps
#print axioms Chapter02BBExamples.constant_tie_weak_one_step
#print axioms Chapter02BBExamples.constant_tie_integral_choice_one_step
#print axioms Chapter02BBExamples.duplicate_occurrences_two_steps
#print axioms Chapter02BBExamples.source_trace_minimum
#print axioms Chapter02BBExamples.source_trace_infeasible
#print axioms Chapter02BBExamples.quad_full_model_trace_return
#print axioms Chapter02BBExamples.literal_boxes_full_trace_returns
#print axioms Chapter02BBExamples.two_empty_routes_full_trace_returns
#print axioms Chapter02BBExamples.bad_status_full_trace_returns
#print axioms Chapter02BBExamples.irrational_strip_full_trace_return
#print axioms Chapter02BBExamples.bookkeeping_full_model_trace_return
#print axioms Chapter02BBExamples.nonlinear_objective_full_trace_return
#print axioms Chapter02BBExamples.all_zero_edge_counted_traces
#print axioms Chapter02BBExamples.all_zero_edge_source_returns
#print axioms Chapter02BBExamples.literal_box_integer_contents
#print axioms Chapter02BBExamples.literal_bound_counts_are_not_integer_cardinality
#print axioms Chapter02BBExamples.empty_dimension_potentials
#print axioms Chapter02BBExamples.bookkeeping_prefix_reachable
#print axioms Chapter02BBExamples.reset_is_not_a_legal_process
#print axioms Chapter02BBExamples.selected_working_node_omission_false
#print axioms Chapter02BBExamples.nonoptimal_point_cannot_supply_exact_reply
#print axioms Chapter02BBExamples.strip_derived_continuous_compact
#print axioms Chapter02BBExamples.quad_warm_incumbent_three_steps
#print axioms Chapter02BBExamples.quad_warm_trace_return
#print axioms Chapter02BBExamples.fractional_box_potentials
#print axioms Chapter02BBExamples.quad_every_selector_exact_return
#print axioms Chapter02BBExamples.noncompact_full_bad_route_ablation
#print axioms Chapter02BBExamples.nonempty_affine_base_empty_nonlinear_control
