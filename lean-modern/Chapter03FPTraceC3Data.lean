module

public import Chapter03FPTraceCommon

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C3
abbrev P := Point 1 2

def pt (x u v : ℝ) : P := (fun _ => x,![u,v])
def seed : P := pt 0 0 (1/2)
def proj0 : P := pt 1 (1/5) (2/5)
def proj1 : P := pt 1 0 (1/2)
def proj2 : P := pt 1 1 0
def polished : P := pt 0 1 0

def model : ModelData 1 2 1 2 where
  g _ p := (p.2 0+2*p.2 1-1)^2
  A := ![fun _ => -1,fun _ => 1]
  B := fun _ _ => 0
  rhs := ![0,1]
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

def d : Data 1 2 1 2 where
  model := model
  f p := p.1 0+(p.2 0)^2+(p.2 1-1/2)^2
  Df p := x0+(2*p.2 0) • y0+(2*(p.2 1-1/2)) • y1
  Dg _ p := (2*(p.2 0+2*p.2 1-1)) • (y0+(2:ℝ) • y1)
  nonlinear := Set.univ
  delta := 0

theorem point_ext (p : P) (x u v : ℝ)
    (hx : p.1 0=x) (h0 : p.2 0=u) (h1 : p.2 1=v) : p=pt x u v := by
  apply Prod.ext
  · funext j; fin_cases j; exact hx
  · funext j; fin_cases j <;> simp [pt,h0,h1]

theorem linear_iff (p : P) : p ∈ model.linearRegion ↔ 0 ≤ p.1 0 ∧ p.1 0 ≤ 1 := by
  simp only [ModelData.linearRegion,model,Set.mem_setOf_eq,Fin.forall_fin_two,
    LinearForm,Fin.sum_univ_one,Fin.sum_univ_two]
  norm_num

theorem base_iff (p : P) : p ∈ d.base ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 ∧
      0 ≤ p.2 1 ∧ p.2 1 ≤ 1 := by
  change (p ∈ model.linearRegion ∧ ∀ j, 0 ≤ p.2 j ∧ p.2 j ≤ 1) ↔ _
  rw [linear_iff]
  simp only [Fin.forall_fin_two,and_assoc]

theorem relaxation_iff (p : P) : p ∈ d.relaxation ↔
    0 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 ∧
      0 ≤ p.2 1 ∧ p.2 1 ≤ 1 ∧ p.2 0+2*p.2 1=1 := by
  rw [relaxation_mem_iff,base_iff]
  simp only [d,model,Fin.forall_fin_one]
  constructor
  · rintro ⟨⟨hx,hX,h0,hU,h1,hV⟩,hg⟩
    exact ⟨hx,hX,h0,hU,h1,hV,by nlinarith [sq_nonneg (p.2 0+2*p.2 1-1)]⟩
  · rintro ⟨hx,hX,h0,hU,h1,hV,hg⟩
    refine ⟨⟨hx,hX,h0,hU,h1,hV⟩,?_⟩
    rw [hg]; norm_num

theorem f_derivative (p : P) : HasFDerivAt d.f (d.Df p) p := by
  simpa only [d,Pi.add_def,sub_zero,y0_apply,y1_apply,x0_apply] using
    (x0.hasFDerivAt.fun_add (square_derivative y0 0 p)).fun_add (square_derivative y1 (1/2) p)

theorem g_derivative (j : Fin 1) (p : P) : HasFDerivAt (d.model.g j) (d.Dg j p) p := by
  exact square_derivative (y0+(2:ℝ) • y1) 1 p

theorem d_analytic : Analytic d := by
  refine ⟨?_,?_,?_,?_,?_,by norm_num [d]⟩
  · simpa only [d,Pi.add_def,sub_zero,y0_apply,y1_apply,x0_apply] using
      ((linear_convex (base_convex d) x0).add (square_convex (base_convex d) y0 0)).add
        (square_convex (base_convex d) y1 (1/2))
  · intro j
    exact square_convex (base_convex d) (y0+(2:ℝ) • y1) 1
  · intro p _; exact f_derivative p
  · intro j p _; exact g_derivative j p
  · apply (isCompact_Icc : IsCompact (Set.Icc (pt 0 0 0) (pt 1 1 1))).isBounded.subset
    intro p hp
    obtain ⟨hx,hX,h0,hU,h1,hV,_⟩ := (relaxation_iff p).mp hp
    constructor <;> constructor
    · intro j; fin_cases j; exact hx
    · intro j; fin_cases j <;> simp [pt,h0,h1]
    · intro j; fin_cases j; exact hX
    · intro j; fin_cases j <;> simp [pt,hU,hV]

theorem seed_minimizer : IsMinimizer d.relaxation d.f seed := by
  refine ⟨(relaxation_iff _).mpr (by norm_num [seed,pt]),?_⟩
  intro p hp
  have hx := ((relaxation_iff p).mp hp).1
  norm_num [d,seed,pt]
  nlinarith [sq_nonneg (p.2 0),sq_nonneg (p.2 1-1/2)]

theorem seed_not_original : seed ∉ d.original := by
  intro h
  obtain ⟨_,_,_,y,hy,he⟩ := (source_feasible_iff model Set.univ seed).mp h
  rcases integer_corner_cases y hy with rfl|rfl|rfl|rfl
  all_goals have h1 := congrFun he (1:Fin 2)
  all_goals norm_num [seed,pt,corner] at h1

theorem box_eq : d.box = {corner 0 0,corner 0 1,corner 1 0,corner 1 1} := by
  ext y
  simp only [Data.box,Set.Finite.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · exact integer_corner_cases y
  · intro h
    rcases h with rfl|rfl|rfl|rfl <;> norm_num [IntegerBox,d,model,corner,Fin.forall_fin_two]

theorem box_card : d.box.card=4 := by rw [box_eq]; decide

theorem feasible_line (p : P) (hp : p ∈ d.relaxation) :
    p.2 0=1-2*p.2 1 ∧ 0 ≤ p.2 1 ∧ p.2 1 ≤ 1/2 := by
  obtain ⟨_,_,hy,_,ht,_,he⟩ := (relaxation_iff p).mp hp
  exact ⟨by linarith,ht,by linarith⟩

theorem projection0 : IsMinimizer (d.region none) (distance (corner 0 0)) proj0 := by
  refine ⟨⟨(relaxation_iff _).mpr (by norm_num [proj0,pt]),trivial⟩,?_⟩
  intro p hp
  obtain ⟨he,ht,hu⟩ := feasible_line p hp.1
  rw [distance_two,distance_two]
  norm_num [corner,proj0,pt]
  rw [he]
  nlinarith [sq_nonneg (p.2 1-2/5)]

theorem projection1 : IsMinimizer (d.region none) (distance (corner 0 1)) proj1 := by
  refine ⟨⟨(relaxation_iff _).mpr (by norm_num [proj1,pt]),trivial⟩,?_⟩
  intro p hp
  obtain ⟨he,ht,hu⟩ := feasible_line p hp.1
  rw [distance_two,distance_two]
  norm_num [corner,proj1,pt]
  rw [he]
  have hprod := mul_nonneg (show (0:ℝ) ≤ 1/2-p.2 1 by linarith)
    (show (0:ℝ) ≤ 7/2-5*p.2 1 by linarith)
  nlinarith

theorem projection2 : IsMinimizer (d.region none) (distance (corner 1 0)) proj2 := by
  refine ⟨⟨(relaxation_iff _).mpr (by norm_num [proj2,pt]),trivial⟩,?_⟩
  intro p _
  rw [distance_two,distance_two]
  norm_num [corner,proj2,pt]
  positivity

theorem polishing : IsMinimizer (d.fiber (corner 1 0)) d.f polished := by
  refine ⟨⟨(relaxation_iff _).mpr (by norm_num [polished,pt]),by ext j; fin_cases j <;> norm_num [polished,pt,intCast,corner]⟩,?_⟩
  intro p hp
  have hx := ((relaxation_iff p).mp hp.1).1
  have h0 := congrFun hp.2 (0:Fin 2)
  have h1 := congrFun hp.2 (1:Fin 2)
  norm_num [intCast,corner] at h0 h1
  norm_num [d,polished,pt,h0,h1]
  linarith

theorem strict_polishing : d.f proj2=9/4 ∧ d.f polished=5/4 ∧ d.f polished < d.f proj2 := by
  norm_num [d,proj2,polished,pt]

end Chapter03.FPTrace.C3

