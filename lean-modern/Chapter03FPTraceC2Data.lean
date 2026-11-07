module

public import Chapter03FPTraceCommon

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C2
abbrev P := Point 0 2

def pt (u v : ℝ) : P := (fun _ => 0,![u,v])
def seed : P := pt (1/3) (1/3)
def zero : P := pt 0 0
def one : P := pt 0 1
def other : P := pt 1 0
def both : P := pt 1 1

def q (p : P) : ℝ := (p.2 0+p.2 1-2/3)^2+(1/9)*(p.2 0-1/3)^2
def Dq (p : P) : P →L[ℝ] ℝ :=
  (2*(p.2 0+p.2 1-2/3)) • (y0+y1)+(2/9*(p.2 0-1/3)) • y0

def model : ModelData 0 2 0 0 where
  g := fun j => Fin.elim0 j
  A := fun j => Fin.elim0 j
  B := fun j => Fin.elim0 j
  rhs := fun j => Fin.elim0 j
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

def data (a b delta : ℝ) : Data 0 2 0 0 where
  model := model
  f p := a*q p+b
  Df p := a • Dq p
  Dg := fun j => Fin.elim0 j
  nonlinear := ∅
  delta := delta

theorem point_ext (p : P) (u v : ℝ) (h0 : p.2 0=u) (h1 : p.2 1=v) : p=pt u v := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · funext j
    fin_cases j <;> simp [pt,h0,h1]

theorem q_derivative (p : P) : HasFDerivAt q (Dq p) p := by
  have h := (square_derivative (y0+y1) (2/3) p).add
    ((square_derivative y0 (1/3) p).const_mul (1/9))
  exact h.congr_fderiv (by
    apply ContinuousLinearMap.ext
    intro v
    simp [Dq]
    ring)

theorem f_derivative (a b delta : ℝ) (p : P) :
    HasFDerivAt (data a b delta).f ((data a b delta).Df p) p := by
  exact ((q_derivative p).const_mul a).add_const b

theorem relaxation_iff (a b delta : ℝ) (p : P) :
    p ∈ (data a b delta).relaxation ↔
      0 ≤ p.2 0 ∧ p.2 0 ≤ 1 ∧ 0 ≤ p.2 1 ∧ p.2 1 ≤ 1 := by
  simp [relaxation_mem_iff,Data.base,data,model,ModelData.linearRegion,
    Fin.forall_fin_two,and_assoc]

theorem analytic (a b delta : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ delta) :
    Analytic (data a b delta) := by
  let d := data a b delta
  refine ⟨?_,?_,?_,?_,?_,hd⟩
  · have hq := (square_convex (base_convex d) (y0+y1) (2/3)).add
      ((square_convex (base_convex d) y0 (1/3)).smul (show (0:ℝ) ≤ 1/9 by norm_num))
    exact (hq.smul ha).add_const b
  · intro j; exact Fin.elim0 j
  · intro p _; exact f_derivative a b delta p
  · intro j; exact Fin.elim0 j
  · apply (isCompact_Icc : IsCompact (Set.Icc zero both)).isBounded.subset
    intro p hp
    obtain ⟨h0,h1,h2,h3⟩ := (relaxation_iff a b delta p).mp hp
    constructor <;> constructor
    · intro j; exact Fin.elim0 j
    · intro j; fin_cases j <;> simp [zero,pt,h0,h2]
    · intro j; exact Fin.elim0 j
    · intro j; fin_cases j <;> simp [both,pt,h1,h3]

theorem q_nonnegative (p : P) : 0 ≤ q p := by unfold q; positivity

theorem q_seed : q seed=0 := by norm_num [q,seed,pt]

theorem seed_minimizer (a b delta : ℝ) (ha : 0 ≤ a) :
    IsMinimizer (data a b delta).relaxation (data a b delta).f seed := by
  refine ⟨(relaxation_iff _ _ _ _).mpr (by norm_num [seed,pt]),?_⟩
  intro p hp
  change a*q seed+b ≤ a*q p+b
  rw [q_seed]
  nlinarith [mul_nonneg ha (q_nonnegative p)]

theorem q_sublevel_zero (p : P) (hp : q p ≤ 0) : p=seed := by
  have h0 : p.2 0=1/3 := by
    unfold q at hp
    nlinarith [sq_nonneg (p.2 0+p.2 1-2/3),sq_nonneg (p.2 0-1/3)]
  have h1 : p.2 1=1/3 := by
    unfold q at hp
    rw [h0] at hp
    nlinarith [sq_nonneg (p.2 1-1/3)]
  exact point_ext p _ _ h0 h1

theorem seed_not_original (a b delta : ℝ) : seed ∉ (data a b delta).original := by
  intro h
  obtain ⟨_,_,_,y,hy,he⟩ := (source_feasible_iff model Set.univ seed).mp h
  have hc := integer_corner_cases y hy
  rcases hc with rfl|rfl|rfl|rfl
  all_goals have h0 := congrFun he (0:Fin 2)
  all_goals norm_num [seed,pt,corner] at h0

theorem box_eq (a b delta : ℝ) : (data a b delta).box =
    {corner 0 0,corner 0 1,corner 1 0,corner 1 1} := by
  ext y
  simp only [Data.box,Set.Finite.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · exact integer_corner_cases y
  · intro h
    rcases h with rfl|rfl|rfl|rfl <;>
      norm_num [IntegerBox,data,model,corner,Fin.forall_fin_two]

theorem box_card (a b delta : ℝ) : (data a b delta).box.card=4 := by
  rw [box_eq]
  decide

theorem tangent_seed (a b delta : ℝ) (p : P) :
    (data a b delta).f seed+(data a b delta).Df seed (p-seed)=b := by
  norm_num [data,q,Dq,seed,pt]

theorem tangent_zero (a b delta : ℝ) (p : P) :
    (data a b delta).f zero+(data a b delta).Df zero (p-zero)=
      a*(37/81-(38/27)*p.2 0-(4/3)*p.2 1)+b := by
  norm_num [data,q,Dq,zero,pt]
  ring

end Chapter03.FPTrace.C2

