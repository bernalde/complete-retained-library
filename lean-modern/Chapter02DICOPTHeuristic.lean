module

public import Chapter02DICOPTNonlinear

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT
open scoped BigOperators
namespace Chapter02DICOPTExamples

def triple (a b c : ℝ) : RealVector 3 := ![a,b,c]
@[simp] theorem triple_zero (a b c : ℝ) : triple a b c 0 = a := rfl
@[simp] theorem triple_one (a b c : ℝ) : triple a b c 1 = b := rfl
@[simp] theorem triple_two (a b c : ℝ) : triple a b c 2 = c := rfl

def heuristicData : Data 1 3 0 0 4 where
  f x := (x 0)^2
  h := Fin.elim0
  g := Fin.elim0
  A := Fin.elim0
  B := Fin.elim0
  C := ![triple 1 1 1, triple (-1) (-1) (-1),
    triple (-1) 2 (1/2), triple 1 (-2) (-1/2)]
  D := ![scalar 0,scalar 0,scalar 1,scalar (-1)]
  rhs := ![1,-1,0,0]
  xL := scalar (-2)
  xU := scalar 1
  c := triple 0 0 0

@[simp] theorem dot_triple (a b c : ℝ) (y : RealVector 3) :
    dot (triple a b c) y = a*y 0+b*y 1+c*y 2 := by
  simp [dot, triple, Fin.sum_univ_succ]
  ring

@[simp] theorem heuristic_objective (x : V) (y : RealVector 3) :
    heuristicData.objective x y = (x 0)^2 := by
  simp [Data.objective,heuristicData]

theorem heuristic_hard (x : V) (y : RealVector 3) :
    heuristicData.Hard x y ↔
    (-2 ≤ x 0 ∧ x 0 ≤ 1) ∧ y 0+y 1+y 2=1 ∧ x 0=y 0-2*y 1-y 2/2 := by
  simp [Data.Hard,Data.xBox,heuristicData,Pi.le_def,Fin.forall_fin_succ,
    Data.affineRow,scalar,triple,dot,Fin.sum_univ_succ]
  intro ha hb
  norm_num
  constructor
  · rintro ⟨hc,hd,he,hf⟩
    exact ⟨by linarith,by linarith⟩
  · rintro ⟨hc,hd⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem heuristic_feasible (x : V) (y : RealVector 3) :
    heuristicData.Feasible x y ↔ heuristicData.Hard x y := by
  simp [Data.Feasible]

def heuristicJet (a : ℝ) : Jet heuristicData (scalar a) where
  Df := (2*a) • coord
  Dh := Fin.elim0
  Dg := Fin.elim0
  fderiv := by simpa [heuristicData] using derivative_square (scalar a)
  hderiv := by intro i; exact Fin.elim0 i
  gderiv := by intro i; exact Fin.elim0 i

def heuristicKKT (a : ℝ) (b : RealVector 3) (eta theta : ℝ)
    (ha : -2 ≤ a ∧ a ≤ 1) (hb : b 0+b 1+b 2=1)
    (he : a=b 0-2*b 1-b 2/2) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hs : 2*a+eta-theta=0) : FixedKKT heuristicData (scalar a) b where
  jet := heuristicJet a
  alpha := a^2
  sigma := 1
  lambda := Fin.elim0
  mu := Fin.elim0
  nu := ![0,0,eta,theta]
  xLower := scalar 0
  xUpper := scalar 0
  feasible := (heuristic_feasible _ _).mpr ((heuristic_hard _ _).mpr ⟨ha,hb,he⟩)
  alphaFeasible := le_rfl
  sigmaNonneg := by norm_num
  muNonneg := by intro i; exact Fin.elim0 i
  nuNonneg := by intro i; fin_cases i <;> simp [heta,htheta]
  lowerNonneg := by simp
  upperNonneg := by simp
  alphaComp := by simp [heuristicData]
  ineqComp := by intro i; exact Fin.elim0 i
  affineComp := by
    intro i
    fin_cases i <;> simp [Data.affineRow,heuristicData]
    · right; norm_num; linarith
    · right; norm_num; linarith
  lowerComp := by simp
  upperComp := by simp
  alphaStationarity := by norm_num
  stationarity := by
    intro v
    simp [heuristicJet,heuristicData,Fin.sum_univ_succ]
    nlinarith [mul_eq_zero_of_left hs (v 0)]

def heuristicAnchor (a : ℝ) (b : RealVector 3) (eta theta : ℝ)
    (ha : -2 ≤ a ∧ a ≤ 1) (hb : b 0+b 1+b 2=1)
    (he : a=b 0-2*b 1-b 2/2) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hs : 2*a+eta-theta=0) : Anchor heuristicData where
  x := scalar a
  y := b
  kkt := heuristicKKT a b eta theta ha hb he heta htheta hs
  convex := {
    objective := convex_square_on (convex_Icc _ _)
    inequalities := by intro i; exact Fin.elim0 i
    equalities := by intro i; exact Fin.elim0 i }
  weights := {
    obj := 2
    eq := Fin.elim0
    ineq := Fin.elim0
    obj_gt := by norm_num [heuristicKKT]
    eq_gt := by intro i; exact Fin.elim0 i
    ineq_gt := by intro i; exact Fin.elim0 i }

def heuristicInitial : Anchor heuristicData :=
  heuristicAnchor 0 (triple (2/3) (1/3) 0) 0 0
    (by norm_num) (by norm_num [triple,Matrix.cons_val_two]) (by norm_num [triple,Matrix.cons_val_two])
    (by norm_num) (by norm_num) (by norm_num)
def heuristicOne : Anchor heuristicData :=
  heuristicAnchor 1 (triple 1 0 0) 0 2
    (by norm_num) (by norm_num [triple,Matrix.cons_val_two]) (by norm_num [triple,Matrix.cons_val_two])
    (by norm_num) (by norm_num) (by norm_num)
def heuristicMinusTwo : Anchor heuristicData :=
  heuristicAnchor (-2) (triple 0 1 0) 4 0
    (by norm_num) (by norm_num [triple,Matrix.cons_val_two]) (by norm_num [triple,Matrix.cons_val_two])
    (by norm_num) (by norm_num) (by norm_num)
def heuristicHalf : Anchor heuristicData :=
  heuristicAnchor (-(1/2)) (triple 0 0 1) 1 0
    (by norm_num) (by norm_num [triple,Matrix.cons_val_two]) (by norm_num [triple,Matrix.cons_val_two])
    (by norm_num) (by norm_num) (by norm_num)

def heuristicJoint : JointKKT heuristicData (scalar 0) (triple (2/3) (1/3) 0) where
  toFixedKKT := heuristicInitial.kkt
  yFeasible := by
    constructor <;> intro i <;> fin_cases i <;> norm_num [Data.yBox,triple]
  yLower := triple 0 0 0
  yUpper := triple 0 0 0
  yLowerNonneg := by intro i; fin_cases i <;> norm_num [triple,Matrix.cons_val_two]
  yUpperNonneg := by intro i; fin_cases i <;> norm_num [triple,Matrix.cons_val_two]
  yLowerComp := by intro i; fin_cases i <;> simp [triple]
  yUpperComp := by intro i; fin_cases i <;> simp [triple]
  yStationarity := by
    intro v
    simp [heuristicInitial,heuristicAnchor,heuristicKKT,heuristicData,
      Fin.sum_univ_succ,triple,dot]

theorem heuristic_relaxed_minimum :
    IsMinimizer heuristicData.relaxed (fun z => heuristicData.objective z.1 z.2)
      (heuristicInitial.x,heuristicInitial.y) := by
  refine ⟨⟨heuristicJoint.feasible,heuristicJoint.yFeasible⟩,?_⟩
  intro z hz
  simpa [heuristicInitial,heuristicAnchor] using sq_nonneg (z.1 0)

theorem one_hot_three {y : RealVector 3} (hy : Binary y) (hs : y 0+y 1+y 2=1) :
    y=triple 1 0 0 ∨ y=triple 0 1 0 ∨ y=triple 0 0 1 := by
  rcases hy 0 with h0|h0 <;> rcases hy 1 with h1|h1 <;>
    rcases hy 2 with h2|h2 <;> norm_num [h0,h1,h2] at hs
  · right; right; ext i; fin_cases i <;> simp_all [triple,Matrix.cons_val_two]
  · right; left; ext i; fin_cases i <;> simp_all [triple,Matrix.cons_val_two]
  · left; ext i; fin_cases i <;> simp_all [triple,Matrix.cons_val_two]

theorem heuristic_original_points (x : V) (y : RealVector 3) :
    (x,y) ∈ heuristicData.original ↔
      (x=scalar 1 ∧ y=triple 1 0 0) ∨
      (x=scalar (-2) ∧ y=triple 0 1 0) ∨
      (x=scalar (-(1/2)) ∧ y=triple 0 0 1) := by
  constructor
  · intro h
    have hh := (heuristic_hard _ _).mp h.1.1
    rcases one_hot_three h.2 hh.2.1 with rfl|rfl|rfl
    · exact Or.inl ⟨scalar_ext (by simpa [triple,Matrix.cons_val_two] using hh.2.2),rfl⟩
    · exact Or.inr (Or.inl ⟨scalar_ext (by simpa [triple,Matrix.cons_val_two] using hh.2.2),rfl⟩)
    · exact Or.inr (Or.inr ⟨scalar_ext (by simpa [triple,Matrix.cons_val_two] using hh.2.2),rfl⟩)
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;>
      refine ⟨(heuristic_feasible _ _).mpr ((heuristic_hard _ _).mpr ?_),?_⟩
    all_goals try norm_num [triple,Matrix.cons_val_two]
    all_goals intro i; fin_cases i <;> simp [triple]

theorem heuristic_original_minimum :
    IsMinimizer heuristicData.original (fun z => heuristicData.objective z.1 z.2)
      (scalar (-(1/2)),triple 0 0 1) := by
  refine ⟨(heuristic_original_points _ _).mpr (Or.inr (Or.inr ⟨rfl,rfl⟩)),?_⟩
  intro z hz
  rcases (heuristic_original_points _ _).mp hz with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩ <;>
    norm_num [hx,hy]

def heuristicFirstPoint : MasterPoint heuristicData [heuristicInitial] where
  x := scalar 1
  y := triple 1 0 0
  alpha := 0
  s _ := 0
  p _ := Fin.elim0
  q _ := Fin.elim0

def firstBinary : BVector 3 := ![true,false,false]

def heuristicSecondPoint : MasterPoint heuristicData [heuristicInitial,heuristicOne] where
  x := scalar (-2)
  y := triple 0 1 0
  alpha := 0
  s _ := 0
  p _ := Fin.elim0
  q _ := Fin.elim0

def heuristicUnvisitedPoint : MasterPoint heuristicData [heuristicInitial,heuristicOne] where
  x := scalar (-(1/2))
  y := triple 0 0 1
  alpha := 0
  s _ := 0
  p _ := Fin.elim0
  q _ := Fin.elim0

theorem heuristic_first_master_feasible :
    heuristicFirstPoint ∈ masterFeasible heuristicData [heuristicInitial] ∅ := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · exact heuristicOne.kkt.feasible.1
  · intro i; fin_cases i <;> norm_num [heuristicFirstPoint,triple]
  · simp
  · intro k; exact le_rfl
  · intro k i; exact Fin.elim0 i
  · intro k i; exact Fin.elim0 i
  · intro k
    fin_cases k
    · change (0:ℝ)^2+(2*0)*(1-0)-0 ≤ 0
      norm_num
  · intro k i; exact Fin.elim0 i
  · intro k i; exact Fin.elim0 i

theorem heuristic_second_master_feasible :
    heuristicSecondPoint ∈ masterFeasible heuristicData [heuristicInitial,heuristicOne]
      {firstBinary} := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · exact heuristicMinusTwo.kkt.feasible.1
  · intro i; fin_cases i <;> norm_num [heuristicSecondPoint,triple]
  · intro b hb
    have he : b=firstBinary := Finset.mem_singleton.mp hb
    subst b
    norm_num [heuristicSecondPoint,noGoodRow,firstBinary,Fin.sum_univ_succ,triple]
    exact le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Nat.cast_nonneg _)
  · intro k; exact le_rfl
  · intro k i; exact Fin.elim0 i
  · intro k i; exact Fin.elim0 i
  · intro k
    fin_cases k
    · change (0:ℝ)^2+(2*0)*((-2)-0)-0 ≤ 0
      norm_num
    · change (1:ℝ)^2+(2*1)*((-2)-1)-0 ≤ 0
      norm_num
  · intro k i; exact Fin.elim0 i
  · intro k i; exact Fin.elim0 i

theorem heuristic_unvisited_master_feasible :
    heuristicUnvisitedPoint ∈ masterFeasible heuristicData [heuristicInitial,heuristicOne]
      {firstBinary} := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · exact heuristicHalf.kkt.feasible.1
  · intro i; fin_cases i <;> norm_num [heuristicUnvisitedPoint,triple]
  · intro b hb
    have he : b=firstBinary := Finset.mem_singleton.mp hb
    subst b
    norm_num [heuristicUnvisitedPoint,noGoodRow,firstBinary,Fin.sum_univ_succ,triple]
    exact le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Nat.cast_nonneg _)
  · intro k; exact le_rfl
  · intro k i; exact Fin.elim0 i
  · intro k i; exact Fin.elim0 i
  · intro k
    fin_cases k
    · change (0:ℝ)^2+(2*0)*((-(1/2))-0)-0 ≤ 0
      norm_num
    · change (1:ℝ)^2+(2*1)*((-(1/2))-1)-0 ≤ 0
      norm_num
  · intro k i; exact Fin.elim0 i
  · intro k i; exact Fin.elim0 i

theorem heuristic_first_master_minimum :
    IsMinimizer (masterFeasible heuristicData [heuristicInitial] ∅)
      (masterObjective heuristicData [heuristicInitial]) heuristicFirstPoint := by
  refine ⟨heuristic_first_master_feasible,?_⟩
  intro z hz
  have hs := hz.2.1 (0 : Fin 1)
  have hc := hz.2.2.2.2.1 (0 : Fin 1)
  simp [objTangent,heuristicInitial,heuristicAnchor,heuristicKKT,heuristicJet,
    heuristicData] at hc
  simp [masterObjective,heuristicFirstPoint,heuristicInitial,heuristicAnchor,
    heuristicData,Fin.sum_univ_succ]
  linarith

theorem heuristic_two_master_nonneg (R : Finset (BVector 3))
    (z : MasterPoint heuristicData [heuristicInitial,heuristicOne])
    (hz : z ∈ masterFeasible heuristicData [heuristicInitial,heuristicOne] R) :
    0 ≤ masterObjective heuristicData [heuristicInitial,heuristicOne] z := by
  have hs := hz.2.1 (0 : Fin 2)
  have ht := hz.2.1 (1 : Fin 2)
  have hc := hz.2.2.2.2.1 (0 : Fin 2)
  simp [objTangent,heuristicInitial,heuristicAnchor,heuristicKKT,heuristicJet,
    heuristicData] at hc
  simp [masterObjective,heuristicInitial,heuristicOne,heuristicAnchor,
    heuristicData,Fin.sum_univ_succ]
  linarith

theorem heuristic_second_master_minimum :
    IsMinimizer (masterFeasible heuristicData [heuristicInitial,heuristicOne] {firstBinary})
      (masterObjective heuristicData [heuristicInitial,heuristicOne]) heuristicSecondPoint := by
  refine ⟨heuristic_second_master_feasible,?_⟩
  intro z hz
  convert heuristic_two_master_nonneg {firstBinary} z hz using 1
  norm_num [masterObjective,heuristicSecondPoint,heuristicData,heuristicInitial,
    heuristicOne,heuristicAnchor,Fin.sum_univ_succ]

theorem heuristic_unvisited_master_minimum :
    IsMinimizer (masterFeasible heuristicData [heuristicInitial,heuristicOne] {firstBinary})
      (masterObjective heuristicData [heuristicInitial,heuristicOne]) heuristicUnvisitedPoint := by
  refine ⟨heuristic_unvisited_master_feasible,?_⟩
  intro z hz
  convert heuristic_two_master_nonneg {firstBinary} z hz using 1
  norm_num [masterObjective,heuristicUnvisitedPoint,heuristicData,heuristicInitial,
    heuristicOne,heuristicAnchor,Fin.sum_univ_succ]

theorem heuristic_fiber_singleton (a : Anchor heuristicData) :
    heuristicData.fiber a.y = {a.x} := by
  ext x
  constructor
  · intro hx
    have h1 := (heuristic_hard _ _).mp hx.1
    have h2 := (heuristic_hard _ _).mp a.kkt.feasible.1
    exact scalar_ext (h1.2.2.trans h2.2.2.symm)
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    exact a.kkt.feasible

theorem heuristic_fixed_minimum (a : Anchor heuristicData) :
    IsMinimizer (heuristicData.fiber a.y) (fun x => heuristicData.objective x a.y) a.x := by
  rw [heuristic_fiber_singleton]
  exact ⟨rfl,by intro x hx; rw [Set.mem_singleton_iff.mp hx]⟩

theorem heuristic_strict_weak_stop :
    heuristicData.objective heuristicOne.x heuristicOne.y = 1 ∧
    heuristicData.objective heuristicMinusTwo.x heuristicMinusTwo.y = 4 ∧
    heuristicData.objective heuristicHalf.x heuristicHalf.y = 1/4 ∧
    heuristicData.objective heuristicOne.x heuristicOne.y <
      heuristicData.objective heuristicMinusTwo.x heuristicMinusTwo.y ∧
    heuristicData.objective heuristicOne.x heuristicOne.y ≤
      heuristicData.objective heuristicMinusTwo.x heuristicMinusTwo.y ∧
    heuristicData.objective heuristicHalf.x heuristicHalf.y <
      heuristicData.objective heuristicOne.x heuristicOne.y := by
  norm_num [heuristicOne,heuristicMinusTwo,heuristicHalf,heuristicAnchor]

end Chapter02DICOPTExamples
