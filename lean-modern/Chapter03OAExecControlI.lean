module

public import Chapter03OAExecControlBase

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Controls.I

def seed : P := pt (1/2) (11/16)
def slack : RealVector 3 := ![7/16,0,0]

theorem rows (p : P) : (∀j,data.g j p≤0) ↔
    (p.1 0)^2+7/16≤p.2 0 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  simp [data,Fin.forall_fin_succ]

theorem relaxation (p : P) : p∈data.relaxationOn Set.univ ↔
    (p.1 0)^2+7/16≤p.2 0 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  change ((p∈Set.univ ∧ ∀j,data.g j p≤0) ∧ p∈data.linearRegion ∧
    ∀i,data.lo i≤p.2 i ∧ p.2 i≤data.hi i) ↔ _
  rw [rows]
  simp only [hard,Set.mem_univ,true_and]
  simp [data,scalar,Fin.forall_fin_one]

theorem thesis_relaxation_identity :
    {p : P | ∀j,data.g j p≤0}=data.relaxationOn Set.univ := by
  ext p; exact (rows p).trans (relaxation p).symm

theorem seed_minimum : IsMinimizer (data.relaxationOn Set.univ) objective seed := by
  refine ⟨(relaxation seed).mpr (by norm_num [seed,pt,scalar]),?_⟩
  intro p hp
  have hg := ((relaxation p).mp hp).1
  norm_num [objective,seed,pt,scalar]
  nlinarith [sq_nonneg (p.1 0-1/2)]

theorem seed_unique {p : P} (hp : IsMinimizer (data.relaxationOn Set.univ) objective p) :
    p=seed := by
  have hg := ((relaxation p).mp hp.1).1
  have hh := hp.2 seed seed_minimum.1
  norm_num [objective,seed,pt,scalar] at hh
  have hx : p.1 0=1/2 := by nlinarith [sq_nonneg (p.1 0-1/2)]
  apply point_ext
  · simpa [seed,pt,scalar] using hx
  · norm_num [seed,pt,scalar]; nlinarith

theorem fiber_membership (x : V) (b : ℝ) : x∈fiber data (scalar b) ↔
    (x 0)^2+7/16≤b ∧ 0≤b ∧ b≤1 := by
  change ((x,scalar b)∈data.linearRegion ∧ ∀j,data.g j (x,scalar b)≤0) ↔ _
  rw [rows]
  simp [scalar]

theorem zero_fiber_empty : ¬ (fiber data (scalar 0)).Nonempty := by
  rintro ⟨x,hx⟩
  have hh := ((fiber_membership x 0).mp hx).1
  nlinarith [sq_nonneg (x 0)]

theorem fixed_minimum :
    IsMinimizer (fiber data (scalar 1)) (fiberObjective objective (scalar 1)) (scalar (3/4)) := by
  refine ⟨(fiber_membership _ _).mpr (by norm_num [scalar]),?_⟩
  intro x hx
  have hh := ((fiber_membership x 1).mp hx).1
  norm_num [fiberObjective,objective,scalar]
  nlinarith [sq_nonneg (x 0-3/4)]

theorem fixed_unique {x : V}
    (hx : IsMinimizer (fiber data (scalar 1)) (fiberObjective objective (scalar 1)) x) :
    x=scalar (3/4) := by
  have hh := ((fiber_membership x 1).mp hx.1).1
  have hm := hx.2 (scalar (3/4)) fixed_minimum.1
  norm_num [fiberObjective,objective,scalar] at hm
  apply scalar_ext
  norm_num [scalar]
  nlinarith [sq_nonneg (x 0-3/4)]

def fixedKKT : FixedKKT data objective (scalar (3/4)) (scalar 1) where
  Df := Df
  Dg := Dg (pt (3/4) 1)
  lambda := ![2/3,0,0]
  mu := Fin.elim0
  primal := fixed_minimum.1
  derivative_f := objective_derivative _
  derivative_g := row_derivative _
  lambda_nonneg := by intro j; fin_cases j <;> norm_num
  mu_nonneg i := Fin.elim0 i
  soft_compl := by intro j; fin_cases j <;> norm_num [soft,data,scalar]
  hard_compl i := Fin.elim0 i
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    norm_num [restrict_apply,Df,Dg,pt,scalar,Fin.sum_univ_succ]
    ring

theorem restoration_primal :
    weightedInsert (scalar 0) slack ∈ restSet data (scalar 0) := by
  rw [restSet_insert_iff]
  refine ⟨fun i => Fin.elim0 i,?_,?_⟩ <;>
    intro j <;> fin_cases j <;> norm_num [soft,data,slack,scalar]

theorem restoration_bound (x : V) (s : RealVector 3)
    (hg : ∀j,data.g j (x,scalar 0)≤s j) (hs : ∀j,0≤s j) :
    (x 0)^2+7/16≤∑j,s j := by
  have hh := hg 0
  norm_num [data,scalar] at hh
  norm_num [Fin.sum_univ_succ]
  linarith [hs 1,hs 2]

theorem restoration_minimum :
    IsMinimizer (restSet data (scalar 0)) (restCost (n:=1) (l:=3))
      (weightedInsert (scalar 0) slack) := by
  refine ⟨restoration_primal,?_⟩
  intro q hq
  have hq' : weightedInsert (weightedX (n:=1) (s:=3) q)
      (weightedV (n:=1) (s:=3) q)∈restSet data (scalar 0) := by
    rw [weightedInsert_project]; exact hq
  obtain ⟨_,hg,hs⟩ := (restSet_insert_iff data (scalar 0) _ _).mp hq'
  have hb := restoration_bound _ _ hg hs
  change weightedLiftObjective (n:=1) (fun _ : Fin 3 => 1) _ ≤
    weightedLiftObjective (n:=1) (fun _ : Fin 3 => 1) q
  rw [weightedLiftObjective_apply,weightedLiftObjective_apply,weightedV_insert]
  norm_num [slack,Fin.sum_univ_succ,one_mul] at hb ⊢
  nlinarith [sq_nonneg (weightedX (n:=1) (s:=3) q 0)]

theorem restoration_unique {x : V} {s : RealVector 3}
    (hm : IsMinimizer (restSet data (scalar 0)) (restCost (n:=1) (l:=3))
      (weightedInsert x s)) : x=scalar 0 ∧ s=slack := by
  obtain ⟨_,hg,hs⟩ := (restSet_insert_iff data (scalar 0) x s).mp hm.1
  have hb := restoration_bound x s hg hs
  have hm' := hm.2 _ restoration_primal
  rw [restCost_insert,restCost_insert] at hm'
  norm_num [slack,Fin.sum_univ_succ] at hm' hb
  have h0 := hg 0
  norm_num [soft,data,scalar] at h0
  have hx : x 0=0 := by nlinarith [sq_nonneg (x 0)]
  refine ⟨scalar_ext hx,?_⟩
  have hs0 : s 0=7/16 := by nlinarith [hs 1,hs 2,sq_nonneg (x 0)]
  have hs1 : s 1=0 := by linarith [hs 1,hs 2]
  have hs2 : s 2=0 := by linarith [hs 1,hs 2]
  ext j; fin_cases j <;> simp [slack,hs0,hs1,hs2]

theorem restoration_value : restCost (weightedInsert (scalar 0) slack)=(7/16:ℝ) := by
  rw [restCost_insert]; norm_num [slack,Fin.sum_univ_succ]

theorem objective_tangent (a q : P) : objective a+Df (q-a)=objective q := by
  simp [objective,Df]; ring

theorem row_tangent (a q : P) :
    data.g 0 a+Dg a 0 (q-a)=2*a.1 0*q.1 0-(a.1 0)^2+7/16-q.2 0 := by
  norm_num [data,Dg]; ring

theorem seed_row_tangent (q : P) :
    data.g 0 seed+Dg seed 0 (q-seed)=q.1 0-q.2 0+3/16 := by
  rw [row_tangent]; norm_num [seed,pt,scalar]; ring

theorem fixed_row_tangent (q : P) :
    data.g 0 (pt (3/4) 1)+Dg (pt (3/4) 1) 0 (q-pt (3/4) 1)=
      (3/2)*q.1 0-q.2 0-1/8 := by
  rw [row_tangent]; norm_num [pt,scalar]; ring

theorem restoration_row_tangent (q : P) :
    data.g 0 (pt 0 0)+Dg (pt 0 0) 0 (q-pt 0 0)=7/16-q.2 0 := by
  rw [row_tangent]; norm_num [pt,scalar]

theorem selected_rows (a q : P) (ha : 0≤data.g 0 a) :
    (∀j, (¬ AffineRow (data.g j) ∧ 0≤data.g j a) →
      data.g j a+Dg a j (q-a)≤0) ↔ data.g 0 a+Dg a 0 (q-a)≤0 := by
  simp only [row_classification]
  constructor
  · intro h; exact h 0 ⟨rfl,ha⟩
  · intro h j hj; rcases hj with ⟨rfl,_⟩; exact h

end Chapter03.OAExec.Controls.I
