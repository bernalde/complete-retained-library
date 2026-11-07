module

public import Chapter03OAExecControlBase

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Controls.U

def seed : P := pt 0 (1/2)

theorem rows (p : P) : (∀j,data.g j p≤0) ↔
    p.1 0=0 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  constructor
  · intro h
    have h0:=h 0; have h3:=h 3; have h4:=h 4
    change (p.1 0)^2≤0 at h0
    change -p.2 0≤0 at h3
    change p.2 0-1≤0 at h4
    exact ⟨by nlinarith [sq_nonneg (p.1 0)],by linarith,by linarith⟩
  · rintro ⟨hx,hy0,hy1⟩ j
    have hm := mul_nonneg hy0 (sub_nonneg.mpr hy1)
    fin_cases j <;> norm_num [data,hx] <;> nlinarith

theorem relaxation (p : P) : p∈data.relaxationOn Set.univ ↔
    p.1 0=0 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  change ((p∈Set.univ ∧ ∀j,data.g j p≤0) ∧ p∈data.linearRegion ∧
    ∀i,data.lo i≤p.2 i ∧ p.2 i≤data.hi i) ↔ _
  rw [rows]
  simp only [hard,Set.mem_univ,true_and]
  simp [data,scalar,Fin.forall_fin_one]

theorem thesis_relaxation_identity :
    {p : P | ∀j,data.g j p≤0}=data.relaxationOn Set.univ := by
  ext p; exact (rows p).trans (relaxation p).symm

theorem relaxation_compact : IsCompact (data.relaxationOn Set.univ) := by
  have he : data.relaxationOn Set.univ=(fun t : ℝ => pt 0 t) '' Set.Icc 0 1 := by
    ext p
    rw [relaxation]
    constructor
    · rintro ⟨hx,hy0,hy1⟩
      exact ⟨p.2 0,⟨hy0,hy1⟩,point_ext (by simpa [pt,scalar] using hx.symm) rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨rfl,ht⟩
  rw [he]
  apply isCompact_Icc.image
  unfold pt scalar
  fun_prop

theorem seed_minimum : IsMinimizer (data.relaxationOn Set.univ) objective seed := by
  refine ⟨(relaxation seed).mpr (by norm_num [seed,pt,scalar]),?_⟩
  intro p hp
  obtain ⟨hx,_,_⟩ := (relaxation p).mp hp
  simpa [objective,seed,pt,scalar,hx] using sq_nonneg (p.2 0-1/2)

theorem seed_unique {p : P} (hp : IsMinimizer (data.relaxationOn Set.univ) objective p) :
    p=seed := by
  obtain ⟨hx,_,_⟩ := (relaxation p).mp hp.1
  have hh := hp.2 seed seed_minimum.1
  norm_num [objective,seed,pt,scalar,hx] at hh
  apply point_ext
  · simpa [seed,pt,scalar] using hx
  · norm_num [seed,pt,scalar]
    nlinarith [sq_nonneg (p.2 0-1/2)]

theorem fiber_membership (x : V) (b : ℝ) : x∈fiber data (scalar b) ↔
    x 0=0 ∧ 0≤b ∧ b≤1 := by
  change ((x,scalar b)∈data.linearRegion ∧ ∀j,data.g j (x,scalar b)≤0) ↔ _
  rw [rows]
  simp [scalar]

theorem fixed_minimum (b : ℝ) (hb : b=0 ∨ b=1) :
    IsMinimizer (fiber data (scalar b)) (fiberObjective objective (scalar b)) (scalar 0) := by
  refine ⟨(fiber_membership _ _).mpr ?_,?_⟩
  · rcases hb with rfl|rfl <;> norm_num [scalar]
  · intro x hx
    have he := ((fiber_membership x b).mp hx).1
    simp [fiberObjective,objective,scalar,he]

theorem fixed_unique (b : ℝ) {x : V}
    (hx : IsMinimizer (fiber data (scalar b)) (fiberObjective objective (scalar b)) x) :
    x=scalar 0 := by
  apply scalar_ext
  exact ((fiber_membership x b).mp hx.1).1

def lambda (b : ℝ) : Fin 5 → ℝ := ![0,1-b,b,0,0]

def fixedKKT (b : ℝ) (hb : b=0 ∨ b=1) :
    FixedKKT data objective (scalar 0) (scalar b) where
  Df := Df (pt 0 b)
  Dg := Dg (pt 0 b)
  lambda := lambda b
  mu := Fin.elim0
  primal := (fixed_minimum b hb).1
  derivative_f := objective_derivative _
  derivative_g := row_derivative _
  lambda_nonneg := by intro j; rcases hb with rfl|rfl <;> fin_cases j <;> norm_num [lambda]
  mu_nonneg i := Fin.elim0 i
  soft_compl := by
    intro j; rcases hb with rfl|rfl <;> fin_cases j <;>
      norm_num [lambda,soft,data,scalar]
  hard_compl i := Fin.elim0 i
  stationarity := by
    apply ContinuousLinearMap.ext
    intro v
    rcases hb with rfl|rfl <;>
      norm_num [restrict_apply,Df,Dg,lambda,pt,scalar,Fin.sum_univ_succ]

theorem fixed_value (b : ℝ) (hb : b=0 ∨ b=1) : objective (pt 0 b)=1/4 := by
  rcases hb with rfl|rfl <;> norm_num [objective,pt,scalar]

/-- Actual fixed-x active family contains the zero derivative of x squared.
This is a precise LICQ failure, not a counterexample to a CQ-qualified theorem. -/
theorem fixed_active_not_independent (b : ℝ) :
    ¬ LinearIndependent ℝ
      (fun j : {j : Fin 5 // data.g j (pt 0 b)=0} => restrict (Dg (pt 0 b) j.1)) := by
  intro h
  have hn := LinearIndependent.ne_zero
    (⟨0,by norm_num [data,pt,scalar]⟩ : {j : Fin 5 // data.g j (pt 0 b)=0}) h
  simp [Dg,pt,scalar,restrict] at hn

theorem seed_objective_tangent (q : P) :
    objective seed+Df seed (q-seed)=q.1 0 := by
  norm_num [objective,Df,seed,pt,scalar]

theorem objective_tangent (b : ℝ) (hb : b=0 ∨ b=1) (q : P) :
    objective (pt 0 b)+Df (pt 0 b) (q-pt 0 b)=
      q.1 0+(2*b-1)*q.2 0+1/4-b := by
  rcases hb with rfl|rfl <;> norm_num [objective,Df,pt,scalar] <;> ring

theorem row_tangent (a q : P) (j : Fin 5) :
    data.g j a+Dg a j (q-a)=
      (![fun p : P => 2*a.1 0*p.1 0-(a.1 0)^2,
        fun p => 2*(a.1 0+a.2 0-1/2)*(p.1 0+p.2 0-1/2)-
          (a.1 0+a.2 0-1/2)^2-1/4,
        fun p => 2*(a.1 0-a.2 0+1/2)*(p.1 0-p.2 0+1/2)-
          (a.1 0-a.2 0+1/2)^2-1/4,
        fun p => -p.2 0,fun p => p.2 0-1] j q) := by
  fin_cases j <;> norm_num [data,Dg] <;> ring

theorem seed_rows (q : P) : (∀j,data.g j seed+Dg seed j (q-seed)≤0) ↔
    0≤q.2 0 ∧ q.2 0≤1 := by
  simp [data,Dg,seed,pt,scalar,Fin.forall_fin_succ]

theorem active_rows (b : ℝ) (hb : b=0 ∨ b=1) (q : P) :
    (∀j, (¬ AffineRow (data.g j) ∧ 0≤data.g j (pt 0 b)) →
      data.g j (pt 0 b)+Dg (pt 0 b) j (q-pt 0 b)≤0) ↔
    (if b=0 then -q.1 0-q.2 0≤0 ∧ q.1 0-q.2 0≤0
     else q.1 0+q.2 0-1≤0 ∧ -q.1 0+q.2 0-1≤0) := by
  simp only [row_classification]
  rcases hb with rfl|rfl <;>
    norm_num [data,Dg,pt,scalar,Fin.forall_fin_succ]
  all_goals intros; constructor <;> intro h <;> linarith

end Chapter03.OAExec.Controls.U
