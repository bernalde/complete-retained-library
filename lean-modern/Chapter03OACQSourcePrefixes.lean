module

public import Chapter03
public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! Concrete source recurrence for the CQ-failing x²≤0 witness.
No KKT-bearing EventValid or generic driver is used. -/
noncomputable section
namespace Chapter03.CQSourcePrefixes
open Chapter02

abbrev P := ℝ × ℝ
abbrev Candidate := ℝ × Bool × ℝ

def f (p : P) : ℝ := -p.1+(p.2-1/2)^2
def relaxation : Set P := {p | p.1^2 ≤ 0 ∧ -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}
def seed : P := (0,1/2)
def anchor (b : Bool) : P := (0,bit b)
def fixedSet : Set ℝ := {x | x^2 ≤ 0 ∧ -1 ≤ x ∧ x ≤ 1}
def objectiveTangent (a p : P) : ℝ :=
  f a - (p.1-a.1) + 2*(a.2-1/2)*(p.2-a.2)
def constraintTangent (a p : P) : ℝ := a.1^2+2*a.1*(p.1-a.1)

def fx : P →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
def fy : P →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
def Df (p : P) : P →L[ℝ] ℝ := -fx + (2*(p.2-1/2)) • fy
def row : Fin 5 → P → ℝ := ![fun p=>p.1^2,fun p=>-p.1-1,
  fun p=>p.1-1,fun p=>-p.2,fun p=>p.2-1]
def rowD (j : Fin 5) (p : P) : P →L[ℝ] ℝ :=
  ![(2*p.1) • fx,-fx,fx,-fy,fy] j

theorem objective_derivative (p : P) : HasFDerivAt f (Df p) p := by
  exact fx.hasFDerivAt.neg.add (Chapter03.FPUnboundedControls.square_derivative fy (1/2) p)

theorem row_derivative (j : Fin 5) (p : P) : HasFDerivAt (row j) (rowD j p) p := by
  fin_cases j
  · simpa [row,rowD,fx] using Chapter03.FPUnboundedControls.square_derivative fx 0 p
  · exact fx.hasFDerivAt.neg.sub_const 1
  · exact fx.hasFDerivAt.sub_const 1
  · exact fy.hasFDerivAt.neg
  · exact fy.hasFDerivAt.sub_const 1

theorem objective_convex : ConvexOn ℝ Set.univ f := by
  exact (Chapter03.FPTrace.linear_convex convex_univ (-fx)).add
    (Chapter03.FPUnboundedControls.square_convex convex_univ fy (1/2))

theorem rows_convex (j : Fin 5) : ConvexOn ℝ Set.univ (row j) := by
  fin_cases j
  · simpa [row,fx] using Chapter03.FPUnboundedControls.square_convex convex_univ fx 0
  · exact (Chapter03.FPTrace.linear_convex convex_univ (-fx)).add_const (-1)
  · exact (Chapter03.FPTrace.linear_convex convex_univ fx).add_const (-1)
  · exact Chapter03.FPTrace.linear_convex convex_univ (-fy)
  · exact (Chapter03.FPTrace.linear_convex convex_univ fy).add_const (-1)

theorem derivative_continuity : Continuous Df ∧ ∀j,Continuous (rowD j) := by
  constructor
  · exact continuous_const.add
      ((continuous_const.mul (continuous_snd.sub continuous_const)).smul continuous_const)
  · intro j
    fin_cases j
    · exact (continuous_const.mul continuous_fst).smul continuous_const
    all_goals exact continuous_const

theorem source_tangent_identity (a p : P) :
    f a + Df a (p-a)=objectiveTangent a p ∧
    row 0 a + rowD 0 a (p-a)=constraintTangent a p := by
  simp [Df,fx,fy,objectiveTangent,constraintTangent,row,rowD]
  ring

theorem source_rows (p : P) : (∀j,row j p≤0) ↔ p∈relaxation := by
  simp only [Fin.forall_fin_succ]
  simp [row,relaxation]
  intros
  constructor <;> intro h <;> linarith

theorem seed_rows_exact (p : P) :
    (∀j,row j seed + rowD j seed (p-seed)≤0) ↔
    -1≤p.1 ∧ p.1≤1 ∧ 0≤p.2 ∧ p.2≤1 := by
  simp [Fin.forall_fin_succ,row,rowD,seed,fx,fy]

/-- The sole nonlinear row is active with zero derivative at every fixed solve. -/
theorem nonlinear_row_selection :
    (¬∃ (L : P →L[ℝ] ℝ) (c : ℝ), ∀p,row 0 p=L p+c) ∧
    (∀j:Fin 5,j≠0 → ∃ (L : P →L[ℝ] ℝ) (c : ℝ), ∀p,row j p=L p+c) ∧
    ∀b,row 0 (anchor b)=0 ∧ rowD 0 (anchor b)=0 := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨L,c,h⟩
    have h0 := h (0,0)
    have h1 := h (1,0)
    have h2 := h (2,0)
    have hs : L (2,0)=2*L (1,0) := by
      have hh := L.map_smul (2:ℝ) (1,0)
      simpa using hh
    simp [row] at h0 h1 h2
    norm_num at h0 h1 h2
    have hz : L (0,0) = 0 := L.map_zero
    linarith [hz]
  · intro j hj
    fin_cases j
    · exact False.elim (hj rfl)
    · exact ⟨-fx,-1,fun p=>by simp [row,fx]; ring⟩
    · exact ⟨fx,-1,fun p=>by simp [row,fx]; ring⟩
    · exact ⟨-fy,0,fun p=>by simp [row,fy]⟩
    · exact ⟨fy,-1,fun p=>by simp [row,fy]; ring⟩
  · intro b
    simp [row,rowD,anchor]

theorem relaxation_bounded : Bornology.IsBounded relaxation := by
  apply (isCompact_Icc : IsCompact (Set.Icc ((-1,0):P) ((1,1):P))).isBounded.subset
  intro p hp
  exact ⟨⟨hp.2.1,hp.2.2.2.1⟩,⟨hp.2.2.1,hp.2.2.2.2⟩⟩

/-- An active zero-gradient nonlinear row and a nonzero objective x-gradient:
no LICQ is asserted or imported from the qualified KKT execution. -/
theorem cq_failure_witness (b : Bool) :
    row 0 (anchor b)=0 ∧ rowD 0 (anchor b)=0 ∧ Df (anchor b) (1,0)=-1 := by
  simp [row,rowD,Df,anchor,fx,fy]

theorem initializer : IsMinimizer relaxation f seed := by
  refine ⟨by norm_num [relaxation,seed], ?_⟩
  rintro ⟨x,y⟩ hp
  have hx : x=0 := by nlinarith [hp.1, sq_nonneg x]
  subst x
  simpa [f,seed] using sq_nonneg (y-1/2)

theorem seed_fractional : ¬ ∃ k : ℤ, seed.2 = (k:ℝ) := by
  rintro ⟨k,h⟩
  have hl : (0:ℝ)<(k:ℝ) := by rw [←h]; norm_num [seed]
  have hu : (k:ℝ)<1 := by rw [←h]; norm_num [seed]
  have : 0<k ∧ k<1 := ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩
  omega

theorem fixed_minimum (b : Bool) : IsMinimizer fixedSet (fun x => f (x,bit b)) 0 := by
  refine ⟨by norm_num [fixedSet], ?_⟩
  intro x hx
  have : x=0 := by nlinarith [hx.1, sq_nonneg x]
  subst x
  exact le_refl _

theorem anchor_value (b : Bool) : f (anchor b)=1/4 := by
  cases b <;> norm_num [f,anchor,bit]

theorem original_correspondence (x : ℝ) (b : Bool) :
    ((x,bit b)∈relaxation ↔ (x,b)∈Chapter03.cqOriginal) ∧
    f (x,bit b)=Chapter03.cqCost (x,b) := by
  cases b <;> simp [relaxation,Chapter03.cqOriginal,f,Chapter03.cqCost,bit]

theorem tangent_at_seed (p : P) : objectiveTangent seed p = -p.1 := by
  simp [objectiveTangent,f,seed]

theorem tangent_at_anchor (b : Bool) (p : P) :
    objectiveTangent (anchor b) p =
      1/4-p.1+(if b then p.2-1 else -p.2) := by
  cases b <;> simp [objectiveTangent,f,anchor,bit] <;> ring

theorem nonlinear_tangent_zero (b : Bool) (p : P) :
    constraintTangent seed p=0 ∧ constraintTangent (anchor b) p=0 := by
  simp [constraintTangent,seed,anchor]

/-- Actual history: target0, then target1, then target0 forever. -/
def history : ℕ → List Bool
  | 0 => []
  | 1 => [false]
  | n+2 => false :: true :: List.replicate n false

def target : ℕ → Bool
  | 1 => true
  | _ => false

def master (H : List Bool) : Set Candidate :=
  {z | -1≤z.1 ∧ z.1≤1 ∧ -z.1≤z.2.2 ∧
    ∀ b∈H, objectiveTangent (anchor b) (z.1,bit z.2.1)≤z.2.2}

def sourceMaster (H : List Bool) : Set Candidate :=
  {z | (∀j,row j seed+rowD j seed ((z.1,bit z.2.1)-seed)≤0) ∧
    objectiveTangent seed (z.1,bit z.2.1)≤z.2.2 ∧
    (∀b∈H,objectiveTangent (anchor b) (z.1,bit z.2.1)≤z.2.2) ∧
    (∀b∈H,constraintTangent (anchor b) (z.1,bit z.2.1)≤0)}

theorem source_master_eq (H : List Bool) : sourceMaster H=master H := by
  ext z
  simp only [sourceMaster,master,Set.mem_setOf_eq,seed_rows_exact,tangent_at_seed]
  have hy : 0≤bit z.2.1 ∧ bit z.2.1≤1 := by cases z.2.1 <;> norm_num [bit]
  have hz : ∀b∈H,constraintTangent (anchor b) (z.1,bit z.2.1)≤0 := by
    intro b hb
    simp [constraintTangent,anchor]
  tauto

def exclusions (_n : ℕ) : Finset Bool := ∅

def chosen : ℕ → Candidate
  | 0 => (1,false,-1)
  | 1 => (1,true,-1)
  | _+2 => (1,false,-3/4)

def upper : ℕ → Option ℝ
  | 0 => none
  | _+1 => some (1/4)

def lower : ℕ → ℝ
  | 0 => 0
  | 1 => -1
  | 2 => -1
  | _+3 => -3/4

def record (u : Option ℝ) (v : ℝ) : Option ℝ :=
  match u with | none => some v | some old => some (min old v)

def openGap (epsilon : ℝ) (n : ℕ) : Prop :=
  match upper n with | none => True | some u => epsilon < u-lower n

theorem history_append (n : ℕ) : history (n+1)=history n++[target n] := by
  rcases n with _|n
  · rfl
  rcases n with _|n
  · rfl
  simp [history,target,List.replicate_succ']

theorem history_length (n : ℕ) : (history n).length=n := by
  rcases n with _|n
  · rfl
  rcases n with _|n
  · rfl
  simp [history]

theorem accumulated_master (n : ℕ) : master (history (n+2))=Chapter03.cqMaster := by
  ext z
  simp only [master,history,Set.mem_setOf_eq,List.mem_cons,forall_eq_or_imp]
  simp only [tangent_at_anchor, Bool.false_eq_true, ↓reduceIte,Chapter03.cqMaster,Set.mem_setOf_eq]
  constructor
  · rintro ⟨hl,hu,h0,hf,ht,_⟩
    exact ⟨hl,hu,h0,by linarith,by linarith⟩
  · rintro ⟨hl,hu,h0,hf,ht⟩
    refine ⟨hl,hu,h0,by linarith,by linarith,?_⟩
    intro b hb
    have : b=false := (List.mem_replicate.mp hb).2
    subst b
    simpa using (show 1/4-z.1 + -bit z.2.1 ≤ z.2.2 by linarith)

theorem chosen_minimum (n : ℕ) :
    IsMinimizer (master (history n)) (fun z => z.2.2) (chosen n) := by
  rcases n with _|n
  · refine ⟨by norm_num [master,history,chosen], ?_⟩
    intro z hz
    change -1 ≤ z.2.2
    linarith [hz.2.1,hz.2.2.1]
  rcases n with _|n
  · refine ⟨?_, ?_⟩
    · norm_num [master,history,chosen,tangent_at_anchor,bit]
    · intro z hz
      change -1 ≤ z.2.2
      linarith [hz.2.1,hz.2.2.1]
  · rw [accumulated_master]
    exact Chapter03.cq_master_optimal

theorem target_link (n : ℕ) : (chosen n).2.1=target n := by
  rcases n with _|n
  · rfl
  rcases n with _|n <;> rfl

theorem bound_updates (n : ℕ) :
    lower (n+1)=(chosen n).2.2 ∧
    upper (n+1)=record (upper n) (f (anchor (target n))) := by
  rw [anchor_value]
  rcases n with _|n
  · norm_num [lower,chosen,upper,record]
  rcases n with _|n
  · norm_num [lower,chosen,upper,record]
  · norm_num [lower,chosen,upper,record]

theorem always_open (epsilon : ℝ) (he : epsilon < 1) (n : ℕ) : openGap epsilon n := by
  rcases n with _|n
  · trivial
  rcases n with _|n
  · change epsilon < (1/4:ℝ)-(-1)
    linarith
  rcases n with _|n
  · change epsilon < (1/4:ℝ)-(-1)
    linarith
  · change epsilon < (1/4:ℝ)-(-3/4)
    linarith

/-- Every actual finite prefix has attained exact solves, source min-update,
unchanged empty exclusions and an open delayed gap. No KKT premise. -/
theorem cq_exact_prefixes (epsilon : ℝ) (he0 : 0≤epsilon) (he1 : epsilon<1) :
    0≤epsilon ∧ IsMinimizer relaxation f seed ∧
    (¬∃k:ℤ,seed.2=(k:ℝ)) ∧
    IsMinimizer Chapter03.cqOriginal Chapter03.cqCost (0,false) ∧
    ∀ n, (history n).length=n ∧ history (n+1)=history n++[target n] ∧
      IsMinimizer (master (history n)) (fun z=>z.2.2) (chosen n) ∧
      IsMinimizer (sourceMaster (history n)) (fun z=>z.2.2) (chosen n) ∧
      exclusions (n+1)=exclusions n ∧ exclusions n=∅ ∧
      (chosen n).2.1=target n ∧
      IsMinimizer fixedSet (fun x=>f (x,bit (target n))) 0 ∧
      lower (n+1)=(chosen n).2.2 ∧
      upper (n+1)=record (upper n) (f (anchor (target n))) ∧
      openGap epsilon n := by
  refine ⟨he0,initializer,seed_fractional,Chapter03.cq_original_optimal,?_⟩
  intro n
  exact ⟨history_length n,history_append n,chosen_minimum n,by rw [source_master_eq]; exact chosen_minimum n,
    rfl,rfl,target_link n,
    fixed_minimum _,(bound_updates n).1,(bound_updates n).2,always_open epsilon he1 n⟩

end Chapter03.CQSourcePrefixes
