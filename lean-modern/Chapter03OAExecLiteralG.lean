module

public import Chapter03OAExecArticleData

@[expose] public section

/-! A separate literal published policy, preserving its reversed improving
comparison. Absence denotes +infinity for U and unassigned output coordinates.
This module does not import the corrected recursive driver. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open scoped BigOperators
namespace Chapter03.OAExec.Article.LiteralG

def anchor (b : ℤ) : P := pt 0 (b:ℝ)
def seed : P := pt 0 (1/2)

def family (H : List ℤ) : TangentFamily 1 1 1 (H.length+1) where
  origin := Fin.cases seed (fun i => anchor (H.get i))
  selected := Fin.cases Set.univ (fun _ => ∅)
  derivative i := Gdg (Fin.cases seed (fun j => anchor (H.get j)) i)

def objectiveDerivatives (H : List ℤ) (i : Fin (H.length+1)) : P →L[ℝ] ℝ :=
  Gdf ((family H).origin i)

theorem later_rows_exact (b : ℤ) :
    {j | ¬ AffineRow (G.g j) ∧ 0 ≤ G.g j (anchor b)} = ∅ := by
  ext j
  norm_num [G,boxModel,xSquareRow,anchor,pt,scalar]

theorem all_derivatives (H : List ℤ) :
    (∀ i j, HasFDerivAt (G.g j) ((family H).derivative i j) ((family H).origin i)) ∧
    (∀ i, HasFDerivAt Gf (objectiveDerivatives H i) ((family H).origin i)) := by
  exact ⟨fun _ _ => xSquareRow_derivative _ _,fun _ => quadratic_derivative _ _⟩

def tangent (b : ℤ) (y : ℝ) : ℝ := ((b:ℝ)-1/2)^2+2*((b:ℝ)-1/2)*(y-b)

def master (H C : List ℤ) : Set (P × ℝ) :=
  {z | z ∈ Chapter06.EpigraphMaster G Gf (family H) (objectiveDerivatives H) Set.univ ∧
    ∀ b ∈ C, z.1.2 0 ≠ (b:ℝ)}

theorem master_iff (H C : List ℤ) (z : P × ℝ) : z ∈ master H C ↔
    (-1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1) ∧
    (z.1.2 0=0 ∨ z.1.2 0=1) ∧ 0 ≤ z.2 ∧
    (∀ b ∈ H, tangent b (z.1.2 0) ≤ z.2) ∧
    (∀ b ∈ C, z.1.2 0 ≠ (b:ℝ)) := by
  have hi : z.1 ∈ IntegerCylinder G.lo G.hi ↔ z.1.2 0=0 ∨ z.1.2 0=1 := by
    constructor
    · rintro ⟨y,hy,he⟩
      have hy' := (binary_box (-1) 1 _ y).mp hy
      rcases hy' with h | h <;> simp [he,h]
    · intro h
      rcases h with h | h
      · refine ⟨fun _ => 0,?_,?_⟩
        · intro i; norm_num [G,boxModel,scalar]
        · ext i; fin_cases i; simpa using h
      · refine ⟨fun _ => 1,?_,?_⟩
        · intro i; norm_num [G,boxModel,scalar]
        · ext i; fin_cases i; simpa using h
  have hc : z.1 ∈ (family H).cutRegion G := by
    intro i j hj
    refine Fin.cases ?_ (fun k => ?_) i
    · norm_num [G,boxModel,xSquareRow,family,Gdg,xSquareD,seed,pt,scalar]
    · norm_num [G,boxModel,xSquareRow,family,Gdg,xSquareD,anchor,pt,scalar]
  have ho : (∀ i, Gf ((family H).origin i)+objectiveDerivatives H i
      (z.1-(family H).origin i) ≤ z.2) ↔
      0 ≤ z.2 ∧ ∀ b ∈ H, tangent b (z.1.2 0) ≤ z.2 := by
    rw [Fin.forall_fin_succ]
    have he (i : Fin H.length) : Gf ((family H).origin i.succ)+
        objectiveDerivatives H i.succ (z.1-(family H).origin i.succ)=
        tangent (H.get i) (z.1.2 0) := by
      simp [family,objectiveDerivatives,Gf,Gdf,quadratic,quadraticD,anchor,pt,scalar,tangent]
    simp only [he]
    have hs : Gf ((family H).origin 0)+objectiveDerivatives H 0
        (z.1-(family H).origin 0)=0 := by
      norm_num [family,objectiveDerivatives,Gf,Gdf,quadratic,quadraticD,seed,pt,scalar]
    rw [hs]
    constructor
    · intro h
      refine ⟨h.1,?_⟩
      intro b hb
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hb
      exact h.2 i
    · intro h
      exact ⟨h.1,fun i => h.2 (H.get i) (List.get_mem _ _)⟩
  change (z.1 ∈ G.masterOn (family H) Set.univ ∧ _) ∧ _ ↔ _
  rw [ho]
  simp only [ModelData.masterOn,MixedFeasible,Set.mem_inter_iff,Set.mem_univ,
    true_and,hc,true_and,hi]
  rw [show G.linearRegion=(boxModel (-1) 1 (xSquareRow 4)).linearRegion from rfl,
    box_hard]
  tauto

@[ext] structure State where
  history : List ℤ
  excluded : List ℤ
  lower : ℝ
  upper : Option ℝ
  output : Option P

/-- C^1=empty is an explicit indexing completion. -/
def initial : State := ⟨[],[],0,none,none⟩

def gapOpen (epsilon : ℝ) (s : State) : Prop :=
  match s.upper with
  | none => True
  | some u => epsilon < u-s.lower

def wronglyImproves (upper : Option ℝ) (v : ℝ) : Prop :=
  match upper with
  | none => False
  | some u => u<v

def store (s : State) (b : ℤ) : Option ℝ × Option P := by
  classical
  exact if wronglyImproves s.upper (Gf (anchor b)) then
    (some (Gf (anchor b)),some (anchor b)) else (s.upper,s.output)

inductive Reply (s : State)
  | attained (z : P × ℝ) (minimum : IsMinimizer (master s.history s.excluded) Prod.snd z)
  | unbounded (z : P × ℝ) (mem : z ∈ master s.history s.excluded)
      (below : ∀ r : ℝ, ∃ w ∈ master s.history s.excluded, w.2<r)

def Reply.point {s : State} : Reply s → P × ℝ
  | .attained z _ => z
  | .unbounded z _ _ => z

def Reply.nextLower {s : State} : Reply s → ℝ
  | .attained z _ => z.2
  | .unbounded _ _ _ => s.lower

/-- The empty-master completion returns infeasibility immediately: it never
evaluates infinity-minus-infinity. The theorem below proves it unreachable in
the exhibited G execution. This convention leaves all displayed G steps intact. -/
def emptyExit (s : State) : Prop := ¬ (master s.history s.excluded).Nonempty

/-- A literal successful round, with delayed guard and exact mandatory fixed
solve before recursion. Every G fixed minimum is uniquely x=0. -/
inductive Step (epsilon : ℝ) (s : State) : State → Prop
  | solve (openGap : gapOpen epsilon s) (reply : Reply s) (b : ℤ)
      (target : reply.point.1.2 0=(b:ℝ))
      (fixed : IsMinimizer (fiber G (scalar (b:ℝ)))
        (fiberObjective Gf (scalar (b:ℝ))) (scalar 0)) :
      Step epsilon s
        ⟨s.history++[b],s.excluded,reply.nextLower,(store s b).1,(store s b).2⟩

def chosen (n : ℕ) : ℤ := if n=0 then 0 else 1
def history (n : ℕ) : List ℤ := (List.range n).map chosen
def lower (n : ℕ) : ℝ := if n≤2 then 0 else 1/4
def trace (n : ℕ) : State := ⟨history n,[],lower n,none,none⟩
def trial (n : ℕ) : P × ℝ := (anchor (chosen n),if n<2 then 0 else 1/4)

theorem history_succ (n : ℕ) : history (n+1)=history n++[chosen n] := by
  simp [history,List.range_succ]

theorem history_mem (n : ℕ) {b : ℤ} (hb : b ∈ history n) : b=0 ∨ b=1 := by
  rcases List.mem_map.mp hb with ⟨k,hk,rfl⟩
  by_cases h : k=0 <;> simp [chosen,h]

theorem trial_minimum (n : ℕ) :
    IsMinimizer (master (history n) []) Prod.snd (trial n) := by
  refine ⟨?_,?_⟩
  · rw [master_iff]
    refine ⟨?_,?_,?_,?_,by simp⟩
    · norm_num [trial,anchor,pt,scalar]
    · by_cases h : n=0 <;> simp [trial,anchor,pt,scalar,chosen,h]
    · dsimp [trial]
      split_ifs <;> norm_num
    · intro b hb
      rcases history_mem n hb with rfl | rfl
      · by_cases hn : n<2
        · have hn0 : n≠0 := by intro h; subst n; simpa [history] using hb
          norm_num [trial,chosen,hn,hn0,anchor,pt,scalar,tangent]
        · norm_num [trial,chosen,hn,show n≠0 by omega,anchor,pt,scalar,tangent]
      · have hn : ¬ n<2 := by
          intro h
          interval_cases n <;> norm_num [history,chosen] at hb
        norm_num [trial,chosen,hn,show n≠0 by omega,anchor,pt,scalar,tangent]
  · intro z hz
    obtain ⟨hx,hy,hheight,hcuts,hC⟩ := (master_iff _ _ _).mp hz
    by_cases hn : n<2
    · simpa [trial,hn] using hheight
    · have h0 : (0:ℤ) ∈ history n := by
        apply List.mem_map.mpr
        exact ⟨0,List.mem_range.mpr (by omega),by simp [chosen]⟩
      have h1 : (1:ℤ) ∈ history n := by
        apply List.mem_map.mpr
        exact ⟨1,List.mem_range.mpr (by omega),by simp [chosen]⟩
      rcases hy with hy | hy
      · have h := hcuts 0 h0
        norm_num [tangent,hy] at h
        simpa [trial,hn] using h
      · have h := hcuts 1 h1
        norm_num [tangent,hy] at h
        simpa [trial,hn] using h

theorem trace_initial : trace 0=initial := by rfl

theorem infinite_exact_step (epsilon : ℝ) (n : ℕ) :
    Step epsilon (trace n) (trace (n+1)) := by
  have hs := Step.solve (s:=trace n) (epsilon:=epsilon) (by trivial)
    (Reply.attained (trial n) (trial_minimum n)) (chosen n) rfl
    (G_fiber_minimum (scalar (chosen n:ℝ)))
  convert hs using 1
  apply State.ext
  · exact history_succ n
  · rfl
  · have h : (n+1≤2) ↔ n<2 := by omega
    simp only [trace,Reply.nextLower,trial,lower,h]
  · simp [trace,store,wronglyImproves]
  · simp [trace,store,wronglyImproves]

theorem literal_infinite_execution (epsilon : ℝ) :
    trace 0=initial ∧ (∀ n, Step epsilon (trace n) (trace (n+1))) ∧
    (∀ n, gapOpen epsilon (trace n)) ∧
    (∀ n, (trace n).upper=none ∧ (trace n).output=none) ∧
    (∀ n, ¬ emptyExit (trace n)) := by
  refine ⟨trace_initial,infinite_exact_step epsilon,fun _ => trivial,
    fun _ => ⟨rfl,rfl⟩,?_⟩
  intro n h
  exact h ⟨trial n,(trial_minimum n).1⟩

end Chapter03.OAExec.Article.LiteralG
