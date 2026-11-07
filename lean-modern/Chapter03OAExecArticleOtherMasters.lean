module

public import Chapter03OAExecState
public import Chapter03OAExecArticleGMaster

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open scoped BigOperators
namespace Chapter03.OAExec.Article

theorem box_integer_iff (a b : ℝ) (g : P → ℝ) (p : P) :
    p ∈ IntegerCylinder (boxModel a b g).lo (boxModel a b g).hi ↔
      p.2 0=0 ∨ p.2 0=1 := G_integer_iff p

theorem T_event_characterization (e : Event Tdata) (he : EventValid Tdata e) :
    e.restoration=none ∧ e.x=scalar 0 := by
  have hn : e.restoration=none := by
    by_contra h
    exact event_empty he h ⟨scalar 0,(T_fiber_minimum (intCast e.target)).1⟩
  refine ⟨hn,?_⟩
  have hm := he.2
  rw [hn] at hm
  have hbound := hm.1.2 (scalar 0) (T_fiber_minimum (intCast e.target)).1
  have hlo := ((T_fiber _ _).mp hm.1.1).1
  have hx : e.x 0=0 := by
    change e.x 0+((e.target 0:ℝ)-1/4)^2 ≤ 0+((e.target 0:ℝ)-1/4)^2 at hbound
    linarith
  ext i
  fin_cases i
  exact hx

def Ttangent (b : ℤ) (y : ℝ) : ℝ := ((b:ℝ)-1/4)^2+2*((b:ℝ)-1/4)*(y-b)

theorem T_event_rows (e : Event Tdata) (he : EventValid Tdata e) (z : P × ℝ) :
    e.rows z ↔ z.1.1 0+Ttangent (e.target 0) (z.1.2 0) ≤ z.2 := by
  have hx := (T_event_characterization e he).2
  simp [Event.rows,Data.selected,Data.nonlinear,Tdata,T,boxModel,Event.anchor,hx,
    Tf,Tdf,Tdg,linearQuadratic,linearQuadraticD,xSquareRow,xSquareD,scalar,intCast,Ttangent]
  ring_nf

theorem T_master_iff (H : List (Event Tdata))
    (hH : ∀ e ∈ H, EventValid Tdata e) (z : P × ℝ) :
    z ∈ master Tdata (pt 0 (1/4)) H ↔
      (0 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1) ∧ (z.1.2 0=0 ∨ z.1.2 0=1) ∧
      z.1.1 0 ≤ z.2 ∧ ∀ e ∈ H, z.1.1 0+Ttangent (e.target 0) (z.1.2 0) ≤ z.2 := by
  rw [master_mem_iff]
  have hn : noGoods H z.1 := by
    intro e he hrest
    exact (hrest (T_event_characterization e (hH e he)).1).elim
  have hg : ∀ j, Tdata.model.g j (pt 0 (1/4))+
      Tdata.Dg (pt 0 (1/4)) j (z.1-pt 0 (1/4)) ≤ 0 := by
    intro j
    norm_num [Tdata,T,boxModel,Tdg,xSquareRow,xSquareD,pt,scalar]
  have hf : Tdata.f (pt 0 (1/4))+Tdata.Df (pt 0 (1/4))
      (z.1-pt 0 (1/4))=z.1.1 0 := by
    norm_num [Tdata,Tf,Tdf,linearQuadratic,linearQuadraticD,pt,scalar]
  have hr := forall₂_congr fun e he => T_event_rows e (hH e he) z
  change (z.1 ∈ T.linearRegion ∧ z.1 ∈ IntegerCylinder T.lo T.hi ∧ _ ∧ _ ∧ _) ↔ _
  rw [show T.linearRegion=(boxModel 0 1 (xSquareRow 2)).linearRegion from rfl,
    box_hard,show (z.1 ∈ IntegerCylinder T.lo T.hi ↔ _) from box_integer_iff 0 1 _ _,hf,hr]
  simp only [hg,hn,true_and,and_true,implies_true]

theorem T_master_attained (H : List (Event Tdata))
    (hH : ∀ e ∈ H, EventValid Tdata e) :
    ∃ z, IsMinimizer (master Tdata (pt 0 (1/4)) H) Prod.snd z := by
  classical
  have hb (e : Event Tdata) : e.target 0=0 ∨ e.target 0=1 :=
    (binary_box 0 1 _ e.target).mp e.target_mem
  by_cases h0 : ∃ e ∈ H, e.target 0=0
  · by_cases h1 : ∃ e ∈ H, e.target 0=1
    · refine ⟨(pt 0 0,1/16),?_,?_⟩
      · rw [T_master_iff H hH]
        refine ⟨by norm_num [pt,scalar],by simp [pt,scalar],by norm_num [pt,scalar],?_⟩
        intro e he
        rcases hb e with h | h <;> norm_num [Ttangent,h,pt,scalar]
      · intro z hz
        obtain ⟨hx,hy,hh,hc⟩ := (T_master_iff H hH z).mp hz
        rcases hy with hy | hy
        · obtain ⟨e,he,he0⟩ := h0
          have h := hc e he
          norm_num [Ttangent,he0,hy] at h
          linarith [hx.1]
        · obtain ⟨e,he,he1⟩ := h1
          have h := hc e he
          norm_num [Ttangent,he1,hy] at h
          linarith [hx.1]
    · refine ⟨(pt 0 1,0),?_,?_⟩
      · rw [T_master_iff H hH]
        refine ⟨by norm_num [pt,scalar],by simp [pt,scalar],by norm_num [pt,scalar],?_⟩
        intro e he
        rcases hb e with h | h
        · norm_num [Ttangent,h,pt,scalar]
        · exact (h1 ⟨e,he,h⟩).elim
      · intro z hz
        have h := (T_master_iff H hH z).mp hz
        exact h.1.1.trans h.2.2.1
  · refine ⟨(pt 0 0,0),?_,?_⟩
    · rw [T_master_iff H hH]
      refine ⟨by norm_num [pt,scalar],by simp [pt,scalar],by norm_num [pt,scalar],?_⟩
      intro e he
      rcases hb e with h | h
      · exact (h0 ⟨e,he,h⟩).elim
      · norm_num [Ttangent,h,pt,scalar]
    · intro z hz
      have h := (T_master_iff H hH z).mp hz
      exact h.1.1.trans h.2.2.1

theorem A_event_characterization (e : Event Adata) (he : EventValid Adata e) :
    e.restoration=some (scalar (3/16)) ∧ e.x=scalar 0 := by
  cases hs : e.restoration with
  | none =>
    have hm := he.2
    rw [hs] at hm
    exact (A_fiber_empty e.target e.target_mem ⟨e.x,hm.1.1⟩).elim
  | some s =>
    have hm := he.2
    rw [hs] at hm
    have hbound := hm.2.2 _ (A_restoration_minimum e.target e.target_mem).1
    rw [restCost_insert,restCost_insert] at hbound
    simp only [Fin.sum_univ_one,scalar] at hbound
    have hg := ((restSet_insert_iff A (intCast e.target) e.x s).mp hm.2.1).2.1 0
    change (e.x 0)^2+((e.target 0:ℝ)-1/2)^2-1/16 ≤ s 0 at hg
    rw [binary_square e.target e.target_mem] at hg
    have hx : e.x 0=0 := by nlinarith [sq_nonneg (e.x 0)]
    have hv : s 0=3/16 := by nlinarith [sq_nonneg (e.x 0)]
    constructor
    · congr 1
      ext i
      fin_cases i
      exact hv
    · ext i
      fin_cases i
      exact hx

theorem A_event_rows (e : Event Adata) (he : EventValid Adata e) (z : P × ℝ) :
    e.rows z ↔ LiteralG.tangent (e.target 0) (z.1.2 0) ≤ z.2 ∧
      LiteralG.tangent (e.target 0) (z.1.2 0)-1/16 ≤ 0 := by
  have hx := (A_event_characterization e he).2
  have hy := binary_square e.target e.target_mem
  have hpos : 0 ≤ Adata.model.g 0 e.anchor := by
    change 0 ≤ (e.x 0)^2+((e.target 0:ℝ)-1/2)^2-1/16
    rw [hx]
    norm_num [scalar,hy]
  have hsel : Adata.selected e.anchor=Set.univ := by
    ext j
    change (¬ AffineRow (Adata.model.g j) ∧ 0 ≤ Adata.model.g j e.anchor) ↔ True
    constructor
    · intro _; trivial
    · intro _
      refine ⟨quadraticRow_nonaffine _ _,?_⟩
      fin_cases j
      exact hpos
  have hf : Adata.f e.anchor+Adata.Df e.anchor (z.1-e.anchor)=
      LiteralG.tangent (e.target 0) (z.1.2 0) := by
    simp [Adata,Af,Adf,Event.anchor,hx,quadratic,quadraticD,scalar,intCast,LiteralG.tangent]
  have hg : Adata.model.g 0 e.anchor+Adata.Dg e.anchor 0 (z.1-e.anchor)=
      LiteralG.tangent (e.target 0) (z.1.2 0)-1/16 := by
    simp [Adata,A,boxModel,Adg,Event.anchor,hx,quadratic,quadraticD,scalar,intCast,LiteralG.tangent]
    ring
  simp only [Event.rows,hsel,Set.mem_univ,forall_true_left,Fin.forall_fin_one,hf,hg]

end Chapter03.OAExec.Article
