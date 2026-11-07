module

public import Chapter03OAExecHistory
public import Chapter03OAExecArticleAdapters
public import Chapter03OAExecLiteralG

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

theorem G_integer_iff (p : P) : p ∈ IntegerCylinder G.lo G.hi ↔
    p.2 0=0 ∨ p.2 0=1 := by
  constructor
  · rintro ⟨y,hy,he⟩
    rcases (binary_box (-1) 1 _ y).mp hy with h | h <;> simp [he,h]
  · intro h
    rcases h with h | h
    · refine ⟨fun _ => 0,?_,?_⟩
      · intro i; norm_num [G,boxModel,scalar]
      · ext i; fin_cases i; simpa using h
    · refine ⟨fun _ => 1,?_,?_⟩
      · intro i; norm_num [G,boxModel,scalar]
      · ext i; fin_cases i; simpa using h

theorem G_event_rows (e : Event Gdata) (he : EventValid Gdata e) (z : P × ℝ) :
    e.rows z ↔ LiteralG.tangent (e.target 0) (z.1.2 0) ≤ z.2 := by
  have hx := (G_event_characterization e he).2
  simp [Event.rows,Data.selected,Data.nonlinear,Gdata,G,boxModel,Event.anchor,hx,
    Gf,Gdf,Gdg,quadratic,quadraticD,xSquareRow,xSquareD,scalar,intCast,
    LiteralG.tangent]

theorem G_master_literal (H : List (Event Gdata))
    (hH : ∀ e ∈ H, EventValid Gdata e) :
    master Gdata (pt 0 (1/2)) H=
      LiteralG.master (H.map (fun e => e.target 0)) [] := by
  ext z
  rw [master_mem_iff,LiteralG.master_iff]
  have hn : noGoods H z.1 := by
    intro e he hrest
    exact (hrest (G_event_characterization e (hH e he)).1).elim
  have hg : ∀ j, Gdata.model.g j (pt 0 (1/2))+
      Gdata.Dg (pt 0 (1/2)) j (z.1-pt 0 (1/2)) ≤ 0 := by
    intro j
    norm_num [Gdata,G,boxModel,Gdg,xSquareRow,xSquareD,pt,scalar]
  have hf : Gdata.f (pt 0 (1/2))+Gdata.Df (pt 0 (1/2))
      (z.1-pt 0 (1/2))=0 := by
    norm_num [Gdata,Gf,Gdf,quadratic,quadraticD,pt,scalar]
  have hr : (∀ e ∈ H, e.rows z) ↔
      ∀ b ∈ H.map (fun e => e.target 0), LiteralG.tangent b (z.1.2 0) ≤ z.2 := by
    simp only [List.forall_mem_map]
    exact forall₂_congr fun e he => G_event_rows e (hH e he) z
  change (z.1 ∈ G.linearRegion ∧ z.1 ∈ IntegerCylinder G.lo G.hi ∧ _ ∧ _ ∧ _) ↔ _
  rw [show G.linearRegion=(boxModel (-1) 1 (xSquareRow 4)).linearRegion from rfl,
    box_hard,G_integer_iff,hf,hr]
  simp only [hg,hn,true_and,and_true,List.not_mem_nil,IsEmpty.forall_iff,
    implies_true]

theorem binary_history_attained (H : List ℤ) (hH : ∀ b ∈ H, b=0 ∨ b=1) :
    ∃ z, IsMinimizer (LiteralG.master H []) Prod.snd z := by
  classical
  by_cases h0 : (0:ℤ) ∈ H
  · by_cases h1 : (1:ℤ) ∈ H
    · refine ⟨(pt 0 0,1/4),?_,?_⟩
      · rw [LiteralG.master_iff]
        refine ⟨by norm_num [pt,scalar],by simp [pt,scalar],by norm_num,?_,by simp⟩
        intro b hb
        rcases hH b hb with rfl | rfl <;> norm_num [LiteralG.tangent,pt,scalar]
      · intro z hz
        obtain ⟨hx,hy,hh,hc,hC⟩ := (LiteralG.master_iff _ _ _).mp hz
        rcases hy with hy | hy
        · have h := hc 0 h0
          norm_num [LiteralG.tangent,hy] at h
          exact h
        · have h := hc 1 h1
          norm_num [LiteralG.tangent,hy] at h
          exact h
    · refine ⟨(pt 0 1,0),?_,?_⟩
      · rw [LiteralG.master_iff]
        refine ⟨by norm_num [pt,scalar],by simp [pt,scalar],le_rfl,?_,by simp⟩
        intro b hb
        rcases hH b hb with rfl | rfl
        · norm_num [LiteralG.tangent,pt,scalar]
        · exact (h1 hb).elim
      · intro z hz
        exact ((LiteralG.master_iff _ _ _).mp hz).2.2.1
  · refine ⟨(pt 0 0,0),?_,?_⟩
    · rw [LiteralG.master_iff]
      refine ⟨by norm_num [pt,scalar],by simp [pt,scalar],le_rfl,?_,by simp⟩
      intro b hb
      rcases hH b hb with rfl | rfl
      · exact (h0 hb).elim
      · norm_num [LiteralG.tangent,pt,scalar]
    · intro z hz
      exact ((LiteralG.master_iff _ _ _).mp hz).2.2.1

/-- Stronger than local reachable availability: every valid concrete G
history has an attained complete master minimum, including all master ties. -/
theorem G_master_attained (H : List (Event Gdata))
    (hH : ∀ e ∈ H, EventValid Gdata e) :
    ∃ z, IsMinimizer (master Gdata (pt 0 (1/2)) H) Prod.snd z := by
  rw [G_master_literal H hH]
  apply binary_history_attained
  intro b hb
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
  exact (binary_box (-1) 1 _ e.target).mp e.target_mem

theorem G_initial_fractional : ¬ integral (pt 0 (1/2)) := by
  rintro ⟨y,hy⟩
  have h := congrFun hy 0
  change (1/2:ℝ)=(y 0:ℝ) at h
  have hl : (0:ℤ)<y 0 := by exact_mod_cast (show (0:ℝ)<(y 0:ℝ) by linarith)
  have hu : y 0<(1:ℤ) := by exact_mod_cast (show (y 0:ℝ)<(1:ℝ) by linarith)
  omega

theorem G_original_at_zero : pt 0 0 ∈ Gdata.original := by
  rw [Data.original,source_feasible_iff]
  refine ⟨Set.mem_univ _,?_,?_,fun _ => 0,?_,?_⟩
  · intro j
    norm_num [Gdata,G,boxModel,xSquareRow,pt,scalar]
  · exact (G_fiber_minimum (scalar 0)).1.1
  · intro i
    norm_num [Gdata,G,boxModel,scalar]
  · ext i
    fin_cases i
    norm_num [pt,scalar]

end Chapter03.OAExec.Article
