module

public import Chapter03OAExecArticleGTrace

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

theorem G_choice_minimum {s : State Gdata}
    (hH : ∀ e ∈ s.history, EventValid Gdata e)
    (q : MasterChoice Gdata (pt 0 (1/2)) s) :
    q.attained=true ∧ IsMinimizer (master Gdata (pt 0 (1/2)) s.history) Prod.snd q.point := by
  obtain ⟨w,hw⟩ := G_master_attained s.history hH
  have hb : BddBelow (Prod.snd '' master Gdata (pt 0 (1/2)) s.history) := by
    refine ⟨w.2,?_⟩
    rintro v ⟨z,hz,rfl⟩
    exact hw.2 z hz
  have hv := q.valid
  cases ha : q.attained
  · simp only [ha,Bool.false_eq_true,↓reduceIte] at hv
    exact (hv.2 hb).elim
  · simp only [ha,↓reduceIte] at hv
    exact ⟨rfl,hv⟩

theorem literal_single_minimum (b : ℤ) (hb : b=0 ∨ b=1) :
    ∃ w, IsMinimizer (LiteralG.master [b] []) Prod.snd w ∧ w.2=0 := by
  rcases hb with rfl | rfl
  · refine ⟨(pt 0 1,0),⟨?_,?_⟩,rfl⟩
    · norm_num [LiteralG.master_iff,LiteralG.tangent,pt,scalar]
    · intro z hz
      exact ((LiteralG.master_iff _ _ _).mp hz).2.2.1
  · refine ⟨(pt 0 0,0),⟨?_,?_⟩,rfl⟩
    · norm_num [LiteralG.master_iff,LiteralG.tangent,pt,scalar]
    · intro z hz
      exact ((LiteralG.master_iff _ _ _).mp hz).2.2.1

theorem literal_double_minimum (b c : ℤ) (hb : b=0 ∨ b=1) (hc : c=0 ∨ c=1)
    (hne : b≠c) :
    ∃ w, IsMinimizer (LiteralG.master [b,c] []) Prod.snd w ∧ w.2=1/4 := by
  have h0 : (0:ℤ) ∈ [b,c] := by rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp_all
  have h1 : (1:ℤ) ∈ [b,c] := by rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp_all
  refine ⟨(pt 0 0,1/4),⟨?_,?_⟩,rfl⟩
  · rw [LiteralG.master_iff]
    refine ⟨by norm_num [pt,scalar],by simp [pt,scalar],by norm_num,?_,by simp⟩
    intro a ha
    have ha' : a=0 ∨ a=1 := by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hb
      · simpa only [List.mem_singleton.mp ha] using hc
    rcases ha' with rfl | rfl <;> norm_num [LiteralG.tangent,pt,scalar]
  · intro z hz
    have h := (LiteralG.master_iff _ _ _).mp hz
    rcases h.2.1 with hy | hy
    · have hh := h.2.2.2.1 0 h0
      norm_num [LiteralG.tangent,hy] at hh
      exact hh
    · have hh := h.2.2.2.1 1 h1
      norm_num [LiteralG.tangent,hy] at hh
      exact hh

theorem G_choice_empty_history {s : State Gdata} (hs : s.history=[])
    (q : MasterChoice Gdata (pt 0 (1/2)) s) : q.nextLower=0 := by
  have hvalid : ∀ e ∈ s.history, EventValid Gdata e := by simp [hs]
  obtain ⟨ha,hm⟩ := G_choice_minimum hvalid q
  rw [hs] at hm
  have hl := Gminimum0.2 q.point hm.1
  have hu := hm.2 (pt 0 0,0) Gminimum0.1
  simp only [MasterChoice.nextLower,ha,↓reduceIte]
  exact le_antisymm hu hl

theorem G_choice_single_history {s : State Gdata} (e : Event Gdata)
    (he : EventValid Gdata e) (hs : s.history=[e])
    (q : MasterChoice Gdata (pt 0 (1/2)) s) :
    q.nextLower=0 ∧ q.point.1.2 0 ≠ (e.target 0:ℝ) := by
  have hvalid : ∀ a ∈ s.history, EventValid Gdata a := by simp [hs,he]
  obtain ⟨ha,hm⟩ := G_choice_minimum hvalid q
  rw [G_master_literal s.history hvalid] at hm
  simp only [hs,List.map_cons,List.map_nil] at hm
  have hb := (binary_box (-1) 1 _ e.target).mp e.target_mem
  obtain ⟨w,hw,hw0⟩ := literal_single_minimum (e.target 0) hb
  have hl := hw.2 q.point hm.1
  have hu := hm.2 w hw.1
  have hq0 : q.point.2=0 := by rw [hw0] at hl hu; exact le_antisymm hu hl
  refine ⟨by simp only [MasterChoice.nextLower,ha,↓reduceIte,hq0],?_⟩
  intro hy
  have hh := ((LiteralG.master_iff _ _ _).mp hm.1).2.2.2.1 (e.target 0) (by simp)
  rw [hy,hq0] at hh
  rcases hb with hb | hb <;> norm_num [LiteralG.tangent,hb] at hh

theorem G_choice_double_history {s : State Gdata} (e v : Event Gdata)
    (he : EventValid Gdata e) (hv : EventValid Gdata v)
    (hneq : e.target 0≠v.target 0) (hs : s.history=[e,v])
    (q : MasterChoice Gdata (pt 0 (1/2)) s) : q.nextLower=1/4 := by
  have hvalid : ∀ a ∈ s.history, EventValid Gdata a := by simp [hs,he,hv]
  obtain ⟨ha,hm⟩ := G_choice_minimum hvalid q
  rw [G_master_literal s.history hvalid] at hm
  simp only [hs,List.map_cons,List.map_nil] at hm
  obtain ⟨w,hw,hw0⟩ := literal_double_minimum (e.target 0) (v.target 0)
    ((binary_box (-1) 1 _ e.target).mp e.target_mem)
    ((binary_box (-1) 1 _ v.target).mp v.target_mem) hneq
  have hl := hw.2 q.point hm.1
  have hu := hm.2 w hw.1
  rw [hw0] at hl hu
  simp only [MasterChoice.nextLower,ha,↓reduceIte]
  exact le_antisymm hu hl

theorem G_advance_incumbent {s : State Gdata} {seed : P}
    (q : MasterChoice Gdata seed s) (e : Event Gdata) (he : EventValid Gdata e)
    (hold : s.incumbent=none ∨ ∃ p, s.incumbent=some p ∧ Gdata.f p=1/4) :
    ∃ p, (advance s q e).incumbent=some p ∧ Gdata.f p=1/4 := by
  have hn := (G_event_characterization e he).1
  have hv := G_event_value e he
  rcases hold with hold | ⟨p,hold,hp⟩
  · exact ⟨e.anchor,by simp [advance,nextIncumbent,hn,keepBest,hold],hv⟩
  · exact ⟨p,by simp [advance,nextIncumbent,hn,keepBest,hold,hv,hp],hp⟩

/-- Universal exact three-round G control: arbitrary master x choices and all
integer ties are covered, as are all certificate-bearing fixed selections. -/
theorem G_every_selector_three_rounds (choose : Selector Gdata (pt 0 (1/2)) 0) :
    ∃ p, runFuel Gdata (pt 0 (1/2)) 0 choose 3
      (initialState Gdata (pt 0 (1/2))) .initial=
      some ⟨.solution p,3,3,0⟩ ∧ Gdata.f p=1/4 := by
  let s0 := initialState Gdata (pt 0 (1/2))
  have ho0 : loopOpen Gdata 0 s0 := by simp [s0,loopOpen,initialState]
  cases hc0 : choose s0 Reachable.initial ho0 with
  | empty hempty =>
    have h := Gminimum0.1
    change (pt 0 0,0) ∈ master Gdata (pt 0 (1/2)) s0.history at h
    rw [hempty] at h
    exact h.elim
  | next q0 e0 he0 hy0 =>
    let s1 := advance s0 q0 e0
    have hr1 : Reachable Gdata (pt 0 (1/2)) 0 s1 :=
      .next .initial (.step ho0 q0 e0 he0 hy0)
    have hl1 : s1.lower=0 := G_choice_empty_history rfl q0
    obtain ⟨p1,hp1,hv1⟩ := G_advance_incumbent q0 e0 he0 (Or.inl rfl)
    have ho1 : loopOpen Gdata 0 s1 := by
      intro p hp
      rw [hp1] at hp
      cases hp
      rw [hl1,hv1]
      norm_num
    cases hc1 : choose s1 hr1 ho1 with
    | empty hempty =>
      obtain ⟨z,hz⟩ := G_master_attained s1.history (G_reachable_events hr1)
      rw [hempty] at hz
      exact hz.1.elim
    | next q1 e1 he1 hy1 =>
      have hchoice1 := G_choice_single_history e0 he0 rfl q1
      have hneq : e0.target 0≠e1.target 0 := by
        intro hh
        apply hchoice1.2
        rw [hy1]
        simp [Chapter03.OAKKT.intCast,hh]
      let s2 := advance s1 q1 e1
      have hr2 : Reachable Gdata (pt 0 (1/2)) 0 s2 :=
        .next hr1 (.step ho1 q1 e1 he1 hy1)
      obtain ⟨p2,hp2,hv2⟩ := G_advance_incumbent q1 e1 he1 (Or.inr ⟨p1,hp1,hv1⟩)
      have ho2 : loopOpen Gdata 0 s2 := by
        intro p hp
        rw [hp2] at hp
        cases hp
        change 0 < Gdata.f p2-q1.nextLower
        rw [hchoice1.1,hv2]
        norm_num
      cases hc2 : choose s2 hr2 ho2 with
      | empty hempty =>
        obtain ⟨z,hz⟩ := G_master_attained s2.history (G_reachable_events hr2)
        rw [hempty] at hz
        exact hz.1.elim
      | next q2 e2 he2 hy2 =>
        have hchoice2 := G_choice_double_history e0 e1 he0 he1 hneq rfl q2
        let s3 := advance s2 q2 e2
        have hr3 : Reachable Gdata (pt 0 (1/2)) 0 s3 :=
          .next hr2 (.step ho2 q2 e2 he2 hy2)
        obtain ⟨p3,hp3,hv3⟩ := G_advance_incumbent q2 e2 he2 (Or.inr ⟨p2,hp2,hv2⟩)
        have hgap3 : Gdata.f p3-s3.lower≤0 := by
          change Gdata.f p3-q2.nextLower≤0
          rw [hchoice2,hv3]
          norm_num
        have ht3 := runFuel_closed choose 0 s3 hr3 p3 hp3 hgap3
        have ht2 := runFuel_next choose 0 s2 hr2 ho2 q2 e2 he2 hy2 hc2 _ ht3
        have ht1 := runFuel_next choose 1 s1 hr1 ho1 q1 e1 he1 hy1 hc1 _ ht2
        have ht0 := runFuel_next choose 2 s0 .initial ho0 q0 e0 he0 hy0 hc0 _ ht1
        refine ⟨p3,?_,hv3⟩
        simpa only [countStep,eventRestorations,(G_event_characterization e0 he0).1,
          (G_event_characterization e1 he1).1,(G_event_characterization e2 he2).1,
          ↓reduceIte,Nat.zero_add,Nat.add_zero] using ht0

end Chapter03.OAExec.Article

#print axioms Chapter03.OAExec.Article.G_every_selector_three_rounds
