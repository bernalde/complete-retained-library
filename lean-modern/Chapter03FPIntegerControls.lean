module

public import Chapter03FPC1Execution

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPControls

def generalData : Data 1 1 1 2 := data true 0 1 2 0 0
theorem general_analytic : Analytic generalData := analytic true 0 1 2 0 (by norm_num) (by norm_num)
theorem general_seed : IsMinimizer generalData.relaxation generalData.f seed :=
  relaxation_seed true 0 1 2 0 (by norm_num) (by norm_num)

theorem ternary_value {k : ℤ} (h0 : 0 ≤ (k:ℝ)) (h2 : (k:ℝ) ≤ 2) : k=0 ∨ k=1 ∨ k=2 := by
  have h0' : 0 ≤ k := by exact_mod_cast h0
  have h2' : k ≤ 2 := by exact_mod_cast h2
  omega

theorem general_box : generalData.box = {iv 0,iv 1,iv 2} := by
  classical
  ext y
  simp only [Data.box,Set.Finite.mem_toFinset,IntegerBox,Set.mem_setOf_eq,generalData,data,model,
    Fin.forall_fin_one,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    rcases ternary_value h.1 h.2 with he|he|he
    · left; rw [← iv_eta y,he]
    · right; left; rw [← iv_eta y,he]
    · right; right; rw [← iv_eta y,he]
  · rintro (rfl|rfl|rfl) <;> norm_num [iv]

theorem general_box_card : generalData.box.card = 3 := by
  classical
  rw [general_box]
  have h01 : iv 0 ≠ iv 1 := by intro h; have := congrFun h 0; norm_num [iv] at this
  have h02 : iv 0 ≠ iv 2 := by intro h; have := congrFun h 0; norm_num [iv] at this
  have h12 : iv 1 ≠ iv 2 := by intro h; have := congrFun h 0; norm_num [iv] at this
  simp [h01,h02,h12]

theorem general_master0 :
    IsMinimizer (master generalData s0) (masterCost s0) (pt 0 0,0) := by
  refine ⟨(master_s0 _ _ _ _ _ _).mpr ⟨by norm_num,⟨0,by norm_num,by norm_num,by norm_num [pt]⟩,by norm_num⟩,?_⟩
  intro z hz
  obtain ⟨_,⟨k,h0,h2,he⟩,_⟩ := (master_s0 true 0 1 2 0 z).mp hz
  rcases ternary_value h0 h2 with rfl|rfl|rfl <;>
    norm_num [masterCost,l1_formula,State.reference,s0,initialState,seed,pt,he,abs_of_nonneg]

theorem general_projection0 :
    IsMinimizer (generalData.region none) (distance (iv 0)) (pt 0 0) := by
  refine ⟨⟨(relaxation_iff _ _ _ _ _ _).mpr ⟨rfl,by norm_num,by norm_num⟩,trivial⟩,?_⟩
  intro p hp
  norm_num only [distance_formula,iv_apply,pt_snd,Int.cast_zero,sub_self,zero_pow]
  exact sq_nonneg _

theorem general_reply0 : EventReply generalData s0 (pt 0 0,0) e0 := by
  refine ⟨by funext j; norm_num [e0,pt,intCast,iv],rfl,general_projection0,?_⟩
  exact ⟨by norm_num [e0,distance_formula],
    by simpa [generalData,e0] using fiber_minimum true 0 1 2 0 0 (by norm_num) (by norm_num),rfl⟩

theorem general_continue0 : Continue generalData none s0 e0 :=
  ⟨(pt 0 0,0),general_master0,by simp [BeforeCap],general_reply0⟩

theorem general_master1 :
    IsMinimizer (master generalData s1) (masterCost s1) (pt 0 1,1/4) := by
  refine ⟨(master_s1 _ _ _ _ _ _).mpr ?_,?_⟩
  · refine ⟨by norm_num [pt],⟨1,by norm_num,by norm_num,by norm_num [pt]⟩,?_,?_,?_,?_⟩ <;>
      norm_num [pt,cutoffValue]
  · intro z hz
    obtain ⟨_,⟨k,h0,h2,he⟩,_,_,hn,_⟩ := (master_s1 true 0 1 2 0 z).mp hz
    rcases ternary_value h0 h2 with rfl|rfl|rfl
    · exact False.elim (hn (by simpa using he))
    · norm_num [masterCost,l1_formula,State.reference,s1,s0,append,initialState,e0,Event.anchor,pt,he]
    · norm_num [masterCost,l1_formula,State.reference,s1,s0,append,initialState,e0,Event.anchor,pt,he]

theorem general_projection1 :
    IsMinimizer (generalData.region (generalData.level s1.incumbent)) (distance (iv 1)) (pt 0 1) := by
  refine ⟨⟨(relaxation_iff _ _ _ _ _ _).mpr ⟨rfl,by norm_num,by norm_num⟩,?_⟩,?_⟩
  · norm_num [generalData,data,Data.level,s1,s0,append,initialState,e0,pt,Allows,cutoffValue]
  · intro p hp
    norm_num only [distance_formula,iv_apply,pt_snd,Int.cast_one,sub_self,zero_pow]
    exact sq_nonneg _

theorem general_reply1 : EventReply generalData s1 (pt 0 1,1/4) e1 := by
  refine ⟨by funext j; norm_num [e1,pt,intCast,iv],?_,general_projection1,?_⟩
  · norm_num [e1,generalData,data,Data.level,s1,s0,append,initialState,e0,pt,cutoffValue]
  · refine ⟨by norm_num [e1,distance_formula],?_,?_⟩
    · simpa [generalData,e1] using fiber_minimum true 0 1 2 0 1 (by norm_num) (by norm_num)
    · norm_num [e1,s1,s0,append,initialState,e0,BestChoice,generalData,data,pt]

theorem general_continue1 : Continue generalData none s1 e1 :=
  ⟨(pt 0 1,1/4),general_master1,by simp [BeforeCap],general_reply1⟩

theorem general_master2_empty : ¬ (master generalData s2).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨_,⟨k,h0,h2,he⟩,_,_,ht,hn0,hn1,hc⟩ := (master_s2 true 0 1 2 0 z).mp hz
  rcases ternary_value h0 h2 with rfl|rfl|rfl
  · exact hn0 (by simpa using he)
  · exact hn1 (by simpa using he)
  · norm_num [he,cutoffValue] at ht hc
    linarith

def generalSelector : Selector generalData none :=
  patch s0 (.next e0 general_continue0)
    (patch s1 (.next e1 general_continue1)
      (patch s2 (.stop .emptyMaster (.emptyMaster general_master2_empty))
        (Classical.choice (selector_nonempty generalData general_analytic none))))

theorem general_run (fuel : ℕ) : run generalData generalSelector (fuel+3) s0 = some out0 := by
  rw [run]
  simp only [generalSelector,patch_same]
  change ((run generalData generalSelector (fuel+2) s1).map (LoopOutput.bump e0)) = _
  rw [run]
  simp only [generalSelector,patch_other _ _ _ _ s01.symm,patch_same]
  change ((run generalData generalSelector (fuel+1) s2).map (LoopOutput.bump e1)).map (LoopOutput.bump e0) = _
  rw [run]
  simp [generalSelector,patch,s02.symm,s12.symm,terminalOutput,terminalProjectionCount,LoopOutput.bump,
    polishCount,e0,e1,out0]

theorem general_procedure : procedure generalData (.minimum seed general_seed) generalSelector =
    some (.loop out0) := by
  rw [procedure_fractional_eq generalData seed general_seed generalSelector
    (fractional_seed true 0 1 2 0 0),general_box_card]
  change (run generalData generalSelector (1+3) s0).map Outcome.loop = _
  rw [general_run]; rfl

theorem general_installed_nogoods :
    s2.history = [e0,e1] ∧ ¬noGoods s2 (pt 0 0) ∧ ¬noGoods s2 (pt 0 1) ∧
    pt 0 2 ∈ generalData.original := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro h
    exact h e0 (by simp [s2,s1,s0,append,initialState]) (by simp [e0])
      (by funext j; norm_num [e0,intCast,iv,pt])
  · intro h
    exact h e1 (by simp [s2,s1,s0,append,initialState]) (by simp [e1])
      (by funext j; norm_num [e1,intCast,iv,pt])
  · apply fiber_original generalData (iv 2)
    simpa [generalData] using (fiber_minimum true 0 1 2 0 2 (by norm_num) (by norm_num)).1

end Chapter03.FPControls
