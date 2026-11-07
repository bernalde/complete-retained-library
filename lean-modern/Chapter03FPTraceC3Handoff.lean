module

public import Chapter03FPTraceC3Runs

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C3

theorem projection_normal_rows (p : P) :
    e0.normal p=(p.2 0+2*p.2 1-1)/5 ∧ e1.normal p=(1/2-p.2 1)/2 := by
  constructor <;> norm_num [normal_two,e0,e1,proj0,proj1,pt,corner] <;> ring

theorem capTwo_normals_eq_current (p : P) : handoffNormals s2 p ↔ retainedNormals s2 p := by
  constructor
  · intro hh e he hn
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
    exact hh i hn (by simp [s2,s1,s0,append,initialState,e0,e1])
  · intro hr i hn _
    exact hr _ (List.get_mem _ _) hn

theorem polished_master2 : (polished,5/4) ∈ master d s2 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨?_,⟨corner 1 0,?_,?_⟩,?_,?_,?_,?_,?_⟩
  · intro row;fin_cases row <;> norm_num [d,model,LinearForm,polished,pt,Fin.sum_univ_one,Fin.sum_univ_two]
  · norm_num [IntegerBox,d,model,corner,Fin.forall_fin_two]
  · simpa [polished] using point_cast 0 1 0
  · intro i j _;fin_cases i <;> fin_cases j <;>
      norm_num [family,anchors,s2,s1,s0,append,initialState,e1,e0,Event.anchor,d,model,seed,proj0,proj1,polished,pt]
  · intro i;fin_cases i <;>
      norm_num [family,anchors,s2,s1,s0,append,initialState,e1,e0,Event.anchor,d,seed,proj0,proj1,polished,pt]
  · norm_num [retainedNormals,s2,s1,s0,append,initialState,e0,e1,normal_two,proj0,proj1,polished,corner,pt]
  · simp [noGoods,s2,s1,s0,append,initialState,e0,e1]
  · trivial

theorem capTwo_handoff_retains_optimum : (polished,d.f polished) ∈ handoff d s2 := by
  rw [strict_polishing.2.1]
  exact ⟨polished_master2.1,(capTwo_normals_eq_current polished).mpr polished_master2.2.1,
    polished_master2.2.2.1⟩

theorem delta_zero_result : d.delta=0 ∧ d.level s3.incumbent=some (5/4) ∧
    IsMinimizer d.original d.f polished := by
  refine ⟨rfl,?_,polished_global_minimum⟩
  norm_num [Data.level,s3,e2,append,d,cutoffValue,polished,pt]

theorem final_filter_retains_prior_normals (p : P) : handoffNormals s3 p ↔ retainedNormals s3 p := by
  constructor
  · intro hh e he hn
    simp only [s3,s2,s1,s0,append,initialState,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,false_or] at he
    rcases he with (rfl | rfl) | rfl
    · apply hh ⟨0,by decide⟩ rfl
      intro k hk
      have he : k=2 := by simpa [s3,e2,append,s2,s1,s0,initialState] using hk.symm
      change 0 < k
      omega
    · apply hh ⟨1,by decide⟩ rfl
      intro k hk
      have he : k=2 := by simpa [s3,e2,append,s2,s1,s0,initialState] using hk.symm
      change 1 < k
      omega
    · simp [e2] at hn
  · intro hr i hn _
    exact hr _ (List.get_mem _ _) hn

theorem final_handoff_excludes_saved_point (alpha : ℝ) : (polished,alpha) ∉ handoff d s3 := by
  intro h
  have hn := h.2.2 e2 (by simp [s3,s2,s1,s0,append,initialState]) (by simp [e2])
  apply hn
  simpa [polished,e2] using point_cast 0 1 0

end Chapter03.FPTrace.C3
