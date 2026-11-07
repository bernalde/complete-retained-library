module

public import Chapter03FPTraceC2Runs

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C2

theorem capTwo_normals_vacuous (p : P) : handoffNormals s2 p := by
  intro i hn hk
  have hi := hk 0 rfl
  omega

theorem capTwo_handoff_retains_better : (one,10/81) ∈ handoff d s2 := by
  refine ⟨?_,capTwo_normals_vacuous one,?_⟩
  · refine ⟨⟨⟨⟨trivial,?_⟩,?_⟩,corner 0 1,?_,?_⟩,?_⟩
    · intro i j;exact Fin.elim0 j
    · intro row;exact Fin.elim0 row
    · norm_num [IntegerBox,d,data,model,corner,Fin.forall_fin_two]
    · change (pt 0 1).2 = Chapter03.FP.intCast (corner 0 1)
      simpa only [Int.cast_zero,Int.cast_one] using point_cast 0 1
    · intro i;fin_cases i <;>
        norm_num [family,anchors,s2,s1,s0,append,initialState,e0,e1,Event.anchor,d,data,q,Dq,seed,zero,one,pt]
  · simp [noGoods,s2,s1,s0,append,initialState,e1,e0,one,intCast,corner,pt,funext_iff,Fin.forall_fin_two]

theorem original_one_optimal : IsMinimizer d.original d.f one := by
  refine ⟨better_original.1,?_⟩
  intro p hp
  obtain ⟨_,_,_,y,hy,he⟩ := (source_feasible_iff model Set.univ p).mp hp
  rcases integer_point_cases p ⟨y,hy,he⟩ with h|h|h|h
  all_goals norm_num [h,d,data,q,zero,one,other,both,pt]

theorem unsafe_transfer_witness : IsMinimizer d.original d.f one ∧
    d.f one < d.f zero ∧ ¬retainedNormals s2 one ∧
    (one,d.f one) ∈ handoff d s2 := by
  refine ⟨original_one_optimal,?_,late_normal_excludes_better.2,?_⟩
  · rw [better_original.2.1,better_original.2.2];norm_num
  · rw [better_original.2.1];exact capTwo_handoff_retains_better

end Chapter03.FPTrace.C2
