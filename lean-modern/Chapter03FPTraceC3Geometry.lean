module

public import Chapter03FPTraceC3Data

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C3

def s0 : State 1 2 := initialState seed
def e0 : Event 1 2 := ⟨corner 0 0,proj0,none,none⟩
def s1 : State 1 2 := append s0 e0
def e1 : Event 1 2 := ⟨corner 0 1,proj1,none,none⟩
def s2 : State 1 2 := append s1 e1
def e2 : Event 1 2 := ⟨corner 1 0,proj2,none,some (polished,polished)⟩
def s3 : State 1 2 := append s2 e2

theorem point_cast (x : ℝ) (u v : ℤ) : (pt x u v).2=intCast (corner u v) := by
  funext j;fin_cases j <;> rfl

theorem master_coordinates (s : State 1 2) {z : P × ℝ} (hz : z ∈ master d s) :
    z.1.2=intCast (corner 0 0) ∨ z.1.2=intCast (corner 0 1) ∨
    z.1.2=intCast (corner 1 0) ∨ z.1.2=intCast (corner 1 1) := by
  obtain ⟨y,hy,he⟩ := FPAdapters.epigraph_integer_box hz.1
  rcases integer_corner_cases y hy with h|h|h|h
  · exact Or.inl (he.trans (congrArg intCast h))
  · exact Or.inr (Or.inl (he.trans (congrArg intCast h)))
  · exact Or.inr (Or.inr (Or.inl (he.trans (congrArg intCast h))))
  · exact Or.inr (Or.inr (Or.inr (he.trans (congrArg intCast h))))

theorem master0_mem : (pt 1 0 0,1) ∈ master d s0 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨?_,⟨corner 0 0,?_,?_⟩,?_,?_,?_,?_,?_⟩
  · intro row;fin_cases row <;> norm_num [d,model,LinearForm,pt,Fin.sum_univ_one,Fin.sum_univ_two]
  · norm_num [IntegerBox,d,model,corner,Fin.forall_fin_two]
  · simpa using point_cast 1 0 0
  · intro i j _;fin_cases i;fin_cases j
    norm_num [family,anchors,s0,initialState,d,model,seed,pt]
  · intro i;fin_cases i
    norm_num [family,anchors,s0,initialState,d,seed,pt]
  · simp [retainedNormals,s0,initialState]
  · simp [noGoods,s0,initialState]
  · trivial

theorem master0_min : IsMinimizer (master d s0) (masterCost s0) (pt 1 0 0,1) := by
  refine ⟨master0_mem,?_⟩
  intro z hz
  change l1 seed (pt 1 0 0) ≤ l1 seed z.1
  rcases master_coordinates s0 hz with h|h|h|h
  all_goals norm_num [l1_two,h,seed,pt,intCast,corner,abs_div]

theorem reply0 : EventReply d s0 (pt 1 0 0,1) e0 := by
  refine ⟨by simpa [e0] using point_cast 1 0 0,rfl,projection0,?_⟩
  norm_num [e0,distance_two,corner,proj0,pt]

theorem master1_mem : (pt 1 0 1,1) ∈ master d s1 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨?_,⟨corner 0 1,?_,?_⟩,?_,?_,?_,?_,?_⟩
  · intro row;fin_cases row <;> norm_num [d,model,LinearForm,pt,Fin.sum_univ_one,Fin.sum_univ_two]
  · norm_num [IntegerBox,d,model,corner,Fin.forall_fin_two]
  · simpa using point_cast 1 0 1
  · intro i j _;fin_cases i <;> fin_cases j <;>
      norm_num [family,anchors,s1,s0,append,initialState,e0,Event.anchor,d,model,seed,proj0,pt]
  · intro i;fin_cases i <;>
      norm_num [family,anchors,s1,s0,append,initialState,e0,Event.anchor,d,seed,proj0,pt]
  · norm_num [retainedNormals,s1,s0,append,initialState,e0,normal_two,proj0,corner,pt]
  · simp [noGoods,s1,s0,append,initialState,e0]
  · trivial

theorem master1_min : IsMinimizer (master d s1) (masterCost s1) (pt 1 0 1,1) := by
  refine ⟨master1_mem,?_⟩
  intro z hz
  have hn := hz.2.1 e0 (by simp [s1,s0,append,initialState]) rfl
  change l1 proj0 (pt 1 0 1) ≤ l1 proj0 z.1
  rcases master_coordinates s1 hz with h|h|h|h
  · norm_num [normal_two,e0,proj0,corner,pt,h,intCast] at hn
  all_goals norm_num [l1_two,h,proj0,pt,intCast,corner,abs_div]

theorem reply1 : EventReply d s1 (pt 1 0 1,1) e1 := by
  refine ⟨by simpa [e1] using point_cast 1 0 1,rfl,projection1,?_⟩
  norm_num [e1,distance_two,corner,proj1,pt]

theorem master2_mem : (proj2,29/20) ∈ master d s2 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨?_,⟨corner 1 0,?_,?_⟩,?_,?_,?_,?_,?_⟩
  · intro row;fin_cases row <;> norm_num [d,model,LinearForm,proj2,pt,Fin.sum_univ_one,Fin.sum_univ_two]
  · norm_num [IntegerBox,d,model,corner,Fin.forall_fin_two]
  · simpa [proj2] using point_cast 1 1 0
  · intro i j _;fin_cases i <;> fin_cases j <;>
      norm_num [family,anchors,s2,s1,s0,append,initialState,e1,e0,Event.anchor,d,model,seed,proj0,proj1,proj2,pt]
  · intro i;fin_cases i <;>
      norm_num [family,anchors,s2,s1,s0,append,initialState,e1,e0,Event.anchor,d,seed,proj0,proj1,proj2,pt]
  · norm_num [retainedNormals,s2,s1,s0,append,initialState,e0,e1,normal_two,proj0,proj1,proj2,corner,pt]
  · simp [noGoods,s2,s1,s0,append,initialState,e0,e1]
  · trivial

theorem master2_coordinates {z : P × ℝ} (hz : z ∈ master d s2) : z.1.2=intCast (corner 1 0) := by
  have hn0 := hz.2.1 e0 (by simp [s2,s1,s0,append,initialState]) rfl
  have hn1 := hz.2.1 e1 (by simp [s2,s1,s0,append,initialState]) rfl
  rcases master_coordinates s2 hz with h|h|h|h
  · norm_num [normal_two,e0,proj0,corner,pt,h,intCast] at hn0
  · norm_num [normal_two,e1,proj1,corner,pt,h,intCast] at hn1
  · exact h
  · norm_num [normal_two,e1,proj1,corner,pt,h,intCast] at hn1

theorem master2_min : IsMinimizer (master d s2) (masterCost s2) (proj2,29/20) := by
  refine ⟨master2_mem,?_⟩
  intro z hz
  have h := master2_coordinates hz
  change l1 proj1 proj2 ≤ l1 proj1 z.1
  norm_num [l1_two,h,proj1,proj2,pt,intCast,corner,abs_div]

theorem reply2 : EventReply d s2 (proj2,29/20) e2 := by
  refine ⟨by simpa [e2,proj2] using point_cast 1 1 0,rfl,projection2,?_,polishing,rfl⟩
  norm_num [e2,distance_two,corner,proj2,pt]

theorem master3_empty : ¬(master d s3).Nonempty := by
  rintro ⟨z,hz⟩
  have hn0 := hz.2.1 e0 (by simp [s3,s2,s1,s0,append,initialState]) rfl
  have hn1 := hz.2.1 e1 (by simp [s3,s2,s1,s0,append,initialState]) rfl
  have hng := hz.2.2.1 e2 (by simp [s3,s2,s1,s0,append,initialState]) (by simp [e2])
  rcases master_coordinates s3 hz with h|h|h|h
  · norm_num [normal_two,e0,proj0,corner,pt,h,intCast] at hn0
  · norm_num [normal_two,e1,proj1,corner,pt,h,intCast] at hn1
  · exact hng h
  · norm_num [normal_two,e1,proj1,corner,pt,h,intCast] at hn1

end Chapter03.FPTrace.C3
