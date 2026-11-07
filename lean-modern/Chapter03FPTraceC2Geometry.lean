module

public import Chapter03FPTraceC2Data

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.FP Chapter03.FPTrace
namespace Chapter03.FPTrace.C2

def d : Data 0 2 0 0 := data 1 0 (37/81)
def s0 : State 0 2 := initialState seed
def e0 : Event 0 2 := ⟨corner 0 0,zero,none,some (zero,zero)⟩
def s1 : State 0 2 := append s0 e0
def e1 : Event 0 2 := ⟨corner 0 1,seed,some 0,none⟩
def s2 : State 0 2 := append s1 e1
def e2 : Event 0 2 := ⟨corner 1 0,seed,some 0,none⟩
def s3 : State 0 2 := append s2 e2

theorem point_cast (u v : ℤ) : (pt u v).2=intCast (corner u v) := by
  funext j
  fin_cases j <;> rfl

theorem d_analytic : Analytic d := analytic _ _ _ (by norm_num) (by norm_num)

theorem integer_point_cases (p : P)
    (hp : ∃ y : IntVector 2, (∀ j, (0:ℝ) ≤ (y j:ℝ) ∧ (y j:ℝ) ≤ 1) ∧ p.2=intCast y) :
    p=zero ∨ p=one ∨ p=other ∨ p=both := by
  obtain ⟨y,hy,he⟩ := hp
  have hh : p=pt (y 0:ℝ) (y 1:ℝ) := point_ext p _ _ (congrFun he 0) (congrFun he 1)
  rcases integer_corner_cases y hy with rfl|rfl|rfl|rfl
  · exact Or.inl (by simpa [corner,zero] using hh)
  · exact Or.inr (Or.inl (by simpa [corner,one] using hh))
  · exact Or.inr (Or.inr (Or.inl (by simpa [corner,other] using hh)))
  · exact Or.inr (Or.inr (Or.inr (by simpa [corner,both] using hh)))

theorem master_point_cases (a b delta : ℝ) (s : State 0 2)
    {z : P × ℝ} (hz : z ∈ master (data a b delta) s) :
    z.1=zero ∨ z.1=one ∨ z.1=other ∨ z.1=both :=
  integer_point_cases z.1 (FPAdapters.epigraph_integer_box hz.1)

theorem master0_mem (a b delta : ℝ) : (zero,b) ∈ master (data a b delta) s0 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨(fun row => Fin.elim0 row),⟨corner 0 0,?_,?_⟩,(fun i j => Fin.elim0 j),?_,?_,?_,?_⟩
  · norm_num [IntegerBox,data,model,corner,Fin.forall_fin_two]
  · simpa [zero,one,other] using point_cast 0 0
  · intro i
    fin_cases i
    simpa [family,anchors,s0,initialState] using (tangent_seed a b delta zero).le
  · simp [retainedNormals,s0,initialState]
  · simp [noGoods,s0,initialState]
  · trivial

theorem master0_min (a b delta : ℝ) :
    IsMinimizer (master (data a b delta) s0) (masterCost s0) (zero,b) := by
  refine ⟨master0_mem a b delta,?_⟩
  intro z hz
  change l1 seed zero ≤ l1 seed z.1
  rcases master_point_cases a b delta s0 hz with h|h|h|h
  all_goals rw [h]
  all_goals simp only [l1_two]
  all_goals norm_num [seed,zero,one,other,both,pt,abs_div]

theorem region_zero_mem (a b delta : ℝ) : zero ∈ (data a b delta).region none := by
  exact ⟨(relaxation_iff _ _ _ _).mpr (by norm_num [zero,pt]),trivial⟩

theorem integer_projection_min (a b delta : ℝ) (level : Option ℝ) (u v : ℤ)
    (hp : pt u v ∈ (data a b delta).region level) :
    IsMinimizer ((data a b delta).region level) (distance (corner u v)) (pt u v) := by
  refine ⟨hp,?_⟩
  intro p _
  rw [distance_two,distance_two]
  norm_num [corner,pt]
  positivity

theorem integer_fiber_min (a b delta : ℝ) (u v : ℤ)
    (hp : pt u v ∈ (data a b delta).relaxation) :
    IsMinimizer ((data a b delta).fiber (corner u v)) (data a b delta).f (pt u v) := by
  refine ⟨⟨hp,point_cast u v⟩,?_⟩
  intro p h
  have hpv : p=pt u v := point_ext p _ _ (congrFun h.2 0) (congrFun h.2 1)
  rw [hpv]

theorem reply0 (a b delta : ℝ) : EventReply (data a b delta) s0 (zero,b) e0 := by
  refine ⟨by simpa [zero,e0] using point_cast 0 0,rfl,?_,?_⟩
  · simpa [zero,e0,s0,initialState,Data.level] using integer_projection_min a b delta none 0 0 (by simpa [zero] using region_zero_mem a b delta)
  · refine ⟨?_,?_,rfl⟩
    · norm_num [e0,distance_two,corner,zero,pt]
    · simpa [zero,e0] using integer_fiber_min a b delta 0 0 (by simpa [zero] using (region_zero_mem a b delta).1)

theorem level1 : d.level s1.incumbent=some 0 := by
  norm_num [d,data,Data.level,s1,s0,e0,append,initialState,cutoffValue,q,zero,pt,max_def,abs_div]

theorem level2 : d.level s2.incumbent=some 0 := by
  simpa [s2,append,e1] using level1

theorem level3 : d.level s3.incumbent=some 0 := by
  simpa [s3,append,e2] using level2

theorem seed_projection (y : IntVector 2) :
    IsMinimizer (d.region (some 0)) (distance y) seed := by
  refine ⟨⟨(relaxation_iff _ _ _ _).mpr (by norm_num [seed,pt]),?_⟩,?_⟩
  · norm_num [Allows,d,data,q_seed]
  · intro p hp
    have hh : q p ≤ 0 := by simpa [d,data,Allows] using hp.2
    rw [q_sublevel_zero p hh]

theorem master1_mem : (one,0) ∈ master d s1 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨(fun row => Fin.elim0 row),⟨corner 0 1,?_,?_⟩,(fun i j => Fin.elim0 j),?_,?_,?_,?_⟩
  · norm_num [IntegerBox,d,data,model,corner,Fin.forall_fin_two]
  · simpa [zero,one,other] using point_cast 0 1
  · intro i
    fin_cases i <;>
      norm_num [family,anchors,s1,s0,append,initialState,e0,Event.anchor,d,data,q,Dq,seed,zero,one,pt]
  · simp [retainedNormals,s1,s0,append,initialState,e0]
  · simp [noGoods,s1,s0,append,initialState,e0,one,intCast,corner,pt,funext_iff,Fin.forall_fin_two]
  · rw [level1]; exact le_rfl

theorem not_zero_s1 {z : P × ℝ} (hz : z ∈ master d s1) : z.1 ≠ zero := by
  intro he
  have h := hz.2.2.1 e0 (by simp [s1,s0,append,initialState]) (by simp [e0])
  apply h
  rw [he]
  simpa [zero,e0] using point_cast 0 0

theorem master1_min : IsMinimizer (master d s1) (masterCost s1) (one,0) := by
  refine ⟨master1_mem,?_⟩
  intro z hz
  have hn := not_zero_s1 hz
  change l1 zero one ≤ l1 zero z.1
  rcases master_point_cases 1 0 (37/81) s1 hz with h|h|h|h
  · exact False.elim (hn h)
  all_goals rw [h]
  all_goals simp only [l1_two]
  all_goals norm_num [zero,one,other,both,pt]

theorem reply1 : EventReply d s1 (one,0) e1 := by
  refine ⟨by simpa [one,e1] using point_cast 0 1,level1.symm,?_,?_⟩
  · rw [level1]; exact seed_projection _
  · norm_num [e1,distance_two,corner,seed,pt]

theorem master2_mem : (other,0) ∈ master d s2 := by
  apply (FPAdapters.master_source_rows_iff _ _ _).mpr
  refine ⟨(fun row => Fin.elim0 row),⟨corner 1 0,?_,?_⟩,(fun i j => Fin.elim0 j),?_,?_,?_,?_⟩
  · norm_num [IntegerBox,d,data,model,corner,Fin.forall_fin_two]
  · simpa [zero,one,other] using point_cast 1 0
  · intro i
    fin_cases i <;>
      norm_num [family,anchors,s2,s1,s0,append,initialState,e1,e0,Event.anchor,d,data,q,Dq,seed,zero,other,pt]
  · simp [retainedNormals,s2,s1,s0,append,initialState,e0,e1,
      normal_two,seed,other,zero,corner,pt]
    norm_num

  · simp [noGoods,s2,s1,s0,append,initialState,e1,e0,other,intCast,corner,pt,funext_iff,Fin.forall_fin_two]
  · rw [level2]; exact le_rfl

theorem master2_min : IsMinimizer (master d s2) (masterCost s2) (other,0) := by
  refine ⟨master2_mem,?_⟩
  intro z hz
  have hzero := hz.2.2.1 e0 (by simp [s2,s1,s0,append,initialState]) (by simp [e0])
  have hnormal := hz.2.1 e1 (by simp [s2,s1,s0,append,initialState]) rfl
  rw [normal_two] at hnormal
  change l1 seed other ≤ l1 seed z.1
  rcases master_point_cases 1 0 (37/81) s2 hz with h|h|h|h
  · exact False.elim (hzero (by rw [h];simpa [zero,e0] using point_cast 0 0))
  · norm_num [h,e1,seed,one,corner,pt] at hnormal
  · rw [h]
  · norm_num [h,e1,seed,both,corner,pt] at hnormal

theorem reply2 : EventReply d s2 (other,0) e2 := by
  refine ⟨by simpa [other,e2] using point_cast 1 0,level2.symm,?_,?_⟩
  · rw [level2]; exact seed_projection _
  · norm_num [e2,distance_two,corner,seed,pt]

theorem master3_empty : ¬(master d s3).Nonempty := by
  rintro ⟨z,hz⟩
  have hzero := hz.2.2.1 e0 (by simp [s3,s2,s1,s0,append,initialState]) (by simp [e0])
  have hfirst := hz.2.1 e1 (by simp [s3,s2,s1,s0,append,initialState]) rfl
  have hsecond := hz.2.1 e2 (by simp [s3,s2,s1,s0,append,initialState]) rfl
  rw [normal_two] at hfirst hsecond
  rcases master_point_cases 1 0 (37/81) s3 hz with h|h|h|h
  · exact hzero (by rw [h];simpa [zero,e0] using point_cast 0 0)
  · norm_num [h,e1,seed,one,corner,pt] at hfirst
  · norm_num [h,e2,seed,other,corner,pt] at hsecond
  · norm_num [h,e1,seed,both,corner,pt] at hfirst

end Chapter03.FPTrace.C2


