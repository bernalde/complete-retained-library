module

public import Chapter03PumpOAC2Source
public import Chapter03PumpOATransfer

@[expose] public section

noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.FPTrace
namespace Chapter03.PumpOA.C2

def eventOne : OAExec.Event spec where
  target := corner 0 1
  target_mem := by norm_num [IntegerBox,spec,C2.model,corner,Fin.forall_fin_two]
  x := fun _ => 0
  restoration := none

def eventOther : OAExec.Event spec where
  target := corner 1 0
  target_mem := by norm_num [IntegerBox,spec,C2.model,corner,Fin.forall_fin_two]
  x := fun _ => 0
  restoration := none

theorem eventOne_anchor : eventOne.anchor=C2.one := by
  apply Prod.ext
  · rfl
  · funext j; fin_cases j <;> norm_num [OAExec.Event.anchor,eventOne,intCast,C2.one,C2.pt,corner]
theorem eventOther_anchor : eventOther.anchor=C2.other := by
  apply Prod.ext
  · rfl
  · funext j; fin_cases j <;> norm_num [OAExec.Event.anchor,eventOther,intCast,C2.other,C2.pt,corner]

theorem all_fixed_minima (y : IntVector 2) (x : RealVector 0) :
    IsMinimizer (fiber spec.model (intCast y)) (fiberObjective spec.f (intCast y)) x := by
  refine ⟨⟨fun j => Fin.elim0 j,fun j => Fin.elim0 j⟩,?_⟩
  intro z _
  rw [show z=x from Subsingleton.elim _ _]

theorem eventOne_valid : OAExec.EventValid spec eventOne :=
  source_package.every_exact_fixed_event _ eventOne.target_mem _ (all_fixed_minima _ _)
theorem eventOther_valid : OAExec.EventValid spec eventOther :=
  source_package.every_exact_fixed_event _ eventOther.target_mem _ (all_fixed_minima _ _)

theorem handoff_points (p : C2.P) (hp : p=C2.one ∨ p=C2.other ∨ p=C2.both)
    (a : ℝ) (ha : 0≤a) : (p,a)∈FP.handoff C2.d C2.s2 := by
  refine ⟨?_,C2.capTwo_normals_vacuous p,?_⟩
  · refine ⟨⟨⟨⟨trivial,fun _ j => Fin.elim0 j⟩,fun j => Fin.elim0 j⟩,?_⟩,?_⟩
    · rcases hp with rfl|rfl|rfl
      · exact ⟨corner 0 1,by norm_num [IntegerBox,C2.d,C2.data,C2.model,corner,Fin.forall_fin_two],by
        change (C2.pt 0 1).2 = FP.intCast (corner 0 1)
        simpa only [Int.cast_zero,Int.cast_one] using C2.point_cast 0 1⟩
      · exact ⟨corner 1 0,by norm_num [IntegerBox,C2.d,C2.data,C2.model,corner,Fin.forall_fin_two],by
        change (C2.pt 1 0).2 = FP.intCast (corner 1 0)
        simpa only [Int.cast_zero,Int.cast_one] using C2.point_cast 1 0⟩
      · exact ⟨corner 1 1,by norm_num [IntegerBox,C2.d,C2.data,C2.model,corner,Fin.forall_fin_two],by
        change (C2.pt 1 1).2 = FP.intCast (corner 1 1)
        simpa only [Int.cast_zero,Int.cast_one] using C2.point_cast 1 1⟩
    · intro i
      fin_cases i <;> rcases hp with rfl|rfl|rfl
      all_goals norm_num [FP.family,FP.anchors,C2.s2,C2.s1,C2.s0,FP.append,
        FP.initialState,C2.e0,C2.e1,FP.Event.anchor,C2.d,C2.data,C2.q,C2.Dq,
        C2.seed,C2.zero,C2.one,C2.other,C2.both,C2.pt]
      all_goals linarith
  · rcases hp with rfl|rfl|rfl
    all_goals simp [FP.noGoods,C2.s2,C2.s1,C2.s0,FP.append,FP.initialState,
      C2.e0,C2.e1,C2.one,C2.other,C2.both,C2.pt,FP.intCast,corner,funext_iff,Fin.forall_fin_two]

theorem combined_points (p : C2.P) (hp : p=C2.one ∨ p=C2.other ∨ p=C2.both)
    (a : ℝ) (ha : 0≤a) (H : List (OAExec.Event spec))
    (hr : ∀ e∈H, e.rows (p,a)) (hn : ∀ e∈H, e.restoration=none) :
    (p,a)∈master spec (37/81) C2.s2 H := by
  refine ⟨?_,(OAExec.master_mem_iff spec C2.seed H (p,a)).mpr ?_⟩
  · rw [adapter_exact]; exact handoff_points p hp a ha
  · refine ⟨(fun j => Fin.elim0 j),?_,(fun j => Fin.elim0 j),?_,hr,?_⟩
    · rcases hp with rfl|rfl|rfl
      · exact ⟨corner 0 1,eventOne.target_mem,by
        change (C2.pt 0 1).2 = FP.intCast (corner 0 1)
        simpa only [Int.cast_zero,Int.cast_one] using C2.point_cast 0 1⟩
      · exact ⟨corner 1 0,eventOther.target_mem,by
        change (C2.pt 1 0).2 = FP.intCast (corner 1 0)
        simpa only [Int.cast_zero,Int.cast_one] using C2.point_cast 1 0⟩
      · exact ⟨corner 1 1,by norm_num [IntegerBox,spec,C2.model,corner,Fin.forall_fin_two],by
        change (C2.pt 1 1).2 = FP.intCast (corner 1 1)
        simpa only [Int.cast_zero,Int.cast_one] using C2.point_cast 1 1⟩
    · change C2.d.f C2.seed+C2.d.Df C2.seed (p-C2.seed)≤a
      have hs := C2.tangent_seed 1 0 (37/81) p
      change C2.d.f C2.seed+C2.d.Df C2.seed (p-C2.seed)=0 at hs
      rw [hs]; exact ha
    · intro e he hrest
      exact False.elim (hrest (hn e he))

theorem combined_point_cases {H : List (OAExec.Event spec)} {z : C2.P×ℝ}
    (hz : z∈master spec (37/81) C2.s2 H) :
    z.1=C2.one ∨ z.1=C2.other ∨ z.1=C2.both := by
  have hfp : z∈FP.handoff C2.d C2.s2 := by simpa only [adapter_exact] using hz.1
  have hn := hfp.2.2 C2.e0 (by simp [C2.s2,C2.s1,C2.s0,FP.append,FP.initialState])
    (by simp [C2.e0])
  rcases C2.integer_point_cases z.1 (FPAdapters.epigraph_integer_box hfp.1) with h|h|h|h
  · exact False.elim (hn (by rw [h]; simpa [C2.zero,C2.e0] using C2.point_cast 0 0))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem master0_minimum : IsMinimizer (master spec (37/81) C2.s2 []) Prod.snd (C2.one,0) := by
  refine ⟨combined_points C2.one (Or.inl rfl) 0 le_rfl [] (by simp) (by simp),?_⟩
  intro z hz
  have h := ((OAExec.master_mem_iff spec C2.seed [] z).mp hz.2).2.2.2.1
  change C2.d.f C2.seed+C2.d.Df C2.seed (z.1-C2.seed)≤z.2 at h
  have hs := C2.tangent_seed 1 0 (37/81) z.1
  change C2.d.f C2.seed+C2.d.Df C2.seed (z.1-C2.seed)=0 at hs
  rw [hs] at h
  exact h

theorem master1_minimum : IsMinimizer (master spec (37/81) C2.s2 [eventOne])
    Prod.snd (C2.other,4/81) := by
  refine ⟨combined_points C2.other (Or.inr (Or.inl rfl)) (4/81) (by norm_num)
    [eventOne] ?_ (by simp [eventOne]),?_⟩
  · intro e he
    have heq := List.mem_singleton.mp he
    rw [heq]
    simp only [OAExec.Event.rows,eventOne_anchor]
    simp [OAExec.Event.rows,eventOne_anchor,spec,C2.d,C2.data,C2.q,C2.Dq,C2.one,C2.other,C2.pt]
    norm_num
  · intro z hz
    have hf := (((OAExec.master_mem_iff spec C2.seed [eventOne] z).mp hz.2).2.2.2.2.1
      eventOne (by simp)).1
    rcases combined_point_cases hz with h|h|h
    all_goals change C2.d.f eventOne.anchor+C2.d.Df eventOne.anchor (z.1-eventOne.anchor)≤z.2 at hf
    all_goals rw [eventOne_anchor,h] at hf
    all_goals norm_num [C2.d,C2.data,C2.q,C2.Dq,C2.one,C2.other,C2.both,C2.pt] at hf ⊢
    all_goals linarith

theorem master2_minimum : IsMinimizer (master spec (37/81) C2.s2 [eventOne,eventOther])
    Prod.snd (C2.one,10/81) := by
  refine ⟨combined_points C2.one (Or.inl rfl) (10/81) (by norm_num)
    [eventOne,eventOther] ?_ (by simp [eventOne,eventOther]),?_⟩
  · intro e he
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    all_goals simp only [OAExec.Event.rows,eventOne_anchor,eventOther_anchor]
    all_goals simp [OAExec.Event.rows,eventOne_anchor,eventOther_anchor,spec,C2.d,C2.data,
      C2.q,C2.Dq,C2.one,C2.other,C2.pt]
    all_goals norm_num
  · intro z hz
    have hh := ((OAExec.master_mem_iff spec C2.seed [eventOne,eventOther] z).mp hz.2).2.2.2.2.1
    have hf := (hh eventOne (by simp)).1
    have hg := (hh eventOther (by simp)).1
    rcases combined_point_cases hz with h|h|h
    all_goals change C2.d.f eventOne.anchor+C2.d.Df eventOne.anchor (z.1-eventOne.anchor)≤z.2 at hf
    all_goals change C2.d.f eventOther.anchor+C2.d.Df eventOther.anchor (z.1-eventOther.anchor)≤z.2 at hg
    all_goals rw [eventOne_anchor,h] at hf
    all_goals rw [eventOther_anchor,h] at hg
    all_goals norm_num [C2.d,C2.data,C2.q,C2.Dq,C2.one,C2.other,C2.both,C2.pt] at hf hg ⊢
    all_goals linarith

end Chapter03.PumpOA.C2

#print axioms Chapter03.PumpOA.C2.eventOne_valid
#print axioms Chapter03.PumpOA.C2.eventOther_valid
#print axioms Chapter03.PumpOA.C2.master0_minimum
#print axioms Chapter03.PumpOA.C2.master1_minimum
#print axioms Chapter03.PumpOA.C2.master2_minimum
