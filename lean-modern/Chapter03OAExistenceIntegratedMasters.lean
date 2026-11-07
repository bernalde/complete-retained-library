module

public import Chapter03OAExistenceIntegratedSolves

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Integrated

def master0 : P×ℝ := (pt (-3/16) 0,15/16)
def master1 : P×ℝ := (solution,5/4)

theorem master_empty_iff (z : P×ℝ) : z∈master spec seed [] ↔
    z.1.1 0≤1/2 ∧ (z.1.2 0=0 ∨ z.1.2 0=1) ∧
      z.1.1 0-z.1.2 0+3/16≤0 ∧ -z.1.1 0+z.1.2 0+3/4≤z.2 := by
  rw [master_mem_iff]
  change (z.1∈model.linearRegion ∧ z.1∈IntegerCylinder (scalar 0) (scalar 1) ∧
    (∀j,model.g j seed+Dg seed j (z.1-seed)≤0) ∧
    objective seed+Df seed (z.1-seed)≤z.2 ∧ _ ∧ _) ↔ _
  rw [hard_region,cylinder_binary,seed_objective_tangent]
  simp only [seed_constraint_tangent]
  simp [noGoods]

theorem master_after0_iff (z : P×ℝ) : z∈master spec seed [event0] ↔
    z.1.1 0≤1/2 ∧ z.1.2 0=1 ∧ -z.1.1 0+7/4≤z.2 ∧ 2-2*z.1.1 0≤z.2 := by
  rw [master_mem_iff]
  change (z.1∈model.linearRegion ∧ z.1∈IntegerCylinder (scalar 0) (scalar 1) ∧
    (∀j,model.g j seed+Dg seed j (z.1-seed)≤0) ∧
    objective seed+Df seed (z.1-seed)≤z.2 ∧ _ ∧ _) ↔ _
  rw [hard_region,cylinder_binary,seed_objective_tangent]
  simp only [seed_constraint_tangent,Fin.forall_fin_one,List.mem_singleton,forall_eq,
    event0_rows]
  constructor
  · rintro ⟨hx,hy,hg,hf,he,hn⟩
    have hy1 : z.1.2 0=1 := by rcases hy with h|h; linarith [he.2]; exact h
    exact ⟨hx,hy1,by linarith,by linarith [he.1]⟩
  · rintro ⟨hx,hy,hf,he⟩
    refine ⟨hx,Or.inr hy,by linarith,by linarith,⟨by linarith,by linarith⟩,?_⟩
    intro e hem hrest hsame
    have ee : e=event0 := List.mem_singleton.mp hem
    subst e
    have hh := congrArg (fun v : V => v 0) hsame
    norm_num [event0,intCast,target0] at hh
    linarith

theorem master0_minimum : IsMinimizer (master spec seed []) Prod.snd master0 := by
  refine ⟨(master_empty_iff _).mpr (by norm_num [master0,pt,scalar]),?_⟩
  intro z hz
  obtain ⟨hx,hy,hg,hf⟩ := (master_empty_iff z).mp hz
  change (15/16:ℝ)≤z.2
  rcases hy with hy|hy <;> linarith

theorem master0_unique {z : P×ℝ} (hm : IsMinimizer (master spec seed []) Prod.snd z) :
    z=master0 := by
  obtain ⟨hx,hy,hg,hf⟩ := (master_empty_iff z).mp hm.1
  have hh := hm.2 _ master0_minimum.1
  change z.2≤(15/16:ℝ) at hh
  rcases hy with hy|hy
  · apply Prod.ext
    · apply point_ext
      · norm_num [master0,pt,scalar]; linarith
      · exact hy
    · change z.2=(15/16:ℝ); linarith
  · exfalso; linarith

theorem master1_minimum : IsMinimizer (master spec seed [event0]) Prod.snd master1 := by
  refine ⟨(master_after0_iff _).mpr (by norm_num [master1,solution,pt,scalar]),?_⟩
  intro z hz
  obtain ⟨hx,hy,hf,he⟩ := (master_after0_iff z).mp hz
  change (5/4:ℝ)≤z.2
  linarith

theorem master1_unique {z : P×ℝ} (hm : IsMinimizer (master spec seed [event0]) Prod.snd z) :
    z=master1 := by
  obtain ⟨hx,hy,hf,he⟩ := (master_after0_iff z).mp hm.1
  have hh := hm.2 _ master1_minimum.1
  change z.2≤(5/4:ℝ) at hh
  apply Prod.ext
  · apply point_ext
    · change z.1.1 0=1/2; linarith
    · exact hy
  · change z.2=(5/4:ℝ); linarith

/-- Any actual master reply at either reachable open history must use the
attained branch. The unbounded branch is ruled out by a derived lower bound. -/
theorem choice_is_minimum {s : State spec} (q : MasterChoice spec seed s)
    {z : P×ℝ} (hm : IsMinimizer (master spec seed s.history) Prod.snd z) :
    q.attained=true ∧ IsMinimizer (master spec seed s.history) Prod.snd q.point := by
  have hb : BddBelow (Prod.snd '' master spec seed s.history) := by
    refine ⟨z.2,?_⟩
    rintro a ⟨w,hw,rfl⟩
    exact hm.2 w hw
  have hv := q.valid
  cases ha : q.attained
  · simp only [ha,Bool.false_eq_true,↓reduceIte] at hv
    exact (hv.2 hb).elim
  · simp only [ha,↓reduceIte] at hv
    exact ⟨rfl,hv⟩

theorem choice0_unique {s : State spec} (hs : s.history=[])
    (q : MasterChoice spec seed s) : q.point=master0 ∧ q.nextLower=15/16 := by
  have hm : IsMinimizer (master spec seed s.history) Prod.snd master0 := by
    rw [hs]; exact master0_minimum
  obtain ⟨ha,hq⟩ := choice_is_minimum q hm
  rw [hs] at hq
  have hp := master0_unique hq
  exact ⟨hp,by simp [MasterChoice.nextLower,ha,hp,master0]⟩

theorem choice1_unique {s : State spec} (hs : s.history=[event0])
    (q : MasterChoice spec seed s) : q.point=master1 ∧ q.nextLower=5/4 := by
  have hm : IsMinimizer (master spec seed s.history) Prod.snd master1 := by
    rw [hs]; exact master1_minimum
  obtain ⟨ha,hq⟩ := choice_is_minimum q hm
  rw [hs] at hq
  have hp := master1_unique hq
  exact ⟨hp,by simp [MasterChoice.nextLower,ha,hp,master1]⟩

theorem event_of_y0 {e : Event spec} (he : EventValid spec e)
    (hy : intCast e.target 0=0) : e=event0 := by
  rcases valid_event_cases he with rfl|rfl
  · rfl
  · norm_num [event1,intCast,target1] at hy

theorem event_of_y1 {e : Event spec} (he : EventValid spec e)
    (hy : intCast e.target 0=1) : e=event1 := by
  rcases valid_event_cases he with rfl|rfl
  · norm_num [event0,intCast,target0] at hy
  · rfl

end Chapter03.OAExec.Integrated
