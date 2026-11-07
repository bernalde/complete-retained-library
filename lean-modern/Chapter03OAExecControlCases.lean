module

public import Chapter03OAExecControlModels
public import Chapter03OAExecState

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Controls

theorem cylinder_binary (p : P) : p∈IntegerCylinder (scalar 0) (scalar 1) ↔
    p.2 0=0 ∨ p.2 0=1 := by
  constructor
  · rintro ⟨y,hy,hp⟩
    rcases target_cases y hy with rfl|rfl
    · left; simpa [target0] using congrArg (fun v => v 0) hp
    · right; simpa [target1] using congrArg (fun v => v 0) hp
  · rintro (h|h)
    · exact ⟨target0,target0_mem,scalar_ext (by simpa [target0] using h)⟩
    · exact ⟨target1,target1_mem,scalar_ext (by simpa [target1] using h)⟩

theorem scalar_zero_iff (v : V) : v=scalar 0 ↔ v 0=0 := by
  constructor
  · intro h; exact congrArg (fun w => w 0) h
  · intro h; apply scalar_ext; exact h

theorem fractional_not_integral (x y : ℝ) (hl : 0<y) (hu : y<1) :
    ¬ integral (pt x y) := by
  rintro ⟨z,hz⟩
  have he : y=(z 0:ℝ) := congrArg (fun v => v 0) hz
  rw [he] at hl hu
  have zl : (0:ℤ)<z 0 := by exact_mod_cast hl
  have zu : z 0<(1:ℤ) := by exact_mod_cast hu
  omega

namespace U

theorem seed_valid : SeedValid spec seed :=
  ⟨seed_minimum,Set.mem_univ _,fractional_not_integral 0 (1/2) (by norm_num) (by norm_num)⟩

theorem any_fixed_reply {s : State spec} (q : MasterChoice spec seed s) :
    ∃ e : Event spec, EventValid spec e ∧ q.point.1.2=intCast e.target := by
  obtain ⟨y,hy,hq⟩ := master_integer q.mem
  rcases target_cases y hy with rfl|rfl
  · exact ⟨event0,event0_valid,hq⟩
  · exact ⟨event1,event1_valid,hq⟩

theorem event0_rows (z : P × ℝ) : event0.rows z ↔
    z.1.1 0-z.1.2 0+1/4≤z.2 ∧ -z.1.1 0-z.1.2 0≤0 ∧ z.1.1 0-z.1.2 0≤0 := by
  unfold Event.rows
  rw [event0_anchor]
  change (objective (pt 0 0)+Df (pt 0 0) (z.1-pt 0 0)≤z.2 ∧
    ∀j, (¬ AffineRow (data.g j) ∧ 0≤data.g j (pt 0 0)) →
      data.g j (pt 0 0)+Dg (pt 0 0) j (z.1-pt 0 0)≤0) ↔ _
  rw [objective_tangent 0 (Or.inl rfl),active_rows 0 (Or.inl rfl)]
  norm_num [sub_eq_add_neg,add_assoc]

theorem event1_rows (z : P × ℝ) : event1.rows z ↔
    z.1.1 0+z.1.2 0-3/4≤z.2 ∧ z.1.1 0+z.1.2 0-1≤0 ∧ -z.1.1 0+z.1.2 0-1≤0 := by
  unfold Event.rows
  rw [event1_anchor]
  change (objective (pt 0 1)+Df (pt 0 1) (z.1-pt 0 1)≤z.2 ∧
    ∀j, (¬ AffineRow (data.g j) ∧ 0≤data.g j (pt 0 1)) →
      data.g j (pt 0 1)+Dg (pt 0 1) j (z.1-pt 0 1)≤0) ↔ _
  rw [objective_tangent 1 (Or.inr rfl),active_rows 1 (Or.inr rfl)]
  norm_num
  intros; constructor <;> intro h <;> linarith

end U

namespace I
theorem seed_valid : SeedValid spec seed :=
  ⟨seed_minimum,Set.mem_univ _,fractional_not_integral (1/2) (11/16) (by norm_num) (by norm_num)⟩

theorem any_fixed_reply {s : State spec} (q : MasterChoice spec seed s) :
    ∃ e : Event spec, EventValid spec e ∧ q.point.1.2=intCast e.target := by
  obtain ⟨y,hy,hq⟩ := master_integer q.mem
  rcases target_cases y hy with rfl|rfl
  · exact ⟨event0,event0_valid,hq⟩
  · exact ⟨event1,event1_valid,hq⟩

theorem seed_rows (q : P) : (∀j,data.g j seed+Dg seed j (q-seed)≤0) ↔
    q.1 0-q.2 0+3/16≤0 ∧ 0≤q.2 0 ∧ q.2 0≤1 := by
  norm_num [data,Dg,seed,pt,scalar,Fin.forall_fin_succ]

theorem event0_rows (z : P × ℝ) : event0.rows z ↔
    -z.1.1 0+z.1.2 0≤z.2 ∧ 7/16-z.1.2 0≤0 := by
  unfold Event.rows
  rw [event0_anchor]
  change (objective (pt 0 0)+Df (z.1-pt 0 0)≤z.2 ∧
    ∀j, (¬ AffineRow (data.g j) ∧ 0≤data.g j (pt 0 0)) →
      data.g j (pt 0 0)+Dg (pt 0 0) j (z.1-pt 0 0)≤0) ↔ _
  rw [objective_tangent,selected_rows _ _ (by norm_num [data,pt,scalar]),restoration_row_tangent]
  rfl

theorem event1_rows (z : P × ℝ) : event1.rows z ↔
    -z.1.1 0+z.1.2 0≤z.2 ∧ (3/2)*z.1.1 0-z.1.2 0-1/8≤0 := by
  unfold Event.rows
  rw [event1_anchor]
  change (objective (pt (3/4) 1)+Df (z.1-pt (3/4) 1)≤z.2 ∧
    ∀j, (¬ AffineRow (data.g j) ∧ 0≤data.g j (pt (3/4) 1)) →
      data.g j (pt (3/4) 1)+Dg (pt (3/4) 1) j (z.1-pt (3/4) 1)≤0) ↔ _
  rw [objective_tangent,selected_rows _ _ (by norm_num [data,pt,scalar]),fixed_row_tangent]
  rfl

end I
end Chapter03.OAExec.Controls
