module

public import Chapter03OAExecControlEndpoints

@[expose] public section

/-! Full-source U/I controls. The theorem endpoints range over the actual
initializer, reachable states, all exact ties and the shared recursive driver.
This module's source set identities preserve the thesis's soft bound rows. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
namespace Chapter03.OAExec.Controls

namespace U

theorem source_original (p : P) :
    p∈spec.original ↔ (∀j,data.g j p≤0) ∧ integral p :=
  thesis_original_iff spec boundRows p

theorem original_geometry (p : P) : p∈spec.original ↔ p=pt 0 0 ∨ p=pt 0 1 := by
  constructor
  · intro hp
    obtain ⟨_,hg,_,y,hy,hcast⟩ := (source_feasible_iff data Set.univ p).mp hp
    have hx := ((rows p).mp hg).1
    rcases target_cases y hy with rfl|rfl
    · left
      apply point_ext hx
      simpa [cast_target0,scalar,target0] using congrArg (fun z : V => z 0) hcast
    · right
      apply point_ext hx
      simpa [cast_target1,scalar,target1] using congrArg (fun z : V => z 0) hcast
  · rintro (rfl|rfl)
    · simpa only [event0_anchor] using event_feasible event0_valid rfl
    · simpa only [event1_anchor] using event_feasible event1_valid rfl

theorem source_restoration (y x : V) (s : RealVector 5) :
    weightedInsert x s∈restSet data y ↔
      (∀j,data.g j (x,y)≤s j) ∧ (∀j,0≤s j) :=
  thesis_restoration_iff spec y x s

end U

namespace I

theorem source_original (p : P) :
    p∈spec.original ↔ (∀j,data.g j p≤0) ∧ integral p :=
  thesis_original_iff spec boundRows p

theorem original_geometry (p : P) :
    p∈spec.original ↔ p.2 0=1 ∧ (p.1 0)^2≤9/16 := by
  constructor
  · intro hp
    obtain ⟨_,hg,_,y,hy,hcast⟩ := (source_feasible_iff data Set.univ p).mp hp
    have hx := ((rows p).mp hg).1
    rcases target_cases y hy with rfl|rfl
    · have h0 : p.2 0=0 := by simpa [cast_target0,scalar,target0] using congrArg (fun z : V => z 0) hcast
      rw [h0] at hx
      nlinarith [sq_nonneg (p.1 0)]
    · have h1 : p.2 0=1 := by simpa [cast_target1,scalar,target1] using congrArg (fun z : V => z 0) hcast
      exact ⟨h1,by rw [h1] at hx; linarith⟩
  · rintro ⟨hy,hx⟩
    apply (source_feasible_iff data Set.univ p).mpr
    refine ⟨Set.mem_univ _,(rows p).mpr ?_,hard _,target1,target1_mem,?_⟩
    · rw [hy]; norm_num; linarith
    · apply scalar_ext; simpa [target1] using hy

theorem source_restoration (y x : V) (s : RealVector 3) :
    weightedInsert x s∈restSet data y ↔
      (∀j,data.g j (x,y)≤s j) ∧ (∀j,0≤s j) :=
  thesis_restoration_iff spec y x s

end I

#print axioms U.complete_control
#print axioms I.complete_control
#print axioms U.original_geometry
#print axioms I.original_geometry
#print axioms U.fixed_active_not_independent
#print axioms U.thesis_master_obstruction
#print axioms U.every_selector_bound_drop
end Chapter03.OAExec.Controls
