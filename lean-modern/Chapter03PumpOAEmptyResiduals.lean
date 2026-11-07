module

public import Chapter03PumpOASymmetricPump
public import Chapter03PumpOAInfeasiblePump
public import Chapter03PumpOARun

@[expose] public section

noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA

namespace Symmetric

theorem combined_empty (H : List (OAExec.Event spec)) : master spec 0 s2 H=∅ := by
  change FP.handoff pump s2 ∩ OAExec.master spec s2.seed H=∅
  rw [handoff_empty]
  simp

theorem suffix_returns_saved (epsilon : ℝ) (heps : epsilon<1/4)
    (choose : Selector spec 0 s2 epsilon) (fuel : ℕ) :
    runFuel spec 0 s2 epsilon choose (fuel+1) (initialState spec s2) .initial=
      some ⟨.solution (pt 0),1,0,0⟩ := by
  have ho : OAExec.loopOpen spec epsilon (initialState spec s2) := by
    simp only [OAExec.loopOpen,initialState,show s2.incumbent=some (pt 0) from rfl,
      Option.some.injEq,forall_eq']
    norm_num [spec,s2,s1,s0,e0,e1,FP.append,FP.initialState,seed,pt]
    exact heps
  cases hc : choose (initialState spec s2) .initial ho with
  | empty he =>
    simpa only [emptyResult,initialState,show s2.incumbent=some (pt 0) from rfl] using
      runFuel_empty spec 0 s2 epsilon choose fuel (initialState spec s2) .initial ho he hc
  | next q e hv hy =>
    have hm := q.mem
    rw [combined_empty] at hm
    exact hm.elim

theorem saved_incumbent_feasible : pt 0∈spec.original := by
  exact FP.fiber_subset_original pump (iv 0) (by simpa using (fiber_minimum 0 (Or.inl rfl)).1)

end Symmetric

namespace Infeasible

theorem combined_empty (H : List (OAExec.Event spec)) : master spec 0 s0 H=∅ := by
  change FP.handoff pump s0 ∩ OAExec.master spec s0.seed H=∅
  rw [handoff_empty]
  simp

theorem suffix_returns_infeasible (epsilon : ℝ) (choose : Selector spec 0 s0 epsilon)
    (fuel : ℕ) : runFuel spec 0 s0 epsilon choose (fuel+1)
      (initialState spec s0) .initial=some ⟨.infeasible,1,0,0⟩ := by
  have ho : OAExec.loopOpen spec epsilon (initialState spec s0) := by
    simp [OAExec.loopOpen,initialState,s0,FP.initialState]
  cases hc : choose (initialState spec s0) .initial ho with
  | empty he =>
    simpa only [emptyResult,initialState,s0,FP.initialState] using
      runFuel_empty spec 0 s0 epsilon choose fuel (initialState spec s0) .initial ho he hc
  | next q e hv hy =>
    have hm := q.mem
    rw [combined_empty] at hm
    exact hm.elim

end Infeasible
end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.Symmetric.suffix_returns_saved
#print axioms Chapter03.PumpOA.Symmetric.saved_incumbent_feasible
#print axioms Chapter03.PumpOA.Infeasible.suffix_returns_infeasible
