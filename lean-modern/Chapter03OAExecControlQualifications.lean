module

public import Chapter03OAExecControlUExecution
public import Chapter03OAExecControlIExecution

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
namespace Chapter03.OAExec.Controls

namespace U

theorem objective_C1 : ContDiff ℝ 1 objective := by unfold objective; fun_prop

theorem rows_C1 (j : Fin 5) : ContDiff ℝ 1 (data.g j) := by
  fin_cases j <;> dsimp [data] <;> fun_prop

/-- Thesis A1--A3's convex C1 data and nonempty compact relaxation reading
still does not supply its requested first optimal master solution. -/
theorem thesis_master_obstruction :
    ContDiff ℝ 1 objective ∧ (∀j,ContDiff ℝ 1 (data.g j)) ∧
    ConvexOn ℝ Set.univ objective ∧ (∀j,ConvexOn ℝ Set.univ (data.g j)) ∧
    IsCompact (data.relaxationOn Set.univ) ∧ (data.relaxationOn Set.univ).Nonempty ∧
    (master spec seed []).Nonempty ∧ ¬∃z,IsMinimizer (master spec seed []) Prod.snd z :=
  ⟨objective_C1,rows_C1,objective_convex,row_convex,relaxation_compact,
    ⟨seed,seed_minimum.1⟩,initial_nonempty,initial_no_minimizer⟩

theorem one_open {s : State spec} (hs : Reachable spec seed 0 s)
    (hn : s.history.length=1) : loopOpen spec 0 s := by
  intro p hp
  have hv := reachable_incumbent_cost hs hp
  have hl : s.lower=0 := by
    cases reachable_phase hs with
    | zero hh hl => simp [hh] at hn
    | one _ hl => exact hl
    | two hh _ _ _ => omega
    | three hh _ _ _ => omega
  rw [hv,hl]
  norm_num

theorem one_step_bound_drop {s t : State spec} (hs : Reachable spec seed 0 s)
    (hn : s.history.length=1) (ht : RawStep spec seed 0 s t) :
    s.lower=0 ∧ t.lower= -1 := by
  have hlen : t.history.length=2 := by
    cases ht
    simp [advance,hn]
  constructor
  · cases reachable_phase hs with
    | zero hh _ => simp [hh] at hn
    | one _ hl => exact hl
    | two hh _ _ _ => omega
    | three hh _ _ _ => omega
  · cases reachable_phase (.next hs ht) with
    | zero hh _ => simp [hh] at hlen
    | one hh _ => omega
    | two _ _ _ hl => exact hl
    | three hh _ _ _ => omega

/-- Every selector performs an actual transition lowering its stored bound
from zero to minus one, before completing its third round. -/
theorem every_selector_bound_drop (choose : Selector spec seed 0) :
    ∃s t, Reachable spec seed 0 s ∧ RawStep spec seed 0 s t ∧
      s.lower=0 ∧ t.lower= -1 := by
  have ho : loopOpen spec 0 (initialState spec seed) := by
    simp [loopOpen,initialState]
  cases hc : choose (initialState spec seed) .initial ho with
  | empty he =>
    have hn := initial_nonempty
    change (master spec seed [])=∅ at he
    rw [he] at hn
    exact False.elim (Set.not_nonempty_empty hn)
  | next q e hv hy =>
    let s := advance (initialState spec seed) q e
    have hs : Reachable spec seed 0 s := .next .initial (.step ho q e hv hy)
    have hn : s.history.length=1 := by simp [s,advance,initialState]
    have ho1 := one_open hs hn
    cases hc1 : choose s hs ho1 with
    | empty he =>
      have hne := master_nonempty s.history (reachable_invariant analytic seed_valid hs).history.2
      rw [he] at hne
      exact False.elim (Set.not_nonempty_empty hne)
    | next q1 e1 hv1 hy1 =>
      have ht : RawStep spec seed 0 s (advance s q1 e1) := .step ho1 q1 e1 hv1 hy1
      exact ⟨s,advance s q1 e1,hs,ht,one_step_bound_drop hs hn ht⟩

end U

namespace I

theorem objective_C1 : ContDiff ℝ 1 objective := by unfold objective; fun_prop

theorem rows_C1 (j : Fin 3) : ContDiff ℝ 1 (data.g j) := by
  fin_cases j <;> dsimp [data] <;> fun_prop

theorem relaxation_compact : IsCompact (data.relaxationOn Set.univ) := by
  have hc : IsClosed (data.relaxationOn Set.univ) := by
    have he : data.relaxationOn Set.univ =
        {p : P | (p.1 0)^2+7/16≤p.2 0} ∩ {p : P | 0≤p.2 0} ∩ {p : P | p.2 0≤1} := by
      ext p
      rw [relaxation]
      simp only [Set.mem_inter_iff,Set.mem_setOf_eq,and_assoc]
    rw [he]
    exact ((isClosed_le (by fun_prop) (by fun_prop)).inter
      (isClosed_le continuous_const (by fun_prop))).inter
        (isClosed_le (by fun_prop) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  change data.relaxationOn Set.univ ⊆ Set.Icc (pt (-3/4) 0) (pt (3/4) 1)
  intro p hp
  obtain ⟨hg,hy0,hy1⟩ := (relaxation p).mp hp
  constructor
  · constructor
    · intro i; fin_cases i
      change (-3:ℝ)/4≤p.1 0
      nlinarith [sq_nonneg (p.1 0+3/4)]
    · intro i; fin_cases i; exact hy0
  · constructor
    · intro i; fin_cases i
      change p.1 0≤(3/4:ℝ)
      nlinarith [sq_nonneg (p.1 0-3/4)]
    · intro i; fin_cases i; exact hy1

end I

#print axioms U.thesis_master_obstruction
#print axioms U.every_selector_bound_drop
#print axioms I.relaxation_compact
end Chapter03.OAExec.Controls
