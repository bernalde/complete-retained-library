module

public import Chapter03OAExecControlUMaster
public import Chapter03OAExecControlIMaster
public import Chapter03OAExecInvariant
public import Chapter03OAExecRun

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Controls

theorem minimum_bddBelow {S : Set (P×ℝ)} {z : P×ℝ}
    (hm : IsMinimizer S Prod.snd z) : BddBelow (Prod.snd '' S) := by
  refine ⟨z.2,?_⟩
  rintro a ⟨w,hw,rfl⟩
  exact hm.2 w hw

theorem choice_attained_of_minimum {l : ℕ} {d : Data 1 1 l 0} {seed : P}
    {s : State d} (q : MasterChoice d seed s) {z : P×ℝ}
    (hm : IsMinimizer (master d seed s.history) Prod.snd z) : q.attained=true := by
  cases hq : q.attained with
  | false =>
    have hv := q.valid
    simp only [hq,Bool.false_eq_true,↓reduceIte] at hv
    exact False.elim (hv.2 (minimum_bddBelow hm))
  | true => rfl

theorem choice_minimum {l : ℕ} {d : Data 1 1 l 0} {seed : P}
    {s : State d} (q : MasterChoice d seed s) (hq : q.attained=true) :
    IsMinimizer (master d seed s.history) Prod.snd q.point := by
  have hv := q.valid
  simpa only [hq,↓reduceIte] using hv

theorem target_distinct : target0≠target1 := by
  intro h
  have hh := congrArg (fun y : IntVector 1 => y 0) h
  norm_num [target0,target1] at hh

theorem binary_box_card : ((integerBox_finite (scalar (0:ℝ)) (scalar 1)).toFinset).card=2 := by
  classical
  have he : (integerBox_finite (scalar (0:ℝ)) (scalar 1)).toFinset={target0,target1} := by
    ext y
    simp only [Set.Finite.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · exact target_cases y
    · rintro (rfl|rfl)
      · exact target0_mem
      · exact target1_mem
  rw [he]
  simp [target_distinct]

namespace U
theorem event_distinct : event0≠event1 := by
  intro h; exact target_distinct (congrArg Event.target h)

theorem localAvailability (epsilon : ℝ) : LocalAvailability spec seed epsilon where
  master_attainment s hs _ _ hb :=
    bounded_master_attained s.history (reachable_invariant analytic seed_valid hs).history.2 hb
  fixed_or_restoration _ _ _ q := any_fixed_reply q

theorem selectors_inhabited (epsilon : ℝ) : Nonempty (Selector spec seed epsilon) :=
  selector_inhabited (localAvailability epsilon)

theorem box_card : spec.box.card=2 := binary_box_card

theorem event_cost {e : Event spec} (he : EventValid spec e) :
    spec.f e.anchor=1/4 ∧ e.restoration=none := by
  rcases valid_event_cases he with rfl|rfl <;>
    norm_num [spec,objective,event0_anchor,event1_anchor,event0,event1,Event.anchor,intCast,target0,target1,pt,scalar]

theorem reachable_incumbent_cost {epsilon : ℝ} {s : State spec}
    (hs : Reachable spec seed epsilon s) {p : P} (hp : s.incumbent=some p) :
    spec.f p=1/4 := by
  have inv := reachable_invariant analytic seed_valid hs
  obtain ⟨e,he,_,ha⟩ := inv.provenance p hp
  rw [←ha]
  exact (event_cost (inv.history.2 e he)).1

theorem reachable_nonempty_incumbent {epsilon : ℝ} {s : State spec}
    (hs : Reachable spec seed epsilon s) (hn : s.history≠[]) :
    ∃p,s.incumbent=some p ∧ spec.f p=1/4 := by
  have inv := reachable_invariant analytic seed_valid hs
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil s.history hn
  obtain ⟨p,hp,_⟩ := inv.dominates e he (event_cost (inv.history.2 e he)).2
  exact ⟨p,hp,reachable_incumbent_cost hs hp⟩

end U

namespace I
theorem event_distinct : event0≠event1 := by
  intro h; exact target_distinct (congrArg Event.target h)

theorem localAvailability (epsilon : ℝ) : LocalAvailability spec seed epsilon where
  master_attainment s hs _ _ _ :=
    master_attained s.history (reachable_invariant analytic seed_valid hs).history.2
  fixed_or_restoration _ _ _ q := any_fixed_reply q

theorem selectors_inhabited (epsilon : ℝ) : Nonempty (Selector spec seed epsilon) :=
  selector_inhabited (localAvailability epsilon)

theorem box_card : spec.box.card=2 := binary_box_card

theorem reachable_incumbent {epsilon : ℝ} {s : State spec}
    (hs : Reachable spec seed epsilon s) {p : P} (hp : s.incumbent=some p) :
    p=pt (3/4) 1 := by
  have inv := reachable_invariant analytic seed_valid hs
  obtain ⟨e,he,hn,ha⟩ := inv.provenance p hp
  rcases valid_event_cases (inv.history.2 e he) with rfl|rfl
  · simp [event0] at hn
  · simpa using ha.symm

theorem reachable_has_incumbent {epsilon : ℝ} {s : State spec}
    (hs : Reachable spec seed epsilon s) (h1 : event1∈s.history) :
    s.incumbent=some (pt (3/4) 1) := by
  have inv := reachable_invariant analytic seed_valid hs
  obtain ⟨p,hp,_⟩ := inv.dominates event1 h1 rfl
  simpa only [reachable_incumbent hs hp] using hp

end I
end Chapter03.OAExec.Controls
