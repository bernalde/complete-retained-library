module

public import Chapter03OAExecControlQualifications
public import Chapter03OAExecInitialization

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
namespace Chapter03.OAExec.Controls

namespace U

theorem reachable_incumbent_point {s : State spec} (hs : Reachable spec seed 0 s)
    {p : P} (hp : s.incumbent=some p) : p=pt 0 0 ∨ p=pt 0 1 := by
  have inv := reachable_invariant analytic seed_valid hs
  obtain ⟨e,he,_,ha⟩ := inv.provenance p hp
  rcases valid_event_cases (inv.history.2 e he) with rfl|rfl
  · exact Or.inl (by simpa only [event0_anchor] using ha.symm)
  · exact Or.inr (by simpa only [event1_anchor] using ha.symm)

theorem execution_result {s : State spec} {out : Output 1 1}
    (hx : Execution spec seed 0 s out) (hs : Reachable spec seed 0 s) :
    ∃p,out.result=.solution p ∧ (p=pt 0 0 ∨ p=pt 0 1) := by
  induction hx with
  | gap hi _ => exact ⟨_,rfl,reachable_incumbent_point hs hi⟩
  | @empty s _ he =>
    have hn := master_nonempty s.history (reachable_invariant analytic seed_valid hs).history.2
    rw [he] at hn
    exact False.elim (Set.not_nonempty_empty hn)
  | step ho q e he hy _ ih => exact ih (.next hs (.step ho q e he hy))

theorem initial_availability : InitialAvailability spec :=
  Or.inr ⟨seed,seed_valid.1,seed_valid.2.1⟩

theorem initialized_availability (p : P) (hp : SeedValid spec p) :
    LocalAvailability spec p 0 := by
  have he : p=seed := seed_unique hp.1
  subst p
  exact localAvailability 0

/-- Full initializer and source-ordered driver, with every local premise
proved for the actual model, all tied choices included, and defined output. -/
theorem complete_control :
    Nonempty (Initialization spec) ∧ Nonempty (InitializedSelectors spec 0) ∧
    ∀choose : InitializedSelectors spec 0, ∀initial : Initialization spec, ∃out p,
      execute spec 0 choose initial=some out ∧ ReturnCertificate spec 0 out.result ∧
      out.result=.solution p ∧ (p=pt 0 0 ∨ p=pt 0 1) ∧
      out.masters=3 ∧ out.fixed=3 ∧ out.restorations=0 := by
  refine ⟨initialization_inhabited initial_availability,
    initialized_selectors_inhabited initialized_availability,?_⟩
  intro choose initial
  cases initial with
  | empty he =>
    have hm := seed_valid.1.1
    rw [he] at hm
    exact False.elim hm
  | minimum p hm hd =>
    have he : p=seed := seed_unique hm
    subst p
    have hi := seed_valid.2.2
    let selected := choose seed ⟨hm,hd,hi⟩
    obtain ⟨out,hr,hc,hmaster,hfixed,hrest⟩ := every_selector_three_rounds.2 selected
    have hex := runFuel_execution spec seed 0 selected 3 _ .initial hr
    obtain ⟨p,hp,hpoints⟩ := execution_result hex .initial
    exact ⟨out,p,by simpa only [execute,dif_neg hi,box_card] using hr,
      hc,hp,hpoints,hmaster,hfixed,hrest⟩

end U

namespace I

theorem execution_result {s : State spec} {out : Output 1 1}
    (hx : Execution spec seed 0 s out) (hs : Reachable spec seed 0 s) :
    out.result=.solution (pt (3/4) 1) := by
  induction hx with
  | gap hi _ => simp only [reachable_incumbent hs hi]
  | @empty s _ he =>
    obtain ⟨z,hz⟩ := master_attained s.history (reachable_invariant analytic seed_valid hs).history.2
    have hz := hz.1
    rw [he] at hz
    exact False.elim hz
  | step ho q e he hy _ ih => exact ih (.next hs (.step ho q e he hy))

theorem initial_availability : InitialAvailability spec :=
  Or.inr ⟨seed,seed_valid.1,seed_valid.2.1⟩

theorem initialized_availability (p : P) (hp : SeedValid spec p) :
    LocalAvailability spec p 0 := by
  have he : p=seed := seed_unique hp.1
  subst p
  exact localAvailability 0

/-- Every exact initial reply, every tied master choice, the actual sum
restoration, and the final repeated feasible fiber occur in the real driver. -/
theorem complete_control :
    Nonempty (Initialization spec) ∧ Nonempty (InitializedSelectors spec 0) ∧
    ∀choose : InitializedSelectors spec 0, ∀initial : Initialization spec, ∃out,
      execute spec 0 choose initial=some out ∧ ReturnCertificate spec 0 out.result ∧
      out.result=.solution (pt (3/4) 1) ∧
      out.masters=3 ∧ out.fixed=3 ∧ out.restorations=1 := by
  refine ⟨initialization_inhabited initial_availability,
    initialized_selectors_inhabited initialized_availability,?_⟩
  intro choose initial
  cases initial with
  | empty he =>
    have hm := seed_valid.1.1
    rw [he] at hm
    exact False.elim hm
  | minimum p hm hd =>
    have he : p=seed := seed_unique hm
    subst p
    have hi := seed_valid.2.2
    let selected := choose seed ⟨hm,hd,hi⟩
    obtain ⟨out,hr,hc,hmaster,hfixed,hrest⟩ := every_selector_three_rounds.2 selected
    have hex := runFuel_execution spec seed 0 selected 3 _ .initial hr
    exact ⟨out,by simpa only [execute,dif_neg hi,box_card] using hr,
      hc,execution_result hex .initial,hmaster,hfixed,hrest⟩

end I

#print axioms U.complete_control
#print axioms I.complete_control
end Chapter03.OAExec.Controls
