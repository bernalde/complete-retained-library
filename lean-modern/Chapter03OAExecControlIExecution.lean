module

public import Chapter03OAExecControlAvailability
public import Chapter03OAExecReturnCounts

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
namespace Chapter03.OAExec.Controls.I
local instance : DecidableEq (Event spec) := Classical.decEq _

/-- The restoration event occurs exactly once; both possible orders of the
first two binary fibers are admitted by these actual reachable phases. -/
inductive Phase (s : State spec) : Prop
  | zero (history : s.history=[]) (lower : s.lower=3/16)
  | one (length : s.history.length=1) (lower : s.lower=3/16)
  | two (length : s.history.length=2) (zero_mem : event0∈s.history)
      (one_mem : event1∈s.history) (zeros : s.history.count event0=1) (lower : s.lower=3/16)
  | three (length : s.history.length=3) (zero_mem : event0∈s.history)
      (one_mem : event1∈s.history) (zeros : s.history.count event0=1) (lower : s.lower=1/4)

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

theorem phase_step {s t : State spec} (hs : Reachable spec seed 0 s)
    (hp : Phase s) (ht : RawStep spec seed 0 s t) : Phase t := by
  classical
  have hv := (reachable_invariant analytic seed_valid hs).history.2
  cases ht with
  | step ho q e he hy =>
    obtain ⟨w,hw⟩ := master_attained s.history hv
    have hq := choice_attained_of_minimum q hw
    have hm := choice_minimum q hq
    cases hp with
    | zero hh hl =>
      have hz := neither_minimizer_cases _ hv (by simp [hh]) (by simp [hh]) hm
      apply Phase.one
      · simp [advance,hh]
      · rcases hz with hz|hz <;> simp [advance,MasterChoice.nextLower,hq,hz]
    | one hn hl =>
      obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp hn
      have hva : EventValid spec a := hv a (by simp [ha])
      rcases valid_event_cases hva with rfl|rfl
      · have h0 : event0∈s.history := by simp [ha]
        have h1 : event1∉s.history := by simp [ha,Ne.symm event_distinct]
        have hz := only0_unique _ hv h0 h1 hm
        have hy1 : intCast e.target 0=1 := by
          have ht := congrArg (fun y : V => y 0) hy
          simpa [hz,pt,scalar] using ht.symm
        have ee := event_of_y1 he hy1
        apply Phase.two
        · simp [advance,hn]
        · simp [advance,h0]
        · simp [advance,ee]
        · simp [advance,ha,ee,event_distinct,Ne.symm event_distinct]
        · simp [advance,MasterChoice.nextLower,hq,hz]
      · have h0 : event0∉s.history := by simp [ha,event_distinct]
        have h1 : event1∈s.history := by simp [ha]
        have hz := only1_unique _ hv h0 h1 hm
        have hy0 : intCast e.target 0=0 := by
          have ht := congrArg (fun y : V => y 0) hy
          simpa [hz,pt,scalar] using ht.symm
        have ee := event_of_y0 he hy0
        apply Phase.two
        · simp [advance,hn]
        · simp [advance,ee]
        · simp [advance,h1]
        · simp [advance,ha,ee,event_distinct,Ne.symm event_distinct]
        · simp [advance,MasterChoice.nextLower,hq,hz]
    | two hn h0 h1 hc hl =>
      have hz := both_unique _ hv h0 h1 hm
      have hy1 : intCast e.target 0=1 := by
        have ht := congrArg (fun y : V => y 0) hy
        simpa [hz,pt,scalar] using ht.symm
      have ee := event_of_y1 he hy1
      apply Phase.three
      · simp [advance,hn]
      · simp [advance,h0]
      · simp [advance,h1]
      · simp [advance,ee,List.count_append,hc,event_distinct,Ne.symm event_distinct]
      · simp [advance,MasterChoice.nextLower,hq,hz]
    | three hn h0 h1 hc hl =>
      have hi := reachable_has_incumbent hs h1
      have ht := ho _ hi
      norm_num [spec,objective,pt,scalar,hl] at ht

theorem reachable_phase {s : State spec} (hs : Reachable spec seed 0 s) : Phase s := by
  induction hs with
  | initial =>
    apply Phase.zero rfl
    norm_num [initialState,spec,seed,objective,pt,scalar]
  | next before step ih => exact phase_step before ih step

theorem event_restorations {e : Event spec} (he : EventValid spec e) :
    eventRestorations e=[e].count event0 := by
  classical
  rcases valid_event_cases he with rfl|rfl
  · simp [eventRestorations,event0]
  · have hr : event1.restoration=none := rfl
    simp [eventRestorations,hr,Ne.symm event_distinct]

theorem execution_counts_exact {s : State spec} {out : Output 1 1}
    (hx : Execution spec seed 0 s out) (hs : Reachable spec seed 0 s) :
    out.masters+s.history.length=3 ∧ out.fixed=out.masters ∧
      out.restorations+s.history.count event0=1 := by
  induction hx with
  | @gap s p hi ht =>
    have hp := reachable_incumbent hs hi
    have hv : spec.f p=1/4 := by rw [hp]; norm_num [spec,objective,pt,scalar]
    cases reachable_phase hs with
    | zero hh hl =>
      have inv := reachable_invariant analytic seed_valid hs
      obtain ⟨e,he,_,_⟩ := inv.provenance p hi
      simp [hh] at he
    | one hn hl => rw [hv,hl] at ht; norm_num at ht
    | two hn h0 h1 hc hl => rw [hv,hl] at ht; norm_num at ht
    | three hn h0 h1 hc hl => simp [hn,hc]
  | @empty s ho he =>
    obtain ⟨z,hz⟩ := master_attained s.history (reachable_invariant analytic seed_valid hs).history.2
    have hz := hz.1
    rw [he] at hz
    exact False.elim hz
  | @step s ho q e he hy out tail ih =>
    have hr : Reachable spec seed 0 (advance s q e) := .next hs (.step ho q e he hy)
    have hh := ih hr
    have er := event_restorations he
    simp only [advance,List.length_append,List.length_singleton,List.count_append,countStep,er] at hh ⊢
    omega

/-- Both tied initial minima and every later legal choice produce the same
three actual master/fixed calls and one individual-sum restoration call. -/
theorem every_selector_three_rounds :
    Nonempty (Selector spec seed 0) ∧ ∀choose : Selector spec seed 0, ∃out,
      runFuel spec seed 0 choose 3 (initialState spec seed) .initial=some out ∧
      ReturnCertificate spec 0 out.result ∧ out.masters=3 ∧ out.fixed=3 ∧
      out.restorations=1 := by
  refine ⟨selectors_inhabited 0,?_⟩
  intro choose
  obtain ⟨out,hr,hc,_,_,_⟩ := finite_return_with_counts analytic seed_valid (by norm_num : (0:ℝ)≤0) choose
  have hex := runFuel_execution spec seed 0 choose _ _ .initial hr
  have hh := execution_counts_exact hex .initial
  simp only [initialState,List.length_nil,List.count_nil,Nat.add_zero] at hh
  refine ⟨out,?_,hc,hh.1,?_,hh.2.2⟩
  · simpa only [box_card] using hr
  · omega

#print axioms every_selector_three_rounds
#print axioms reachable_phase
end Chapter03.OAExec.Controls.I
