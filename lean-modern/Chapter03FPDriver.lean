module

public import Chapter03FPInvariant
public import Mathlib.Data.Finset.Card

@[expose] public section

noncomputable section
open Chapter02
namespace Chapter03.FP
variable {n m l r : ℕ}

def seen (s : State n m) : Finset (IntVector m) := by
  classical
  exact (s.history.map Event.target).toFinset

theorem seen_card (d : Data n m l r) {s : State n m} (hs : Invariant d s) :
    (seen s).card = s.history.length := by
  classical
  simpa [seen] using List.toFinset_card_of_nodup hs.nodup

theorem seen_subset_box (d : Data n m l r) {s : State n m} (hs : Invariant d s) :
    seen s ⊆ d.box := by
  classical
  intro y hy
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
  exact (hs.valid e he).target_box

theorem history_length_bound (d : Data n m l r) {s : State n m} (hs : Invariant d s) :
    s.history.length ≤ d.box.card := by
  rw [← seen_card d hs]
  exact Finset.card_le_card (seen_subset_box d hs)

theorem fresh_master_card_bound (d : Data n m l r) {s : State n m}
    (hs : Invariant d s) {z : Point n m × ℝ} (hz : z ∈ master d s) :
    s.history.length + 1 ≤ d.box.card := by
  classical
  obtain ⟨y,hy,hye⟩ := master_box_integer d s hz
  have hf : y ∉ seen s := by simpa [seen] using master_target_fresh d hs hz hye
  have hsub : insert y (seen s) ⊆ d.box := Finset.insert_subset hy (seen_subset_box d hs)
  have hc := Finset.card_le_card hsub
  simpa [Finset.card_insert_of_notMem hf,seen_card d hs] using hc

inductive Chain (d : Data n m l r) (cap : Option ℕ) :
    State n m → ℕ → ℕ → State n m → Prop
  | nil (s) : Chain d cap s 0 0 s
  | cons {s t : State n m} {e : Event n m} {k q : ℕ}
      (step : Continue d cap s e) (tail : Chain d cap (append s e) k q t) :
      Chain d cap s (k+1) (q+polishCount e) t

theorem chain_invariant (d : Data n m l r) (h : Analytic d) {cap : Option ℕ}
    {s t : State n m} {k q : ℕ} (hs : Invariant d s) (hc : Chain d cap s k q t) :
    Invariant d t := by
  revert hs
  induction hc with
  | nil _ => exact id
  | cons hstep _ ih =>
    intro hs
    obtain ⟨z,hz,_,hr⟩ := hstep
    exact ih (append_invariant d h hs hz.1 hr)

theorem polishCount_le_one (e : Event n m) : polishCount e ≤ 1 := by
  unfold polishCount
  split <;> omega

theorem chain_counts (d : Data n m l r) {cap : Option ℕ}
    {s t : State n m} {k q : ℕ} (hc : Chain d cap s k q t) :
    s.history.length+k=t.history.length ∧ q≤k := by
  induction hc with
  | nil _ => simp
  | @cons s t e k q _ _ ih =>
    have hp := polishCount_le_one e
    simp only [append,List.length_append,List.length_singleton] at ih
    constructor <;> omega

theorem chain_cap (d : Data n m l r) {cap : Option ℕ}
    {s t : State n m} {k q b : ℕ} (hb : cap=some b) (hs : s.history.length≤b)
    (hc : Chain d cap s k q t) : t.history.length≤b := by
  revert hs
  induction hc with
  | nil _ => exact id
  | @cons s t e k q hstep _ ih =>
    intro _
    obtain ⟨_,_,hc,_⟩ := hstep
    have hl := hc b hb
    apply ih
    simp only [append,List.length_append,List.length_singleton]
    omega

theorem run_execution (d : Data n m l r) {cap : Option ℕ} (choose : Selector d cap)
    (fuel : ℕ) (s : State n m) {out : LoopOutput n m}
    (hr : run d choose fuel s=some out) :
    Chain d cap s out.bodies out.polishes out.state ∧ Stop d cap out.state out.reason ∧
      out.projections=out.bodies+terminalProjectionCount out.reason ∧
      out.masters=out.bodies+1 ∧ out.bodies<fuel := by
  induction fuel generalizing s out with
  | zero => simp [run] at hr
  | succ fuel ih =>
    cases hc : choose s with
    | stop reason hs =>
      simp only [run,hc,Option.some.injEq] at hr
      subst out
      exact ⟨.nil s,hs,by simp [terminalOutput],by rfl,by simp [terminalOutput]⟩
    | next e he =>
      simp only [run,hc] at hr
      cases ht : run d choose fuel (append s e) with
      | none => simp [ht] at hr
      | some tail =>
        rw [ht] at hr
        have hout : tail.bump e = out := Option.some.inj hr
        subst out
        obtain ⟨hchain,hstop,hP,hM,hK⟩ := ih (append s e) ht
        refine ⟨.cons he hchain,hstop,?_,?_,?_⟩
        · simp only [LoopOutput.bump]; omega
        · simp only [LoopOutput.bump]; omega
        · simp only [LoopOutput.bump]; omega

theorem run_sufficient_fuel (d : Data n m l r) (h : Analytic d) {cap : Option ℕ}
    (choose : Selector d cap) (fuel : ℕ) (s : State n m) (hs : Invariant d s)
    (hf : d.box.card<s.history.length+fuel) : ∃ out, run d choose fuel s=some out := by
  induction fuel generalizing s with
  | zero => have hb := history_length_bound d hs; omega
  | succ fuel ih =>
    cases hc : choose s with
    | stop reason ht => exact ⟨terminalOutput s reason,by simp [run,hc]⟩
    | next e he =>
      obtain ⟨z,hz,_,hr⟩ := he
      have hs' := append_invariant d h hs hz.1 hr
      have hf' : d.box.card<(append s e).history.length+fuel := by
        simp only [append,List.length_append,List.length_singleton]
        omega
      obtain ⟨out,hout⟩ := ih (append s e) hs' hf'
      exact ⟨out.bump e,by simp [run,hc,hout]⟩

theorem stop_projection_bound (d : Data n m l r) {cap : Option ℕ}
    {s : State n m} (hs : Invariant d s) {reason : StopReason m}
    (ht : Stop d cap s reason) :
    s.history.length+terminalProjectionCount reason≤d.box.card := by
  cases ht with
  | emptyMaster _ => simpa [terminalProjectionCount] using history_length_bound d hs
  | emptyProjection hm _ _ _ => simpa [terminalProjectionCount] using fresh_master_card_bound d hs hm.1
  | handoff _ _ _ => simpa [terminalProjectionCount] using history_length_bound d hs

theorem stop_cap_projection_bound (d : Data n m l r) {cap : Option ℕ}
    {s : State n m} {b : ℕ} (hb : cap=some b) (hs : s.history.length≤b)
    {reason : StopReason m} (ht : Stop d cap s reason) :
    s.history.length+terminalProjectionCount reason≤b := by
  cases ht with
  | emptyMaster _ => simpa [terminalProjectionCount] using hs
  | emptyProjection _ _ hc _ =>
    have hl := hc b hb
    simp only [terminalProjectionCount]
    omega
  | handoff _ _ _ => simpa [terminalProjectionCount] using hs

theorem stop_without_cap (d : Data n m l r) {s : State n m} {reason : StopReason m}
    (ht : Stop d none s reason) : reason≠.handoff := by
  cases ht with
  | emptyMaster _ => simp
  | emptyProjection _ _ _ _ => simp
  | handoff _ hc _ => cases hc

/-- Exact actual branch counts from a fractional initialization. In particular
an empty final projection consumes a fresh target and one projection inspection. -/
structure LoopBounds (d : Data n m l r) (cap : Option ℕ) (out : LoopOutput n m) : Prop where
  bodies_eq_history : out.bodies=out.state.history.length
  master_exact : out.masters=out.bodies+1
  projection_exact : out.projections=out.bodies+terminalProjectionCount out.reason
  bodies_bound : out.bodies≤d.box.card
  projections_bound : out.projections≤d.box.card
  masters_bound : out.masters≤d.box.card+1
  polishes_bound : out.polishes≤out.bodies
  cap_bodies : ∀ b, cap=some b → out.bodies≤b
  cap_projections : ∀ b, cap=some b → out.projections≤b
  no_cap_terminal : cap=none → out.reason≠.handoff

theorem run_initial_bounds (d : Data n m l r) (h : Analytic d) {cap : Option ℕ}
    (choose : Selector d cap) {p : Point n m} (hp : p∈d.relaxation)
    {fuel : ℕ} {out : LoopOutput n m} (hr : run d choose fuel (initialState p)=some out) :
    Invariant d out.state ∧ LoopBounds d cap out := by
  obtain ⟨hc,ht,hP,hM,_⟩ := run_execution d choose fuel (initialState p) hr
  have hs := chain_invariant d h (initial_invariant d hp) hc
  have counts := chain_counts d hc
  have hk : out.bodies=out.state.history.length := by simpa [initialState] using counts.1
  have hb := history_length_bound d hs
  have hpb := stop_projection_bound d hs ht
  refine ⟨hs,⟨hk,hM,hP,by omega,by omega,by omega,counts.2,?_,?_,?_⟩⟩
  · intro b hcap
    have hcB := chain_cap d hcap (by simp [initialState]) hc
    omega
  · intro b hcap
    have hcB := chain_cap d hcap (by simp [initialState]) hc
    have hstopB := stop_cap_projection_bound d hcap hcB ht
    omega
  · intro hcap
    subst cap
    exact stop_without_cap d ht

end Chapter03.FP
