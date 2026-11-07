module

public import Chapter03OASoftExecutionProgress

@[expose] public section

/-! Source-ordered soft recursion and finite return. Output counts are actual
loop master/fixed/restoration calls, excluding the single relaxation initializer.
Availability remains separate from progress; neither is a selector field. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.OASoftExec
variable {n m l r : ℕ}
attribute [local instance] Classical.propDecidable

def runFuel (d : Data n m l r) (seed : Point n m) (epsilon : ℝ)
    (choose : Selector d seed epsilon) :
    ℕ → (s : State d) → Reachable d seed epsilon s → Option (Output n m)
  | fuel, s, hs =>
    if ho : loopOpen d epsilon s then
      match fuel with
      | 0 => none
      | k+1 => match choose s hs ho with
        | .empty _ => some ⟨.infeasible,1,0,0⟩
        | .next q e G hy =>
          (runFuel d seed epsilon choose k (advance s q e G)
            (.next hs (.step ho q e G hy))).map (countStep e)
    else some ⟨.solution (closedPoint ho),0,0,0⟩

/-- A separate relation records precisely the actions counted by runFuel. -/
inductive Execution (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    State d → Output n m → Prop
  | gap {s : State d} {p : Point n m} (incumbent : s.incumbent = some p)
      (test : d.f p - s.lower ≤ epsilon) :
      Execution d seed epsilon s ⟨.solution p,0,0,0⟩
  | empty {s : State d} (open_gap : loopOpen d epsilon s)
      (empty : historyMaster d seed s.history = ∅) :
      Execution d seed epsilon s ⟨.infeasible,1,0,0⟩
  | step {s : State d} (open_gap : loopOpen d epsilon s)
      (q : MasterChoice d seed s) (e : Event d) (G : Generation d e)
      (same_y : q.point.1.2 = intCast e.target) {out : Output n m}
      (tail : Execution d seed epsilon (advance s q e G) out) :
      Execution d seed epsilon s (countStep e out)

theorem runFuel_execution (d : Data n m l r) (seed : Point n m) (epsilon : ℝ)
    (choose : Selector d seed epsilon) (fuel : ℕ) (s : State d)
    (hs : Reachable d seed epsilon s) {out : Output n m}
    (hout : runFuel d seed epsilon choose fuel s hs = some out) :
    Execution d seed epsilon s out := by
  classical
  induction fuel generalizing s out with
  | zero =>
    rw [runFuel] at hout
    by_cases ho : loopOpen d epsilon s
    · simp [ho] at hout
    · simp only [dif_neg ho,Option.some.injEq] at hout
      subst out
      exact .gap (closedPoint_spec ho).1 (closedPoint_spec ho).2
  | succ fuel ih =>
    rw [runFuel] at hout
    by_cases ho : loopOpen d epsilon s
    · cases hc : choose s hs ho with
      | empty he =>
        simp only [dif_pos ho,hc,Option.some.injEq] at hout
        subst out
        exact .empty ho he
      | next q e G hy =>
        simp only [dif_pos ho,hc] at hout
        obtain ⟨tail,ht,hout⟩ := Option.map_eq_some_iff.mp hout
        subst out
        exact .step ho q e G hy (ih _ _ ht)
    · simp only [dif_neg ho,Option.some.injEq] at hout
      subst out
      exact .gap (closedPoint_spec ho).1 (closedPoint_spec ho).2

theorem execution_counts {d : Data n m l r} {seed : Point n m} {epsilon : ℝ}
    {s : State d} {out : Output n m} (h : Execution d seed epsilon s out) :
    out.fixed ≤ out.masters ∧ out.masters ≤ out.fixed+1 ∧
      out.restorations ≤ out.fixed := by
  induction h with
  | gap _ _ => simp
  | empty _ _ => simp
  | step _ _ e _ _ _ ih =>
    have he : eventRestorations e ≤ 1 := by
      unfold eventRestorations
      split <;> omega
    simp only [countStep]
    omega

theorem execution_sound {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {epsilon : ℝ} {s : State d} {out : Output n m}
    (hi : Invariant d seed s) (h : Execution d seed epsilon s out) :
    ReturnCertificate d epsilon out.result := by
  induction h with
  | gap hu hg =>
    refine ⟨hi.feasible _ hu,?_⟩
    intro z hz
    have hl := hi.lower z hz
    linarith
  | empty _ he => exact empty_master_original_empty a hi.history he
  | step _ q _ G _ _ ih => exact ih (advance_invariant a hi q G)

theorem execution_master_count {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {s : State d} {out : Output n m} (hr : Reachable d seed epsilon s)
    (h : Execution d seed epsilon s out) :
    out.masters + s.history.length ≤ d.box.card+1 := by
  induction h with
  | gap _ _ => simpa using reachable_length_le_succ a hs heps hr
  | empty ho _ =>
    have hb := reachable_open_length_le a hs heps hr ho
    simp only
    omega
  | step ho q e G hy _ ih =>
    have hb := ih (.next hr (.step ho q e G hy))
    simp only [countStep,advance,State.history,State.core,List.length_append,List.length_singleton] at *
    omega

theorem runFuel_total {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d seed epsilon) (fuel : ℕ) (s : State d)
    (hr : Reachable d seed epsilon s) (budget : d.box.card+1 ≤ fuel+s.history.length) :
    ∃ out, runFuel d seed epsilon choose fuel s hr = some out := by
  classical
  induction fuel generalizing s with
  | zero =>
    by_cases ho : loopOpen d epsilon s
    · have hb := reachable_open_length_le a hs heps hr ho
      omega
    · exact ⟨_,by rw [runFuel]; simp only [dif_neg ho]; rfl⟩
  | succ fuel ih =>
    by_cases ho : loopOpen d epsilon s
    · cases hc : choose s hr ho with
      | empty he =>
        exact ⟨_,by rw [runFuel]; simp only [dif_pos ho,hc]; rfl⟩
      | next q e G hy =>
        have hb : d.box.card+1 ≤ fuel+(advance s q e G).history.length := by
          change d.box.card+1 ≤ fuel+(s.history ++ [e]).length
          simp only [List.length_append,List.length_singleton]
          omega
        obtain ⟨out,hout⟩ := ih (advance s q e G) (.next hr (.step ho q e G hy)) hb
        exact ⟨countStep e out,by rw [runFuel]; simp only [dif_pos ho,hc,hout]; rfl⟩
    · exact ⟨_,by rw [runFuel]; simp only [dif_neg ho]; rfl⟩

/-- No original optimum is assumed. The actual recursion returns after at most
N+1 master decisions, even when a last repeated fiber incurs one final NLP. -/
theorem finite_return {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d seed epsilon) (P0 : Policy d []) :
    ∃ out, runFuel d seed epsilon choose (d.box.card+1) (initialState d seed P0)
      (.initial P0) = some out ∧ ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 := by
  obtain ⟨out,hout⟩ := runFuel_total a hs heps choose (d.box.card+1)
    (initialState d seed P0) (.initial P0) (by simp [initialState,State.history,State.core,OAExec.initialState])
  have hex := runFuel_execution d seed epsilon choose _ _ (.initial P0) hout
  have hc := execution_master_count a hs heps (.initial P0) hex
  have hf := (execution_counts hex).1
  refine ⟨out,hout,execution_sound a (initial_invariant hs P0) hex,?_,?_⟩
  · simpa [initialState,State.history,State.core,OAExec.initialState] using hc
  · simpa [initialState,State.history,State.core,OAExec.initialState] using hf.trans (by simpa [initialState,State.history,State.core,OAExec.initialState] using hc)

theorem restorationCount_advance_eq_event {d : Data n m l r}
    {seed : Point n m} (s : State d) (q : MasterChoice d seed s)
    (e : Event d) (G : Generation d e) :
    OAExec.restorationCount (advance s q e G).core =
      OAExec.restorationCount s.core + eventRestorations e := by
  simp only [OAExec.restorationCount,advance,State.core,State.history,restorationEvents_append,List.length_append]
  cases h : e.restoration <;> simp [eventRestorations,h]

theorem execution_restoration_count {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ}
    {s : State d} {out : Output n m} (hr : Reachable d seed epsilon s)
    (h : Execution d seed epsilon s out) :
    out.restorations + OAExec.restorationCount s.core ≤ d.box.card := by
  induction h with
  | gap _ _ => simpa using reachable_restoration_length_le a hs hr
  | empty _ _ => simpa using reachable_restoration_length_le a hs hr
  | step ho q e G hy _ ih =>
    have hb := ih (.next hr (.step ho q e G hy))
    rw [restorationCount_advance_eq_event] at hb
    simp only [countStep]
    omega

/-- Main fractional-loop endpoint: every admitted exact selector, actual
source order, finite return, original-objective guarantee and all solve counts. -/
theorem finite_return_with_counts {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d seed epsilon) (P0 : Policy d []) :
    ∃ out, runFuel d seed epsilon choose (d.box.card+1) (initialState d seed P0)
      (.initial P0) = some out ∧ ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card := by
  obtain ⟨out,hout,hcert,hm,hf⟩ := finite_return a hs heps choose P0
  have hex := runFuel_execution d seed epsilon choose _ _ (.initial P0) hout
  have hc := execution_restoration_count a hs (.initial P0) hex
  exact ⟨out,hout,hcert,hm,hf,by simpa [initialState,State.core,OAExec.restorationCount,restorationEvents,OAExec.initialState] using hc⟩

/-- Local availability inhabits the quantified selectors; finite return itself
does not assume a whole execution or a final result exists. -/
theorem locally_available_finite_return {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (available : LocalAvailability d seed epsilon) (P0 : Policy d []) :
    Nonempty (Selector d seed epsilon) ∧
    ∀ choose : Selector d seed epsilon, ∃ out,
      runFuel d seed epsilon choose (d.box.card+1) (initialState d seed P0)
        (.initial P0) = some out ∧ ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card :=
  ⟨selector_inhabited available,fun choose => finite_return_with_counts a hs heps choose P0⟩

def InitializedSelectors (d : Data n m l r) (epsilon : ℝ) :=
  ∀ seed, SeedValid d seed → Selector d seed epsilon

theorem initialized_selectors_inhabited {d : Data n m l r} {epsilon : ℝ}
    (h : ∀ seed, SeedValid d seed → LocalAvailability d seed epsilon) :
    Nonempty (InitializedSelectors d epsilon) :=
  ⟨fun seed hs => Classical.choice (selector_inhabited (h seed hs))⟩

def execute (d : Data n m l r) (epsilon : ℝ) (choose : InitializedSelectors d epsilon) (P0 : Policy d []) :
    Initialization d → Option (Output n m)
  | .empty _ => some ⟨.infeasible,0,0,0⟩
  | .minimum seed h hd =>
    if hi : integral seed then some ⟨.solution seed,0,0,0⟩
    else runFuel d seed epsilon (choose seed ⟨h,hd,hi⟩) (d.box.card+1)
      (initialState d seed P0) (.initial P0)

/-- Conditional qualified soft-policy endpoint, with the Algorithm1 order and
intended minimum incumbent. Exactly one initializer reply is inspected; the
returned point is explicit on the integral branch. This is not a blanket claim
about the printed pseudocode or software. -/
theorem initialized_finite_return {d : Data n m l r} (a : Analytic d)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) (choose : InitializedSelectors d epsilon)
    (P0 : Policy d []) (initial : Initialization d) :
    ∃ out, execute d epsilon choose P0 initial = some out ∧
      ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card := by
  cases initial with
  | empty he =>
    refine ⟨⟨.infeasible,0,0,0⟩,rfl,?_,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
    rintro ⟨p,hp⟩
    have hr := original_subset_relaxation d hp
    rw [he] at hr
    exact hr
  | minimum seed hm hd =>
    by_cases hi : integral seed
    · refine ⟨⟨.solution seed,0,0,0⟩,by simp only [execute,dif_pos hi],?_,
        Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
      have hs := integral_initializer_minimum hm hi
      refine ⟨hs.1,?_⟩
      intro p hp
      exact (hs.2 p hp).trans (le_add_of_nonneg_right heps)
    · obtain ⟨out,hout,hcert,hmasters,hfixed,hrest⟩ :=
        finite_return_with_counts a ⟨hm,hd,hi⟩ heps (choose seed ⟨hm,hd,hi⟩) P0
      exact ⟨out,by simpa only [execute,dif_neg hi] using hout,
        hcert,hmasters,hfixed,hrest⟩


end Chapter03.OASoftExec
