module

public import Chapter03OAExecRun
public import Chapter03OAExecProgress

@[expose] public section

/-! Conditional soundness and finite return for every exact certificate-bearing
selector. Progress and local availability are separate: the former is derived
from the actual master/event geometry, not included in the selector's type. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

theorem empty_master_no_incumbent {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {s : State d} (hi : Invariant d seed s)
    (he : master d seed s.history = ∅) : s.incumbent = none := by
  cases h : s.incumbent with
  | none => rfl
  | some u =>
    exact False.elim (empty_master_original_empty a hi.history he ⟨u,hi.feasible u h⟩)

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
  | step _ q _ he _ _ ih => exact ih (advance_invariant a hi q he)

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
  | step ho q e hv hy _ ih =>
    have hb := ih (.next hr (.step ho q e hv hy))
    simp only [countStep,advance,List.length_append,List.length_singleton] at *
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
      | next q e hv hy =>
        have hb : d.box.card+1 ≤ fuel+(advance s q e).history.length := by
          simp only [advance,List.length_append,List.length_singleton]
          omega
        obtain ⟨out,hout⟩ := ih (advance s q e) (.next hr (.step ho q e hv hy)) hb
        exact ⟨countStep e out,by rw [runFuel]; simp only [dif_pos ho,hc,hout]; rfl⟩
    · exact ⟨_,by rw [runFuel]; simp only [dif_neg ho]; rfl⟩

/-- No original optimum is assumed. The actual recursion returns after at most
N+1 master decisions, even when a last repeated fiber incurs one final NLP. -/
theorem finite_return {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (choose : Selector d seed epsilon) :
    ∃ out, runFuel d seed epsilon choose (d.box.card+1) (initialState d seed)
      .initial = some out ∧ ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 := by
  obtain ⟨out,hout⟩ := runFuel_total a hs heps choose (d.box.card+1)
    (initialState d seed) .initial (by simp [initialState])
  have hex := runFuel_execution d seed epsilon choose _ _ .initial hout
  have hc := execution_master_count a hs heps .initial hex
  have hf := (execution_counts hex).1
  refine ⟨out,hout,execution_sound a (initial_invariant hs) hex,?_,?_⟩
  · simpa [initialState] using hc
  · simpa [initialState] using hf.trans (by simpa [initialState] using hc)

theorem zero_certificate_exact {d : Data n m l r} {p : Point n m}
    (h : ReturnCertificate d 0 (.solution p)) : IsMinimizer d.original d.f p := by
  exact ⟨h.1,fun z hz => by simpa using h.2 z hz⟩

end Chapter03.OAExec

#print axioms Chapter03.OAExec.finite_return
#print axioms Chapter03.OAExec.empty_master_no_incumbent
