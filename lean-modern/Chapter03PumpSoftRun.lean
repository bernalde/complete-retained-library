module

public import Chapter03PumpSoftState
public import Chapter03PumpOARun

@[expose] public section

/-! Concrete source-ordered recursion over the actual warm state. Both master
outcomes and the delayed gap test are represented; empty residual preserves a
saved incumbent. Counts describe this recursion rather than an abstract oracle. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.PumpSoft
variable {n m l r : ℕ}
attribute [local instance] Classical.propDecidable

def runFuel (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (epsilon : ℝ)
    (choose : Selector d delta P W epsilon) :
    ℕ → (s : State d delta P W) → Reachable d delta P W epsilon s → Option (Output n m)
  | fuel, s, hs =>
    if ho : loopOpen d epsilon s then
      match fuel with
      | 0 => none
      | k+1 => match choose s hs ho with
        | .empty _ => some ⟨PumpOA.emptyResult s.core,1,0,0⟩
        | .next q e G hy =>
          (runFuel d delta P W epsilon choose k (advance s q e G)
            (.next hs (.step ho q e G hy))).map (countStep e)
    else some ⟨.solution (closedPoint ho),0,0,0⟩

/-- A separate relation records precisely the actions counted by runFuel. -/
inductive Execution (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (epsilon : ℝ) :
    State d delta P W → Output n m → Prop
  | gap {s : State d delta P W} {p : Point n m} (incumbent : s.incumbent = some p)
      (test : d.f p - s.lower ≤ epsilon) :
      Execution d delta P W epsilon s ⟨.solution p,0,0,0⟩
  | empty {s : State d delta P W} (open_gap : loopOpen d epsilon s)
      (empty : warmMaster d delta P s.history = ∅) :
      Execution d delta P W epsilon s ⟨PumpOA.emptyResult s.core,1,0,0⟩
  | step {s : State d delta P W} (open_gap : loopOpen d epsilon s)
      (q : MasterChoice d delta P W s) (e : Event d) (G : Generation d e)
      (same_y : q.point.1.2 = intCast e.target) {out : Output n m}
      (tail : Execution d delta P W epsilon (advance s q e G) out) :
      Execution d delta P W epsilon s (countStep e out)

theorem runFuel_execution (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (epsilon : ℝ)
    (choose : Selector d delta P W epsilon) (fuel : ℕ) (s : State d delta P W)
    (hs : Reachable d delta P W epsilon s) {out : Output n m}
    (hout : runFuel d delta P W epsilon choose fuel s hs = some out) :
    Execution d delta P W epsilon s out := by
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

theorem execution_counts {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
    {W : Occurrence (prefixFamily d delta P) → ℝ} {epsilon : ℝ}
    {s : State d delta P W} {out : Output n m} (h : Execution d delta P W epsilon s out) :
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

end Chapter03.PumpSoft
