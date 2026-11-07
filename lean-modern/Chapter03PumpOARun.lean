module

public import Chapter03PumpOAModel

@[expose] public section

/-! The actual source-ordered fuel recursion. A master decision consumes fuel;
a selected nonempty master always incurs its fixed solve before the next gap
inspection. Exhaustion remains visible here and is ruled out by the separate
finite-progress theorem, not assumed by the selector. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}
attribute [local instance] Classical.propDecidable

def emptyResult {d : OAExec.Data n m l r} (s : OAExec.State d) : OAExec.Result n m :=
  match s.incumbent with
  | none => .infeasible
  | some u => .solution u

def runFuel (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) (epsilon : ℝ)
    (choose : Selector d delta P epsilon) :
    ℕ → (s : OAExec.State d) → Reachable d delta P epsilon s → Option (OAExec.Output n m)
  | fuel, s, hs =>
    if ho : OAExec.loopOpen d epsilon s then
      match fuel with
      | 0 => none
      | k+1 => match choose s hs ho with
        | .empty _ => some ⟨emptyResult s,1,0,0⟩
        | .next q e hv hy =>
          (runFuel d delta P epsilon choose k (advance s q e)
            (.next hs (.step ho q e hv hy))).map (OAExec.countStep e)
    else some ⟨.solution (OAExec.closedPoint ho),0,0,0⟩

theorem runFuel_closed (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (epsilon : ℝ) (choose : Selector d delta P epsilon) (fuel : ℕ)
    (s : OAExec.State d) (hs : Reachable d delta P epsilon s)
    (ho : ¬ OAExec.loopOpen d epsilon s) {u : Point n m}
    (hu : s.incumbent = some u) :
    runFuel d delta P epsilon choose fuel s hs = some ⟨.solution u,0,0,0⟩ := by
  rw [runFuel, dif_neg ho]
  have he : OAExec.closedPoint ho = u :=
    Option.some.inj ((OAExec.closedPoint_spec ho).1.symm.trans hu)
  rw [he]

theorem runFuel_empty (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (epsilon : ℝ) (choose : Selector d delta P epsilon) (fuel : ℕ)
    (s : OAExec.State d) (hs : Reachable d delta P epsilon s)
    (ho : OAExec.loopOpen d epsilon s) (he : master d delta P s.history = ∅)
    (hc : choose s hs ho = .empty he) :
    runFuel d delta P epsilon choose (fuel+1) s hs = some ⟨emptyResult s,1,0,0⟩ := by
  rw [runFuel, dif_pos ho, hc]

theorem runFuel_next (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (epsilon : ℝ) (choose : Selector d delta P epsilon) (fuel : ℕ)
    (s : OAExec.State d) (hs : Reachable d delta P epsilon s)
    (ho : OAExec.loopOpen d epsilon s) (q : MasterChoice d delta P s)
    (e : OAExec.Event d) (hv : OAExec.EventValid d e)
    (hy : q.point.1.2 = intCast e.target)
    (hc : choose s hs ho = .next q e hv hy) :
    runFuel d delta P epsilon choose (fuel+1) s hs =
      (runFuel d delta P epsilon choose fuel (advance s q e)
        (.next hs (.step ho q e hv hy))).map (OAExec.countStep e) := by
  rw [runFuel, dif_pos ho, hc]

/-- A separate relation records precisely the actions counted by runFuel. -/
inductive Execution (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) (epsilon : ℝ) :
    OAExec.State d → OAExec.Output n m → Prop
  | gap {s : OAExec.State d} {p : Point n m} (incumbent : s.incumbent = some p)
      (test : d.f p - s.lower ≤ epsilon) :
      Execution d delta P epsilon s ⟨.solution p,0,0,0⟩
  | empty {s : OAExec.State d} (open_gap : OAExec.loopOpen d epsilon s)
      (empty : master d delta P s.history = ∅) :
      Execution d delta P epsilon s ⟨emptyResult s,1,0,0⟩
  | step {s : OAExec.State d} (open_gap : OAExec.loopOpen d epsilon s)
      (q : MasterChoice d delta P s) (e : OAExec.Event d) (valid : OAExec.EventValid d e)
      (same_y : q.point.1.2 = intCast e.target) {out : OAExec.Output n m}
      (tail : Execution d delta P epsilon (advance s q e) out) :
      Execution d delta P epsilon s (OAExec.countStep e out)

theorem runFuel_execution (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) (epsilon : ℝ)
    (choose : Selector d delta P epsilon) (fuel : ℕ) (s : OAExec.State d)
    (hs : Reachable d delta P epsilon s) {out : OAExec.Output n m}
    (hout : runFuel d delta P epsilon choose fuel s hs = some out) :
    Execution d delta P epsilon s out := by
  classical
  induction fuel generalizing s out with
  | zero =>
    rw [runFuel] at hout
    by_cases ho : OAExec.loopOpen d epsilon s
    · simp [ho] at hout
    · simp only [dif_neg ho,Option.some.injEq] at hout
      subst out
      exact .gap (OAExec.closedPoint_spec ho).1 (OAExec.closedPoint_spec ho).2
  | succ fuel ih =>
    rw [runFuel] at hout
    by_cases ho : OAExec.loopOpen d epsilon s
    · cases hc : choose s hs ho with
      | empty he =>
        simp only [dif_pos ho,hc,Option.some.injEq] at hout
        subst out
        exact .empty ho he
      | next q e hv hy =>
        simp only [dif_pos ho,hc] at hout
        obtain ⟨tail,ht,hout⟩ := Option.map_eq_some_iff.mp hout
        subst out
        exact .step ho q e hv hy (ih _ _ ht)
    · simp only [dif_neg ho,Option.some.injEq] at hout
      subst out
      exact .gap (OAExec.closedPoint_spec ho).1 (OAExec.closedPoint_spec ho).2

theorem execution_counts {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m} {epsilon : ℝ}
    {s : OAExec.State d} {out : OAExec.Output n m} (h : Execution d delta P epsilon s out) :
    out.fixed ≤ out.masters ∧ out.masters ≤ out.fixed+1 ∧
      out.restorations ≤ out.fixed := by
  induction h with
  | gap _ _ => simp
  | empty _ _ => simp
  | step _ _ e _ _ _ ih =>
    have he : OAExec.eventRestorations e ≤ 1 := by
      unfold OAExec.eventRestorations
      split <;> omega
    simp only [OAExec.countStep]
    omega

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.runFuel_execution
