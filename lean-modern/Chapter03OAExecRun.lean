module

public import Chapter03OAExecState

@[expose] public section

/-! The actual source-ordered fuel recursion. A master decision consumes fuel;
a selected nonempty master always incurs its fixed solve before the next gap
inspection. Exhaustion remains visible here and is ruled out by the separate
finite-progress theorem, not assumed by the selector. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}
attribute [local instance] Classical.propDecidable

inductive Result (n m : ℕ)
  | infeasible
  | solution (point : Point n m)

def ReturnCertificate (d : Data n m l r) (epsilon : ℝ) : Result n m → Prop
  | .infeasible => ¬ d.original.Nonempty
  | .solution p => p ∈ d.original ∧ ∀ z ∈ d.original, d.f p ≤ d.f z + epsilon

structure Output (n m : ℕ) where
  result : Result n m
  masters : ℕ
  fixed : ℕ
  restorations : ℕ

def eventRestorations {d : Data n m l r} (e : Event d) : ℕ :=
  if e.restoration = none then 0 else 1

def countStep {d : Data n m l r} (e : Event d) (out : Output n m) : Output n m :=
  ⟨out.result, out.masters + 1, out.fixed + 1, out.restorations + eventRestorations e⟩

theorem closed_gap_witness {d : Data n m l r} {epsilon : ℝ} {s : State d}
    (h : ¬ loopOpen d epsilon s) :
    ∃ p, s.incumbent = some p ∧ d.f p - s.lower ≤ epsilon := by
  classical
  by_contra hn
  apply h
  intro p hp
  by_contra hlt
  exact hn ⟨p,hp,le_of_not_gt hlt⟩

def closedPoint {d : Data n m l r} {epsilon : ℝ} {s : State d}
    (h : ¬ loopOpen d epsilon s) : Point n m :=
  Classical.choose (closed_gap_witness h)

theorem closedPoint_spec {d : Data n m l r} {epsilon : ℝ} {s : State d}
    (h : ¬ loopOpen d epsilon s) :
    s.incumbent = some (closedPoint h) ∧ d.f (closedPoint h) - s.lower ≤ epsilon :=
  Classical.choose_spec (closed_gap_witness h)

def runFuel (d : Data n m l r) (seed : Point n m) (epsilon : ℝ)
    (choose : Selector d seed epsilon) :
    ℕ → (s : State d) → Reachable d seed epsilon s → Option (Output n m)
  | fuel, s, hs =>
    if ho : loopOpen d epsilon s then
      match fuel with
      | 0 => none
      | k+1 => match choose s hs ho with
        | .empty _ => some ⟨.infeasible,1,0,0⟩
        | .next q e hv hy =>
          (runFuel d seed epsilon choose k (advance s q e)
            (.next hs (.step ho q e hv hy))).map (countStep e)
    else some ⟨.solution (closedPoint ho),0,0,0⟩

/-- A separate relation records precisely the actions counted by runFuel. -/
inductive Execution (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    State d → Output n m → Prop
  | gap {s : State d} {p : Point n m} (incumbent : s.incumbent = some p)
      (test : d.f p - s.lower ≤ epsilon) :
      Execution d seed epsilon s ⟨.solution p,0,0,0⟩
  | empty {s : State d} (open_gap : loopOpen d epsilon s)
      (empty : master d seed s.history = ∅) :
      Execution d seed epsilon s ⟨.infeasible,1,0,0⟩
  | step {s : State d} (open_gap : loopOpen d epsilon s)
      (q : MasterChoice d seed s) (e : Event d) (valid : EventValid d e)
      (same_y : q.point.1.2 = intCast e.target) {out : Output n m}
      (tail : Execution d seed epsilon (advance s q e) out) :
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
      | next q e hv hy =>
        simp only [dif_pos ho,hc] at hout
        obtain ⟨tail,ht,hout⟩ := Option.map_eq_some_iff.mp hout
        subst out
        exact .step ho q e hv hy (ih _ _ ht)
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

end Chapter03.OAExec

#print axioms Chapter03.OAExec.runFuel_execution
