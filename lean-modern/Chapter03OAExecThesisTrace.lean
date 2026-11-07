module

public import Chapter03OAExecInitialization

@[expose] public section

/-! Trace-level comparison only. The thesis asks a nonempty master for an
optimum; the article also permits unbounded replies. After the explicitly
listed incumbent/output/index/empty-return completions, thesis executions are
exactly the executions here whose nonempty master replies are attained.
This module asserts no totality of that restriction under thesis A1–A3. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

def thesisAdvance {d : Data n m l r} (s : State d) (z : Point n m × ℝ)
    (e : Event d) : State d :=
  ⟨s.history ++ [e], nextIncumbent s e, z.2⟩

inductive ThesisExecution (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    State d → Output n m → Prop
  | gap {s : State d} {p : Point n m} (incumbent : s.incumbent = some p)
      (test : d.f p - s.lower ≤ epsilon) :
      ThesisExecution d seed epsilon s ⟨.solution p,0,0,0⟩
  | empty {s : State d} (open_gap : loopOpen d epsilon s)
      (empty : master d seed s.history = ∅) :
      ThesisExecution d seed epsilon s ⟨.infeasible,1,0,0⟩
  | step {s : State d} (open_gap : loopOpen d epsilon s)
      (z : Point n m × ℝ) (minimum : IsMinimizer (master d seed s.history) Prod.snd z)
      (e : Event d) (valid : EventValid d e) (same_y : z.1.2 = intCast e.target)
      {out : Output n m} (tail : ThesisExecution d seed epsilon (thesisAdvance s z e) out) :
      ThesisExecution d seed epsilon s (countStep e out)

/-- Explicit subrelation; it records the attained branch at every transition
without trying to inspect a proof of the coarser Execution proposition. -/
inductive AttainedExecution (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    State d → Output n m → Prop
  | gap {s : State d} {p : Point n m} (incumbent : s.incumbent = some p)
      (test : d.f p - s.lower ≤ epsilon) :
      AttainedExecution d seed epsilon s ⟨.solution p,0,0,0⟩
  | empty {s : State d} (open_gap : loopOpen d epsilon s)
      (empty : master d seed s.history = ∅) :
      AttainedExecution d seed epsilon s ⟨.infeasible,1,0,0⟩
  | step {s : State d} (open_gap : loopOpen d epsilon s)
      (q : MasterChoice d seed s) (attained : q.attained = true)
      (e : Event d) (valid : EventValid d e)
      (same_y : q.point.1.2 = intCast e.target) {out : Output n m}
      (tail : AttainedExecution d seed epsilon (advance s q e) out) :
      AttainedExecution d seed epsilon s (countStep e out)

theorem thesis_execution_to_attained {d : Data n m l r} {seed : Point n m}
    {epsilon : ℝ} {s : State d} {out : Output n m}
    (h : ThesisExecution d seed epsilon s out) :
    AttainedExecution d seed epsilon s out := by
  induction h with
  | gap hu hg => exact .gap hu hg
  | empty ho he => exact .empty ho he
  | step ho z hz e he hy _ ih =>
    let q : MasterChoice _ _ _ := ⟨z,true,hz⟩
    exact .step ho q rfl e he hy ih

theorem attained_execution_to_thesis {d : Data n m l r} {seed : Point n m}
    {epsilon : ℝ} {s : State d} {out : Output n m}
    (h : AttainedExecution d seed epsilon s out) :
    ThesisExecution d seed epsilon s out := by
  induction h with
  | gap hu hg => exact .gap hu hg
  | empty ho he => exact .empty ho he
  | @step s ho q ht e he hy out tail ih =>
    have hm : IsMinimizer (master d seed s.history) Prod.snd q.point := by
      simpa only [ht,↓reduceIte] using q.valid
    have heq : advance s q e = thesisAdvance s q.point e := by
      simp only [advance,thesisAdvance,MasterChoice.nextLower,ht,↓reduceIte]
    rw [heq] at ih
    exact .step ho q.point hm e he hy ih

theorem attained_execution_to_extended {d : Data n m l r} {seed : Point n m}
    {epsilon : ℝ} {s : State d} {out : Output n m}
    (h : AttainedExecution d seed epsilon s out) : Execution d seed epsilon s out := by
  induction h with
  | gap hu hg => exact .gap hu hg
  | empty ho he => exact .empty ho he
  | step ho q _ e he hy _ ih => exact .step ho q e he hy ih

theorem thesis_execution_iff {d : Data n m l r} {seed : Point n m} {epsilon : ℝ}
    {s : State d} {out : Output n m} :
    ThesisExecution d seed epsilon s out ↔ AttainedExecution d seed epsilon s out :=
  ⟨thesis_execution_to_attained,attained_execution_to_thesis⟩

end Chapter03.OAExec

#print axioms Chapter03.OAExec.thesis_execution_iff
