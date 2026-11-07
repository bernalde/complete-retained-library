module

public import Chapter03FP
public import Chapter03OAExistenceAvailability

@[expose] public section

/-! Author-stage qualified composition on the explicit hard domain. This is
not the literal all-soft thesis model or the article's soft-rMIP/DICOPT call.
The actual pump prefix remains immutable; only the new OA suffix is appended.
No original accepted proof is modified. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

def asFPDelta (d : OAExec.Data n m l r) (delta : ℝ) : FP.Data n m l r :=
  { OAExec.asFP d with delta := delta }

@[simp] theorem asFPDelta_original (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).original = d.original := rfl

@[simp] theorem asFPDelta_relaxation (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).relaxation = d.relaxation := rfl

@[simp] theorem asFPDelta_box (d : OAExec.Data n m l r) (delta : ℝ) :
    (asFPDelta d delta).box = d.box := rfl

theorem asFPDelta_analytic {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} (hd : 0 ≤ delta) :
    FP.Analytic (asFPDelta d delta) := by
  have ha := OAExec.asFP_analytic d h.analytic h.domain_base h.bounded_relaxation
  exact ⟨ha.convex_f,ha.convex_g,ha.derivative_f,ha.derivative_g,
    ha.bounded_relaxation,hd⟩

def master (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) : Set (Point n m × ℝ) :=
  FP.handoff (asFPDelta d delta) P ∩ OAExec.master d P.seed H

def initialState (d : OAExec.Data n m l r) (P : FP.State n m) : OAExec.State d :=
  ⟨[], P.incumbent, d.f P.seed⟩

def Improves (d : OAExec.Data n m l r) (s : OAExec.State d) (p : Point n m) : Prop :=
  ∀ u, s.incumbent = some u → d.f p < d.f u

structure MasterChoice (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (s : OAExec.State d) where
  point : Point n m × ℝ
  attained : Bool
  valid : if attained then IsMinimizer (master d delta P s.history) Prod.snd point
    else point ∈ master d delta P s.history ∧
      ¬ BddBelow (Prod.snd '' master d delta P s.history)

def MasterChoice.nextLower {d : OAExec.Data n m l r} {delta : ℝ}
    {P : FP.State n m} {s : OAExec.State d} (q : MasterChoice d delta P s) : ℝ :=
  if q.attained then q.point.2 else s.lower

theorem MasterChoice.mem {d : OAExec.Data n m l r} {delta : ℝ}
    {P : FP.State n m} {s : OAExec.State d} (q : MasterChoice d delta P s) :
    q.point ∈ master d delta P s.history := by
  have hv := q.valid
  cases h : q.attained <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hv
  · exact hv.1
  · exact hv.1

def advance {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
    (s : OAExec.State d) (q : MasterChoice d delta P s) (e : OAExec.Event d) :
    OAExec.State d :=
  ⟨s.history ++ [e], OAExec.nextIncumbent s e, q.nextLower⟩

inductive RawStep (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (epsilon : ℝ) : OAExec.State d → OAExec.State d → Prop
  | step {s : OAExec.State d} (open_gap : OAExec.loopOpen d epsilon s)
      (q : MasterChoice d delta P s) (e : OAExec.Event d)
      (valid : OAExec.EventValid d e) (same_y : q.point.1.2 = intCast e.target) :
      RawStep d delta P epsilon s (advance s q e)

inductive Reachable (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (epsilon : ℝ) : OAExec.State d → Prop
  | initial : Reachable d delta P epsilon (initialState d P)
  | next {s t : OAExec.State d} (before : Reachable d delta P epsilon s)
      (step : RawStep d delta P epsilon s t) : Reachable d delta P epsilon t

inductive Decision (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (s : OAExec.State d)
  | empty (valid : master d delta P s.history = ∅)
  | next (q : MasterChoice d delta P s) (event : OAExec.Event d)
      (valid : OAExec.EventValid d event) (same_y : q.point.1.2 = intCast event.target)

structure LocalAvailability (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (epsilon : ℝ) : Prop where
  master_attainment : ∀ s, Reachable d delta P epsilon s → OAExec.loopOpen d epsilon s →
    (master d delta P s.history).Nonempty →
    BddBelow (Prod.snd '' master d delta P s.history) →
    ∃ z, IsMinimizer (master d delta P s.history) Prod.snd z
  fixed_or_restoration : ∀ s, Reachable d delta P epsilon s → OAExec.loopOpen d epsilon s →
    ∀ q : MasterChoice d delta P s, ∃ e : OAExec.Event d,
      OAExec.EventValid d e ∧ q.point.1.2 = intCast e.target

def Selector (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) (epsilon : ℝ) :=
  ∀ s, Reachable d delta P epsilon s → OAExec.loopOpen d epsilon s → Decision d delta P s

structure Invariant (d : OAExec.Data n m l r) (P : FP.State n m) (s : OAExec.State d) :
    Prop where
  history : OAExec.ValidHistory d P.seed s.history
  feasible : ∀ u, s.incumbent = some u → u ∈ d.original
  provenance : ∀ u, s.incumbent = some u → P.incumbent = some u ∨
    ∃ e ∈ s.history, e.restoration = none ∧ e.anchor = u
  dominates : ∀ e ∈ s.history, e.restoration = none →
    ∃ u, s.incumbent = some u ∧ d.f u ≤ d.f e.anchor
  pump_dominates : ∀ u, P.incumbent = some u →
    ∃ v, s.incumbent = some v ∧ d.f v ≤ d.f u
  lower : ∀ p ∈ d.original, Improves d s p → s.lower ≤ d.f p

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.asFPDelta_analytic
#print axioms Chapter03.PumpOA.MasterChoice.mem
