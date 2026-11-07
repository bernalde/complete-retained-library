module

public import Chapter03FPUnboundedBasic
public import Chapter03FPProcedureModel

@[expose] public section

noncomputable section
open Chapter02
open Chapter03.FP
namespace Chapter03.FPUnbounded
variable {n m l : ℕ}

inductive Stop (d : Data n m l) (cap : Option ℕ) (s : State n m) : StopReason m → Prop
  | emptyMaster (empty : ¬(master d s).Nonempty) : Stop d cap s .emptyMaster
  | emptyProjection {z : Point n m × ℝ} {y : IntVector m}
      (optimal : IsMinimizer (master d s) (masterCost s) z)
      (same_integer : z.1.2 = intCast y) (before_cap : BeforeCap cap s)
      (empty : ¬(d.region (d.level s.incumbent)).Nonempty) :
      Stop d cap s (.emptyProjection y)
  | handoff {z : Point n m × ℝ} {b : ℕ}
      (optimal : IsMinimizer (master d s) (masterCost s) z)
      (has_cap : cap = some b) (reached : b ≤ s.history.length) : Stop d cap s .handoff

def Continue (d : Data n m l) (cap : Option ℕ) (s : State n m)
    (e : Event n m) : Prop :=
  ∃ z : Point n m × ℝ, IsMinimizer (master d s) (masterCost s) z ∧
    BeforeCap cap s ∧ EventReply d s z e

inductive Decision (d : Data n m l) (cap : Option ℕ) (s : State n m)
  | stop (reason : StopReason m) (valid : Stop d cap s reason)
  | next (event : Event n m) (valid : Continue d cap s event)

def Selector (d : Data n m l) (cap : Option ℕ) := ∀ s, Decision d cap s

/-- `none` means fuel exhaustion only. Each successor inspects one actual
master. Projection and polishing counters track their actual decision branches. -/
def run (d : Data n m l) {cap : Option ℕ} (choose : Selector d cap) :
    ℕ → State n m → Option (LoopOutput n m)
  | 0, _ => none
  | fuel+1, s =>
    match choose s with
    | .stop reason _ => some (terminalOutput s reason)
    | .next e _ => (run d choose fuel (append s e)).map (LoopOutput.bump e)

/-- A fuel-parametrized exact interpreter. Derived sufficient fuel is supplied by
later theorems; no unconditional finite-return claim at delta zero. -/
def procedureWithFuel (d : Data n m l) {cap : Option ℕ} (initial : Initialization d)
    (choose : Selector d cap) (fuel : ℕ) : Option (Outcome n m) := by
  classical
  exact match initial with
  | .empty _ => some .initialInfeasible
  | .minimum p _ =>
    if p ∈ d.original then some (.initialOptimal p)
    else (run d choose fuel (initialState p)).map Outcome.loop

theorem decision_nonempty (d : Data n m l) (h : Analytic d)
    (cap : Option ℕ) (s : State n m) : Nonempty (Decision d cap s) := by
  classical
  obtain ⟨mc⟩ := masterChoice_nonempty d s
  cases mc with
  | empty he => exact ⟨.stop .emptyMaster (.emptyMaster he)⟩
  | minimum z hz =>
    by_cases hb : BeforeCap cap s
    · obtain ⟨y,hy⟩ := master_integer d s hz.1
      obtain ⟨pc⟩ := projectionChoice_nonempty d h s y
      cases pc with
      | empty he => exact ⟨.stop (.emptyProjection y) (.emptyProjection hz hy hb he)⟩
      | minimum p hp =>
        by_cases hzero : distance y p = 0
        · obtain ⟨pol,hpol⟩ := fiber_attained d h y ⟨p,projection_zero_fiber d _ y hp hzero⟩
          obtain ⟨u,hu⟩ := best_exists d s.incumbent pol
          let e : Event n m := ⟨y,p,d.level s.incumbent,some (pol,u)⟩
          exact ⟨.next e ⟨z,hz,hb,hy,rfl,hp,hzero,hpol,hu⟩⟩
        · let e : Event n m := ⟨y,p,d.level s.incumbent,none⟩
          exact ⟨.next e ⟨z,hz,hb,hy,rfl,hp,hzero⟩⟩
    · have hex : ∃ b, cap = some b ∧ b ≤ s.history.length := by
        cases hc : cap with
        | none => exact False.elim (hb (by simp [BeforeCap,hc]))
        | some b =>
          rw [hc] at hb
          exact ⟨b,rfl,le_of_not_gt (fun ht => hb (by simpa [BeforeCap] using ht))⟩
      obtain ⟨b,hb,hle⟩ := hex
      exact ⟨.stop .handoff (.handoff hz hb hle)⟩

theorem selector_nonempty (d : Data n m l) (h : Analytic d) (cap : Option ℕ) :
    Nonempty (Selector d cap) :=
  ⟨fun s => Classical.choice (decision_nonempty d h cap s)⟩

end Chapter03.FPUnbounded
