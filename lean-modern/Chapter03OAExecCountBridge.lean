module

public import Chapter03OAExecRestoration
public import Chapter03OAExecRun

@[expose] public section

noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

theorem restorationCount_initial (d : Data n m l r) (seed : Point n m) :
    restorationCount (initialState d seed) = 0 := rfl

theorem restorationCount_advance_eq_event {d : Data n m l r}
    {seed : Point n m} (s : State d) (q : MasterChoice d seed s) (e : Event d) :
    restorationCount (advance s q e) = restorationCount s + eventRestorations e := by
  rw [restorationCount_advance]
  cases h : e.restoration <;> simp [eventRestorations,h]

end Chapter03.OAExec

#print axioms Chapter03.OAExec.restorationCount_advance_eq_event
