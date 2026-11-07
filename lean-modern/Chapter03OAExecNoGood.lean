module

public import Chapter03OAExecHistory
public import Chapter03FPFormulation

@[expose] public section

noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

theorem noGoods_l1_iff {d : Data n m l r} (H : List (Event d))
    (p : Point n m) (hp : integral p) :
    noGoods H p ↔ ∀ e ∈ H, e.restoration ≠ none →
      1 ≤ FPFormulation.l1Distance p.2 (intCast e.target) := by
  obtain ⟨y,hy⟩ := hp
  have hcast : Function.Injective (@intCast m) := by
    intro v w hv
    funext i
    exact Int.cast_injective (congrFun hv i)
  constructor
  · intro h e he hn
    rw [hy]
    apply (FPFormulation.integer_l1_nogood_iff y e.target).mpr
    intro heq
    exact h e he hn (hy.trans (congrArg intCast heq))
  · intro h e he hn heq
    have hh := h e he hn
    rw [hy] at hh
    have hne := (FPFormulation.integer_l1_nogood_iff y e.target).mp hh
    exact hne (hcast (hy.symm.trans heq))

end Chapter03.OAExec

#print axioms Chapter03.OAExec.noGoods_l1_iff
