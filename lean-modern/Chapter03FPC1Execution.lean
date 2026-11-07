module

public import Chapter03FPC1Controls

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPControls

theorem procedure_fractional_eq {n m l r : ℕ} (d : Data n m l r) {cap : Option ℕ}
    (p : Point n m) (hp : IsMinimizer d.relaxation d.f p) (choose : Selector d cap)
    (hn : p ∉ d.original) : procedure d (.minimum p hp) choose =
      (run d choose (d.box.card+1) (initialState p)).map Outcome.loop := by
  simp only [procedure,hn,if_false]

theorem procedure_integral_eq {n m l r : ℕ} (d : Data n m l r) {cap : Option ℕ}
    (p : Point n m) (hp : IsMinimizer d.relaxation d.f p) (choose : Selector d cap)
    (hi : p ∈ d.original) : procedure d (.minimum p hp) choose = some (.initialOptimal p) := by
  simp only [procedure,hi,if_true]

theorem procedure_delta1 :
    procedure (c1 1) (.minimum seed (seed_minimum 1)) choose1 = some (.loop out1) := by
  rw [procedure_fractional_eq (c1 1) seed (seed_minimum 1) choose1
    (fractional_seed true 1 1 1 1 0)]
  rw [show (c1 1).box.card=2 from box_binary_card true 1 1 1 0]
  change (run (c1 1) choose1 (1+2) s0).map Outcome.loop = _
  rw [run_delta1]; rfl

theorem procedure_delta0 :
    procedure (c1 0) (.minimum seed (seed_minimum 0)) choose0 = some (.loop out0) := by
  rw [procedure_fractional_eq (c1 0) seed (seed_minimum 0) choose0
    (fractional_seed true 1 1 1 0 0)]
  rw [show (c1 0).box.card=2 from box_binary_card true 1 1 0 0]
  change (run (c1 0) choose0 (0+3) s0).map Outcome.loop = _
  rw [run_delta0]; rfl

end Chapter03.FPControls
