module

public import Chapter03FPSearchFinite
public import Chapter03FPUnboundedInitialControls

@[expose] public section

/-! Actual empty and integral initialization, including zero integer dimension.
Static analytic inputs are reused; no improving-pump execution is substituted. -/
noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch
variable {n m l : ℕ}

def Data.fromUnbounded (d : FPUnbounded.Data n m l) : Data n m l :=
  ⟨d.base,d.f,d.g,d.Df,d.Dg⟩

theorem fromUnbounded_relaxation (d : FPUnbounded.Data n m l) :
    (Data.fromUnbounded d).relaxation=d.relaxation := rfl

theorem fromUnbounded_analytic (d : FPUnbounded.Data n m l) (h : FPUnbounded.Analytic d) :
    Analytic (Data.fromUnbounded d) := by
  exact ⟨h.base_closed,h.base_convex,h.convex_f,h.convex_g,h.derivative_f,
    h.derivative_g,h.bounded_relaxation,le_rfl⟩

namespace InitialControls

def emptyData : Data 0 1 0 := Data.fromUnbounded FPUnboundedControls.Initial.emptyData
def integralData : Data 0 1 0 := Data.fromUnbounded FPUnboundedControls.Initial.integralData

theorem empty_analytic : Analytic emptyData :=
  fromUnbounded_analytic _ FPUnboundedControls.Initial.empty_analytic

theorem integral_analytic : Analytic integralData :=
  fromUnbounded_analytic _ FPUnboundedControls.Initial.integral_analytic

theorem empty_relaxation : emptyData.relaxation=∅ :=
  FPUnboundedControls.Initial.empty_relaxation

def emptyInitialization : Initialization emptyData :=
  .empty (by rw [empty_relaxation]; exact Set.not_nonempty_empty)

def emptySelector (mode : Mode) : Selector emptyData mode :=
  Classical.choice (selector_nonempty emptyData empty_analytic mode)

theorem empty_run (mode : Mode) (fuel : ℕ) :
    procedureWithFuel emptyData mode emptyInitialization (emptySelector mode) fuel =
      some .initialEmpty := rfl

theorem empty_target_bound (mode : Mode) : TargetBound emptyData mode ∅ := by
  intro s hs
  have h := hs.seed
  rw [empty_relaxation] at h
  exact False.elim h

theorem empty_enhanced_endpoint :
    Nonempty (Initialization emptyData) ∧ Nonempty (Selector emptyData .enhanced) ∧
      ∀ initial choose, ∃ out,
        procedureWithFuel emptyData .enhanced initial choose 1=some out ∧
          out.Correct emptyData ∧ out.Counts 0 := by
  simpa using qualified_enhanced_first_feasibility emptyData empty_analytic ∅
    (empty_target_bound .enhanced)

def integralInitialization : Initialization integralData :=
  .minimum (FPUnboundedControls.pt 0) FPUnboundedControls.Initial.integral_minimum

def integralSelector (mode : Mode) : Selector integralData mode :=
  Classical.choice (selector_nonempty integralData integral_analytic mode)

theorem initial_integral : Integral (FPUnboundedControls.pt 0) :=
  FPUnboundedControls.Initial.integral_original.2

theorem integral_run (mode : Mode) (fuel : ℕ) :
    procedureWithFuel integralData mode integralInitialization (integralSelector mode) fuel =
      some (.initialOptimal (FPUnboundedControls.pt 0)) := by
  simp only [procedureWithFuel,integralInitialization,initial_integral,if_true]

def zeroData : Data 0 0 0 where
  base := Set.univ
  f _ := 0
  g := Fin.elim0
  Df _ := 0
  Dg := Fin.elim0

theorem zero_relaxation : zeroData.relaxation={(0 : Point 0 0)} := by
  ext p
  have hp : p=0 := Subsingleton.elim _ _
  simp [Data.relaxation,zeroData,hp]

theorem zero_analytic : Analytic zeroData := by
  refine ⟨isClosed_univ,convex_univ,convexOn_const 0 convex_univ,?_,?_,?_,?_,le_rfl⟩
  · intro j; exact Fin.elim0 j
  · intro p hp; exact hasFDerivAt_const 0 p
  · intro j; exact Fin.elim0 j
  · change Bornology.IsBounded zeroData.relaxation
    rw [zero_relaxation]
    exact isCompact_singleton.isBounded

theorem zero_minimum : IsMinimizer zeroData.relaxation zeroData.f 0 := by
  refine ⟨by rw [zero_relaxation]; exact Set.mem_singleton _,fun _ _ => le_rfl⟩

theorem zero_integral : Integral (0 : Point 0 0) :=
  ⟨fun i => Fin.elim0 i,Subsingleton.elim _ _⟩

def zeroSelector (mode : Mode) : Selector zeroData mode :=
  Classical.choice (selector_nonempty zeroData zero_analytic mode)

theorem zero_run (mode : Mode) (fuel : ℕ) :
    procedureWithFuel zeroData mode (.minimum 0 zero_minimum) (zeroSelector mode) fuel =
      some (.initialOptimal 0) := by
  simp only [procedureWithFuel,zero_integral,if_true]

theorem initial_calls (p : Point n m) :
    (Outcome.initialOptimal p).initializerCalls=1 ∧
    (Outcome.initialOptimal p).masterCalls=0 ∧
    (Outcome.initialOptimal p).projectionCalls=0 := ⟨rfl,rfl,rfl⟩

end InitialControls
end Chapter03.FPSearch
