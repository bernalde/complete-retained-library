module

public import Chapter03FPUnboundedControlAnalytic

@[expose] public section

/-! Actual empty-relaxation and initially integral exact-optimum branches. -/
noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedControls.Initial

def emptyData : FPUnbounded.Data 0 1 0 where
  base := ∅
  f _ := 0
  g := Fin.elim0
  Df _ := 0
  Dg := Fin.elim0
  delta := 1

theorem empty_relaxation : emptyData.relaxation = ∅ := by
  ext p
  simp [FPUnbounded.Data.relaxation,emptyData]

theorem empty_analytic : FPUnbounded.Analytic emptyData := by
  refine ⟨isClosed_empty,convex_empty,convexOn_const 0 convex_empty,?_,?_,?_,?_,by norm_num [emptyData]⟩
  · intro j; exact Fin.elim0 j
  · intro p hp; exact hasFDerivAt_const 0 p
  · intro j; exact Fin.elim0 j
  · rw [empty_relaxation]; exact isCompact_empty.isBounded

def emptyChoose : FPUnbounded.Selector emptyData none :=
  Classical.choice (FPUnbounded.selector_nonempty emptyData empty_analytic none)

theorem empty_initial (fuel : ℕ) :
    FPUnbounded.procedureWithFuel emptyData
      (.empty (by rw [empty_relaxation]; exact Set.not_nonempty_empty)) emptyChoose fuel =
      some .initialInfeasible := rfl

def integralData : FPUnbounded.Data 0 1 0 where
  base := {pt 0}
  f p := (p.2 0)^2
  g := Fin.elim0
  Df p := (2*p.2 0) • yc 0
  Dg := Fin.elim0
  delta := 1

theorem integral_relaxation : integralData.relaxation = {pt 0} := by
  ext p
  simp [FPUnbounded.Data.relaxation,integralData]

theorem integral_analytic : FPUnbounded.Analytic integralData := by
  refine ⟨isClosed_singleton,convex_singleton _,?_,?_,?_,?_,?_,by norm_num [integralData]⟩
  · simpa [integralData] using square_convex (convex_singleton (pt 0)) (yc 0) 0
  · intro j; exact Fin.elim0 j
  · intro p hp
    simpa [integralData] using square_derivative (yc 0) 0 p
  · intro j; exact Fin.elim0 j
  · rw [integral_relaxation]; exact isCompact_singleton.isBounded

theorem integral_minimum : IsMinimizer integralData.relaxation integralData.f (pt 0) := by
  refine ⟨by rw [integral_relaxation]; exact Set.mem_singleton _,?_⟩
  intro p hp
  simpa [integralData] using sq_nonneg (p.2 0)

theorem integral_original : pt 0 ∈ integralData.original := by
  exact ⟨integral_minimum.1,iv 0,by funext j; norm_num [pt,intCast,iv]⟩

def integralChoose : FPUnbounded.Selector integralData none :=
  Classical.choice (FPUnbounded.selector_nonempty integralData integral_analytic none)

theorem integral_initial (fuel : ℕ) :
    FPUnbounded.procedureWithFuel integralData (.minimum (pt 0) integral_minimum)
      integralChoose fuel = some (.initialOptimal (pt 0)) := by
  simp only [FPUnbounded.procedureWithFuel,integral_original,if_true]

end Chapter03.FPUnboundedControls.Initial
