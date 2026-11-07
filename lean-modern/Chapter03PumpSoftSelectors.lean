module

public import Chapter03PumpSoftState
public import Chapter03PumpSoftAvailability

@[expose] public section

/-! Actual warm choices exist under data assumptions. Weights may depend on the
returned prefix, but are then fixed throughout its continuation. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy Chapter03.OASoftExecutionAvailability
namespace Chapter03.PumpSoft
variable {n m l r : ℕ} {d : OAExec.Data n m l r}

theorem local_available (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (delta : ℝ) (P : FP.State n m)
    (hs : OAExec.SeedValid d P.seed)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (epsilon : ℝ) :
    LocalAvailability d delta P W epsilon := by
  constructor
  · intro s _ _ he hb
    exact warm_master_attained_of_bddBelow d delta P s.history
      (weight d delta P W s.policy) he hb
  · intro s _ _ q
    exact PumpSoft.requested_generation_exists h hard ⟨P.seed,hs.1.1⟩ delta P s.history q.mem

def PrefixWeights (d : OAExec.Data n m l r) (delta : ℝ) :=
  ∀ P : FP.State n m, Occurrence (prefixFamily d delta P) → ℝ

def Selectors (d : OAExec.Data n m l r) (delta : ℝ)
    (V : PrefixWeights d delta) (epsilon : ℝ) :=
  ∀ P, OAExec.SeedValid d P.seed → FP.Invariant (PumpOA.asFPDelta d delta) P →
    Selector d delta P (V P) epsilon

theorem selectors_nonempty (h : OAExec.AvailabilityAssumptions d)
    (hard : HardAffineEntailment d) (delta : ℝ) (V : PrefixWeights d delta) (epsilon : ℝ) :
    Nonempty (Selectors d delta V epsilon) :=
  ⟨fun P hs _ => Classical.choice (selector_inhabited (local_available h hard delta P hs (V P) epsilon))⟩

end Chapter03.PumpSoft
