module

public import Chapter03PumpOAPolyhedron

@[expose] public section

/-! Exact choice existence for every combined-master request. The immutable
pump prefix may be arbitrary finite data; soundness uses its actual execution
separately. No optimizer, progress, return or pump-correctness oracle is assumed.
The accepted hard-domain qualifications and uniform fixed-fiber LICQ remain. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

/-- Bounded-master attainment and exact fixed/restoration choices for the same
master and target used by the continuation. No restoration LICQ is needed. -/
theorem local_available {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta : ℝ) (P : FP.State n m)
    (hs : OAExec.SeedValid d P.seed) (epsilon : ℝ) :
    LocalAvailability d delta P epsilon := by
  classical
  refine ⟨?_,?_⟩
  · intro state _ _ hne hbb
    exact master_attained_of_bddBelow d delta P state.history hne hbb
  · intro state _ _ q
    obtain ⟨y,hy,hsame⟩ := OAExec.master_integer q.mem.2
    by_cases hne : (fiber d.model (intCast y)).Nonempty
    · obtain ⟨x,hm⟩ := OAExec.fixed_minimum_exists d h.analytic h.domain_base
        h.bounded_relaxation y hy hne
      exact ⟨⟨y,hy,x,none⟩,h.every_exact_fixed_event y hy x hm,hsame⟩
    · obtain ⟨x,s,hm⟩ := OAExec.requested_restoration_minimum_exists d h.analytic
        h.domain_base h.bounded_relaxation P.seed hs state.history q.mem.2 y hy hsame
      exact ⟨⟨y,hy,x,some s⟩,h.every_exact_restoration_event y hy x s hne hm,hsame⟩

/-- The exact local cases construct a selector; freshness and finite return
remain separate theorems about every selector. -/
theorem selector_inhabited {d : OAExec.Data n m l r} {delta : ℝ}
    {P : FP.State n m} {epsilon : ℝ}
    (availability : LocalAvailability d delta P epsilon) :
    Nonempty (Selector d delta P epsilon) := by
  classical
  have hd : ∀ s, Reachable d delta P epsilon s → OAExec.loopOpen d epsilon s →
      Nonempty (Decision d delta P s) := by
    intro s hs ho
    by_cases he : (master d delta P s.history).Nonempty
    · have hq : Nonempty (MasterChoice d delta P s) := by
        by_cases hb : BddBelow (Prod.snd '' master d delta P s.history)
        · obtain ⟨z,hz⟩ := availability.master_attainment s hs ho he hb
          exact ⟨⟨z,true,hz⟩⟩
        · obtain ⟨z,hz⟩ := he
          exact ⟨⟨z,false,hz,hb⟩⟩
      obtain ⟨q⟩ := hq
      obtain ⟨e,hv,hy⟩ := availability.fixed_or_restoration s hs ho q
      exact ⟨.next q e hv hy⟩
    · exact ⟨.empty (Set.not_nonempty_iff_eq_empty.mp he)⟩
  exact ⟨fun s hs ho => Classical.choice (hd s hs ho)⟩

/-- A total family over finite prefixes with valid fractional initializer
seeds. Prefix correctness is derived from the actual pump in composition. -/
def Selectors (d : OAExec.Data n m l r) (delta epsilon : ℝ) :=
  ∀ P : FP.State n m, OAExec.SeedValid d P.seed → Selector d delta P epsilon

theorem selectors_nonempty {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) (delta epsilon : ℝ) :
    Nonempty (Selectors d delta epsilon) :=
  ⟨fun P hs => Classical.choice (selector_inhabited (local_available h delta P hs epsilon))⟩

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.local_available
#print axioms Chapter03.PumpOA.selector_inhabited
#print axioms Chapter03.PumpOA.selectors_nonempty
