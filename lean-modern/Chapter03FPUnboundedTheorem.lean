module

public import Chapter03FPUnboundedHandoff
public import Chapter03FPUnboundedFiniteCounts
public import Chapter03FPUnboundedSourceAdapters

@[expose] public section

/-! Qualified normalized relative-cutoff pump with success exclusions disabled.
Bounded feasible relaxation is explicit; no finite hard integer bounds, compact
master, supplied optimizer, or progress oracle is assumed. Exact classical
choices, not numerical subsolvers, are modeled. Source index/infinity/incumbent
normalization and the additional empty-projection outcome remain disclosed. -/
noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnbounded
variable {n m l : ℕ}

theorem qualified_source_pump (d : Data n m l) (h : Analytic d) (hd : 0 < d.delta)
    (cap : Option ℕ) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d cap) ∧
    (∀ initial : Initialization d, ∀ choose : Selector d cap,
      ∃ out, procedure d h hd initial choose = some out ∧ ReturnClaims d cap initial out ∧
        CountBounds (historyBound d h hd) cap out) ∧
    (∀ seed, IsMinimizer d.relaxation d.f seed → ∀ k q s,
      Chain d cap (initialState seed) k q s →
      SafeHandoff d s ∧
        (∀ p ∈ d.original, belowIncumbent d s p → (p,d.f p) ∈ handoff d s) ∧
        (∀ u, s.incumbent = some u → (u,d.f u) ∈ handoff d s)) := by
  refine ⟨initialization_nonempty d h,selector_nonempty d h cap,
    procedure_returns d h hd cap,?_⟩
  intro seed hseed k q s hc
  exact ⟨reachable_safe_handoff d h hseed hc,reachable_handoff_embedding d h hseed.1 hc⟩

theorem qualified_capped_pump (d : Data n m l) (h : Analytic d) (b : ℕ) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d (some b)) ∧
    ∀ initial : Initialization d, ∀ choose : Selector d (some b),
      ∃ out, cappedProcedure d b initial choose = some out ∧
        ReturnClaims d (some b) initial out ∧ CountBounds b (some b) out :=
  ⟨initialization_nonempty d h,selector_nonempty d h _,cappedProcedure_returns d h b⟩

theorem article_source_pump (a : ArticleData n m l) (h : Analytic a.toData)
    (hd : 0 < a.delta) (cap : Option ℕ) :
    Nonempty (Initialization a.toData) ∧ Nonempty (Selector a.toData cap) ∧
    ∀ initial : Initialization a.toData, ∀ choose : Selector a.toData cap,
      ∃ out, procedure a.toData h hd initial choose = some out ∧
        ReturnClaims a.toData cap initial out ∧ CountBounds (historyBound a.toData h hd) cap out :=
  ⟨initialization_nonempty _ h,selector_nonempty _ h cap,procedure_returns _ h hd cap⟩

/-- Exact all-soft source rows equal the derived hard-base master at every
reachable prefix, because the permanent initial affine tangents imply that base.
The base is not introduced solely from boundedness of the feasible relaxation. -/
theorem reachable_soft_master_identity (d : Data n m l) (h : Analytic d)
    (A : AffineBaseRows d) {cap : Option ℕ} {seed : Point n m}
    (hseed : IsMinimizer d.relaxation d.f seed) {k q : ℕ} {s : State n m}
    (hc : Chain d cap (initialState seed) k q s) :
    softMaster d s = master d s ∧ softHandoff d s = handoff d s := by
  have hs := chain_invariant d h (initial_invariant d hseed.1) hc
  have hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed :=
    fun j => h.derivative_g j s.seed (relaxation_subset_base d hs.seed)
  constructor
  · ext z
    exact A.master_iff s hd z
  · ext z
    exact A.handoff_iff s hd z

end Chapter03.FPUnbounded

#print axioms Chapter03.FPUnbounded.qualified_source_pump
#print axioms Chapter03.FPUnbounded.qualified_capped_pump
#print axioms Chapter03.FPUnbounded.article_source_pump
#print axioms Chapter03.FPUnbounded.reachable_soft_master_identity
#print axioms Chapter03.FPUnbounded.finite_hard_target_counts
#print axioms Chapter03.FPUnbounded.zero_postsuccess_run_none
#print axioms Chapter03.FPUnbounded.terminal_gap
