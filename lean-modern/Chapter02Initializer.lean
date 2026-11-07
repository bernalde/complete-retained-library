module

public import Chapter02Restoration

@[expose] public section

/-! Relative-domain free-height initialization and consumers of exact evidence.
The signed maximum is used only for finite nonempty rows. Its attainment is
derived from compactness and relative continuity on the original domain, not
from compactness of the unbounded height lift. Feasible-height and positive
lower-bound consumers support arbitrary row types, including empty types.
These statements do not produce numerical witnesses, certify solver statuses,
assert ambient interior, or establish termination of an ECP/ESH procedure. -/

noncomputable section
namespace Chapter02

/-- A finite nonempty signed maximum is continuous on the same domain as its
rows. No ambient continuous extension is required. -/
theorem initializer_maximum_continuousOn {E J : Type*} [TopologicalSpace E]
    [Fintype J] [Nonempty J] {S : Set E} {g : J → E → ℝ}
    (hg : ∀ j, ContinuousOn (g j) S) : ContinuousOn (eshMaximum g) S := by
  exact ContinuousOn.finset_sup'_apply Finset.univ_nonempty (fun j _ => hg j)

/-- Actual attainment on the compact original domain, transported to the
free-height formulation at its exact signed-maximum height. -/
theorem initializer_minimum_attained {E J : Type*} [TopologicalSpace E]
    [Fintype J] [Nonempty J] {S : Set E} {g : J → E → ℝ}
    (hS : IsCompact S) (hne : S.Nonempty) (hg : ∀ j, ContinuousOn (g j) S) :
    ∃ p, IsMinimizer S (eshMaximum g) p ∧
      IsMinimizer (RestorationPairs S g) Prod.snd (p, eshMaximum g p) := by
  obtain ⟨p, hp⟩ := compact_feasible_attainment hS hne
    (initializer_maximum_continuousOn hg)
  exact ⟨p, hp, (restorationPairs_minimizer_iff S g _).mpr ⟨hp, rfl⟩⟩

/-- A feasible height supplies row signs without an optimization premise.
Strict rows are not a claim of ambient topological interior. -/
theorem initializer_feasible_height {E J : Type*} {S : Set E} {g : J → E → ℝ}
    {q : E × ℝ} (hq : q ∈ RestorationPairs S g) :
    q.1 ∈ S ∧ (q.2 < 0 → ∀ j, g j q.1 < 0) ∧
      (q.2 ≤ 0 → ∀ j, g j q.1 ≤ 0) := by
  exact ⟨hq.1, (fun h j => (hq.2 j).trans_lt h),
    (fun h j => (hq.2 j).trans h)⟩

/-- A positive universal bound on feasible pair heights excludes nonlinear
feasibility on the declared domain. A feasible height alone is not this bound. -/
theorem initializer_positive_bound_empty {E J : Type*} {S : Set E}
    {g : J → E → ℝ} {rho : ℝ}
    (hb : IsLowerBound (RestorationPairs S g) Prod.snd rho) (hrho : 0 < rho) :
    {p | p ∈ S ∧ ∀ j, g j p ≤ 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hzero : rho ≤ 0 := hb (p, 0) ⟨hp.1, hp.2⟩
  exact (not_le_of_gt hrho) hzero

end Chapter02

#print axioms Chapter02.initializer_maximum_continuousOn
#print axioms Chapter02.initializer_minimum_attained
#print axioms Chapter02.initializer_feasible_height
#print axioms Chapter02.initializer_positive_bound_empty
