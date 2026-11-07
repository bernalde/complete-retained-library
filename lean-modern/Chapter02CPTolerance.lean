module

public import Chapter02CPDriver

@[expose] public section

/-! Three different endpoints: the literal weak residual test, an unshifted
half-tolerance run for strict residuals, and ESH Remark1's shifted model.
Constraint tolerance alone proves neither exact feasibility nor an objective
gap. The shifted model preserves the original affine base and objective. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

def cpShiftModel (d : ModelData n m l r) (eta : ℝ) : ModelData n m l r :=
  { d with g := eshShiftRows d.g eta }

theorem cp_shift_base (d : ModelData n m l r) (eta : ℝ) :
    cpBase (cpShiftModel d eta) = cpBase d := rfl

theorem cp_shift_objective (d : ModelData n m l r) (eta : ℝ) :
    (cpShiftModel d eta).objective = d.objective := rfl

theorem cp_shift_feasible_subset (d : ModelData n m l r) {eta : ℝ}
    (heta : 0 ≤ eta) :
    d.feasibleOn Set.univ ⊆ (cpShiftModel d eta).feasibleOn Set.univ := by
  intro q hq
  exact ⟨⟨⟨hq.1.1.1,esh_shift_preserves_feasible hq.1.1.2 heta⟩,hq.1.2⟩,hq.2⟩

theorem cp_shift_interior (d : ModelData n m l r) {eta : ℝ}
    (heta : 0 < eta) {a : Point n m} (ha : a ∈ d.linearRegion)
    (hrows : ∀ j, d.g j a ≤ 0) : CPInterior (cpShiftModel d eta) (.esh a) :=
  ⟨ha,esh_shift_strict_start hrows heta⟩

theorem cp_shift_convex (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j)) (eta : ℝ) :
    ∀ j, ConvexOn ℝ Set.univ ((cpShiftModel d eta).g j) :=
  esh_shift_convex hconv eta

theorem cp_shift_contDiff (d : ModelData n m l r)
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (eta : ℝ) :
    ∀ j, ContDiff ℝ 1 ((cpShiftModel d eta).g j) :=
  esh_shift_contDiff hC1 eta

theorem cp_shift_certificate_transfer (d : ModelData n m l r) {eps : ℝ}
    (heps : 0 ≤ eps) {out : CPResult n m}
    (h : CPReturnCertificate (cpShiftModel d (eps / 2)) (eps / 2) out) :
    CPReturnCertificate d eps out := by
  cases out with
  | infeasible =>
    exact Set.eq_empty_of_subset_empty
      (h ▸ cp_shift_feasible_subset d (div_nonneg heps (by norm_num)))
  | point q =>
    exact ⟨h.1,esh_shift_half_tolerance_transfer h.2.1,
      fun z hz => h.2.2 z (cp_shift_feasible_subset d (div_nonneg heps (by norm_num)) hz)⟩

def CPStrictReturnCertificate (d : ModelData n m l r) (eps : ℝ) : CPResult n m → Prop
  | .infeasible => d.feasibleOn Set.univ = ∅
  | .point q => q ∈ cpBase d ∧ (∀ j, d.g j q < eps) ∧
      IsLowerBound (d.feasibleOn Set.univ) d.objective (d.objective q)

theorem cp_half_certificate_strict (d : ModelData n m l r) {eps : ℝ}
    (heps : 0 < eps) {out : CPResult n m}
    (h : CPReturnCertificate d (eps / 2) out) : CPStrictReturnCertificate d eps out := by
  cases out with
  | infeasible => exact h
  | point q => exact ⟨h.1,fun j => (h.2.1 j).trans_lt (half_lt_self heps),h.2.2⟩

theorem cp_certificate_not_infeasible (d : ModelData n m l r) {eps : ℝ}
    (hne : (d.feasibleOn Set.univ).Nonempty)
    (h : CPReturnCertificate d eps .infeasible) : False := by
  exact Set.nonempty_iff_ne_empty.mp hne h

theorem cp_certificate_point_of_feasible (d : ModelData n m l r) {eps : ℝ}
    (hne : (d.feasibleOn Set.univ).Nonempty) {out : CPResult n m}
    (h : CPReturnCertificate d eps out) :
    ∃ q, out = .point q ∧ q ∈ cpBase d ∧ CPFeasibleWithin d eps q ∧
      IsLowerBound (d.feasibleOn Set.univ) d.objective (d.objective q) := by
  cases out with
  | infeasible => exact (cp_certificate_not_infeasible d hne h).elim
  | point q => exact ⟨q,rfl,h⟩

/-- Run the unshifted source procedure at half the desired tolerance to get
strict residuals; this is a changed guard, not the literal weak-guard theorem. -/
theorem cp_half_every_selector_finite_return (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ (choose : CPSelector d mode (eps / 2)) (seed : List (CPBatch n m l)),
      ∃ T out, cpRun d mode (eps / 2) choose seed (N + 1) = .stopped T out ∧
        CPTrace d mode (eps / 2) seed T ∧ T.length ≤ N ∧
        CPStop d (eps / 2) (seed ++ T) out ∧ CPStrictReturnCertificate d eps out := by
  obtain ⟨N,hN⟩ := cp_every_selector_finite_return d mode hbase hconv hC1 ha (half_pos heps)
  refine ⟨N,?_⟩
  intro choose seed
  obtain ⟨T,out,hr,hT,hlen,hs,hc⟩ := hN choose seed
  exact ⟨T,out,hr,hT,hlen,hs,cp_half_certificate_strict d heps hc⟩

/-- ESH Remark1: a nonstrict continuous start becomes strict for shifted
rows. The actual shifted procedure returns a weak original-eps certificate.
This theorem does not claim the continuous start is integer feasible. -/
theorem cp_shift_every_selector_finite_return (d : ModelData n m l r)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j))
    {a : Point n m} (ha : a ∈ d.linearRegion) (hrows : ∀ j, d.g j a ≤ 0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ (choose : CPSelector (cpShiftModel d (eps / 2)) (.esh a) (eps / 2))
      (seed : List (CPBatch n m l)),
      ∃ T out, cpRun (cpShiftModel d (eps / 2)) (.esh a) (eps / 2) choose seed (N + 1) =
        .stopped T out ∧ CPTrace (cpShiftModel d (eps / 2)) (.esh a) (eps / 2) seed T ∧
        T.length ≤ N ∧ CPStop (cpShiftModel d (eps / 2)) (eps / 2) (seed ++ T) out ∧
        CPReturnCertificate d eps out := by
  obtain ⟨N,hN⟩ := cp_every_selector_finite_return (cpShiftModel d (eps / 2)) (.esh a)
    hbase (cp_shift_convex d hconv _) (cp_shift_contDiff d hC1 _)
    (cp_shift_interior d (half_pos heps) ha hrows) (half_pos heps)
  refine ⟨N,?_⟩
  intro choose seed
  obtain ⟨T,out,hr,hT,hlen,hs,hc⟩ := hN choose seed
  exact ⟨T,out,hr,hT,hlen,hs,cp_shift_certificate_transfer d heps.le hc⟩

theorem cp_shift_stopped_run_exists (d : ModelData n m l r)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j))
    {a : Point n m} (ha : a ∈ d.linearRegion) (hrows : ∀ j, d.g j a ≤ 0)
    {eps : ℝ} (heps : 0 < eps) (seed : List (CPBatch n m l)) :
    ∃ (choose : CPSelector (cpShiftModel d (eps / 2)) (.esh a) (eps / 2))
      (k : ℕ) (T : List (CPBatch n m l)) (out : CPResult n m),
      cpRun (cpShiftModel d (eps / 2)) (.esh a) (eps / 2) choose seed k = .stopped T out ∧
      CPTrace (cpShiftModel d (eps / 2)) (.esh a) (eps / 2) seed T ∧
      CPStop (cpShiftModel d (eps / 2)) (eps / 2) (seed ++ T) out ∧
      CPReturnCertificate d eps out := by
  obtain ⟨choose,k,T,out,hr,hT,hs,hc⟩ := cp_stopped_run_exists (cpShiftModel d (eps / 2))
    (.esh a) hbase (cp_shift_convex d hconv _) (cp_shift_contDiff d hC1 _)
    (cp_shift_interior d (half_pos heps) ha hrows) (half_pos heps) seed
  exact ⟨choose,k,T,out,hr,hT,hs,cp_shift_certificate_transfer d heps.le hc⟩

#print axioms cp_shift_base
#print axioms cp_shift_objective
#print axioms cp_shift_feasible_subset
#print axioms cp_shift_interior
#print axioms cp_shift_convex
#print axioms cp_shift_contDiff
#print axioms cp_shift_certificate_transfer
#print axioms cp_half_certificate_strict
#print axioms cp_certificate_not_infeasible
#print axioms cp_certificate_point_of_feasible
#print axioms cp_half_every_selector_finite_return
#print axioms cp_shift_every_selector_finite_return
#print axioms cp_shift_stopped_run_exists
end Chapter02
