module

public import Chapter02CPDriver

@[expose] public section

/-! Actual infinite executions of the retained-tangent ECP/ESH procedure.
An execution stores literal append equations and actual exact-master steps.
All analytic progress and limiting properties are derived, not run fields.
-/
noncomputable section
open scoped Topology
open Filter
namespace Chapter02
variable {n m l r : ℕ}

structure CPExecution (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (seed : List (CPBatch n m l)) where
  history : ℕ → List (CPBatch n m l)
  batch : ℕ → CPBatch n m l
  initial : history 0 = seed
  append : ∀ k, history (k + 1) = history k ++ [batch k]
  step : ∀ k, CPStep d mode eps (history k) (batch k)

def CPExecution.trial {d : ModelData n m l r} {mode : CPMode n m} {eps : ℝ}
    {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed) (k : ℕ) : Point n m :=
  (run.batch k).trial

theorem cp_execution_history_length {d : ModelData n m l r} {mode : CPMode n m}
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed) (k : ℕ) :
    (run.history k).length = seed.length + k := by
  induction k with
  | zero => simp [run.initial]
  | succ k ih => simp [run.append, ih, Nat.add_assoc]

theorem cp_execution_history_nested {d : ModelData n m l r} {mode : CPMode n m}
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed)
    {i k : ℕ} (hik : i ≤ k) : run.history i ⊆ run.history k := by
  induction k with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact List.Subset.refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hik with heq | hlt
    · subst i; exact List.Subset.refl _
    · intro b hb
      rw [run.append]
      exact List.mem_append_left _ (ih (by omega) hb)

theorem cp_execution_batch_mem_later {d : ModelData n m l r} {mode : CPMode n m}
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed)
    {i k : ℕ} (hik : i < k) : run.batch i ∈ run.history k := by
  have hi : run.batch i ∈ run.history (i + 1) := by rw [run.append]; simp
  exact cp_execution_history_nested run (by omega) hi

theorem cp_execution_trial_master {d : ModelData n m l r} {mode : CPMode n m}
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed) (k : ℕ) :
    IsMinimizer (cpMaster d (run.history k)) d.objective (run.trial k) := (run.step k).1

theorem cp_execution_trial_base {d : ModelData n m l r} {mode : CPMode n m}
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed) (k : ℕ) :
    run.trial k ∈ cpBase d :=
  ((cp_master_mem_iff d _ _).mp (cp_execution_trial_master run k).1).1

theorem cp_execution_retains_cut {d : ModelData n m l r} {mode : CPMode n m}
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed)
    {i k : ℕ} (hik : i < k) : cpBatchCuts d (run.batch i) (run.trial k) :=
  ((cp_master_mem_iff d _ _).mp (cp_execution_trial_master run k).1).2
    (run.batch i) (cp_execution_batch_mem_later run hik)

theorem cp_execution_objective_monotone {d : ModelData n m l r} {mode : CPMode n m}
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed) :
    Monotone (d.objective ∘ run.trial) := by
  intro i k hik
  exact cp_master_values_monotone d (cp_execution_history_nested run hik)
    (cp_execution_trial_master run i) (cp_execution_trial_master run k)

theorem cp_execution_lowerBound {d : ModelData n m l r} {mode : CPMode n m}
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (k : ℕ) :
    IsLowerBound (d.feasibleOn Set.univ) d.objective (d.objective (run.trial k)) :=
  cp_master_lowerBound d _ hconv (fun j => (hC1 j).differentiable (by norm_num))
    (cp_execution_trial_master run k)

theorem cp_feasible_set_eq_base_rows (d : ModelData n m l r) :
    d.feasibleOn Set.univ = {p | p ∈ cpBase d ∧ ∀ j, d.g j p ≤ 0} := by
  ext p
  simp [ModelData.feasibleOn, MixedFeasible, ModelData.nonlinearRegion, cpBase,
    and_assoc, and_comm, and_left_comm]

structure CPLimitingCertificate (d : ModelData n m l r) (q : ℕ → Point n m) : Prop where
  threshold_finite : ∀ theta : ℝ, 0 < theta → {k | ∃ j, theta < d.g j (q k)}.Finite
  feasible_nonempty : (d.feasibleOn Set.univ).Nonempty
  cluster_minimizer : ∀ p, MapClusterPt p atTop q →
    IsMinimizer (d.feasibleOn Set.univ) d.objective p
  objective_monotone : Monotone (d.objective ∘ q)
  optimum_subsequence : ∃ p, IsMinimizer (d.feasibleOn Set.univ) d.objective p ∧
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (q ∘ phi) atTop (𝓝 p) ∧
      Tendsto (d.objective ∘ q) atTop (𝓝 (d.objective p))

theorem cp_execution_threshold_separation (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed)
    {theta : ℝ} (htheta : 0 < theta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i k, i < k →
      (∃ j, theta < d.g j (run.trial i)) → delta ≤ dist (run.trial i) (run.trial k) := by
  obtain ⟨delta, hd, hsep⟩ := cp_policy_uniform_separation d mode hbase hconv hC1 ha htheta
  exact ⟨delta, hd, fun i k hik hbad =>
    hsep (run.batch i) (run.step i).2.2 (cp_execution_trial_base run i)
      hbad (run.trial k) (cp_execution_retains_cut run hik)⟩

/-- Every infinite exact zero-tolerance execution of either source ECP policy
or strict-start ESH has the complete limiting certificate. Its hypotheses
contain no progress, separation, root/master-success, or convergence oracle. -/
theorem source_cp_zero_execution_limiting (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {seed : List (CPBatch n m l)} (run : CPExecution d mode 0 seed) :
    CPLimitingCertificate d run.trial := by
  have hsep := fun theta htheta =>
    cp_execution_threshold_separation d mode hbase hconv hC1 ha run (theta := theta) htheta
  have hlower : ∀ k, IsLowerBound {p | p ∈ cpBase d ∧ ∀ j, d.g j p ≤ 0}
      d.objective (d.objective (run.trial k)) := by
    rw [← cp_feasible_set_eq_base_rows d]
    exact cp_execution_lowerBound run hconv hC1
  obtain ⟨hfinite, hnonempty, hcluster, hsubseq⟩ :=
    cp_compact_limiting_certificate hbase (cp_execution_trial_base run)
      (fun j => (hC1 j).continuous) (linearForm_continuous d.c1 d.c2) hsep hlower
      (cp_execution_objective_monotone run)
  rw [← cp_feasible_set_eq_base_rows d] at hnonempty hcluster hsubseq
  exact ⟨hfinite, hnonempty, hcluster, cp_execution_objective_monotone run, hsubseq⟩

theorem source_cp_no_infinite_positive_execution (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 < eps) (seed : List (CPBatch n m l)) :
    IsEmpty (CPExecution d mode eps seed) := by
  refine ⟨fun run => ?_⟩
  have hsmall := cp_eventually_residual_le hbase run.trial (cp_execution_trial_base run)
    (fun theta htheta => cp_execution_threshold_separation d mode hbase hconv hC1 ha run htheta)
  obtain ⟨k, hk⟩ := (hsmall eps heps).exists
  exact (run.step k).2.1 hk

/-- Exact terminal meaning of the zero-tolerance source procedure. -/
def CPExactReturn (d : ModelData n m l r) : CPResult n m → Prop
  | .infeasible => d.feasibleOn Set.univ = ∅
  | .point p => IsMinimizer (d.feasibleOn Set.univ) d.objective p

theorem cp_zero_stop_exact (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j))
    {H : List (CPBatch n m l)} {out : CPResult n m} (hstop : CPStop d 0 H out) :
    CPExactReturn d out := by
  have hc := cp_stop_sound d hconv (fun j => (hC1 j).differentiable (by norm_num)) hstop
  cases out with
  | infeasible => exact hc
  | point p => exact cp_zero_certificate_optimal d hc

/-- Records that the infinite execution is generated by this exact selector
and its actual driver, not merely an unrelated legal infinite run. -/
def CPExecutionFollowsSelector {d : ModelData n m l r} {mode : CPMode n m} {eps : ℝ}
    {seed : List (CPBatch n m l)} (run : CPExecution d mode eps seed)
    (choose : CPSelector d mode eps) : Prop :=
  (∀ k, cpRun d mode eps choose seed k =
    .active (cpRun d mode eps choose seed k).trace) ∧
  (∀ k, run.history k = seed ++ (cpRun d mode eps choose seed k).trace) ∧
  ∀ k, (choose (run.history k)).val = .inr (run.batch k)

theorem cp_execution_of_selector_never_stops (d : ModelData n m l r) (mode : CPMode n m)
    (eps : ℝ) (choose : CPSelector d mode eps) (seed : List (CPBatch n m l))
    (hnever : ¬ ∃ k T out, cpRun d mode eps choose seed k = .stopped T out) :
    ∃ run : CPExecution d mode eps seed, CPExecutionFollowsSelector run choose := by
  let T (k : ℕ) := (cpRun d mode eps choose seed k).trace
  have hactive (k : ℕ) : cpRun d mode eps choose seed k = .active (T k) := by
    cases h : cpRun d mode eps choose seed k with
    | active t => simp [T, h, CPDriverState.trace]
    | stopped t out => exact (hnever ⟨k, t, out, h⟩).elim
  have hnext (k : ℕ) : ∃ b, (choose (seed ++ T k)).val = .inr b := by
    cases h : (choose (seed ++ T k)).val with
    | inr b => exact ⟨b, rfl⟩
    | inl out =>
      have hs : cpRun d mode eps choose seed (k + 1) = .stopped (T k) out := by
        simp only [cpRun, hactive k, h]
      exact (hnever ⟨k + 1, T k, out, hs⟩).elim
  choose b hb using hnext
  have happ (k : ℕ) : T (k + 1) = T k ++ [b k] := by
    have hr : cpRun d mode eps choose seed (k + 1) = .active (T k ++ [b k]) := by
      simp only [cpRun, hactive k, hb k]
    exact congrArg CPDriverState.trace hr
  have hstep (k : ℕ) : CPStep d mode eps (seed ++ T k) (b k) := by
    have hlegal := (choose (seed ++ T k)).property
    simpa only [hb k, CPDecisionLegal] using hlegal
  let run : CPExecution d mode eps seed := {
    history := fun k => seed ++ T k
    batch := b
    initial := by simp [T, cpRun, CPDriverState.trace]
    append := fun k => by simp only [happ k, List.append_assoc]
    step := hstep }
  exact ⟨run, hactive, fun _ => rfl, hb⟩

/-- The finite alternative includes an actual terminal driver state, retained
trace and exact result. The infinite alternative follows the same selector and
has the complete derived limiting certificate. -/
def CPZeroDichotomy (d : ModelData n m l r) (mode : CPMode n m)
    (choose : CPSelector d mode 0) (seed : List (CPBatch n m l)) : Prop :=
  (∃ k T out, cpRun d mode 0 choose seed k = .stopped T out ∧
    CPTrace d mode 0 seed T ∧ CPStop d 0 (seed ++ T) out ∧ CPExactReturn d out) ∨
  ∃ run : CPExecution d mode 0 seed,
    CPExecutionFollowsSelector run choose ∧ CPLimitingCertificate d run.trial

theorem source_cp_zero_finite_or_limiting (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    (choose : CPSelector d mode 0) (seed : List (CPBatch n m l)) :
    CPZeroDichotomy d mode choose seed := by
  classical
  by_cases hs : ∃ k T out, cpRun d mode 0 choose seed k = .stopped T out
  · obtain ⟨k, T, out, hr⟩ := hs
    have hi := cp_run_stopped_invariant d mode 0 choose seed hr
    exact Or.inl ⟨k, T, out, hr, hi.1, hi.2.1, cp_zero_stop_exact d hconv hC1 hi.2.1⟩
  · obtain ⟨run, hfollow⟩ := cp_execution_of_selector_never_stops d mode 0 choose seed hs
    exact Or.inr ⟨run, hfollow, source_cp_zero_execution_limiting d mode hbase hconv hC1 ha run⟩

/-- Selector nonvacuity is derived from compact exact masters and source row/
root existence, so the dichotomy describes at least one actual procedure. -/
theorem source_cp_zero_procedure_exists (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    (seed : List (CPBatch n m l)) :
    ∃ choose : CPSelector d mode 0, CPZeroDichotomy d mode choose seed := by
  obtain ⟨choose⟩ := cp_selector_exists d mode (le_refl (0 : ℝ)) hbase
    (fun j => (hC1 j).continuous) ha
  exact ⟨choose, source_cp_zero_finite_or_limiting d mode hbase hconv hC1 ha choose seed⟩

end Chapter02

#print axioms Chapter02.cp_execution_history_length
#print axioms Chapter02.cp_execution_history_nested
#print axioms Chapter02.cp_execution_batch_mem_later
#print axioms Chapter02.cp_execution_trial_master
#print axioms Chapter02.cp_execution_trial_base
#print axioms Chapter02.cp_execution_retains_cut
#print axioms Chapter02.cp_execution_objective_monotone
#print axioms Chapter02.cp_execution_lowerBound
#print axioms Chapter02.cp_feasible_set_eq_base_rows
#print axioms Chapter02.cp_execution_threshold_separation
#print axioms Chapter02.source_cp_zero_execution_limiting
#print axioms Chapter02.source_cp_no_infinite_positive_execution
#print axioms Chapter02.cp_zero_stop_exact
#print axioms Chapter02.cp_execution_of_selector_never_stops
#print axioms Chapter02.source_cp_zero_finite_or_limiting
#print axioms Chapter02.source_cp_zero_procedure_exists
