module

public import Chapter02GBDState
public import Mathlib.Tactic

@[expose] public section

/-! Arbitrary exact-choice executions for repaired linearized GBD. Counts are
mathematical decisions, not measured solver calls. Empty-affine replies do not
perform an NLP optimization; deriving an initialization floor is not counted.
No freshness or fairness premise is introduced by this driver. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

/-- The three actual kinds of continuing fiber decision. -/
@[ext] structure GBDCounts where
  optimal : ℕ
  restoration : ℕ
  emptyLinear : ℕ
  deriving DecidableEq

def GBDCounts.zero : GBDCounts := ⟨0,0,0⟩
def GBDCounts.add (a b : GBDCounts) : GBDCounts :=
  ⟨a.optimal+b.optimal,a.restoration+b.restoration,a.emptyLinear+b.emptyLinear⟩
def GBDCounts.fiber (c : GBDCounts) : ℕ := c.optimal+c.restoration+c.emptyLinear
def GBDCounts.optimizations (c : GBDCounts) : ℕ := c.optimal+c.restoration

def gbdCountBatch (b : GBDBatch n m l r) : GBDCounts :=
  match b.payload with
  | .optimal _ _ _ => ⟨1,0,0⟩
  | .restoration _ _ _ _ => ⟨0,1,0⟩
  | .emptyLinear => ⟨0,0,1⟩

def gbdCountHistory : List (GBDBatch n m l r) → GBDCounts
  | [] => .zero
  | b :: H => (gbdCountBatch b).add (gbdCountHistory H)

theorem gbd_counts_partition (c : GBDCounts) :
    c.optimizations + c.emptyLinear = c.fiber ∧
    c.optimizations = c.fiber - c.emptyLinear ∧
    c.optimal ≤ c.fiber ∧ c.restoration ≤ c.fiber ∧ c.emptyLinear ≤ c.fiber := by
  refine ⟨rfl,?_,?_,?_,?_⟩
  all_goals dsimp only [GBDCounts.optimizations,GBDCounts.fiber]; omega

theorem gbd_count_add_fiber (a b : GBDCounts) :
    (a.add b).fiber = a.fiber + b.fiber := by
  simp only [GBDCounts.add,GBDCounts.fiber]
  omega

theorem gbd_count_batch_fiber (b : GBDBatch n m l r) : (gbdCountBatch b).fiber = 1 := by
  cases hp : b.payload <;> simp [gbdCountBatch,hp,GBDCounts.fiber]

theorem gbd_count_history_length (H : List (GBDBatch n m l r)) :
    (gbdCountHistory H).fiber = H.length := by
  induction H with
  | nil => rfl
  | cons b H ih =>
    simp only [gbdCountHistory,gbd_count_add_fiber,gbd_count_batch_fiber,ih,List.length_cons]
    omega

/-- An arbitrary raw chain, indexed by its number of fiber decisions. -/
inductive GBDChain (d : ModelData n m l r) (floor epsilon : ℝ) :
    GBDState n m l r → ℕ → GBDState n m l r → Prop
  | nil (s : GBDState n m l r) : GBDChain d floor epsilon s 0 s
  | cons {s t u : GBDState n m l r} {k : ℕ}
      (step : GBDContinue d floor epsilon s t)
      (tail : GBDChain d floor epsilon t k u) : GBDChain d floor epsilon s (k+1) u

def GBDCompleted (d : ModelData n m l r) (floor epsilon : ℝ)
    (s : GBDState n m l r) (k : ℕ) (result : GBDResult n m) : Prop :=
  ∃ t, GBDChain d floor epsilon s k t ∧ GBDStop d floor epsilon t result

/-- A transcript retains the actual appended batches, including their kinds. -/
inductive GBDTrace (d : ModelData n m l r) (floor epsilon : ℝ) :
    GBDState n m l r → List (GBDBatch n m l r) → GBDState n m l r → Prop
  | nil (s : GBDState n m l r) : GBDTrace d floor epsilon s [] s
  | cons {s t : GBDState n m l r} {b : GBDBatch n m l r}
      {H : List (GBDBatch n m l r)}
      (step : GBDContinue d floor epsilon s (gbdAppend d s b))
      (tail : GBDTrace d floor epsilon (gbdAppend d s b) H t) :
      GBDTrace d floor epsilon s (b::H) t

def GBDCountedCompleted (d : ModelData n m l r) (floor epsilon : ℝ)
    (s : GBDState n m l r) (counts : GBDCounts) (result : GBDResult n m) : Prop :=
  ∃ t H, GBDTrace d floor epsilon s H t ∧
    GBDStop d floor epsilon t result ∧ counts = gbdCountHistory H

theorem gbd_trace_to_chain (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} {H : List (GBDBatch n m l r)}
    (h : GBDTrace d floor epsilon s H t) : GBDChain d floor epsilon s H.length t := by
  induction h with
  | nil s => exact .nil s
  | cons hstep _ ih => exact .cons hstep ih

theorem gbd_chain_has_trace (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} {k : ℕ} (h : GBDChain d floor epsilon s k t) :
    ∃ H, H.length = k ∧ GBDTrace d floor epsilon s H t := by
  induction h with
  | nil s => exact ⟨[],rfl,.nil s⟩
  | cons hstep _ ih =>
    obtain ⟨H,hH,htrace⟩ := ih
    cases hstep with
    | @step z b hm hc hb hy =>
      exact ⟨b::H,by simp only [List.length_cons,hH],.cons (.step hm hc hb hy) htrace⟩

theorem gbd_trace_history (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} {H : List (GBDBatch n m l r)}
    (h : GBDTrace d floor epsilon s H t) : t.history = s.history ++ H := by
  induction h with
  | nil s => simp
  | cons _ _ ih => simpa only [gbdAppend,List.append_assoc,List.singleton_append] using ih

theorem gbd_counted_completed_is_completed (d : ModelData n m l r) {floor epsilon : ℝ}
    {s : GBDState n m l r} {counts : GBDCounts} {result : GBDResult n m}
    (h : GBDCountedCompleted d floor epsilon s counts result) :
    GBDCompleted d floor epsilon s counts.fiber result := by
  obtain ⟨t,H,htrace,hstop,rfl⟩ := h
  rw [gbd_count_history_length]
  exact ⟨t,gbd_trace_to_chain d htrace,hstop⟩

theorem gbd_completed_has_counts (d : ModelData n m l r) {floor epsilon : ℝ}
    {s : GBDState n m l r} {k : ℕ} {result : GBDResult n m}
    (h : GBDCompleted d floor epsilon s k result) :
    ∃ counts, GBDCountedCompleted d floor epsilon s counts result ∧ counts.fiber = k := by
  obtain ⟨t,hchain,hstop⟩ := h
  obtain ⟨H,hH,htrace⟩ := gbd_chain_has_trace d hchain
  exact ⟨gbdCountHistory H,⟨t,H,htrace,hstop,rfl⟩,(gbd_count_history_length H).trans hH⟩

theorem gbd_chain_invariant (d : ModelData n m l r) {floor epsilon : ℝ}
    {s t : GBDState n m l r} {k : ℕ} (hs : GBDInvariant d s)
    (h : GBDChain d floor epsilon s k t) : GBDInvariant d t := by
  revert hs
  induction h with
  | nil _ => exact id
  | cons hstep _ ih => intro hs; exact ih (gbd_continue_invariant d hs hstep)

theorem gbd_chain_remaining_bound (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s t : GBDState n m l r} {k : ℕ}
    (hs : GBDInvariant d s) (h : GBDChain d floor epsilon s k t) :
    k + gbdRemaining d t ≤ gbdRemaining d s := by
  revert hs
  induction h with
  | nil _ => intro _; omega
  | cons hstep _ ih =>
    intro hs
    have hlt := gbd_continue_remaining_lt d hepsilon hs hstep
    have htail := ih (gbd_continue_invariant d hs hstep)
    omega

theorem gbd_chain_length_bound (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s t : GBDState n m l r} {k : ℕ}
    (hs : GBDInvariant d s) (h : GBDChain d floor epsilon s k t) :
    k ≤ gbdRemaining d s := by
  have := gbd_chain_remaining_bound d hepsilon hs h
  omega

theorem gbd_completed_sound (d : ModelData n m l r) {floor epsilon : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {s : GBDState n m l r} {k : ℕ} {result : GBDResult n m}
    (hs : GBDInvariant d s) (h : GBDCompleted d floor epsilon s k result) :
    GBDReturnCertificate d epsilon result := by
  obtain ⟨t,hchain,hstop⟩ := h
  exact gbd_stop_sound d hf hconv (gbd_chain_invariant d hs hchain) hstop

theorem gbd_completed_length_bound (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s : GBDState n m l r} {k : ℕ} {result : GBDResult n m}
    (hs : GBDInvariant d s) (h : GBDCompleted d floor epsilon s k result) :
    k ≤ gbdRemaining d s ∧ k+1 ≤ gbdRemaining d s+1 := by
  obtain ⟨t,hchain,_⟩ := h
  have hk := gbd_chain_length_bound d hepsilon hs hchain
  exact ⟨hk,Nat.add_le_add_right hk 1⟩

/-- Each next decision carries the batch as data so that its actual kind can
be counted. Every raw continuation has this form. -/
inductive GBDDecision (d : ModelData n m l r) (floor epsilon : ℝ)
    (s : GBDState n m l r)
  | stop (result : GBDResult n m) (valid : GBDStop d floor epsilon s result)
  | next (b : GBDBatch n m l r)
      (valid : GBDContinue d floor epsilon s (gbdAppend d s b))

def GBDSelector (d : ModelData n m l r) (floor epsilon : ℝ) :=
  ∀ s : GBDState n m l r, GBDInvariant d s → GBDDecision d floor epsilon s

theorem gbd_selector_exists (d : ModelData n m l r) (floor epsilon : ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d) :
    Nonempty (GBDSelector d floor epsilon) := by
  classical
  have hex (s : GBDState n m l r) : Nonempty (GBDDecision d floor epsilon s) := by
    rcases gbd_step_total d floor epsilon hbase hconv hdiff hCQ s with
      ⟨result,hstop⟩ | ⟨t,hstep⟩
    · exact ⟨.stop result hstop⟩
    · cases hstep with
      | @step z b hm hc hb hy => exact ⟨.next b (.step hm hc hb hy)⟩
  exact ⟨fun s _ => Classical.choice (hex s)⟩

/-- Fuel counts master decisions, including the final stopping decision. -/
def gbdRun (d : ModelData n m l r) {floor epsilon : ℝ}
    (choose : GBDSelector d floor epsilon) :
    ℕ → (s : GBDState n m l r) → GBDInvariant d s → Option (GBDResult n m × GBDCounts)
  | 0, _, _ => none
  | fuel+1, s, hs =>
    match choose s hs with
    | .stop result _ => some (result,.zero)
    | .next b hstep =>
      (gbdRun d choose fuel (gbdAppend d s b) (gbd_continue_invariant d hs hstep)).map
        (fun out => (out.1,(gbdCountBatch b).add out.2))

theorem gbd_run_counted_completed (d : ModelData n m l r) {floor epsilon : ℝ}
    (choose : GBDSelector d floor epsilon) (fuel : ℕ) (s : GBDState n m l r)
    (hs : GBDInvariant d s) {result : GBDResult n m} {counts : GBDCounts}
    (h : gbdRun d choose fuel s hs = some (result,counts)) :
    GBDCountedCompleted d floor epsilon s counts result ∧ counts.fiber < fuel := by
  induction fuel generalizing s result counts with
  | zero => simp [gbdRun] at h
  | succ fuel ih =>
    cases hchoice : choose s hs with
    | stop out hstop =>
      simp only [gbdRun,hchoice,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨⟨s,[],.nil s,hstop,rfl⟩,Nat.succ_pos _⟩
    | next b hstep =>
      simp only [gbdRun,hchoice] at h
      cases hr : gbdRun d choose fuel (gbdAppend d s b)
          (gbd_continue_invariant d hs hstep) with
      | none => simp [hr] at h
      | some out =>
        rcases out with ⟨out,c⟩
        simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨⟨t,H,htrace,hstop,hc⟩,hlt⟩ :=
          ih (gbdAppend d s b) (gbd_continue_invariant d hs hstep) hr
        refine ⟨⟨t,b::H,.cons hstep htrace,hstop,?_⟩,?_⟩
        · simp only [gbdCountHistory,hc]
        · rw [gbd_count_add_fiber,gbd_count_batch_fiber]
          omega

theorem gbd_run_completed (d : ModelData n m l r) {floor epsilon : ℝ}
    (choose : GBDSelector d floor epsilon) (fuel : ℕ) (s : GBDState n m l r)
    (hs : GBDInvariant d s) {result : GBDResult n m} {counts : GBDCounts}
    (h : gbdRun d choose fuel s hs = some (result,counts)) :
    GBDCompleted d floor epsilon s counts.fiber result ∧ counts.fiber < fuel := by
  have hc := gbd_run_counted_completed d choose fuel s hs h
  exact ⟨gbd_counted_completed_is_completed d hc.1,hc.2⟩

theorem gbd_run_sound (d : ModelData n m l r) {floor epsilon : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (choose : GBDSelector d floor epsilon) (fuel : ℕ) (s : GBDState n m l r)
    (hs : GBDInvariant d s) {result : GBDResult n m} {counts : GBDCounts}
    (h : gbdRun d choose fuel s hs = some (result,counts)) :
    GBDReturnCertificate d epsilon result :=
  gbd_completed_sound d hf hconv hs (gbd_run_completed d choose fuel s hs h).1

theorem gbd_run_exhausted_chain (d : ModelData n m l r) {floor epsilon : ℝ}
    (choose : GBDSelector d floor epsilon) (fuel : ℕ) (s : GBDState n m l r)
    (hs : GBDInvariant d s) (h : gbdRun d choose fuel s hs = none) :
    ∃ t, GBDChain d floor epsilon s fuel t := by
  induction fuel generalizing s with
  | zero => exact ⟨s,.nil s⟩
  | succ fuel ih =>
    cases hchoice : choose s hs with
    | stop result hstop => simp [gbdRun,hchoice] at h
    | next b hstep =>
      have hrun : gbdRun d choose fuel (gbdAppend d s b)
          (gbd_continue_invariant d hs hstep) = none := by
        simpa only [gbdRun,hchoice,Option.map_eq_none_iff] using h
      obtain ⟨t,ht⟩ := ih (gbdAppend d s b) (gbd_continue_invariant d hs hstep) hrun
      exact ⟨t,.cons hstep ht⟩

theorem gbd_run_sufficient_fuel (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (choose : GBDSelector d floor epsilon) (fuel : ℕ)
    (s : GBDState n m l r) (hs : GBDInvariant d s) (hfuel : gbdRemaining d s < fuel) :
    ∃ result counts, gbdRun d choose fuel s hs = some (result,counts) := by
  cases hrun : gbdRun d choose fuel s hs with
  | some out => exact ⟨out.1,out.2,rfl⟩
  | none =>
    obtain ⟨t,hchain⟩ := gbd_run_exhausted_chain d choose fuel s hs hrun
    have hbound := gbd_chain_length_bound d hepsilon hs hchain
    omega

theorem gbd_completed_init_bound (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ)
    {k : ℕ} {result : GBDResult n m}
    (h : GBDCompleted d floor epsilon (gbdInit warm) k result) :
    k ≤ (oaBox d).card ∧ k+1 ≤ (oaBox d).card+1 := by
  simpa only [gbd_init_remaining] using
    gbd_completed_length_bound d hepsilon (gbd_init_invariant d warm hwarm) h

theorem gbd_chain_init_bound (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ)
    {k : ℕ} {t : GBDState n m l r}
    (h : GBDChain d floor epsilon (gbdInit warm) k t) : k ≤ (oaBox d).card := by
  simpa only [gbd_init_remaining] using
    gbd_chain_length_bound d hepsilon (gbd_init_invariant d warm hwarm) h

theorem gbd_driver_finite_return (d : ModelData n m l r) {floor epsilon : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hepsilon : 0 ≤ epsilon) (choose : GBDSelector d floor epsilon)
    (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    ∃ result counts,
      gbdRun d choose ((oaBox d).card+1) (gbdInit warm)
        (gbd_init_invariant d warm hwarm) = some (result,counts) ∧
      GBDCountedCompleted d floor epsilon (gbdInit warm) counts result ∧
      GBDCompleted d floor epsilon (gbdInit warm) counts.fiber result ∧
      counts.fiber ≤ (oaBox d).card ∧ counts.fiber+1 ≤ (oaBox d).card+1 ∧
      counts.optimizations = counts.fiber-counts.emptyLinear ∧
      GBDReturnCertificate d epsilon result := by
  have hs := gbd_init_invariant d warm hwarm
  obtain ⟨result,counts,hrun⟩ := gbd_run_sufficient_fuel d hepsilon choose
    ((oaBox d).card+1) (gbdInit warm) hs (by rw [gbd_init_remaining]; omega)
  have hcounted := (gbd_run_counted_completed d choose _ _ hs hrun).1
  have hcompleted := gbd_counted_completed_is_completed d hcounted
  have hbound := gbd_completed_init_bound d hepsilon warm hwarm hcompleted
  exact ⟨result,counts,hrun,hcounted,hcompleted,hbound.1,hbound.2,
    (gbd_counts_partition counts).2.1,gbd_completed_sound d hf hconv hs hcompleted⟩

theorem gbd_completed_solution_within (d : ModelData n m l r) {floor epsilon : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {s : GBDState n m l r} {k : ℕ} {p : Point n m} (hs : GBDInvariant d s)
    (h : GBDCompleted d floor epsilon s k (.solution p)) : ObjectiveWithin d epsilon p :=
  gbd_certificate_objectiveWithin d (gbd_completed_sound d hf hconv hs h)

theorem gbd_completed_zero_optimal (d : ModelData n m l r) {floor : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {s : GBDState n m l r} {k : ℕ} {p : Point n m} (hs : GBDInvariant d s)
    (h : GBDCompleted d floor 0 s k (.solution p)) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective p :=
  gbd_certificate_zero_optimal d (gbd_completed_sound d hf hconv hs h)

/-- The source assumptions produce a floor and a nonempty selector type; every
selector then returns with the actual branch counts and model-level certificate.
The derived floor is valid on the full mixed affine base, including an empty one. -/
theorem gbd_procedure_exists_and_returns (d : ModelData n m l r) (epsilon : ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (hepsilon : 0 ≤ epsilon) (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    ∃ floor, GBDBaseFloorValid d floor ∧ GBDFloorValid d floor ∧
      Nonempty (GBDSelector d floor epsilon) ∧
      ∀ choose : GBDSelector d floor epsilon, ∃ result counts,
        gbdRun d choose ((oaBox d).card+1) (gbdInit warm)
          (gbd_init_invariant d warm hwarm) = some (result,counts) ∧
        GBDCountedCompleted d floor epsilon (gbdInit warm) counts result ∧
        GBDCompleted d floor epsilon (gbdInit warm) counts.fiber result ∧
        counts.fiber ≤ (oaBox d).card ∧ counts.fiber+1 ≤ (oaBox d).card+1 ∧
        counts.optimizations = counts.fiber-counts.emptyLinear ∧
        GBDReturnCertificate d epsilon result := by
  obtain ⟨floor,hfloor⟩ := gbd_base_floor_exists d hbase
  have hf := gbd_base_floor_valid d floor hfloor
  exact ⟨floor,hfloor,hf,gbd_selector_exists d floor epsilon hbase hconv hdiff hCQ,
    fun choose => gbd_driver_finite_return d hf hconv hepsilon choose warm hwarm⟩

/-- Exact zero-tolerance interpretation of the returned data. -/
def GBDExactCertificate (d : ModelData n m l r) : GBDResult n m → Prop
  | .infeasible => ¬ (d.feasibleOn Set.univ).Nonempty
  | .solution p => IsMinimizer (d.feasibleOn Set.univ) d.objective p

theorem gbd_driver_exact_finite_return (d : ModelData n m l r) {floor : ℝ}
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (choose : GBDSelector d floor 0) (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    ∃ result counts,
      gbdRun d choose ((oaBox d).card+1) (gbdInit warm)
        (gbd_init_invariant d warm hwarm) = some (result,counts) ∧
      GBDCountedCompleted d floor 0 (gbdInit warm) counts result ∧
      GBDCompleted d floor 0 (gbdInit warm) counts.fiber result ∧
      counts.fiber ≤ (oaBox d).card ∧ counts.fiber+1 ≤ (oaBox d).card+1 ∧
      counts.optimizations = counts.fiber-counts.emptyLinear ∧
      GBDExactCertificate d result := by
  obtain ⟨result,counts,hrun,hcounted,hcompleted,hbound,hdec,hopt,hcert⟩ :=
    gbd_driver_finite_return d hf hconv le_rfl choose warm hwarm
  refine ⟨result,counts,hrun,hcounted,hcompleted,hbound,hdec,hopt,?_⟩
  cases result with
  | infeasible => exact hcert
  | solution p => exact gbd_certificate_zero_optimal d hcert

theorem gbd_exact_procedure_exists_and_returns (d : ModelData n m l r)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ) :
    ∃ floor, GBDBaseFloorValid d floor ∧ GBDFloorValid d floor ∧
      Nonempty (GBDSelector d floor 0) ∧
      ∀ choose : GBDSelector d floor 0, ∃ result counts,
        gbdRun d choose ((oaBox d).card+1) (gbdInit warm)
          (gbd_init_invariant d warm hwarm) = some (result,counts) ∧
        GBDCountedCompleted d floor 0 (gbdInit warm) counts result ∧
        GBDCompleted d floor 0 (gbdInit warm) counts.fiber result ∧
        counts.fiber ≤ (oaBox d).card ∧ counts.fiber+1 ≤ (oaBox d).card+1 ∧
        counts.optimizations = counts.fiber-counts.emptyLinear ∧
        GBDExactCertificate d result := by
  obtain ⟨floor,hfloor⟩ := gbd_base_floor_exists d hbase
  have hf := gbd_base_floor_valid d floor hfloor
  exact ⟨floor,hfloor,hf,gbd_selector_exists d floor 0 hbase hconv hdiff hCQ,
    fun choose => gbd_driver_exact_finite_return d hf hconv choose warm hwarm⟩

/-- All branch counts are tied to the executed transcript, and every one obeys
the remaining-fiber bound. Optimization decisions omit empty-affine replies. -/
theorem gbd_counted_completed_bounds (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {s : GBDState n m l r}
    {counts : GBDCounts} {result : GBDResult n m} (hs : GBDInvariant d s)
    (h : GBDCountedCompleted d floor epsilon s counts result) :
    counts.fiber ≤ gbdRemaining d s ∧
    counts.optimal ≤ gbdRemaining d s ∧
    counts.restoration ≤ gbdRemaining d s ∧
    counts.emptyLinear ≤ gbdRemaining d s ∧
    counts.optimizations = counts.fiber-counts.emptyLinear ∧
    counts.optimizations ≤ gbdRemaining d s := by
  have hb := (gbd_completed_length_bound d hepsilon hs
    (gbd_counted_completed_is_completed d h)).1
  obtain ⟨hpart,hopt,ho,hr,he⟩ := gbd_counts_partition counts
  exact ⟨hb,ho.trans hb,hr.trans hb,he.trans hb,hopt,by omega⟩

/-- An empty box permits no continuing fiber decision. A completed execution
still contains its final master stopping decision. -/
theorem gbd_empty_box_completed_counts (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hbox : (oaBox d).card = 0)
    (warm : Option (Point n m))
    (hwarm : ∀ u, warm = some u → u ∈ d.feasibleOn Set.univ)
    {counts : GBDCounts} {result : GBDResult n m}
    (h : GBDCountedCompleted d floor epsilon (gbdInit warm) counts result) :
    counts = .zero ∧ counts.fiber+1 = 1 := by
  have hb := (gbd_completed_init_bound d hepsilon warm hwarm
    (gbd_counted_completed_is_completed d h)).1
  rw [hbox] at hb
  have hz : counts.fiber = 0 := by omega
  constructor
  · ext <;> simp only [GBDCounts.zero]
    all_goals dsimp only [GBDCounts.fiber] at hz; omega
  · omega

theorem gbd_chain_of_sequence (d : ModelData n m l r) {floor epsilon : ℝ}
    (states : ℕ → GBDState n m l r)
    (hsteps : ∀ i, GBDContinue d floor epsilon (states i) (states (i+1)))
    (start k : ℕ) : GBDChain d floor epsilon (states start) k (states (start+k)) := by
  induction k generalizing start with
  | zero => simpa using GBDChain.nil (d := d) (floor := floor) (epsilon := epsilon) (states start)
  | succ k ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1 k] using GBDChain.cons (hsteps start) (ih (start+1))

theorem gbd_no_infinite_continuations (d : ModelData n m l r) {floor epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (states : ℕ → GBDState n m l r)
    (hs : GBDInvariant d (states 0)) :
    ¬ (∀ i, GBDContinue d floor epsilon (states i) (states (i+1))) := by
  intro hsteps
  have hc := gbd_chain_of_sequence d states hsteps 0 (gbdRemaining d (states 0)+1)
  have hb := gbd_chain_length_bound d hepsilon hs hc
  omega

end Chapter02

#print axioms Chapter02.gbd_counts_partition
#print axioms Chapter02.gbd_count_history_length
#print axioms Chapter02.gbd_trace_to_chain
#print axioms Chapter02.gbd_chain_has_trace
#print axioms Chapter02.gbd_trace_history
#print axioms Chapter02.gbd_counted_completed_is_completed
#print axioms Chapter02.gbd_completed_has_counts
#print axioms Chapter02.gbd_chain_invariant
#print axioms Chapter02.gbd_chain_remaining_bound
#print axioms Chapter02.gbd_chain_length_bound
#print axioms Chapter02.gbd_completed_sound
#print axioms Chapter02.gbd_completed_length_bound
#print axioms Chapter02.gbd_selector_exists
#print axioms Chapter02.gbd_run_counted_completed
#print axioms Chapter02.gbd_run_completed
#print axioms Chapter02.gbd_run_sound
#print axioms Chapter02.gbd_run_exhausted_chain
#print axioms Chapter02.gbd_run_sufficient_fuel
#print axioms Chapter02.gbd_completed_init_bound
#print axioms Chapter02.gbd_chain_init_bound
#print axioms Chapter02.gbd_driver_finite_return
#print axioms Chapter02.gbd_completed_solution_within
#print axioms Chapter02.gbd_completed_zero_optimal
#print axioms Chapter02.gbd_procedure_exists_and_returns
#print axioms Chapter02.gbd_driver_exact_finite_return
#print axioms Chapter02.gbd_exact_procedure_exists_and_returns
#print axioms Chapter02.gbd_counted_completed_bounds
#print axioms Chapter02.gbd_empty_box_completed_counts
#print axioms Chapter02.gbd_chain_of_sequence
#print axioms Chapter02.gbd_no_infinite_continuations
