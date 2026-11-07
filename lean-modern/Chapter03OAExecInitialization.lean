module

public import Chapter03OAExecReturnCounts

@[expose] public section

/-! One actual continuous-relaxation initialization, immediate empty/integral
returns, and the fractional execution. Initialization's attained/domain premise
is explicit; no compactness or regularity theorem is silently substituted. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}
attribute [local instance] Classical.propDecidable

inductive Initialization (d : Data n m l r)
  | empty (valid : d.relaxation = ∅)
  | minimum (seed : Point n m) (valid : IsMinimizer d.relaxation d.f seed)
      (domain : seed ∈ d.domain)

def InitialAvailability (d : Data n m l r) : Prop :=
  d.relaxation = ∅ ∨ ∃ seed, IsMinimizer d.relaxation d.f seed ∧ seed ∈ d.domain

theorem initialization_inhabited {d : Data n m l r} (h : InitialAvailability d) :
    Nonempty (Initialization d) := by
  rcases h with he | ⟨seed,hm,hd⟩
  · exact ⟨.empty he⟩
  · exact ⟨.minimum seed hm hd⟩

theorem integral_relaxation_original {d : Data n m l r} {p : Point n m}
    (hp : p ∈ d.relaxation) (hi : integral p) : p ∈ d.original := by
  obtain ⟨hg,hl,hb⟩ := (relaxation_mem_iff d p).mp hp
  obtain ⟨y,hy⟩ := hi
  apply (source_feasible_iff d.model Set.univ p).mpr
  refine ⟨Set.mem_univ _,hg,hl,y,?_,hy⟩
  simpa only [hy,Chapter03.OAKKT.intCast] using hb

theorem integral_initializer_minimum {d : Data n m l r} {seed : Point n m}
    (h : IsMinimizer d.relaxation d.f seed) (hi : integral seed) :
    IsMinimizer d.original d.f seed :=
  ⟨integral_relaxation_original h.1 hi,
    fun p hp => h.2 p (original_subset_relaxation d hp)⟩

/-- A family of local choices ranges over exactly admitted fractional seeds;
each resulting loop selector remains restricted to its open reachable states. -/
def InitializedSelectors (d : Data n m l r) (epsilon : ℝ) :=
  ∀ seed, SeedValid d seed → Selector d seed epsilon

theorem initialized_selectors_inhabited {d : Data n m l r} {epsilon : ℝ}
    (h : ∀ seed, SeedValid d seed → LocalAvailability d seed epsilon) :
    Nonempty (InitializedSelectors d epsilon) :=
  ⟨fun seed hs => Classical.choice (selector_inhabited (h seed hs))⟩

def execute (d : Data n m l r) (epsilon : ℝ) (choose : InitializedSelectors d epsilon) :
    Initialization d → Option (Output n m)
  | .empty _ => some ⟨.infeasible,0,0,0⟩
  | .minimum seed h hd =>
    if hi : integral seed then some ⟨.solution seed,0,0,0⟩
    else runFuel d seed epsilon (choose seed ⟨h,hd,hi⟩) (d.box.card+1)
      (initialState d seed) .initial

/-- Complete conditional Algorithm1 endpoint. Exactly one initializer reply is
inspected; the returned point is explicitly defined on the integral branch. -/
theorem initialized_finite_return {d : Data n m l r} (a : Analytic d)
    {epsilon : ℝ} (heps : 0 ≤ epsilon) (choose : InitializedSelectors d epsilon)
    (initial : Initialization d) :
    ∃ out, execute d epsilon choose initial = some out ∧
      ReturnCertificate d epsilon out.result ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card := by
  cases initial with
  | empty he =>
    refine ⟨⟨.infeasible,0,0,0⟩,rfl,?_,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
    rintro ⟨p,hp⟩
    have hr := original_subset_relaxation d hp
    rw [he] at hr
    exact hr
  | minimum seed hm hd =>
    by_cases hi : integral seed
    · refine ⟨⟨.solution seed,0,0,0⟩,by simp only [execute,dif_pos hi],?_,
        Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
      have hs := integral_initializer_minimum hm hi
      refine ⟨hs.1,?_⟩
      intro p hp
      exact (hs.2 p hp).trans (le_add_of_nonneg_right heps)
    · obtain ⟨out,hout,hcert,hmasters,hfixed,hrest⟩ :=
        finite_return_with_counts a ⟨hm,hd,hi⟩ heps (choose seed ⟨hm,hd,hi⟩)
      exact ⟨out,by simpa only [execute,dif_neg hi] using hout,
        hcert,hmasters,hfixed,hrest⟩

end Chapter03.OAExec

#print axioms Chapter03.OAExec.initialized_finite_return
