module

public import Chapter03OAExistenceRestoration
public import Chapter03OAExistenceCQEvent
public import Chapter03OAExistenceMaster

@[expose] public section

/-! Complete existence of exact choices for the unchanged initialized OA.
Finite Y bounds are in ModelData. Convexity is on the exact hard domain.
The bounded feasible-set interpretation of A3, ambient derivatives at boundary
points and uniform LICQ at every minimizer of every nonempty box fiber are
explicit sufficient qualifications. No restoration LICQ is needed. This is not
a theorem about the literal thesis's all-soft binary bounds or the published
reversed incumbent update. The article box encoding is supplied separately. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

/-- Source-compatible sufficient interpretations, not solution/certificate
oracles. Uniform all-minimizer LICQ is stronger than a visited-solution reading. -/
structure AvailabilityAssumptions (d : Data n m l r) : Prop where
  analytic : Analytic d
  domain_base : d.domain = (asFP d).base
  bounded_relaxation : Bornology.IsBounded d.relaxation
  fixed_licq : ∀ y : IntVector m, y ∈ IntegerBox d.model.lo d.model.hi →
    ∀ x : RealVector n,
      IsMinimizer (fiber d.model (intCast y)) (fiberObjective d.f (intCast y)) x →
      FixedLICQ d.model x (intCast y) (d.Dg (x,intCast y))

theorem AvailabilityAssumptions.every_exact_initialization {d : Data n m l r}
    (h : AvailabilityAssumptions d) (seed : Point n m)
    (hm : IsMinimizer d.relaxation d.f seed) : seed ∈ d.domain :=
  relaxation_minimum_domain d h.domain_base hm

theorem AvailabilityAssumptions.every_exact_fixed_event {d : Data n m l r}
    (h : AvailabilityAssumptions d) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi) (x : RealVector n)
    (hm : IsMinimizer (fiber d.model (intCast y)) (fiberObjective d.f (intCast y)) x) :
    EventValid d ⟨y,hy,x,none⟩ :=
  fixed_event_valid_of_licq d h.analytic y hy x hm (h.fixed_licq y hy x hm)

theorem AvailabilityAssumptions.every_exact_restoration_event {d : Data n m l r}
    (h : AvailabilityAssumptions d) (y : IntVector m)
    (hy : y ∈ IntegerBox d.model.lo d.model.hi) (x : RealVector n) (s : RealVector l)
    (he : ¬ (fiber d.model (intCast y)).Nonempty)
    (hm : IsMinimizer (restSet d.model (intCast y)) restCost (weightedInsert x s)) :
    EventValid d ⟨y,hy,x,some s⟩ :=
  exact_restoration_event_valid d h.domain_base y hy x s he hm

theorem AvailabilityAssumptions.initial_available {d : Data n m l r}
    (h : AvailabilityAssumptions d) : InitialAvailability d :=
  initial_availability_of_bounded_relaxation d h.analytic h.domain_base h.bounded_relaxation

/-- Availability is derived for the exact master/fiber/restoration requests;
no reachability, freshness or optimizer callback is an assumption. -/
theorem AvailabilityAssumptions.local_available {d : Data n m l r}
    (h : AvailabilityAssumptions d) (seed : Point n m) (hs : SeedValid d seed)
    (epsilon : ℝ) : LocalAvailability d seed epsilon := by
  classical
  refine ⟨?_,?_⟩
  · intro state _ _ hne hbb
    exact master_attained_of_bddBelow d seed state.history hne hbb
  · intro state _ _ q
    obtain ⟨y,hy,hsame⟩ := master_integer q.mem
    by_cases hne : (fiber d.model (intCast y)).Nonempty
    · obtain ⟨x,hm⟩ := fixed_minimum_exists d h.analytic h.domain_base
        h.bounded_relaxation y hy hne
      exact ⟨⟨y,hy,x,none⟩,h.every_exact_fixed_event y hy x hm,hsame⟩
    · obtain ⟨x,s,hm⟩ := requested_restoration_minimum_exists d h.analytic
        h.domain_base h.bounded_relaxation seed hs state.history q.mem y hy hsame
      exact ⟨⟨y,hy,x,some s⟩,h.every_exact_restoration_event y hy x s hne hm,hsame⟩

theorem AvailabilityAssumptions.initialization_nonempty {d : Data n m l r}
    (h : AvailabilityAssumptions d) : Nonempty (Initialization d) :=
  initialization_inhabited h.initial_available

theorem AvailabilityAssumptions.selectors_nonempty {d : Data n m l r}
    (h : AvailabilityAssumptions d) (epsilon : ℝ) : Nonempty (InitializedSelectors d epsilon) :=
  initialized_selectors_inhabited (fun seed hs => h.local_available seed hs epsilon)

/-- The new content supplies initializer/local choice existence; the universal
execution clause reuses initialized_finite_return. Each selector has its own
returned point/certificate. No uniqueness across selectors is asserted. -/
theorem source_initialized_finite_return {d : Data n m l r}
    (h : AvailabilityAssumptions d) {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (Initialization d) ∧
    (∀ seed, SeedValid d seed → LocalAvailability d seed epsilon) ∧
    Nonempty (InitializedSelectors d epsilon) ∧
    ∀ (choose : InitializedSelectors d epsilon) (initial : Initialization d),
      ∃ out, execute d epsilon choose initial = some out ∧
        ReturnCertificate d epsilon out.result ∧
        out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
        out.restorations ≤ d.box.card :=
  ⟨h.initialization_nonempty,fun seed hs => h.local_available seed hs epsilon,
    h.selectors_nonempty epsilon,fun choose initial =>
      initialized_finite_return h.analytic heps choose initial⟩

def articleDomain (bounds : Bounds n) (d : Data n m l r) : Set (Point n m) :=
  {p | p.1 ∈ bounds.region ∧
    ∀ j, d.model.lo j ≤ p.2 j ∧ p.2 j ≤ d.model.hi j}

theorem articleDomain_eq_base (bounds : Bounds n) (d : Data n m l r)
    (encoding : HardBoundEncoding bounds d.model) : articleDomain bounds d = (asFP d).base := by
  ext p
  exact and_congr (encoding.region_iff p.1 p.2) Iff.rfl

/-- Exact finite-side encoding of X identifies the generic hard-domain package
with article X×Y. Infinite absent X sides are allowed and need not be bounded. -/
theorem article_availability_assumptions (bounds : Bounds n) (d : Data n m l r)
    (encoding : HardBoundEncoding bounds d.model) (a : Analytic d)
    (hdom : d.domain = articleDomain bounds d)
    (hbounded : Bornology.IsBounded d.relaxation)
    (hlicq : ∀ y : IntVector m, y ∈ IntegerBox d.model.lo d.model.hi →
      ∀ x : RealVector n,
        IsMinimizer (fiber d.model (intCast y)) (fiberObjective d.f (intCast y)) x →
        FixedLICQ d.model x (intCast y) (d.Dg (x,intCast y))) :
    AvailabilityAssumptions d :=
  ⟨a,hdom.trans (articleDomain_eq_base bounds d encoding),hbounded,hlicq⟩

/-- Article-scoped qualified complete endpoint. Source A3 is read as a bounded
feasible set; boundary gradients and all-minimizer LICQ are explicit sufficient
interpretations. The accepted corrected incumbent/return policy is retained. -/
theorem article_source_initialized_finite_return (bounds : Bounds n) (d : Data n m l r)
    (encoding : HardBoundEncoding bounds d.model) (a : Analytic d)
    (hdom : d.domain = articleDomain bounds d)
    (hbounded : Bornology.IsBounded d.relaxation)
    (hlicq : ∀ y : IntVector m, y ∈ IntegerBox d.model.lo d.model.hi →
      ∀ x : RealVector n,
        IsMinimizer (fiber d.model (intCast y)) (fiberObjective d.f (intCast y)) x →
        FixedLICQ d.model x (intCast y) (d.Dg (x,intCast y)))
    {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Nonempty (Initialization d) ∧
    (∀ seed, SeedValid d seed → LocalAvailability d seed epsilon) ∧
    Nonempty (InitializedSelectors d epsilon) ∧
    ∀ (choose : InitializedSelectors d epsilon) (initial : Initialization d),
      ∃ out, execute d epsilon choose initial = some out ∧
        ReturnCertificate d epsilon out.result ∧
        out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
        out.restorations ≤ d.box.card :=
  source_initialized_finite_return
    (article_availability_assumptions bounds d encoding a hdom hbounded hlicq) heps

/-- At zero tolerance the returned solution is an actual global minimum of
the original mixed feasible set. Empty initialization and infeasibility remain. -/
theorem source_initialized_zero_return {d : Data n m l r}
    (h : AvailabilityAssumptions d) (choose : InitializedSelectors d 0)
    (initial : Initialization d) :
    ∃ out, execute d 0 choose initial = some out ∧
      (match out.result with
       | .infeasible => ¬ d.original.Nonempty
       | .solution p => IsMinimizer d.original d.f p) ∧
      out.masters ≤ d.box.card+1 ∧ out.fixed ≤ d.box.card+1 ∧
      out.restorations ≤ d.box.card := by
  obtain ⟨out,he,hc,hm,hf,hr⟩ :=
    (source_initialized_finite_return h (le_refl (0 : ℝ))).2.2.2 choose initial
  refine ⟨out,he,?_,hm,hf,hr⟩
  cases hresult : out.result with
  | infeasible => simpa only [hresult,ReturnCertificate] using hc
  | solution p => simpa only [hresult,ReturnCertificate,add_zero,IsMinimizer] using hc

end Chapter03.OAExec

#print axioms Chapter03.OAExec.AvailabilityAssumptions.local_available
#print axioms Chapter03.OAExec.source_initialized_finite_return
#print axioms Chapter03.OAExec.article_source_initialized_finite_return
#print axioms Chapter03.OAExec.source_initialized_zero_return
