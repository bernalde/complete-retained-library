module

public import Chapter02FBBTLP
public import Chapter02FBBTLimit
public import Chapter02FBBTContinuity

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Chapter02FBBT

/-- The canonical endpoint limit of the concrete simultaneous iteration. -/
def limitBounds {n m} (A : Matrix n m) (q0 : JointBounds n m) :=
  endpointLimit (rawF A q0) q0

def RunNonempty {n m} (A : Matrix n m) (q0 : JointBounds n m) : Prop :=
  ∀ k, (publicRun A q0 k).members.Nonempty

def FixedExists {n m} (A : Matrix n m) (q0 : JointBounds n m) : Prop :=
  ∃ q, Ordered q ∧ rawF A q0 q = q

 theorem fixed_within_run {n m} (A : Matrix n m) (q0 q : JointBounds n m)
    (hf : rawF A q0 q = q) (k) : Within q (rawRun A q0 k) := by
  have hq : Within q q0 := (rawF_fixed_iff A q0 q).1 hf |>.1
  induction k with
  | zero => exact hq
  | succ k ih =>
    have ht := rawF_mono A q0 ih
    rw [hf] at ht
    simpa only [rawRun, Function.iterate_succ_apply'] using ht

 theorem fixed_implies_nonempty_run {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (h : FixedExists A q0) : RunNonempty A q0 := by
  rcases h with ⟨q,ho,hf⟩
  apply (public_run_nonempty_iff _ _).2
  exact fun k => ordered_of_within ho (fixed_within_run A q0 q hf k)

 theorem actual_limit {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (h : RunNonempty A q0) :
    Ordered (limitBounds A q0) ∧ Within (limitBounds A q0) q0 ∧
    Tendsto (rawRun A q0) atTop (𝓝 (limitBounds A q0)) ∧
    rawF A q0 (limitBounds A q0) = limitBounds A q0 ∧
    (∀ q, Ordered q → rawF A q0 q = q → Within q (limitBounds A q0)) := by
  have ht := bounds_iterate_limit (rawF A q0) q0 (rawF_continuous A q0)
    (fun q _ => rawF_contract A q0 q)
    (fun _ _ _ _ hpq => rawF_mono A q0 hpq)
    ((public_run_nonempty_iff _ _).1 h)
  exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,
    fun q ho hf => ht.2.2.2.2 q ho ((rawF_fixed_iff _ _ _).1 hf).1 hf⟩

 theorem run_nonempty_iff_fixed {n m} (A : Matrix n m) (q0 : JointBounds n m) :
    RunNonempty A q0 ↔ FixedExists A q0 := by
  constructor
  · intro h
    have hl := actual_limit A q0 h
    exact ⟨limitBounds A q0,hl.1,hl.2.2.2.1⟩
  · exact fixed_implies_nonempty_run A q0

 theorem fixed_iff_lp_feasible {n m} (A : Matrix n m) (q0 : JointBounds n m) :
    FixedExists A q0 ↔ ∃ p, LPFeasible A q0 p := by
  constructor
  · rintro ⟨q,ho,hf⟩
    exact ⟨canonicalAssignment A q,(canonical_feasible_iff _ _ _).2 ⟨ho,hf⟩⟩
  · rintro ⟨p,hp⟩
    have ht := (lp_fixed_equivalence A q0 p).1 hp
    exact ⟨p.bounds,ht.1,ht.2.1⟩

 theorem limit_graph_preservation {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (h : RunNonempty A q0) (x) (hx : graph A x ∈ members q0) :
    graph A x ∈ members (limitBounds A q0) := by
  have ht := (actual_limit A q0 h).2.2.2.2 (graph A x,graph A x)
    (fun _ => le_rfl) (graph_singleton_fixed A q0 x hx)
  exact ht

 theorem unique_attained_lp {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (h : RunNonempty A q0) :
    LPFeasible A q0 (canonicalAssignment A (limitBounds A q0)) ∧
    (∀ p, LPFeasible A q0 p →
      LPObjective p ≤ LPObjective (canonicalAssignment A (limitBounds A q0))) ∧
    (∀ p, LPFeasible A q0 p →
      LPObjective (canonicalAssignment A (limitBounds A q0)) ≤ LPObjective p →
      p = canonicalAssignment A (limitBounds A q0)) := by
  have hl := actual_limit A q0 h
  have hgreat (p) (hp : LPFeasible A q0 p) : Within p.bounds (limitBounds A q0) :=
    hl.2.2.2.2 p.bounds hp.1 ((lp_fixed_equivalence _ _ _).1 hp).2.1
  refine ⟨(canonical_feasible_iff _ _ _).2 ⟨hl.1,hl.2.2.2.1⟩,
    (fun p hp => bounds_width_le (hgreat p hp)), ?_⟩
  intro p hp hw
  have he : p.bounds = limitBounds A q0 := bounds_eq_of_within_width_eq (hgreat p hp)
    (le_antisymm (bounds_width_le (hgreat p hp)) hw)
  calc p = canonicalAssignment A p.bounds := assignment_unique A q0 p hp
       _ = canonicalAssignment A (limitBounds A q0) := congrArg (canonicalAssignment A) he

/-- The auxiliary interval-order rows (2010 equation 31) are redundant after
all signed product equalities and endpoint ordering have been imposed. -/
 theorem lp_auxiliary_ordered {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (p : LPAssignment n m) (hp : LPFeasible A q0 p) (i j) : p.zLo i j ≤ p.zHi i j := by
  rw [hp.2.2.1 i j, hp.2.2.2.1 i j]
  have hb := Chapter02.affine_product_bounds (a := A i j)
    (x := p.bounds.1 (.inl j)) ⟨le_rfl, hp.1 (.inl j)⟩
  exact hb.1.trans hb.2

/-- Transparent full conditional conclusion. Nonemptiness is Cartesian;
no original graph feasibility premise, finite stabilization or complexity claim. -/
structure SimultaneousConclusion {n m} (A : Matrix n m) (q0 : JointBounds n m) : Prop where
  limitOrdered : Ordered (limitBounds A q0)
  limitWithinInitial : Within (limitBounds A q0) q0
  actualEndpointConvergence : Tendsto (rawRun A q0) atTop (𝓝 (limitBounds A q0))
  actualFixed : rawF A q0 (limitBounds A q0) = limitBounds A q0
  greatestNonemptyFixed : ∀ q, Ordered q → rawF A q0 q = q → Within q (limitBounds A q0)
  attainedLP : LPFeasible A q0 (canonicalAssignment A (limitBounds A q0))
  globalWidthMaximum : ∀ p, LPFeasible A q0 p →
    LPObjective p ≤ LPObjective (canonicalAssignment A (limitBounds A q0))
  uniqueEntireAssignment : ∀ p, LPFeasible A q0 p →
    LPObjective (canonicalAssignment A (limitBounds A q0)) ≤ LPObjective p →
    p = canonicalAssignment A (limitBounds A q0)
  graphSurvivesEveryIteration : ∀ x, graph A x ∈ members q0 → ∀ k,
    graph A x ∈ members (rawRun A q0 k)
  graphSurvivesLimit : ∀ x, graph A x ∈ members q0 → graph A x ∈ members (limitBounds A q0)

/-- Source-qualified finite simultaneous real result. The three-way equivalence
is unconditional; the analytic/LP conclusion requires actual Cartesian nonemptiness. -/
structure SimultaneousTheory {n m} (A : Matrix n m) (q0 : JointBounds n m) : Prop where
  initialOrdered : Ordered q0
  runIffFixed : RunNonempty A q0 ↔ FixedExists A q0
  fixedIffLP : FixedExists A q0 ↔ ∃ p, LPFeasible A q0 p
  publicRawAgreement : ∀ k, publicRun A q0 k = publicOfBounds (rawRun A q0 k)
  conditionalConclusion : RunNonempty A q0 → SimultaneousConclusion A q0
  unconditionalInfeasibility : (¬ ∃ p, LPFeasible A q0 p) → ¬ ∃ x, graph A x ∈ members q0

/-- The single proposed counted core endpoint. All concrete operator hypotheses,
LP correspondence and nonempty-run existence implications are discharged above. -/
theorem qualified_simultaneous_fbbt {n m} (A : Matrix n m) (q0 : JointBounds n m)
    (h0 : Ordered q0) : SimultaneousTheory A q0 := by
  refine ⟨h0,run_nonempty_iff_fixed _ _,fixed_iff_lp_feasible _ _,
    public_raw_agreement _ _,?_,lp_infeasible_no_graph _ _⟩
  intro h
  have hl := actual_limit A q0 h
  have hp := unique_attained_lp A q0 h
  exact ⟨hl.1,hl.2.1,hl.2.2.1,hl.2.2.2.1,hl.2.2.2.2,
    hp.1,hp.2.1,hp.2.2,graph_rawRun _ _,limit_graph_preservation _ _ h⟩

end Chapter02FBBT
#print axioms Chapter02FBBT.qualified_simultaneous_fbbt
