module

public import Chapter02FBBTTheorem
public import Chapter02FBBTSourceData

@[expose] public section

/-! Qualified transport to the thesis's full retained original-coordinate model.
The finite X domain is explicit; no original existence or attainment is asserted. -/
noncomputable section
open Chapter02
namespace Chapter02FBBT

variable {n l r : ℕ}

def sourceLimitX (D : BBPolyData n l r) (X : Bounds (Fin n)) : Bounds (Fin n) :=
  (fun j => (limitBounds D.coefficient (sourceInitial D X)).1 (.inl j),
   fun j => (limitBounds D.coefficient (sourceInitial D X)).2 (.inl j))

lemma source_limit_set_eq (D : BBPolyData n l r) (I : Finset (Fin n))
    (X : Bounds (Fin n)) (h : RunNonempty D.coefficient (sourceInitial D X)) :
    D.feasible I ∩ members (sourceLimitX D X) = D.feasible I ∩ members X := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, fun j => ?_⟩
    have hi := (actual_limit D.coefficient (sourceInitial D X) h).2.1 (.inl j)
    exact ⟨hi.1.trans (hx.2 j).1, (hx.2 j).2.trans hi.2⟩
  · intro hx
    have hg : graph D.coefficient x ∈ members (sourceInitial D X) :=
      (source_feasible_graph_iff D I X x).1 hx |>.2
    have hp := limit_graph_preservation D.coefficient (sourceInitial D X) h x hg
    exact ⟨hx.1, fun j => hp (.inl j)⟩

lemma source_unconditional_infeasibility (D : BBPolyData n l r)
    (I : Finset (Fin n)) (X : Bounds (Fin n))
    (h : ¬ ∃ p, LPFeasible D.coefficient (sourceInitial D X) p) :
    D.feasible I ∩ members X = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hg : graph D.coefficient x ∈ members (sourceInitial D X) :=
    (source_feasible_graph_iff D I X x).1 hx |>.2
  exact lp_infeasible_no_graph D.coefficient (sourceInitial D X) h ⟨x, hg⟩

structure SourceConclusion (D : BBPolyData n l r) (I : Finset (Fin n))
    (X : Bounds (Fin n)) : Prop where
  originalBoundedSetEquality :
    D.feasible I ∩ members (sourceLimitX D X) = D.feasible I ∩ members X
  originalObjectiveMinimizerEquivalence : ∀ x,
    IsMinimizer (D.feasible I ∩ members (sourceLimitX D X)) D.f x ↔
      IsMinimizer (D.feasible I ∩ members X) D.f x
  finiteLimitOrdered : Ordered (sourceLimitX D X)
  finiteLimitWithin : Within (sourceLimitX D X) X

structure SourceTheory (D : BBPolyData n l r) (I : Finset (Fin n))
    (X : Bounds (Fin n)) : Prop where
  core : SimultaneousTheory D.coefficient (sourceInitial D X)
  initialRowEquivalence : ∀ x,
    sourceGraph D x ∈ members (sourceInitial D X) ↔ x ∈ members X ∧ x ∈ D.polyhedron
  unconditionalSourceInfeasibility :
    (¬ ∃ p, LPFeasible D.coefficient (sourceInitial D X) p) → D.feasible I ∩ members X = ∅
  conditionalSourceConclusion : RunNonempty D.coefficient (sourceInitial D X) →
    SourceConclusion D I X

/-- Proposed counted source endpoint. The infeasibility component is independent
of the nonempty-run hypothesis used by the separate limit/minimizer component. -/
theorem qualified_source_fbbt (D : BBPolyData n l r) (I : Finset (Fin n))
    (X : Bounds (Fin n)) (hX : Ordered X) : SourceTheory D I X := by
  refine ⟨qualified_simultaneous_fbbt D.coefficient (sourceInitial D X)
    (source_initial_ordered D X hX), source_graph_mem_iff D X,
    source_unconditional_infeasibility D I X, ?_⟩
  intro h
  have he := source_limit_set_eq D I X h
  have hl := actual_limit D.coefficient (sourceInitial D X) h
  refine ⟨he, ?_, fun j => hl.1 (.inl j), fun j => hl.2.1 (.inl j)⟩
  intro x
  rw [he]

end Chapter02FBBT
#print axioms Chapter02FBBT.qualified_source_fbbt
