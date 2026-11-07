module

public import Chapter03OASoftStoredPolicy

@[expose] public section

/-! Local nonvacuity for stored-generation append; not a continuing driver.
The accepted integral-seed control supplies a positive multiplier and actual
soft optimizer. Repeated append tests certificate and weight retention. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OASoftMaster.StoredPolicy.Control
open RevisitControl

def generation : Generation spec event where
  valid := event_valid
  certificate _ := certificate
  hard := by
    intro hn j hj hne q hq hy
    have hj0 : j = 0 := by fin_cases j <;> simp_all [certificate]
    subst j
    exact (hj row_nonlinear).elim

def empty : Policy spec [] where
  seedWeight j := if j = 0 then 500 else 0
  seed_nonneg j := by split <;> norm_num
  generation i := Fin.elim0 i

def single : Policy spec ([]++[event]) := empty.append event generation

def twice : Policy spec (([]++[event])++[event]) := single.append event generation

theorem single_weight (o : Occurrence tangents) : single.weight seed o = weight o := by
  classical
  rcases o with ⟨⟨i,j⟩,ho⟩
  change single.slotWeight i j = if j=0 then 500 else 0
  fin_cases i
  · rfl
  · change (single.generation (newIndex [] event)).rowWeight j = _
    rw [show single = empty.append event generation from rfl,
      Policy.append_generation_new,Generation.transport_weight]
    rw [Generation.rowWeight_success _ (by rfl)]
    fin_cases j <;> norm_num [generation,certificate]

theorem single_minimum : IsMinimizer softMaster (cost (single.weight seed)) chosen := by
  have he : single.weight seed = weight := funext single_weight
  rw [he]
  exact chosen_minimum

/-- Nonzero selected generation certificate, derived global coverage and an actual
optimizer; after another append the original certificate and weight survive. -/
theorem nonvacuity :
    generation.certificate (by rfl) = certificate ∧
    (generation.certificate (by rfl)).lambda 0 = (1/2:ℝ) ∧
    generation.rowWeight 0 = 500 ∧
    IsMinimizer softMaster (cost (single.weight seed)) chosen ∧
    (∀ o : Occurrence tangents,
      twice.weight seed (occurrenceInjection seed ([]++[event]) event o) = single.weight seed o) ∧
    (let K := (single.generation (newIndex [] event)).certificate (by simp [event])
     GlobalSupportedCoverage K (OAExec.family spec seed ([]++[event])) (single.weight seed)
       (nonlinearSupport K spec.nonlinear)
       (currentOccurrence (OAExec.eventHistory spec analytic seed ([]++[event])
         (single.validHistory (Set.mem_univ _)) (newIndex [] event)) K)) := by
  refine ⟨rfl,?_,?_,single_minimum,?_,?_⟩
  · norm_num [generation,certificate]
  · rw [Generation.rowWeight_success _ (by rfl)]
    norm_num [generation,certificate]
  · intro o
    exact single.append_weight event generation seed o
  · exact single.event_global_coverage analytic seed (Set.mem_univ _) (newIndex [] event) (by simp [event])



/-- The policy-level availability theorem is actually invoked before and after a
repeat append; this is derived attainment, not an assumed chosen optimizer. -/
theorem derived_availability :
    (∃ z, IsMinimizer (historyMaster spec seed ([]++[event])) (cost (single.weight seed)) z) ∧
    (∃ z, IsMinimizer (historyMaster spec seed (([]++[event])++[event])) (cost (twice.weight seed)) z) := by
  constructor
  · exact (single.successful_master_available analytic seed (Set.mem_univ _)
      (newIndex [] event) (by simp [event])).2.2
  · exact (twice.successful_master_available analytic seed (Set.mem_univ _)
      (oldIndex ([]++[event]) event (newIndex [] event)) (by rw [get_oldIndex,get_newIndex]; rfl)).2.2

end Chapter03.OASoftMaster.StoredPolicy.Control
