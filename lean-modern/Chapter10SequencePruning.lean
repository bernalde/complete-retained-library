module

public import Chapter10SequenceTiming

@[expose] public section

/-! The closing-window rule is conservative: a concrete full-domain optimum
changes from 0 to 3 while the pruned feasible set remains nonempty. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Sequence.Pruning
open Chapter10.Routing

theorem pruning_depot_ne_customer {n} (i : Fin n) : (none : Node n) ≠ some i := by
  intro h; cases h
theorem pruning_customer_ne_depot {n} (i : Fin n) : (some i : Node n) ≠ none := by
  intro h; cases h
attribute [local simp] pruning_depot_ne_customer pruning_customer_ne_depot

def A : Fin 2 := 0
def B : Fin 2 := 1

def original : Data 2 where
  allowed i j := decide (i = none ∨ j = none ∨ i ≠ j)
  travel i j := if (i = some A ∧ j = some B) ∨ (i = none ∧ j = some B) then 1 else 0
  cost i j := if i = none ∧ j = some B then 3 else 0
  opening j := if j = A then 0 else 1
  closing j := if j = A then 10 else 2
  demand _ := 0
  initialLoad := 0
  capacity := 1

def pruned : Data 2 := {original with
  allowed := fun i j => original.allowed i j && !decide (i = some A ∧ j = some B)}

def ab : Slots 2 1 2 := fun _ p => if p.val = 1 then some A else if p.val = 2 then some B else none
def ba : Slots 2 1 2 := fun _ p => if p.val = 1 then some B else if p.val = 2 then some A else none

theorem ab_structure : SlotStructure original ab := by
  constructor
  · intro i; fin_cases i <;> simp only [CustomerOnce, Fin.sum_univ_succ] <;> norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, CustomerOnce, encode, ab, A, B, Fin.sum_univ_succ]
  · intro a; rfl
  · intro a; norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, ab, last]
  · intro a p; fin_cases a <;> fin_cases p <;> decide
  · intro a p hp hn
    fin_cases a <;> fin_cases p <;> norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, ab, left, right] at *

theorem ba_structure : SlotStructure pruned ba := by
  constructor
  · intro i; fin_cases i <;> simp only [CustomerOnce, Fin.sum_univ_succ] <;> norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, CustomerOnce, encode, ba, A, B, Fin.sum_univ_succ]
  · intro a; rfl
  · intro a; norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, ba, last]
  · intro a p; fin_cases a <;> fin_cases p <;> decide
  · intro a p hp hn
    fin_cases a <;> fin_cases p <;> norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, ba, left, right] at *

theorem two_orderings (D : Data 2) (q : Slots 2 1 2) (h : SlotStructure D q) :
    q = ab ∨ q = ba := by
  have h0 : q 0 0 = none := h.start_depot 0
  have h3 : q 0 (Fin.succ 2) = none := h.end_depot 0
  have h3' : q 0 3 = none := h3
  have hc0 := h.customer_once A
  have hc1 := h.customer_once B
  generalize h1 : q 0 1 = z1 at *
  generalize h2 : q 0 2 = z2 at *
  simp only [CustomerOnce, Fin.sum_univ_succ] at hc0 hc1
  fin_cases z1 <;> fin_cases z2
  all_goals norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, CustomerOnce, encode, Fin.sum_univ_succ, h0, h1, h2, h3, h3', A, B] at hc0
  all_goals norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, CustomerOnce, encode, Fin.sum_univ_succ, h0, h1, h2, h3, h3', A, B] at hc1
  · left
    funext a p
    fin_cases a <;> fin_cases p <;> simp [ab, h0, h1, h2, h3, h3', A, B]
  · right
    funext a p
    fin_cases a <;> fin_cases p <;> simp [ba, h0, h1, h2, h3, h3', A, B]

theorem original_optimum_zero :
    Literal original (encode ab) ∧ objective original (encode ab) = 0 ∧
      ∀ x : Array 2 1 2, Literal original x → 0 ≤ objective original x := by
  refine ⟨slots_to_literal ab_structure, ?_, ?_⟩
  · rw [objective_decode original ab ab_structure]
    norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, Fin.sum_univ_succ, original, ab, A, B, left, right]
  · intro x hx
    obtain ⟨q,rfl,hq⟩ := (literal_iff_decoded original x).mp hx
    rw [objective_decode original q hq]
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro p _
    dsimp [original]
    split_ifs <;> norm_num

theorem pruned_only_ba (q : Slots 2 1 2) (h : SlotStructure pruned q) : q = ba := by
  rcases two_orderings pruned q h with he | he
  · subst q
    have bad := h.allowed 0 (1 : Fin 3)
    norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, ab, pruned, original, A, B, left, right] at bad
  · exact he

theorem pruned_optimum_three :
    Literal pruned (encode ba) ∧ objective pruned (encode ba) = 3 ∧
      ∀ x : Array 2 1 2, Literal pruned x → objective pruned x = 3 := by
  have hc : objective pruned (encode ba) = 3 := by
    rw [objective_decode pruned ba ba_structure]
    norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, Fin.sum_univ_succ, pruned, original, ba, A, B, left, right]
  refine ⟨slots_to_literal ba_structure, hc, ?_⟩
  intro x hx
  obtain ⟨q,rfl,hq⟩ := (literal_iff_decoded pruned x).mp hx
  rw [pruned_only_ba q hq]
  exact hc

def abClock : Node 2 → ℝ
  | none => 0
  | some i => if i = A then 0 else 1

def baClock : Node 2 → ℝ
  | none => 0
  | some _ => 1

theorem pruning_loss_is_physically_feasible :
    LiteralTiming original (encode ab) abClock (fun _ => 1) ∧
    LiteralTiming pruned (encode ba) baClock (fun _ => 1) ∧
    original.closing A + original.travel (some A) (some B) > original.closing B := by
  refine ⟨?_, ?_, by norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, original, A, B]⟩
  · apply (literal_timing_iff_schedules original ab abClock _ ab_structure rfl
      (by norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, original])).mpr
    intro a
    fin_cases a
    change ScheduleFrom original none 0 [A,B] [0,1] 1
    norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, decode, ab, List.ofFn_succ, abClock, ScheduleFrom, original, A, B]
  · apply (literal_timing_iff_schedules pruned ba baClock _ ba_structure rfl
      (by norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, pruned, original])).mpr
    intro a
    fin_cases a
    change ScheduleFrom pruned none 0 [B,A] [1,1] 1
    norm_num [pruning_depot_ne_customer, pruning_customer_ne_depot, decode, ba, List.ofFn_succ, baClock, ScheduleFrom, pruned, original, A, B]

end Chapter10.Sequence.Pruning
