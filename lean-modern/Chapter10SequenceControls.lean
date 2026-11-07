module

public import Chapter10SequenceTiming
public import Chapter10RouteControls

@[expose] public section

/-! Exact source controls. These check the literal finite arrays and sums,
not just already-reduced route formulae. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Sequence.Controls
open Chapter10.Routing
open Chapter10.Routing.Controls

theorem controls_depot_ne_customer {n} (i : Fin n) : (none : Node n) ≠ some i := by
  intro h; cases h
theorem controls_customer_ne_depot {n} (i : Fin n) : (some i : Node n) ≠ none := by
  intro h; cases h
attribute [local simp] controls_depot_ne_customer controls_customer_ne_depot

def genuineSlots : Slots 2 2 3 := fun a p =>
  if a.val = 0 then if p.val = 1 then some A else if p.val = 2 then some B else none else none

def genuineClock : Node 2 → ℝ
  | none => 0
  | some i => if i = A then 2 else 5

theorem genuine_structure : SlotStructure genuine genuineSlots := by
  constructor
  · intro i
    fin_cases i <;> simp only [CustomerOnce, Fin.sum_univ_succ] <;> norm_num [controls_depot_ne_customer, controls_customer_ne_depot, CustomerOnce, encode, genuineSlots, A, B, Fin.sum_univ_succ]
  · intro a; fin_cases a <;> norm_num [controls_depot_ne_customer, controls_customer_ne_depot, genuineSlots]
  · intro a; fin_cases a <;> norm_num [controls_depot_ne_customer, controls_customer_ne_depot, genuineSlots, last]
  · intro a p
    fin_cases a <;> fin_cases p <;> decide
  · intro a p hp hn
    fin_cases a <;> fin_cases p <;> norm_num [controls_depot_ne_customer, controls_customer_ne_depot, genuineSlots, left, right] at *

theorem genuine_literal : Literal genuine (encode genuineSlots) :=
  slots_to_literal genuine_structure

theorem genuine_decoding : decode genuineSlots 0 = [A,B] ∧ decode genuineSlots 1 = [] := by
  constructor <;> rfl

theorem genuine_full_cost : objective genuine (encode genuineSlots) = 4 := by
  rw [decoded_cost genuine genuineSlots genuine_structure (by norm_num [controls_depot_ne_customer, controls_customer_ne_depot, genuine, A, B])]
  norm_num [controls_depot_ne_customer, controls_customer_ne_depot, Fin.sum_univ_succ, genuine_decoding.1, genuine_decoding.2, edgeCostFrom, genuine, A, B]

theorem genuine_full_cubic_sums :
    customerRHS genuine (encode genuineSlots) genuineClock A = 1 ∧
    customerRHS genuine (encode genuineSlots) genuineClock B = 4 ∧
    returnRHS genuine (encode genuineSlots) genuineClock 0 = 6 ∧
    returnRHS genuine (encode genuineSlots) genuineClock 1 = 0 := by
  repeat' constructor
  · rw [customer_rhs_encode genuine genuineSlots genuineClock A genuine_structure]
    norm_num [controls_depot_ne_customer, controls_customer_ne_depot, Fin.sum_univ_succ, genuineSlots, genuineClock, genuine, A, B, left, right]
  · rw [customer_rhs_encode genuine genuineSlots genuineClock B genuine_structure]
    norm_num [controls_depot_ne_customer, controls_customer_ne_depot, Fin.sum_univ_succ, genuineSlots, genuineClock, genuine, A, B, left, right]
  · rw [return_rhs_encode genuine genuineSlots genuineClock 0 genuine_structure]
    norm_num [controls_depot_ne_customer, controls_customer_ne_depot, Fin.sum_univ_succ, genuineSlots, genuineClock, genuine, A, B, left, right]
  · rw [return_rhs_encode genuine genuineSlots genuineClock 1 genuine_structure]
    norm_num [controls_depot_ne_customer, controls_customer_ne_depot, Fin.sum_univ_succ, genuineSlots, genuineClock, genuine, A, B, left, right]

theorem genuine_slack_returns : LiteralTiming genuine (encode genuineSlots) genuineClock
    (fun a => if a = 0 then 9 else 2) := by
  apply (literal_timing_iff_schedules genuine genuineSlots genuineClock _ genuine_structure
    rfl (by norm_num [controls_depot_ne_customer, controls_customer_ne_depot, genuine, A, B])).mpr
  intro a
  fin_cases a <;> norm_num [controls_depot_ne_customer, controls_customer_ne_depot, genuine_decoding.1, genuine_decoding.2, genuineClock,
    ScheduleFrom, genuine, A, B]

theorem genuine_earliest_return_pair :
    earliestReturn genuine none 0 (decode genuineSlots 0) = 6 ∧
    earliestReturn genuine none 0 (decode genuineSlots 1) = 0 := by
  rw [genuine_decoding.1, genuine_decoding.2]
  norm_num [controls_depot_ne_customer, controls_customer_ne_depot, earliestReturn, genuine, A, B]

def returnAsDepotClock (R : ℝ) : Node 2 → ℝ
  | none => R
  | some i => if i = A then 2 else 5

theorem repeated_depot_clock_full_sum (R : ℝ) :
    returnRHS genuine (encode genuineSlots) (returnAsDepotClock R) 0 = 6 + R := by
  rw [return_rhs_encode genuine genuineSlots (returnAsDepotClock R) 0 genuine_structure]
  norm_num [controls_depot_ne_customer, controls_customer_ne_depot, Fin.sum_univ_succ, genuineSlots, returnAsDepotClock, genuine, A, B, left, right]

theorem repeated_depot_clock_impossible (R : ℝ) :
    ¬ returnRHS genuine (encode genuineSlots) (returnAsDepotClock R) 0 ≤ R := by
  rw [repeated_depot_clock_full_sum]
  linarith

def idleLoop : Data 0 where
  allowed _ _ := true
  travel _ _ := 1
  cost _ _ := 0
  opening := Fin.elim0
  closing := Fin.elim0
  demand := Fin.elim0
  initialLoad := 0
  capacity := 0

def idleSlots : Slots 0 1 1 := fun _ _ => none

theorem nonzero_loop_literal_sum :
    returnRHS idleLoop (encode idleSlots) (fun _ => 0) 0 = 2 := by
  norm_num [controls_depot_ne_customer, controls_customer_ne_depot, returnRHS, idleLoop, encode, idleSlots, Fin.sum_univ_succ,
    Fintype.sum_option, left, right]
  have hd : (default : Node 0) = none := by
    cases h : (default : Node 0) with
    | none => rfl
    | some i => exact Fin.elim0 i
  norm_num [hd]

def emptySlots : Slots 0 1 0 := fun _ _ => none

theorem P2_empty_control : Literal idleLoop (encode emptySlots) ∧
    objective idleLoop (encode emptySlots) = 0 := by
  constructor
  · apply slots_to_literal
    constructor
    · intro i; exact Fin.elim0 i
    · intro a; rfl
    · intro a; rfl
    · intro a p; rfl
    · intro a p hp hn; rfl
  · norm_num [controls_depot_ne_customer, controls_customer_ne_depot, objective, idleLoop]

def solo : Data 1 where
  allowed _ _ := true
  travel i j := if i = j then 0 else 1
  cost i j := if i = none ∧ j = some 0 then -2 else if i = some 0 ∧ j = none then 1 else 0
  opening _ := 1
  closing _ := 2
  demand _ := 0
  initialLoad := 0
  capacity := 1

def soloSlots : Slots 1 1 1 := fun _ p => if p.val = 1 then some 0 else none

theorem solo_structure : SlotStructure solo soloSlots := by
  constructor
  · intro i
    fin_cases i
    simp only [CustomerOnce, Fin.sum_univ_succ]
    norm_num [encode, soloSlots]
  · intro a; rfl
  · intro a; rfl
  · intro a p; rfl
  · intro a p hp hn
    fin_cases p <;> norm_num [soloSlots, left, right] at *

theorem P3_signed_nonempty_control : Literal solo (encode soloSlots) ∧
    objective solo (encode soloSlots) = -1 ∧ decode soloSlots 0 = [0] := by
  refine ⟨slots_to_literal solo_structure, ?_, ?_⟩
  · rw [objective_decode solo soloSlots solo_structure]
    norm_num [Fin.sum_univ_succ, solo, soloSlots, left, right]
  · rfl

theorem P3_two_customers_infeasible (D : Data 2) :
    ¬ ∃ x : Array 2 1 1, Literal D x := by
  rintro ⟨x,hx⟩
  obtain ⟨q,rfl,hq⟩ := (literal_iff_decoded D x).mp hx
  obtain ⟨a,p,hp⟩ := customer_has_incoming hq A
  obtain ⟨b,r,hr⟩ := customer_has_incoming hq B
  have he : q 0 2 = none := hq.end_depot 0
  fin_cases a; fin_cases b
  fin_cases p <;> fin_cases r
  · have hh : (some A : Node 2) = some B := hp.symm.trans hr
    have hn : (A : Fin 2) ≠ B := by decide
    exact hn (Option.some.inj hh)
  · change q 0 2 = some B at hr
    rw [he] at hr
    cases hr
  · change q 0 2 = some A at hp
    rw [he] at hp
    cases hp
  · change q 0 2 = some A at hp
    rw [he] at hp
    cases hp

theorem sequence_capacity_is_separate : Literal overloaded (encode genuineSlots) ∧
    LiteralTiming overloaded (encode genuineSlots) genuineClock (fun a => if a = 0 then 9 else 2) ∧
    ¬ CapacityFeasible overloaded (decode genuineSlots 0) := by
  refine ⟨?_, ?_, ?_⟩
  · apply slots_to_literal
    exact ⟨genuine_structure.customer_once, genuine_structure.start_depot, genuine_structure.end_depot,
      genuine_structure.allowed, genuine_structure.absorbing⟩
  · exact genuine_slack_returns
  · rw [genuine_decoding.1]
    exact uncapacitated_overload_control.2

def pairSlots : Slots 3 1 3 := fun _ p =>
  if p.val = 1 then some pairA else if p.val = 2 then some pairB else
    if p.val = 3 then some pairC else none

theorem pair_structure : SlotStructure pairwise pairSlots := by
  constructor
  · intro i
    fin_cases i <;> simp only [CustomerOnce, Fin.sum_univ_succ] <;>
      norm_num [encode, pairSlots, pairA, pairB, pairC] <;> decide
  · intro a; rfl
  · intro a; rfl
  · intro a p
    fin_cases a <;> fin_cases p <;> decide
  · intro a p hp hn
    fin_cases p <;> norm_num [pairSlots, left, right] at *

theorem pairwise_source_slot_failure : Literal pairwise (encode pairSlots) ∧
    ¬ ∃ clock ret, clock none = 0 ∧ LiteralTiming pairwise (encode pairSlots) clock ret := by
  refine ⟨slots_to_literal pair_structure, ?_⟩
  rw [literal_timing_exists_iff pairwise pairSlots pair_structure (by norm_num [pairwise])]
  intro hw
  have bad := hw 0
  have hd : decode pairSlots 0 = [pairA,pairB,pairC] := by
    rfl
  rw [hd] at bad
  exact pairwise_earliest_misses_closing.2 bad

def laterCustomerClock : Node 2 → ℝ
  | none => 0
  | some i => if i = A then 3 else 5

theorem duration_optimal_customer_not_earliest :
    LiteralTiming genuine (encode genuineSlots) laterCustomerClock
      (fun a => if a = 0 then 6 else 0) ∧
    laterCustomerClock (some A) ≠ 2 ∧
    (∑ a : Fin 2, if a = 0 then (6 : ℝ) else 0) =
      ∑ a : Fin 2, earliestReturn genuine none 0 (decode genuineSlots a) := by
  refine ⟨?_, by norm_num [laterCustomerClock], ?_⟩
  · apply (literal_timing_iff_schedules genuine genuineSlots laterCustomerClock _ genuine_structure
      rfl (by norm_num [genuine, A, B])).mpr
    intro a
    fin_cases a <;> norm_num [genuine_decoding.1, genuine_decoding.2, laterCustomerClock,
      ScheduleFrom, genuine, A, B]
  · norm_num [Fin.sum_univ_succ, genuine_earliest_return_pair.1, genuine_earliest_return_pair.2]

end Chapter10.Sequence.Controls


