module

public import Chapter10SequenceFixed

@[expose] public section

/-! Exact witnesses for all four literal penalty families, genuine feasible
and infeasible assignments, signed costs, threshold equality, and conflicting
source fixed rows. No numerical solver is used. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.SequencePenalty.Controls
open Chapter10.Routing Chapter10.Algebra

@[simp] theorem depot_ne_customer {n : ℕ} (i : Fin n) : (none : Node n) ≠ some i := by
  intro h
  cases h
@[simp] theorem customer_ne_depot {n : ℕ} (i : Fin n) : (some i : Node n) ≠ none := by
  intro h
  cases h

def allData (n : ℕ) : Data n where
  allowed := fun _ _ => true
  travel := fun _ _ => 0
  cost := fun _ _ => 0
  opening := fun _ => 0
  closing := fun _ => 10
  demand := fun _ => 0
  initialLoad := 0
  capacity := 1

def goodSlots : Sequence.Slots 1 1 1 := fun _ p => if p = 1 then some 0 else none
def idleSlots : Sequence.Slots 1 1 1 := fun _ _ => none
def good := Sequence.encode goodSlots
def idle := Sequence.encode idleSlots
def doubledPosition : Sequence.Array 1 1 1 := fun _ p i => if i = none then 1 else if p = 1 then 1 else 0

theorem good_literal : Sequence.Literal (allData 1) good := by
  apply Sequence.slots_to_literal
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    simp only [Sequence.encode, goodSlots, Fin.sum_univ_succ]
    norm_num [Fin.ext_iff]
  · intro a
    norm_num [goodSlots, Sequence.first]
  · intro a
    norm_num [goodSlots, Sequence.last, Fin.ext_iff]
  · intro a p
    rfl
  · intro a p hp hn
    fin_cases p <;> norm_num [goodSlots, Sequence.left, Sequence.right, Fin.ext_iff] at *

theorem idle_domain : idle ∈ domain (allData 1) := by
  refine ⟨Sequence.encode_binary idleSlots,?_⟩
  constructor
  · intro a; simp [idle, Sequence.encode, idleSlots]
  · intro a; simp [idle, Sequence.encode, idleSlots]
  · intro a i; simp [idle, Sequence.encode, idleSlots]
  · intro a i; simp [idle, Sequence.encode, idleSlots]
  · intro a j h; simp [allData] at h
  · intro a j h; simp [allData] at h

theorem customer_family_control :
    customerPenalty idle = 1 ∧ positionPenalty idle = 0 ∧
      forbiddenPenalty (allData 1) idle = 0 ∧ absorbingPenalty idle = 0 := by
  simp only [customerPenalty, positionPenalty, positionTerm, forbiddenPenalty, forbiddenTerm,
    absorbingPenalty, absorbingTerm, idle, Sequence.encode, idleSlots, allData,
    Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

theorem position_family_control :
    customerPenalty doubledPosition = 0 ∧ positionPenalty doubledPosition = 1 ∧
      forbiddenPenalty (allData 1) doubledPosition = 0 ∧ absorbingPenalty doubledPosition = 0 := by
  simp only [customerPenalty, positionPenalty, positionTerm, forbiddenPenalty, forbiddenTerm,
    absorbingPenalty, absorbingTerm, doubledPosition, allData, Sequence.left, Sequence.right,
    Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

def forbiddenData : Data 2 := { allData 2 with
  allowed := fun i j => if i = some 0 ∧ j = some 1 then false else true }
def forbiddenSlots : Sequence.Slots 2 1 2 := fun _ p =>
  if p = 1 then some 0 else if p = 2 then some 1 else none
def forbiddenX := Sequence.encode forbiddenSlots

theorem forbidden_family_control :
    customerPenalty forbiddenX = 0 ∧ positionPenalty forbiddenX = 0 ∧
      forbiddenPenalty forbiddenData forbiddenX = 1 ∧ absorbingPenalty forbiddenX = 0 := by
  simp only [customerPenalty, positionPenalty, positionTerm, forbiddenPenalty, forbiddenTerm,
    absorbingPenalty, absorbingTerm, forbiddenX, Sequence.encode, forbiddenSlots,
    forbiddenData, allData, Sequence.left, Sequence.right,
    Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

def absorbingSlots : Sequence.Slots 1 1 2 := fun _ p => if p = 2 then some 0 else none
def absorbingX := Sequence.encode absorbingSlots

theorem absorbing_family_control :
    customerPenalty absorbingX = 0 ∧ positionPenalty absorbingX = 0 ∧
      forbiddenPenalty (allData 1) absorbingX = 0 ∧ absorbingPenalty absorbingX = 1 := by
  simp only [customerPenalty, positionPenalty, positionTerm, forbiddenPenalty, forbiddenTerm,
    absorbingPenalty, absorbingTerm, absorbingX, Sequence.encode, absorbingSlots,
    allData, Sequence.left, Sequence.right,
    Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

theorem threshold_equality_and_strict_control :
    printedBound (allData 1) 1 1 = 0 ∧
    energy (allData 1) 0 good = energy (allData 1) 0 idle ∧
    energy (allData 1) 1 good < energy (allData 1) 1 idle ∧
    ¬ Sequence.Literal (allData 1) idle := by
  have hg := rows_penalty_zero (allData 1) good ((literal_iff_domain_rows _ _).mp good_literal).2
  have hi : penalty (allData 1) idle = 1 := by
    rcases customer_family_control with ⟨hc,hp,hf,ha⟩
    simp [penalty,hc,hp,hf,ha]
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [printedBound, arcAbsCost, allData]
  · norm_num [energy, Sequence.objective, allData]
  · unfold energy
    rw [hg,hi]
    norm_num [Sequence.objective, allData]
  · intro h
    have hz := rows_penalty_zero (allData 1) idle ((literal_iff_domain_rows _ _).mp h).2
    linarith

def signedData : Data 1 := { allData 1 with cost := fun i j =>
  match i,j with
  | none, some _ => -1
  | some _, none => 2
  | _, _ => 0 }

theorem signed_sequence_control :
    Sequence.objective signedData good = 1 ∧ printedBound signedData 1 1 = 9 ∧
      energy signedData 10 good < energy signedData 10 idle := by
  simp only [Sequence.objective, energy, penalty, customerPenalty, positionPenalty, positionTerm,
    forbiddenPenalty, forbiddenTerm, absorbingPenalty, absorbingTerm, printedBound, arcAbsCost,
    signedData, allData, good, idle, Sequence.encode, goodSlots, idleSlots,
    Sequence.left, Sequence.right, Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

theorem inconsistent_source_fixed_domain (D : Data 0) (hdd : D.allowed none none = false) :
    (domain (v := 1) (k := 0) D) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h0 := hx.2.impossible_departure 0 none hdd
  have h1 := hx.2.end_depot 0
  change x 0 1 none = 0 at h0
  change x 0 1 none = 1 at h1
  linarith

theorem doubled_position_domain : doubledPosition ∈ domain (allData 1) := by
  refine ⟨?_,?_⟩
  · intro a p i
    by_cases hi : i = none <;> by_cases hp : p = 1 <;> simp [doubledPosition,hi,hp]
  · constructor
    · intro a; simp [doubledPosition]
    · intro a; simp [doubledPosition]
    · intro a i; norm_num [doubledPosition,Sequence.first,Fin.ext_iff]
    · intro a i; norm_num [doubledPosition,Sequence.last,Fin.ext_iff]
    · intro a i h; simp [allData] at h
    · intro a i h; simp [allData] at h

theorem forbidden_domain : forbiddenX ∈ domain forbiddenData := by
  refine ⟨Sequence.encode_binary forbiddenSlots,?_⟩
  constructor
  · intro a; norm_num [forbiddenX,Sequence.encode,forbiddenSlots,Sequence.first,Fin.ext_iff]
  · intro a; norm_num [forbiddenX,Sequence.encode,forbiddenSlots,Sequence.last,Fin.ext_iff]
  · intro a i; norm_num [forbiddenX,Sequence.encode,forbiddenSlots,Sequence.first,Fin.ext_iff]
  · intro a i; norm_num [forbiddenX,Sequence.encode,forbiddenSlots,Sequence.last,Fin.ext_iff]
  · intro a i h; simp [forbiddenData] at h
  · intro a i h; simp [forbiddenData] at h

theorem absorbing_domain : absorbingX ∈ domain (allData 1) := by
  refine ⟨Sequence.encode_binary absorbingSlots,?_⟩
  constructor
  · intro a; norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.first,Fin.ext_iff]
  · intro a; norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.last,Fin.ext_iff]
  · intro a i; norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.first,Fin.ext_iff]
  · intro a i; norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.last,Fin.ext_iff]
  · intro a i h; simp [allData] at h
  · intro a i h; simp [allData] at h

def emptyP2Slots : Sequence.Slots 0 1 0 := fun _ _ => none

theorem empty_customers_P2_feasible : Sequence.Literal (allData 0) (Sequence.encode emptyP2Slots) := by
  apply Sequence.slots_to_literal
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; exact Fin.elim0 i
  · intro a; rfl
  · intro a; rfl
  · intro a p; rfl
  · intro a p hp hn; rfl

theorem no_vehicle_infeasible_but_energy_attained (ρ : ℝ) :
    (¬ ∃ x : Sequence.Array 1 0 0, Sequence.Literal (allData 1) x) ∧
    ∃ x : Sequence.Array 1 0 0, IsMinOn (domain (allData 1)) (energy (allData 1) ρ) x := by
  constructor
  · rintro ⟨x,hx⟩
    have h := hx.customer_once 0
    norm_num [Sequence.CustomerOnce] at h
  · exact source_energy_attainment (allData 1) rfl ρ

def overlapData : Data 1 := { allData 1 with
  allowed := fun i j => if i = none ∧ j = some 0 then false else true }

theorem overlapping_families_control :
    customerPenalty absorbingX = 0 ∧ positionPenalty absorbingX = 0 ∧
    forbiddenPenalty overlapData absorbingX = 1 ∧ absorbingPenalty absorbingX = 1 ∧
    penalty overlapData absorbingX = 2 := by
  simp only [penalty, customerPenalty, positionPenalty, positionTerm, forbiddenPenalty, forbiddenTerm,
    absorbingPenalty, absorbingTerm, absorbingX, Sequence.encode, absorbingSlots,
    overlapData, allData, Sequence.left, Sequence.right,
    Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

theorem overlap_domain : absorbingX ∈ domain overlapData := by
  refine ⟨Sequence.encode_binary absorbingSlots,?_⟩
  constructor
  · intro a; norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.first,Fin.ext_iff]
  · intro a; norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.last,Fin.ext_iff]
  · intro a i; norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.first,Fin.ext_iff]
  · intro a i; norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.last,Fin.ext_iff]
  · intro a i h
    cases i with
    | none => simp [overlapData] at h
    | some j => norm_num [absorbingX,Sequence.encode,absorbingSlots,Sequence.second,Fin.ext_iff]
  · intro a i h; simp [overlapData] at h

theorem overlapping_matrix_coefficient_control :
    matrix (v := 1) (k := 2) overlapData 3 (0,1,none) (0,2,some 0) = 6 := by
  simp only [matrix, quboMatrix, diagonal, rowMatrix, objectiveMatrix, forbiddenMatrix,
    absorbingMatrix, productMatrix, transitionLeft, transitionRight, absorptionLeft,
    absorptionRight, coefficient, overlapData, allData, Sequence.left, Sequence.right,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

end Chapter10.SequencePenalty.Controls

#print axioms Chapter10.SequencePenalty.Controls.forbidden_family_control
#print axioms Chapter10.SequencePenalty.Controls.threshold_equality_and_strict_control
#print axioms Chapter10.SequencePenalty.Controls.signed_sequence_control
