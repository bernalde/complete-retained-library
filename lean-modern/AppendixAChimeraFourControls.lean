module

public import AppendixAChimeraFourBranches
public import AppendixAChimeraFourCoverage

@[expose] public section

/-! Concrete controls for the full four-cell branch construction. -/
noncomputable section
namespace AppendixAChimeraFour.FullControls
open AppendixAChimera
attribute [local instance] Classical.propDecidable

def starEdges : Finset (Cell × Cell) :=
  {((false,0),(true,0)), ((false,1),(true,0)), ((false,2),(true,0))}

def verticalEdges : Finset (Phys4 × Phys4) :=
  {((false,first (false,0)),(true,first (false,0))),
   ((false,first (false,1)),(true,first (false,1)))}

def starData (R : Finset Bool) : Sample4 where
  H := (R.biUnion (fun r => starEdges.image
    (fun e => ((r,first e.1),(r,first e.2))))) ∪ verticalEdges
  F := fun r => if r ∈ R then starEdges else ∅
  sampled_hardware := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_biUnion.mp he with ⟨r,_,he⟩
      rcases Finset.mem_image.mp he with ⟨f,hf,rfl⟩
      simp only [starEdges,Finset.mem_insert,Finset.mem_singleton] at hf
      rcases hf with rfl | rfl | rfl <;> exact Or.inl ⟨rfl,by simp [Hardware]⟩
    · simp only [verticalEdges,Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> exact Or.inr ⟨by decide,rfl,rfl⟩
  selected_canonical := by
    intro r e he
    split_ifs at he with hr
    · simp only [starEdges,Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩
    · simp at he
  selected_card := by intro r; split_ifs <;> simp [starEdges]
  selected_sampled := by
    intro r e he
    split_ifs at he with hr
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨r,hr,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩))
    · simp at he

def donor (R : Finset Bool) (r : Bool) : Component (rowSample (starData R) r) :=
  rowComponent (starData R) r (false,0)

theorem star_A_mem (R : Finset Bool) (r : Bool) (hr : r ∈ R)
    {x : Cell} (hx : x ∈ ({(false,0),(false,1),(false,2)} : Finset Cell)) :
    x ∈ aShore (rowSample (starData R) r) (donor R r) := by
  have he : (x,(true,0)) ∈ (rowSample (starData R) r).F := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rowSample_F,starData,hr,starEdges]
  have h0 : ((false,0),(true,0)) ∈ (rowSample (starData R) r).F := by
    simp [rowSample_F,starData,hr,starEdges]
  refine (mem_aShore _ _ x).mpr ⟨?_,(rowSample_canonical (starData R) r _ he).1⟩
  have hp : Relation.ReflTransGen (Adj (rowSample (starData R) r).F) (false,0) (true,0) :=
    Relation.ReflTransGen.single (Or.inl h0)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.trans (Relation.ReflTransGen.single (Or.inr he))⟩

theorem star_three_A (R : Finset Bool) (r : Bool) (hr : r ∈ R) :
    (aShore (rowSample (starData R) r) (donor R r)).card = 3 := by
  have hl := Finset.card_le_card (fun x hx => star_A_mem R r hr hx)
  have ht : ({(false,0),(false,1),(false,2)} : Finset Cell).card = 3 := by simp
  rw [ht] at hl
  have hu := aShore_card_le_three (rowSample (starData R) r)
    (rowSample_canonical (starData R) r) (rowSample_selected_card (starData R) r) (donor R r)
  omega

theorem empty_row_not_bad (R : Finset Bool) (r : Bool) (hr : r ∉ R) :
    ¬ BadRow (starData R) r := by
  rintro ⟨C,hC⟩
  have h := aShore_card_le (rowSample (starData R) r)
    (rowSample_canonical (starData R) r) C (multiA_nontrivial _ C (by omega))
  have hz : (rowSample (starData R) r).F.card = 0 := by simp [rowSample_F,starData,hr]
  rw [hz] at h
  omega

theorem empty_row_component (R : Finset Bool) (r : Bool) (hr : r ∉ R) (x : Cell) :
    (rowComponent (starData R) r x).val = {x} := by
  ext y
  constructor
  · intro hy
    have hpath : Relation.ReflTransGen (Adj (rowSample (starData R) r).F) x y :=
      (Finset.mem_filter.mp hy).2
    have hxy : x = y := by
      induction hpath with
      | refl => rfl
      | @tail b c _ hbc _ => simp [Adj,starData,hr] at hbc
    simp [hxy]
  · intro hy
    have he : y = x := Finset.mem_singleton.mp hy
    subst y
    exact mem_rowComponent (starData R) r x

theorem empty_row_kept (R : Finset Bool) (r : Bool) (hr : r ∉ R) (x : Cell) :
    keptA (rowSample (starData R) r) (rowComponent (starData R) r x) = {x} :=
  keptA_eq_singleton _ _ x (empty_row_component R r hr x)

def oneData : Sample4 := starData {false}
def bothData : Sample4 := starData Finset.univ

def onePlan : RepairPlan oneData :=
  oneBadPlan oneData false (donor {false} false)
    (star_three_A _ _ (by simp)) (empty_row_not_bad _ true (by simp)) (false,0)
    (star_A_mem _ _ (by simp) (by simp))
    (by change (keptA (rowSample (starData {false}) true) (rowComponent (starData {false}) true (false,0))).card ≤ 2
        rw [empty_row_kept _ _ (by simp)]; simp)
    (by change (false,0) ∈ keptA (rowSample (starData {false}) true) (rowComponent (starData {false}) true (false,0))
        rw [empty_row_kept _ _ (by simp)]; simp)

def bothPlan : RepairPlan bothData :=
  pairedBadPlan bothData (false,0) (false,1) (by decide)
    ⟨rfl,star_three_A _ _ (by simp)⟩ ⟨rfl,star_three_A _ _ (by simp)⟩
    (star_A_mem _ _ (by simp) (by simp)) (star_A_mem _ _ (by simp) (by simp))


def donorLabel (R : Finset Bool) (r : Bool) : Label4 (starData R) :=
  ⟨r,.inl (donor R r)⟩

theorem original_A0_fiber (R : Finset Bool) (r : Bool) :
    rowLift r (first (false,0)) ∈ originalFiber4 (starData R) (donorLabel R r) := by
  apply (originalFiber4_lift_mem_iff (starData R) r (.inl (donor R r)) _).mpr
  exact Finset.mem_image.mpr ⟨(false,0),mem_rowComponent (starData R) r (false,0),rfl⟩

theorem original_vertical_quotient (R : Finset Bool) :
    QuotientAdj4 (starData R) (donorLabel R false) (donorLabel R true) := by
  refine ⟨?_,rowLift false (first (false,0)),original_A0_fiber R false,
    rowLift true (first (false,0)),original_A0_fiber R true,?_⟩
  · intro h
    have he : false = true := congrArg Sigma.fst h
    cases he
  · exact Or.inl (Finset.mem_union_right _ (by simp [verticalEdges,rowLift]))

theorem one_plan_exact :
    onePlan.drop false = some (false,0) ∧ onePlan.transfer false = true ∧
    onePlan.drop true = none ∧ onePlan.transfer true = false := by
  simp [onePlan,oneBadPlan]

set_option backward.isDefEq.respectTransparency false in
theorem one_genuine_A_transfer :
    rowLift false (first (false,0)) ∉ finalBranch oneData onePlan (donorLabel {false} false) ∧
    rowLift false (first (false,0)) ∈ finalBranch oneData onePlan (donorLabel {false} true) := by
  constructor
  · rw [donorLabel,finalBranch_same_row,retainedLocal_first_mem,mem_retainedA]
    simp [one_plan_exact.1]
  · exact (finalBranch_incoming_iff oneData onePlan true (.inl (donor {false} true)) (false,0)).mpr
      ⟨one_plan_exact.1,one_plan_exact.2.1,rfl⟩

theorem one_transferred_vertical_witness :
    let b := pick (rowSample oneData false) (donor {false} false) true
    rowLift false (first b) ∈ finalBranch oneData onePlan (donorLabel {false} false) ∧
    rowLift false (first (false,0)) ∈ finalBranch oneData onePlan (donorLabel {false} true) ∧
    Hardware4 (rowLift false (first b)) (rowLift false (first (false,0))) := by
  dsimp only
  have hs : (pick (rowSample oneData false) (donor {false} false) true).1 = true := by
    apply picked_B_of_multiA
    have h := star_three_A {false} false (by simp)
    change 2 ≤ (aShore (rowSample (starData {false}) false) (donor {false} false)).card
    omega
  refine ⟨final_kept_B_survives oneData onePlan false _ (Finset.mem_insert_self _ _) hs,
    one_genuine_A_transfer.2,Or.inl ⟨rfl,?_⟩⟩
  simp [rowLift,Hardware,hs]

theorem one_donor_receiver_caps :
    (finalBranch oneData onePlan (donorLabel {false} false)).card ≤ 3 ∧
    (finalBranch oneData onePlan (donorLabel {false} true)).card ≤ 3 :=
  ⟨finalBranch_card_le_three _ _ _,finalBranch_card_le_three _ _ _⟩

theorem one_original_vertical_covered :
    QuotientAdj4 oneData (donorLabel {false} false) (donorLabel {false} true) ∧
    ∃ u ∈ finalBranch oneData onePlan (donorLabel {false} false),
      ∃ v ∈ finalBranch oneData onePlan (donorLabel {false} true), Hardware4 u v :=
  ⟨original_vertical_quotient {false},
    final_quotient_covered oneData onePlan (original_vertical_quotient {false})⟩

theorem both_plan_exact (r : Bool) :
    bothPlan.drop r = some (false,0) ∧ bothPlan.transfer r = false := by
  exact ⟨rfl,rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem both_A0_omitted (r : Bool) :
    rowLift r (first (false,0)) ∉ finalBranch bothData bothPlan (donorLabel Finset.univ r) := by
  rw [donorLabel,finalBranch_same_row,retainedLocal_first_mem,mem_retainedA]
  simp [(both_plan_exact r).1]

theorem both_second_vertical_witness (r : Bool) :
    rowLift r (first (false,1)) ∈ finalBranch bothData bothPlan (donorLabel Finset.univ r) := by
  have hm := (mem_aShore _ _ (false,1)).mp (star_A_mem Finset.univ r (by simp) (by simp))
  exact final_first_A_survives bothData bothPlan r _ hm.1 hm.2 (by
    rw [(both_plan_exact r).1]
    decide)

theorem both_original_vertical_covered_by_A1 :
    QuotientAdj4 bothData (donorLabel Finset.univ false) (donorLabel Finset.univ true) ∧
    rowLift false (first (false,1)) ∈ finalBranch bothData bothPlan (donorLabel Finset.univ false) ∧
    rowLift true (first (false,1)) ∈ finalBranch bothData bothPlan (donorLabel Finset.univ true) ∧
    Hardware4 (rowLift false (first (false,1))) (rowLift true (first (false,1))) :=
  ⟨original_vertical_quotient Finset.univ,both_second_vertical_witness false,
    both_second_vertical_witness true,Or.inr ⟨by decide,rfl,rfl⟩⟩

theorem both_donor_caps (r : Bool) :
    (finalBranch bothData bothPlan (donorLabel Finset.univ r)).card ≤ 3 :=
  finalBranch_card_le_three _ _ _

def uncorrectedBranches (D : Sample4) (j : Label4 D) : Finset Phys4 :=
  (baseBranch (rowSample D j.1) j.2).image (rowLift j.1)

set_option backward.isDefEq.respectTransparency false in
theorem uncorrected_donor_four :
    (uncorrectedBranches oneData (donorLabel {false} false)).card = 4 := by
  rw [uncorrectedBranches]
  dsimp only [donorLabel]
  rw [Finset.card_image_of_injective _ (rowLift_injective false)]
  change (baseBranch (rowSample oneData false) (.inl (donor {false} false))).card = 4
  rw [base_left_card,keptA_card_of_multiA _ _ (by
    have h := star_three_A {false} false (by simp)
    change 2 ≤ (aShore (rowSample (starData {false}) false) (donor {false} false)).card
    omega)]
  have h := star_three_A {false} false (by simp)
  change (aShore (rowSample (starData {false}) false) (donor {false} false)).card + 1 = 4
  omega

theorem uncorrected_cap_three_fails :
    ¬ ∀ j : Label4 oneData, (uncorrectedBranches oneData j).card ≤ 3 := by
  intro h
  have hb := h (donorLabel {false} false)
  rw [uncorrected_donor_four] at hb
  omega

end AppendixAChimeraFour.FullControls
