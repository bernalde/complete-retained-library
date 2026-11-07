module

public import AppendixAChimeraFourData
public import AppendixAChimeraShoreBudget

@[expose] public section

/-! Finite selector plan only: no repaired branches or embedding conclusion. -/
noncomputable section
namespace AppendixAChimeraFour
open AppendixAChimera
attribute [local instance] Classical.propDecidable

theorem rowSample_canonical (D : Sample4) (r : Bool) : Canonical (rowSample D r) :=
  fun e he => rowSample_selected_canonical D r e he

def rowComponent (D : Sample4) (r : Bool) (x : Cell) : Component (rowSample D r) :=
  componentLabel (rowSample D r) x (by simp)

theorem mem_rowComponent (D : Sample4) (r : Bool) (x : Cell) :
    x ∈ (rowComponent D r x).val := by
  exact Finset.mem_filter.mpr ⟨by simp, Relation.ReflTransGen.refl⟩

theorem rowComponent_eq (D : Sample4) (r : Bool) (x : Cell)
    (C : Component (rowSample D r)) (hx : x ∈ C.val) : rowComponent D r x = C :=
  component_eq_of_shared _ _ _ (mem_rowComponent D r x) hx

def BadRow (D : Sample4) (r : Bool) : Prop :=
  ∃ C : Component (rowSample D r), (aShore (rowSample D r) C).card = 3

theorem bad_component_unique (D : Sample4) (r : Bool)
    (C K : Component (rowSample D r))
    (hc : (aShore (rowSample D r) C).card = 3)
    (hk : (aShore (rowSample D r) K).card = 3) : C = K :=
  multiA_unique _ (rowSample_canonical D r) (rowSample_selected_card D r)
    C K (by omega) (by omega)

/-- A drop is removed from its original donor. A transfer moves that physical
vertex into the opposite original component containing its vertical mate.
Paired nontransferred drops omit both physical vertices; they do not swap them. -/
structure RepairPlan (D : Sample4) where
  drop : Bool → Option Cell
  transfer : Bool → Bool
  drop_none_iff : ∀ r, drop r = none ↔ ¬ BadRow D r
  drop_bad : ∀ r x, drop r = some x →
    x.1 = false ∧ (aShore (rowSample D r) (rowComponent D r x)).card = 3
  transfer_valid : ∀ r, transfer r = true → ∃ x, drop r = some x ∧
    (keptA (rowSample D (!r)) (rowComponent D (!r) x)).card ≤ 2 ∧
    x ∈ keptA (rowSample D (!r)) (rowComponent D (!r) x)
  paired_drop : ∀ r x, drop r = some x → transfer r = false →
    drop (!r) = some x ∧ transfer (!r) = false ∧
    ∃ y, y ≠ x ∧ y ∈ aShore (rowSample D r) (rowComponent D r x) ∧
      y ∈ aShore (rowSample D (!r)) (rowComponent D (!r) x)

theorem RepairPlan.bad_eq_donor (D : Sample4) (P : RepairPlan D) (r : Bool)
    (C : Component (rowSample D r))
    (hc : (aShore (rowSample D r) C).card = 3) :
    ∃ x, P.drop r = some x ∧ C = rowComponent D r x := by
  have hn : P.drop r ≠ none := by
    intro h
    exact (P.drop_none_iff r).mp h ⟨C,hc⟩
  cases he : P.drop r with
  | none => exact (hn he).elim
  | some x => exact ⟨x,rfl,bad_component_unique D r C _ hc (P.drop_bad r x he).2⟩

theorem RepairPlan.receiver_not_bad (D : Sample4) (P : RepairPlan D) (r : Bool)
    (h : P.transfer r = true) (x : Cell) (hx : P.drop r = some x)
    (C : Component (rowSample D (!r)))
    (hc : (aShore (rowSample D (!r)) C).card = 3) :
    rowComponent D (!r) x ≠ C := by
  rcases P.transfer_valid r h with ⟨y,hy,hsmall,_⟩
  have hxy : y = x := Option.some.inj (hy.symm.trans hx)
  subst y
  intro he
  rw [he] at hsmall
  have hbig := keptA_card_of_multiA (rowSample D (!r)) C (by omega)
  omega

theorem aIndices_mem_as_cell (E : Sample) (C : Component E) (i : Fin 4) :
    i ∈ aIndices E C ↔ (false,i) ∈ aShore E C := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨⟨s,j⟩,hx,he⟩
    have hs : s = false := ((mem_aShore E C (s,j)).mp hx).2
    subst s
    change j = i at he
    subst j
    exact hx
  · intro h
    exact Finset.mem_image.mpr ⟨(false,i),h,rfl⟩

/-- The four-index premise supplies two distinct shared A vertices. -/
theorem two_three_A_common_pair (E G : Sample) (C : Component E) (K : Component G)
    (hc : (aShore E C).card = 3) (hk : (aShore G K).card = 3) :
    ∃ x y : Cell, x ≠ y ∧ x ∈ aShore E C ∧ x ∈ aShore G K ∧
      y ∈ aShore E C ∧ y ∈ aShore G K := by
  have hC : (aIndices E C).card = 3 := (aIndices_card E C).trans hc
  have hK : (aIndices G K).card = 3 := (aIndices_card G K).trans hk
  have hu : (aIndices E C ∪ aIndices G K).card ≤ 4 := by
    have h := Finset.card_le_card (Finset.subset_univ (aIndices E C ∪ aIndices G K))
    simpa using h
  have hi := Finset.card_union_add_card_inter (aIndices E C) (aIndices G K)
  have htwo : 1 < (aIndices E C ∩ aIndices G K).card := by omega
  rcases Finset.one_lt_card.mp htwo with ⟨i,hi,j,hj,hne⟩
  rcases Finset.mem_inter.mp hi with ⟨hiC,hiK⟩
  rcases Finset.mem_inter.mp hj with ⟨hjC,hjK⟩
  exact ⟨(false,i),(false,j),fun h => hne (congrArg Prod.snd h),
    (aIndices_mem_as_cell E C i).mp hiC, (aIndices_mem_as_cell G K i).mp hiK,
    (aIndices_mem_as_cell E C j).mp hjC, (aIndices_mem_as_cell G K j).mp hjK⟩

theorem RepairPlan.other_row_of_ne {r s : Bool} (h : s ≠ r) : s = !r := by
  cases r <;> cases s <;> simp_all

def noBadPlan (D : Sample4) (h0 : ¬ BadRow D false) (h1 : ¬ BadRow D true) :
    RepairPlan D where
  drop := fun _ => none
  transfer := fun _ => false
  drop_none_iff := by intro r; cases r <;> simp [h0,h1]
  drop_bad := by simp
  transfer_valid := by simp
  paired_drop := by simp

def oneBadPlan (D : Sample4) (r : Bool) (C : Component (rowSample D r))
    (hc : (aShore (rowSample D r) C).card = 3) (hno : ¬ BadRow D (!r))
    (x : Cell) (hx : x ∈ aShore (rowSample D r) C)
    (hsmall : (keptA (rowSample D (!r)) (rowComponent D (!r) x)).card ≤ 2)
    (hkept : x ∈ keptA (rowSample D (!r)) (rowComponent D (!r) x)) :
    RepairPlan D where
  drop := fun s => if s = r then some x else none
  transfer := fun s => if s = r then true else false
  drop_none_iff := by
    intro s
    by_cases hs : s = r
    · subst s
      simp only [ite_true, reduceCtorEq, false_iff, not_not]
      exact ⟨C,hc⟩
    · have he := RepairPlan.other_row_of_ne hs
      simp only [hs, ite_false, true_iff]
      simpa [he] using hno
  drop_bad := by
    intro s z hz
    by_cases hs : s = r
    · subst s
      have he : x = z := Option.some.inj (by simpa using hz)
      subst z
      refine ⟨((mem_aShore _ C x).mp hx).2,?_⟩
      rw [rowComponent_eq D r x C ((mem_aShore _ C x).mp hx).1]
      exact hc
    · simp [hs] at hz
  transfer_valid := by
    intro s ht
    by_cases hs : s = r
    · subst s
      exact ⟨x,by simp,hsmall,hkept⟩
    · simp [hs] at ht
  paired_drop := by
    intro s z hz ht
    by_cases hs : s = r
    · simp [hs] at ht
    · simp [hs] at hz

def pairedBadPlan (D : Sample4) (x y : Cell) (hne : y ≠ x)
    (h0 : x.1 = false ∧
      (aShore (rowSample D false) (rowComponent D false x)).card = 3)
    (h1 : x.1 = false ∧
      (aShore (rowSample D true) (rowComponent D true x)).card = 3)
    (hy0 : y ∈ aShore (rowSample D false) (rowComponent D false x))
    (hy1 : y ∈ aShore (rowSample D true) (rowComponent D true x)) : RepairPlan D where
  drop := fun _ => some x
  transfer := fun _ => false
  drop_none_iff := by
    intro r
    simp only [reduceCtorEq, false_iff, not_not]
    cases r
    · exact ⟨rowComponent D false x,h0.2⟩
    · exact ⟨rowComponent D true x,h1.2⟩
  drop_bad := by
    intro r z hz
    have he : x = z := Option.some.inj hz
    subst z
    cases r
    · exact h0
    · exact h1
  transfer_valid := by simp
  paired_drop := by
    intro r z hz _
    have he : x = z := Option.some.inj hz
    subst z
    refine ⟨rfl,rfl,y,hne,?_⟩
    cases r
    · exact ⟨hy0,hy1⟩
    · exact ⟨hy1,hy0⟩

theorem repairPlan_one_bad (D : Sample4) (r : Bool)
    (hbad : BadRow D r) (hno : ¬ BadRow D (!r)) : Nonempty (RepairPlan D) := by
  rcases hbad with ⟨C,hc⟩
  have hnot : ∀ K : Component (rowSample D (!r)),
      (aShore (rowSample D (!r)) K).card ≠ 3 := by
    intro K hK
    exact hno ⟨K,hK⟩
  rcases exists_small_opposite_receiver (rowSample D r) (rowSample D (!r)) C hc
    (rowSample_canonical D (!r)) (rowSample_selected_card D (!r)) hnot
    (rowSample_U D (!r)) with ⟨x,hx,K,hxK,hsmall,hkept⟩
  have he := rowComponent_eq D (!r) x K hxK
  exact ⟨oneBadPlan D r C hc hno x hx (by simpa [he] using hsmall)
    (by simpa [he] using hkept)⟩

theorem repairPlan_both_bad (D : Sample4)
    (h0 : BadRow D false) (h1 : BadRow D true) : Nonempty (RepairPlan D) := by
  rcases h0 with ⟨C,hC⟩
  rcases h1 with ⟨K,hK⟩
  rcases two_three_A_common_pair (rowSample D false) (rowSample D true) C K hC hK with
    ⟨x,y,hne,hxC,hxK,hyC,hyK⟩
  have heC := rowComponent_eq D false x C ((mem_aShore _ C x).mp hxC).1
  have heK := rowComponent_eq D true x K ((mem_aShore _ K x).mp hxK).1
  exact ⟨pairedBadPlan D x y hne.symm
    ⟨((mem_aShore _ C x).mp hxC).2,by simpa [heC] using hC⟩
    ⟨((mem_aShore _ K x).mp hxK).2,by simpa [heK] using hK⟩
    (by simpa [heC] using hyC) (by simpa [heK] using hyK)⟩

theorem exists_repairPlan (D : Sample4) : Nonempty (RepairPlan D) := by
  by_cases h0 : BadRow D false
  · by_cases h1 : BadRow D true
    · exact repairPlan_both_bad D h0 h1
    · exact repairPlan_one_bad D false h0 h1
  · by_cases h1 : BadRow D true
    · exact repairPlan_one_bad D true h1 h0
    · exact ⟨noBadPlan D h0 h1⟩

def repairPlan (D : Sample4) : RepairPlan D := Classical.choice (exists_repairPlan D)

end AppendixAChimeraFour

-- Complete explicit types and bounded transitive-axiom diagnostics.
set_option pp.all true
set_option pp.deepTerms true
#check AppendixAChimeraFour.rowSample_canonical
#print axioms AppendixAChimeraFour.rowSample_canonical
#check AppendixAChimeraFour.rowComponent
#print axioms AppendixAChimeraFour.rowComponent
#check AppendixAChimeraFour.mem_rowComponent
#print axioms AppendixAChimeraFour.mem_rowComponent
#check AppendixAChimeraFour.rowComponent_eq
#print axioms AppendixAChimeraFour.rowComponent_eq
#check AppendixAChimeraFour.BadRow
#print axioms AppendixAChimeraFour.BadRow
#check AppendixAChimeraFour.bad_component_unique
#print axioms AppendixAChimeraFour.bad_component_unique
#check AppendixAChimeraFour.RepairPlan
#print axioms AppendixAChimeraFour.RepairPlan
#check AppendixAChimeraFour.RepairPlan.bad_eq_donor
#print axioms AppendixAChimeraFour.RepairPlan.bad_eq_donor
#check AppendixAChimeraFour.RepairPlan.receiver_not_bad
#print axioms AppendixAChimeraFour.RepairPlan.receiver_not_bad
#check AppendixAChimeraFour.aIndices_mem_as_cell
#print axioms AppendixAChimeraFour.aIndices_mem_as_cell
#check AppendixAChimeraFour.two_three_A_common_pair
#print axioms AppendixAChimeraFour.two_three_A_common_pair
#check AppendixAChimeraFour.RepairPlan.other_row_of_ne
#print axioms AppendixAChimeraFour.RepairPlan.other_row_of_ne
#check AppendixAChimeraFour.noBadPlan
#print axioms AppendixAChimeraFour.noBadPlan
#check AppendixAChimeraFour.oneBadPlan
#print axioms AppendixAChimeraFour.oneBadPlan
#check AppendixAChimeraFour.pairedBadPlan
#print axioms AppendixAChimeraFour.pairedBadPlan
#check AppendixAChimeraFour.repairPlan_one_bad
#print axioms AppendixAChimeraFour.repairPlan_one_bad
#check AppendixAChimeraFour.repairPlan_both_bad
#print axioms AppendixAChimeraFour.repairPlan_both_bad
#check AppendixAChimeraFour.exists_repairPlan
#print axioms AppendixAChimeraFour.exists_repairPlan
#check AppendixAChimeraFour.repairPlan
#print axioms AppendixAChimeraFour.repairPlan
#check AppendixAChimeraFour.RepairPlan.drop
#print axioms AppendixAChimeraFour.RepairPlan.drop
#check AppendixAChimeraFour.RepairPlan.transfer
#print axioms AppendixAChimeraFour.RepairPlan.transfer
#check AppendixAChimeraFour.RepairPlan.drop_none_iff
#print axioms AppendixAChimeraFour.RepairPlan.drop_none_iff
#check AppendixAChimeraFour.RepairPlan.drop_bad
#print axioms AppendixAChimeraFour.RepairPlan.drop_bad
#check AppendixAChimeraFour.RepairPlan.transfer_valid
#print axioms AppendixAChimeraFour.RepairPlan.transfer_valid
#check AppendixAChimeraFour.RepairPlan.paired_drop
#print axioms AppendixAChimeraFour.RepairPlan.paired_drop
