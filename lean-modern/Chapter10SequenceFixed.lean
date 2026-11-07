module

public import Chapter10SequenceMatrix
public import Chapter10FixedBits
public import Chapter10FiniteAttainment

@[expose] public section

/-! Exact source fixed-row partition. Depot-loop permission makes the one/zero
prescriptions consistent; no conflicting assignment is silently overwritten. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

def fixedOne {n v k} (r : Coord n v k) : Prop :=
  (r.2.1 = Sequence.first k ∨ r.2.1 = Sequence.last k) ∧ r.2.2 = none
def fixedZero {n v k} (D : Data n) (r : Coord n v k) : Prop :=
  ((r.2.1 = Sequence.first k ∨ r.2.1 = Sequence.last k) ∧ r.2.2 ≠ none) ∨
  (r.2.1 = Sequence.second k ∧ D.allowed none r.2.2 = false) ∨
  (r.2.1 = Sequence.penultimate k ∧ D.allowed r.2.2 none = false)
def fixedCondition {n v k} (D : Data n) (r : Coord n v k) : Prop := fixedOne r ∨ fixedZero D r
abbrev Free (n v k : ℕ) (D : Data n) := {r : Coord n v k // ¬ fixedCondition D r}
abbrev Fixed (n v k : ℕ) (D : Data n) := {r : Coord n v k // fixedCondition D r}

noncomputable def freeFintype {n v k} (D : Data n) : Fintype (Free n v k D) := Fintype.ofFinite _
noncomputable def fixedFintype {n v k} (D : Data n) : Fintype (Fixed n v k D) := Fintype.ofFinite _

attribute [instance] freeFintype fixedFintype

def splitCoordinates {n v k} (D : Data n) : Free n v k D ⊕ Fixed n v k D ≃ Coord n v k := by
  classical
  exact {
    toFun := Sum.elim Subtype.val Subtype.val
    invFun := fun r => if h : fixedCondition D r then .inr ⟨r,h⟩ else .inl ⟨r,h⟩
    left_inv := by
      intro r
      cases r with
      | inl u => simp [u.property]
      | inr f => simp [f.property]
    right_inv := by intro r; dsimp; split_ifs <;> rfl }

@[simp] theorem splitCoordinates_inl {n v k} (D : Data n) (u : Free n v k D) :
    splitCoordinates D (Sum.inl u) = u.val := rfl
@[simp] theorem splitCoordinates_inr {n v k} (D : Data n) (f : Fixed n v k D) :
    splitCoordinates D (Sum.inr f) = f.val := rfl

def fixedValues {n v k} (D : Data n) (f : Fixed n v k D) : ℝ := by
  classical
  exact if fixedOne f.val then 1 else 0

theorem fixedValues_binary {n v k} (D : Data n) : Algebra.Binary (fixedValues (v := v) (k := k) D) := by
  intro f
  classical
  unfold fixedValues
  split_ifs <;> simp

theorem fixed_one_zero_disjoint {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (r : Coord n v k) (ho : fixedOne r) : ¬ fixedZero D r := by
  intro hz
  rcases hz with ⟨_,hne⟩ | ⟨_,hd⟩ | ⟨_,hd⟩
  · exact hne ho.2
  · rw [ho.2, hdd] at hd
    contradiction
  · rw [ho.2, hdd] at hd
    contradiction

theorem fixedRows_iff_prescriptions {n v k} (D : Data n) (x : Sequence.Array n v k) :
    Sequence.FixedRows D x ↔
      (∀ r : Coord n v k, fixedOne r → flatten x r = 1) ∧
      (∀ r : Coord n v k, fixedZero D r → flatten x r = 0) := by
  constructor
  · intro h
    constructor
    · intro r hr
      rcases hr with ⟨hp,hi⟩
      rcases hp with hp | hp
      · simpa only [flatten, hp, hi] using h.start_depot r.1
      · simpa only [flatten, hp, hi] using h.end_depot r.1
    · intro r hr
      rcases hr with ⟨hp,hi⟩ | ⟨hp,ha⟩ | ⟨hp,ha⟩
      · cases hn : r.2.2 with
        | none => exact (hi hn).elim
        | some j =>
          rcases hp with hp | hp
          · simpa only [flatten, hp, hn] using h.start_customer r.1 j
          · simpa only [flatten, hp, hn] using h.end_customer r.1 j
      · simpa only [flatten, hp] using h.impossible_departure r.1 r.2.2 ha
      · simpa only [flatten, hp] using h.impossible_return r.1 r.2.2 ha
  · rintro ⟨ho,hz⟩
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro a; exact ho (a,Sequence.first k,none) ⟨Or.inl rfl,rfl⟩
    · intro a; exact ho (a,Sequence.last k,none) ⟨Or.inr rfl,rfl⟩
    · intro a i; exact hz (a,Sequence.first k,some i) (Or.inl ⟨Or.inl rfl, by simp⟩)
    · intro a i; exact hz (a,Sequence.last k,some i) (Or.inl ⟨Or.inr rfl, by simp⟩)
    · intro a j h; exact hz (a,Sequence.second k,j) (Or.inr (Or.inl ⟨rfl,h⟩))
    · intro a j h; exact hz (a,Sequence.penultimate k,j) (Or.inr (Or.inr ⟨rfl,h⟩))

def splitArray {n v k} (D : Data n) (x : Sequence.Array n v k) : Free n v k D ⊕ Fixed n v k D → ℝ :=
  fun r => flatten x (splitCoordinates D r)

theorem domain_iff_split_fixed {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (x : Sequence.Array n v k) : x ∈ domain D ↔ splitArray D x ∈ fixedDomain (fixedValues D) := by
  classical
  constructor
  · rintro ⟨hb,hf⟩
    obtain ⟨ho,hz⟩ := (fixedRows_iff_prescriptions D x).mp hf
    refine ⟨fun r => flatten_binary x hb _, ?_⟩
    intro f
    change flatten x f.val = fixedValues D f
    by_cases h : fixedOne f.val
    · simpa [fixedValues,h] using ho f.val h
    · have hz' : fixedZero D f.val := f.property.resolve_left h
      simpa [fixedValues,h] using hz f.val hz'
  · rintro ⟨hb,hf⟩
    refine ⟨?_, (fixedRows_iff_prescriptions D x).mpr ⟨?_,?_⟩⟩
    · intro a p i
      have h := hb ((splitCoordinates D).symm (a,p,i))
      simpa only [splitArray, Equiv.apply_symm_apply, flatten] using h
    · intro r ho
      have h := hf ⟨r,Or.inl ho⟩
      simpa [splitArray,fixedValues,ho] using h
    · intro r hz
      have hn : ¬ fixedOne r := fun ho => fixed_one_zero_disjoint D hdd r ho hz
      have h := hf ⟨r,Or.inr hz⟩
      simpa [splitArray,fixedValues,hn] using h

def sourceExtend {n v k} (D : Data n) (z : Free n v k D → ℝ) : Sequence.Array n v k :=
  inflate (fun r => extend (fixedValues D) z ((splitCoordinates D).symm r))
def sourceRestrict {n v k} (D : Data n) (x : Sequence.Array n v k) : Free n v k D → ℝ :=
  restrict (splitArray D x)

theorem split_sourceExtend {n v k} (D : Data n) (z : Free n v k D → ℝ) :
    splitArray D (sourceExtend D z) = extend (fixedValues D) z := by
  funext r
  simp [splitArray, sourceExtend, flatten, inflate]

theorem sourceExtend_mem_domain {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (z : Free n v k D → ℝ) (hz : Algebra.Binary z) : sourceExtend D z ∈ domain D := by
  rw [domain_iff_split_fixed D hdd, split_sourceExtend]
  exact extend_mem_fixedDomain _ (fixedValues_binary D) z hz

theorem sourceRestrict_binary {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (x : Sequence.Array n v k) (hx : x ∈ domain D) : Algebra.Binary (sourceRestrict D x) :=
  restrict_binary _ _ ((domain_iff_split_fixed D hdd x).mp hx)

theorem sourceRestrict_sourceExtend {n v k} (D : Data n) (z : Free n v k D → ℝ) :
    sourceRestrict D (sourceExtend D z) = z := by
  rw [sourceRestrict, split_sourceExtend, restrict_extend]

theorem splitArray_injective {n v k} (D : Data n) : Function.Injective (splitArray (v := v) (k := k) D) := by
  intro x y h
  funext a p i
  have hh := congrFun h ((splitCoordinates D).symm (a,p,i))
  simpa only [splitArray, Equiv.apply_symm_apply, flatten] using hh

theorem sourceExtend_sourceRestrict {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (x : Sequence.Array n v k) (hx : x ∈ domain D) : sourceExtend D (sourceRestrict D x) = x := by
  apply splitArray_injective D
  rw [split_sourceExtend]
  exact extend_restrict _ _ ((domain_iff_split_fixed D hdd x).mp hx)

def sourceFixedEquiv {n v k} (D : Data n) (hdd : D.allowed none none = true) :
    {z : Free n v k D → ℝ // Algebra.Binary z} ≃ {x : Sequence.Array n v k // x ∈ domain D} where
  toFun z := ⟨sourceExtend D z.1, sourceExtend_mem_domain D hdd z.1 z.2⟩
  invFun x := ⟨sourceRestrict D x.1, sourceRestrict_binary D hdd x.1 x.2⟩
  left_inv z := by apply Subtype.ext; exact sourceRestrict_sourceExtend D z.1
  right_inv x := by apply Subtype.ext; exact sourceExtend_sourceRestrict D hdd x.1 x.2

def splitMatrix {n v k} (D : Data n) (ρ : ℝ) :
    (Free n v k D ⊕ Fixed n v k D) → (Free n v k D ⊕ Fixed n v k D) → ℝ :=
  fun i j => matrix D ρ (splitCoordinates D i) (splitCoordinates D j)
def reducedMatrix {n v k : ℕ} (D : Data n) (ρ : ℝ) : Free n v k D → Free n v k D → ℝ :=
  fixedMatrix (splitMatrix (v := v) (k := k) D ρ) (fixedValues D)
def reducedOffset {n v k : ℕ} (D : Data n) (ρ : ℝ) : ℝ :=
  fixedOffset (splitMatrix (v := v) (k := k) D ρ) (fixedValues D)
    (ρ * ((n : ℝ) + (v : ℝ) * (k+2 : ℕ)))
def reducedEnergy {n v k} (D : Data n) (ρ : ℝ) (z : Free n v k D → ℝ) : ℝ :=
  quadratic (reducedMatrix D ρ) z + reducedOffset (v := v) (k := k) D ρ

theorem source_fixed_energy_identity {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (z : Free n v k D → ℝ) (hz : Algebra.Binary z) :
    energy D ρ (sourceExtend D z) = reducedEnergy D ρ z := by
  have hs := source_energy_matrix_identity D (sourceExtend D z) ρ (sourceExtend_mem_domain D hdd z hz).1
  have hr := quadratic_reindex (splitCoordinates D) (matrix D ρ) (flatten (sourceExtend D z))
  change quadratic (splitMatrix D ρ) (splitArray D (sourceExtend D z)) = _ at hr
  rw [split_sourceExtend] at hr
  rw [← hr] at hs
  rw [fixed_qubo_identity _ _ _ _ hz] at hs
  simpa only [reducedEnergy, reducedMatrix, reducedOffset] using hs

theorem source_fixed_min_transport {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (z : Free n v k D → ℝ) :
    IsMinOn (domain D) (energy D ρ) (sourceExtend D z) ↔
      IsMinOn {z | Algebra.Binary z} (reducedEnergy D ρ) z := by
  constructor
  · rintro ⟨hz,hm⟩
    have hb : Algebra.Binary z := by
      have h := sourceRestrict_binary D hdd _ hz
      simpa only [sourceRestrict_sourceExtend] using h
    refine ⟨hb,?_⟩
    intro w hw
    have h := hm (sourceExtend D w) (sourceExtend_mem_domain D hdd w hw)
    simpa only [source_fixed_energy_identity D hdd ρ z hb, source_fixed_energy_identity D hdd ρ w hw] using h
  · rintro ⟨hz,hm⟩
    refine ⟨sourceExtend_mem_domain D hdd z hz,?_⟩
    intro x hx
    have hb := sourceRestrict_binary D hdd x hx
    have h := hm (sourceRestrict D x) hb
    rw [← source_fixed_energy_identity D hdd ρ z hz, ← source_fixed_energy_identity D hdd ρ _ hb,
      sourceExtend_sourceRestrict D hdd x hx] at h
    exact h

theorem source_fixed_feasible_exists {n v k} (D : Data n) (hdd : D.allowed none none = true) :
    (∃ x : Sequence.Array n v k, Sequence.Literal D x) ↔
      ∃ z : Free n v k D → ℝ, Algebra.Binary z ∧ Sequence.Literal D (sourceExtend D z) := by
  constructor
  · rintro ⟨x,hx⟩
    have hd := ((literal_iff_domain_rows D x).mp hx).1
    refine ⟨sourceRestrict D x, sourceRestrict_binary D hdd x hd, ?_⟩
    simpa only [sourceExtend_sourceRestrict D hdd x hd] using hx
  · rintro ⟨z,_,hz⟩
    exact ⟨sourceExtend D z,hz⟩

theorem reduced_minimizers_exact {n v k} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) (hρ : printedBound D v k < ρ) (z : Free n v k D → ℝ) :
    (IsMinOn {z | Algebra.Binary z} (reducedEnergy D ρ) z ∧
      ∃ w : Free n v k D → ℝ, Algebra.Binary w ∧ Sequence.Literal D (sourceExtend D w)) ↔
      IsMinOn {x | Sequence.Literal D x} (Sequence.objective D) (sourceExtend D z) := by
  rw [← source_fixed_min_transport D hdd, ← source_fixed_feasible_exists D hdd]
  exact minimizers_exact D ρ hρ (sourceExtend D z)

theorem source_energy_attainment {n v k : ℕ} (D : Data n) (hdd : D.allowed none none = true)
    (ρ : ℝ) : ∃ x : Sequence.Array n v k, IsMinOn (domain D) (energy D ρ) x := by
  have hn : ({z : Free n v k D → ℝ | Algebra.Binary z} : Set (Free n v k D → ℝ)).Nonempty :=
    ⟨fun _ => 0, fun _ => Or.inl rfl⟩
  obtain ⟨z,hz⟩ := real_binary_domain_attainment {z : Free n v k D → ℝ | Algebra.Binary z}
    (fun _ h => h) hn (reducedEnergy D ρ)
  exact ⟨sourceExtend D z, (source_fixed_min_transport D hdd ρ z).mpr hz⟩

end Chapter10.SequencePenalty

#print axioms Chapter10.SequencePenalty.sourceFixedEquiv
#print axioms Chapter10.SequencePenalty.source_fixed_energy_identity
#print axioms Chapter10.SequencePenalty.source_fixed_min_transport
#print axioms Chapter10.SequencePenalty.reduced_minimizers_exact
