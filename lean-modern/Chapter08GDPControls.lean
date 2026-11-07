module

public import Chapter08GDPFormulation
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-! Nonvacuity and scope controls for the selector-preserving GDP interfaces.
The inactive Big-M domain is fixed independently as a global box. -/
noncomputable section
open scoped BigOperators
open Set
namespace Chapter08.GDP.Controls

abbrev Branch := fun _ : Fin 2 => Fin 2
abbrev SelectorIndex := Sigma Branch

def point (x : ℝ) : Vec 1 := fun _ => x

def twoRows : Vec 1 →ₗ[ℝ] Vec 2 where
  toFun x := ![x 0, -x 0]
  map_add' x z := by ext j; fin_cases j <;> simp <;> ring
  map_smul' a x := by ext j; fin_cases j <;> simp

def orthant : Set (Vec 2) := {z | ∀ j, 0 ≤ z j}

def data : ConicData (Fin 2) Branch 1 where
  dim _ _ := 2
  map _ _ := twoRows
  offset _ i := if i = 0 then ![0, -2] else ![1, -3]
  cone _ _ := orthant
  lower := point 0
  upper := point 2
  global := Set.univ

def clause : Clause SelectorIndex := ⟨{⟨0,0⟩}, {⟨1,0⟩}⟩
def clauses (_ : Unit) := clause

def good (j : SelectorIndex) : Bool := decide (j.2 = 0)
def bad (j : SelectorIndex) : Bool :=
  if j.1 = 0 then decide (j.2 = 1) else decide (j.2 = 0)
def realGood (j : SelectorIndex) : ℝ := if j.2 = 0 then 1 else 0

theorem zero_mem : ∀ k i, (0 : Vec 2) ∈ data.cone k i := by
  intro k i j
  simp [data, orthant]

theorem good_one_hot (k : Fin 2) : OneHot (fun i : Branch k => good ⟨k,i⟩) := by
  refine ⟨0, by simp [good], ?_⟩
  intro i hi
  simpa [good] using hi

theorem bad_one_hot (k : Fin 2) : OneHot (fun i : Branch k => bad ⟨k,i⟩) := by
  fin_cases k
  · refine ⟨1, by norm_num [bad], ?_⟩
    intro i hi
    simpa [bad] using hi
  · refine ⟨0, by norm_num [bad], ?_⟩
    intro i hi
    simpa [bad] using hi

theorem cross_clause_control : CNF clauses good ∧ ¬CNF clauses bad := by
  constructor
  · intro k
    exact Or.inl ⟨⟨0,0⟩, by simp [clauses, clause], by norm_num [good]⟩
  · intro h
    have hc := h ()
    norm_num [clauses, clause, Clause.Holds, bad] at hc

theorem overlapping_rows : ∀ k i,
    data.map k i (point 1) - data.offset k i ∈ data.cone k i := by
  intro k i
  change ∀ j : Fin 2, 0 ≤ twoRows (point 1) j -
    (if i = 0 then ![0,-2] else ![1,-3]) j
  intro j
  fin_cases i <;> fin_cases j <;> norm_num [twoRows, point]

theorem good_source (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    Source data clauses (point x) good := by
  refine ⟨Set.mem_univ _, (fun j => ⟨hx0,hx2⟩), cross_clause_control.1,
    good_one_hot, ?_⟩
  intro k i hi j
  have hi0 : i = 0 := by simpa [good] using hi
  subst i
  change 0 ≤ twoRows (point x) j - (![0,-2] : Vec 2) j
  fin_cases j <;> simp [twoRows, point] <;> linarith

theorem selector_preservation_control :
    Source data clauses (point 1) good ∧
    (∀ k, OneHot (fun i : Branch k => bad ⟨k,i⟩)) ∧
    (∀ k i, bad ⟨k,i⟩ = true →
      data.map k i (point 1) - data.offset k i ∈ data.cone k i) ∧
    ¬Source data clauses (point 1) bad ∧
    Hull data clauses (point 1) (fun j => bit (good j)) ∧
    ¬Hull data clauses (point 1) (fun j => bit (bad j)) := by
  have hg := good_source 1 (by norm_num) (by norm_num)
  have hb : ¬Source data clauses (point 1) bad := fun h => cross_clause_control.2 h.2.2.1
  exact ⟨hg, bad_one_hot, fun k i _ => overlapping_rows k i, hb,
    (source_hull_fixed_selector data clauses zero_mem _ _).mp hg,
    fun h => hb ((source_hull_fixed_selector data clauses zero_mem _ _).mpr h)⟩

theorem real_good_binary (j : SelectorIndex) : realGood j = 0 ∨ realGood j = 1 := by
  by_cases h : j.2 = 0 <;> simp [realGood, h]

theorem real_good_encoding : (fun j => bit (good j)) = realGood := by
  funext j
  by_cases h : j.2 = 0 <;> simp [good, realGood, bit, h]

theorem actual_decoding_control :
    (∀ j, decode (realGood j) = good j) ∧
    CNF clauses (fun j => decode (realGood j)) ∧
    Hull data clauses (point 1) realGood := by
  have hd : ∀ j, decode (realGood j) = good j := by
    intro j
    by_cases h : j.2 = 0 <;> simp [realGood, good, decode, h]
  have hh := (source_hull_fixed_selector data clauses zero_mem (point 1) good).mp
    (good_source 1 (by norm_num) (by norm_num))
  rw [real_good_encoding] at hh
  refine ⟨hd, ?_, hh⟩
  simpa only [hd] using cross_clause_control.1

def offsets (_ : Fin 2) (_ : Fin 2) : Vec 2 := ![-2,-2]

theorem offsets_valid : ValidOffsets data offsets := by
  intro x _ hx k i j
  have hlo := (hx 0).1
  have hhi := (hx 0).2
  change 0 ≤ x 0 at hlo
  change x 0 ≤ 2 at hhi
  change 0 ≤ twoRows x j - (if i = 0 then ![0,-2] else ![1,-3]) j -
    (![-2,-2] : Vec 2) j
  fin_cases i <;> fin_cases j <;>
    simp [twoRows] <;> linarith

theorem inactive_vector_control :
    realGood ⟨0,1⟩ = 0 ∧
    (fun j : Fin 2 => data.map 0 1 (point 1) j - data.offset 0 1 j -
      (1-realGood ⟨0,1⟩) * offsets 0 1 j) = ![2,4] ∧
    BigM data clauses offsets (point 1) realGood := by
  refine ⟨by norm_num [realGood], ?_, ?_⟩
  · change (fun j : Fin 2 => twoRows (point 1) j - (![1,-3] : Vec 2) j -
      (1-0) * (![-2,-2] : Vec 2) j) = ![2,4]
    ext j
    fin_cases j <;> norm_num [twoRows, point]
  · have h := (source_bigM_fixed_selector data clauses offsets offsets_valid _ _).mp
      (good_source 1 (by norm_num) (by norm_num))
    simpa only [real_good_encoding] using h

theorem inactive_row_really_disabled :
    data.map 0 1 (point 0) - data.offset 0 1 ∉ data.cone 0 1 ∧
    BigM data clauses offsets (point 0) realGood := by
  constructor
  · intro h
    have h0 := h 0
    change 0 ≤ (0:ℝ) - 1 at h0
    norm_num at h0
  · have h := (source_bigM_fixed_selector data clauses offsets offsets_valid _ _).mp
      (good_source 0 (by norm_num) (by norm_num))
    simpa only [real_good_encoding] using h

theorem decoded_selector_replay :
    Source data clauses (point 1) (fun j => decode (realGood j)) ∧
    Source data clauses (point 0) (fun j => decode (realGood j)) := by
  exact ⟨(source_hull_decoded_selector data clauses zero_mem _ realGood real_good_binary).mpr
      actual_decoding_control.2.2,
    (source_bigM_decoded_selector data clauses offsets offsets_valid _ realGood
      real_good_binary).mpr inactive_row_really_disabled.2⟩

theorem source_minimum :
    Chapter02.IsMinimizer {x | ∃ Y, Source data clauses x Y} (fun x => x 0) (point 0) := by
  refine ⟨⟨good, good_source 0 (by norm_num) (by norm_num)⟩, ?_⟩
  rintro x ⟨Y,hY⟩
  exact (hY.2.1 0).1

theorem actual_minimizer_transfer :
    Chapter02.IsMinimizer {p : Vec 1 × (SelectorIndex → ℝ) | Hull data clauses p.1 p.2}
      (fun p => p.1 0) (point 0, realGood) ∧
    Chapter02.IsMinimizer {p : Vec 1 × (SelectorIndex → ℝ) | BigM data clauses offsets p.1 p.2}
      (fun p => p.1 0) (point 0, realGood) := by
  have hs := good_source 0 (by norm_num) (by norm_num)
  have hh := (source_hull_fixed_selector data clauses zero_mem _ _).mp hs
  have hm := (source_bigM_fixed_selector data clauses offsets offsets_valid _ _).mp hs
  rw [real_good_encoding] at hh hm
  exact ⟨(hull_minimizer_iff data clauses zero_mem (fun x => x 0) (point 0,realGood)).mpr
      ⟨hh,source_minimum⟩,
    (bigM_minimizer_iff data clauses offsets offsets_valid (fun x => x 0)
      (point 0,realGood)).mpr ⟨hm,source_minimum⟩⟩

/-- The second branch is empty although its cone contains zero. -/
def emptyBranchData : ConicData (Fin 2) Branch 1 :=
  { data with offset := fun _ i => if i = 0 then ![0,-2] else ![3,0] }

theorem empty_branch_control :
    (∀ x, InBox emptyBranchData.lower emptyBranchData.upper x →
      x ∉ {x | emptyBranchData.map 0 1 x - emptyBranchData.offset 0 1 ∈
        emptyBranchData.cone 0 1}) ∧
    Source emptyBranchData clauses (point 1) good ∧
    Hull emptyBranchData clauses (point 1) (fun j => bit (good j)) := by
  have he : ∀ x, InBox emptyBranchData.lower emptyBranchData.upper x →
      x ∉ {x | emptyBranchData.map 0 1 x - emptyBranchData.offset 0 1 ∈
        emptyBranchData.cone 0 1} := by
    intro x hx hc
    have hu := (hx 0).2
    have hl := hc 0
    change x 0 ≤ 2 at hu
    change 0 ≤ x 0 - 3 at hl
    linarith
  have hs : Source emptyBranchData clauses (point 1) good := by
    refine ⟨Set.mem_univ _, (fun _ => ⟨by norm_num [emptyBranchData,data,point],
      by norm_num [emptyBranchData,data,point]⟩), cross_clause_control.1, good_one_hot, ?_⟩
    intro k i hi j
    have hi0 : i = 0 := by simpa [good] using hi
    subst i
    change 0 ≤ twoRows (point 1) j - (![0,-2] : Vec 2) j
    fin_cases j <;> norm_num [twoRows,point]
  refine ⟨he, hs, (source_hull_fixed_selector emptyBranchData clauses ?_ _ _).mp hs⟩
  intro k i j
  change (0 : ℝ) ≤ 0
  exact le_rfl

def impossibleClauses (_ : Unit) : Clause SelectorIndex := ⟨∅,∅⟩

theorem empty_clause_control :
    ¬Source data impossibleClauses (point 1) good ∧
    ¬Hull data impossibleClauses (point 1) (fun j => bit (good j)) := by
  have hs : ¬Source data impossibleClauses (point 1) good :=
    fun h => empty_clause_false good (h.2.2.1 ())
  exact ⟨hs, fun h => hs ((source_hull_fixed_selector data impossibleClauses zero_mem _ _).mpr h)⟩

def emptyClauses {ι : Type*} : Empty → Clause ι := Empty.elim

def noBranches : ConicData Unit (fun _ => Fin 0) 1 where
  dim _ i := Fin.elim0 i
  map _ i := Fin.elim0 i
  offset _ i := Fin.elim0 i
  cone _ i := Fin.elim0 i
  lower := point 0
  upper := point 1
  global := Set.univ

theorem empty_disjunction_control
    (Y : (Sigma (fun _ : Unit => Fin 0)) → Bool)
    (y : (Sigma (fun _ : Unit => Fin 0)) → ℝ) :
    ¬Source noBranches emptyClauses (point 0) Y ∧
    ¬Hull noBranches emptyClauses (point 0) y := by
  constructor
  · intro h
    obtain ⟨i,_,_⟩ := h.2.2.2.1 ()
    exact Fin.elim0 i
  · intro h
    have hz := (h.2.2.2.2 ()).1
    simp at hz

/-- No disjunctions: both the independent global domain and the box survive. -/
def noFamily : ConicData Empty (fun _ => Fin 0) 1 where
  dim k := Empty.elim k
  map k := Empty.elim k
  offset k := Empty.elim k
  cone k := Empty.elim k
  lower := point 0
  upper := point 1
  global := {x | (1:ℝ)/2 ≤ x 0}

def noFamilyOffsets (k : Empty) : (i : Fin 0) → Vec (noFamily.dim k i) := Empty.elim k

theorem empty_family_exact (x : Vec 1)
    (Y : (Sigma (fun _ : Empty => Fin 0)) → Bool)
    (y : (Sigma (fun _ : Empty => Fin 0)) → ℝ) :
    (Source noFamily emptyClauses x Y ↔ (1:ℝ)/2 ≤ x 0 ∧ InBox (point 0) (point 1) x) ∧
    (Hull noFamily emptyClauses x y ↔ (1:ℝ)/2 ≤ x 0 ∧ InBox (point 0) (point 1) x) ∧
    (BigM noFamily emptyClauses noFamilyOffsets x y ↔
      (1:ℝ)/2 ≤ x 0 ∧ InBox (point 0) (point 1) x) := by
  simp [Source,Hull,BigM,CNF,LinearCNF,noFamily]

theorem empty_family_retains_domains
    (Y : (Sigma (fun _ : Empty => Fin 0)) → Bool)
    (y : (Sigma (fun _ : Empty => Fin 0)) → ℝ) :
    Source noFamily emptyClauses (point 1) Y ∧
    Hull noFamily emptyClauses (point 1) y ∧
    BigM noFamily emptyClauses noFamilyOffsets (point 1) y ∧
    ¬Source noFamily emptyClauses (point 0) Y ∧
    ¬Hull noFamily emptyClauses (point 2) y := by
  simp only [(empty_family_exact _ Y y).1, (empty_family_exact _ Y y).2.1,
    (empty_family_exact _ Y y).2.2]
  norm_num [InBox,point]

/-- Conjunction precedes hull: per-disjunction hulls cannot be substituted. -/
def firstSet : Set ℝ := {0,2}
def secondSet : Set ℝ := {0,1}

theorem conjunction_hull_boundary :
    firstSet ∩ secondSet = {0} ∧
    convexHull ℝ (firstSet ∩ secondSet) = {0} ∧
    (1 : ℝ) ∈ convexHull ℝ firstSet ∩ convexHull ℝ secondSet ∧
    (1 : ℝ) ∉ convexHull ℝ (firstSet ∩ secondSet) := by
  have hi : firstSet ∩ secondSet = {0} := by
    ext x
    simp only [firstSet,secondSet,Set.mem_inter_iff,Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h|h,h'|h'⟩ <;> first | exact h | exact h' | linarith
    · intro h
      exact ⟨Or.inl h,Or.inl h⟩
  have hc : convexHull ℝ (firstSet ∩ secondSet) = {0} := by
    rw [hi,convexHull_singleton]
  have h0 : (0:ℝ) ∈ convexHull ℝ firstSet := subset_convexHull ℝ _ (by simp [firstSet])
  have h2 : (2:ℝ) ∈ convexHull ℝ firstSet := subset_convexHull ℝ _ (by simp [firstSet])
  have h1 := convex_convexHull ℝ firstSet h0 h2
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1:ℝ)/2+1/2=1 by norm_num)
  have ha : (1:ℝ) ∈ convexHull ℝ firstSet := by norm_num at h1; exact h1
  have hb : (1:ℝ) ∈ convexHull ℝ secondSet := subset_convexHull ℝ _ (by simp [secondSet])
  exact ⟨hi,hc,⟨ha,hb⟩,by rw [hc]; norm_num⟩

#print axioms cross_clause_control
#print axioms selector_preservation_control
#print axioms actual_decoding_control
#print axioms offsets_valid
#print axioms inactive_vector_control
#print axioms inactive_row_really_disabled
#print axioms decoded_selector_replay
#print axioms actual_minimizer_transfer
#print axioms empty_branch_control
#print axioms empty_clause_control
#print axioms empty_disjunction_control
#print axioms empty_family_exact
#print axioms empty_family_retains_domains
#print axioms conjunction_hull_boundary
end Chapter08.GDP.Controls
