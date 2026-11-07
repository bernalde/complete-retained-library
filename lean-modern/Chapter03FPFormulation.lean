module

public import Chapter03

@[expose] public section

/-! Candidate assembled exact formulations for the repaired Chapter 3 pump.
The binary upper bounds in `AbsLift` are retained; this is not an epigraph lift.
No algorithm or source-adapter correctness is asserted by this module alone. -/
noncomputable section
open scoped BigOperators
namespace Chapter03.FPFormulation

/-- Literal l1 displacement of integer coordinates, not the Pi supremum norm. -/
def l1Distance {N : ℕ} (y c : Fin N → ℝ) : ℝ := ∑ i, |y i - c i|

/-- Exact equality lift in every coordinate, including both binary upper bounds. -/
def AbsVector {N : ℕ} (lo hi c y w : Fin N → ℝ) (v : Fin N → Bool) : Prop :=
  ∀ i, Chapter03.AbsLift (lo i) (hi i) (c i) (y i) (w i) (v i)

/-- Bounds are explicit; no compactness or feasibility oracle is a parameter. -/
def InBox {N : ℕ} (lo hi y : Fin N → ℝ) : Prop := ∀ i, lo i ≤ y i ∧ y i ≤ hi i

theorem absVector_sound {N : ℕ} {lo hi c y w : Fin N → ℝ} {v : Fin N → Bool}
    (h : AbsVector lo hi c y w v) : w = fun i => |y i - c i| := by
  funext i
  exact Chapter03.general_abs_lift_sound (h i)

theorem absVector_complete {N : ℕ} {lo hi c y : Fin N → ℝ}
    (h : InBox lo hi y) : ∃ v, AbsVector lo hi c y (fun i => |y i - c i|) v := by
  classical
  choose v hv using fun i => Chapter03.general_abs_lift_complete (h i).1 (h i).2 (c := c i)
  exact ⟨v, hv⟩

theorem absVector_projection_iff {N : ℕ} (lo hi c y w : Fin N → ℝ) :
    (∃ v, AbsVector lo hi c y w v) ↔ InBox lo hi y ∧ w = fun i => |y i - c i| := by
  constructor
  · rintro ⟨v,h⟩
    exact ⟨fun i => ⟨(h i).1,(h i).2.1⟩,absVector_sound h⟩
  · rintro ⟨h,rfl⟩
    exact absVector_complete h

/-- Projecting all auxiliary variables gives precisely the bounded l1 exclusion. -/
theorem lifted_nogood_projection_iff {N : ℕ} (lo hi c y : Fin N → ℝ) :
    (∃ w v, AbsVector lo hi c y w v ∧ 1 ≤ ∑ i, w i) ↔
      InBox lo hi y ∧ 1 ≤ l1Distance y c := by
  constructor
  · rintro ⟨w,v,h,hs⟩
    have hw := absVector_sound h
    refine ⟨fun i => ⟨(h i).1,(h i).2.1⟩,?_⟩
    simpa [l1Distance,hw] using hs
  · rintro ⟨h,hs⟩
    obtain ⟨v,hv⟩ := absVector_complete (c := c) h
    exact ⟨fun i => |y i-c i|,v,hv,hs⟩

theorem integer_l1_nogood_iff {N : ℕ} (y c : Fin N → ℤ) :
    1 ≤ l1Distance (fun i => (y i : ℝ)) (fun i => (c i : ℝ)) ↔ y ≠ c := by
  classical
  constructor
  · intro h he
    subst y
    norm_num [l1Distance] at h
  · intro h
    have hex : ∃ i, y i ≠ c i := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hex
    have hz : 1 ≤ |y i - c i| := by
      have hn : y i-c i ≠ 0 := sub_ne_zero.mpr hi
      have hp : 0 < |y i-c i| := abs_pos.mpr hn
      omega
    have hr : (1:ℝ) ≤ |(y i:ℝ)-(c i:ℝ)| := by
      exact_mod_cast hz
    have hl := Finset.single_le_sum (fun j _ => abs_nonneg ((y j:ℝ)-(c j:ℝ))) (Finset.mem_univ i)
    exact le_trans hr hl

/-- Full two-way source-coordinate projection, with actual binary auxiliaries. -/
theorem integer_lifted_nogood_iff {N : ℕ} (lo hi : Fin N → ℝ) (y c : Fin N → ℤ) :
    (∃ w v, AbsVector lo hi (fun i => (c i:ℝ)) (fun i => (y i:ℝ)) w v ∧
      1 ≤ ∑ i, w i) ↔ InBox lo hi (fun i => (y i:ℝ)) ∧ y ≠ c := by
  rw [lifted_nogood_projection_iff, integer_l1_nogood_iff]

/-- The literal appendix three-sum row; a fixed coordinate may lie in both
endpoint subsets, but both endpoint contributions are zero. -/
def endpointRow {N : ℕ} (lo hi c y w : Fin N → ℝ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => c i = lo i), (y i-lo i)) +
  (∑ i ∈ Finset.univ.filter (fun i => c i = hi i), (hi i-y i)) +
  (∑ i ∈ Finset.univ.filter (fun i => c i ≠ lo i ∧ c i ≠ hi i), w i)

/-- Only genuinely interior coordinates require the binary equality lift. -/
def InteriorAbsVector {N : ℕ} (lo hi c y w : Fin N → ℝ)
    (v : Fin N → Bool) : Prop :=
  ∀ i, c i ≠ lo i ∧ c i ≠ hi i →
    Chapter03.AbsLift (lo i) (hi i) (c i) (y i) (w i) (v i)

theorem endpointRow_eq_l1 {N : ℕ} {lo hi c y w : Fin N → ℝ} {v : Fin N → Bool}
    (hy : InBox lo hi y) (h : InteriorAbsVector lo hi c y w v) :
    endpointRow lo hi c y w = l1Distance y c := by
  classical
  simp only [endpointRow,Finset.sum_filter,l1Distance]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hcL : c i = lo i
  · have hnot : ¬ (c i ≠ lo i ∧ c i ≠ hi i) := fun hh => hh.1 hcL
    by_cases hcU : c i = hi i
    · have hyc : y i = c i := by
        rcases hy i with ⟨hl,hu⟩
        apply le_antisymm <;> linarith
      have hlz : y i-lo i=0 := by linarith
      have huz : hi i-y i=0 := by linarith
      have haz : |y i-c i|=0 := by rw [hyc]; simp
      simp only [if_pos hcL,if_pos hcU,if_neg hnot,hlz,huz,haz,add_zero]
    · have ha := Chapter03.lower_endpoint_abs (lo i) (c i) (y i) (hy i).1 hcL
      simpa only [if_pos hcL,if_neg hcU,if_neg hnot,add_zero] using ha.symm
  · by_cases hcU : c i = hi i
    · have hnot : ¬ (c i ≠ lo i ∧ c i ≠ hi i) := fun hh => hh.2 hcU
      have ha := Chapter03.upper_endpoint_abs (hi i) (c i) (y i) (hy i).2 hcU
      simpa only [if_neg hcL,if_pos hcU,if_neg hnot,zero_add,add_zero] using ha.symm
    · have hw := Chapter03.general_abs_lift_sound (h i ⟨hcL,hcU⟩)
      simpa only [if_neg hcL,if_neg hcU,if_pos (And.intro hcL hcU),zero_add] using hw

/-- Exact projection identity for the source endpoint/interior presentation. -/
theorem source_lifted_nogood_projection_iff {N : ℕ} (lo hi c y : Fin N → ℝ) :
    (InBox lo hi y ∧ ∃ w v, InteriorAbsVector lo hi c y w v ∧
      1 ≤ endpointRow lo hi c y w) ↔ InBox lo hi y ∧ 1 ≤ l1Distance y c := by
  constructor
  · rintro ⟨hy,w,v,h,hs⟩
    exact ⟨hy,(endpointRow_eq_l1 hy h) ▸ hs⟩
  · rintro ⟨hy,hs⟩
    obtain ⟨v,hv⟩ := absVector_complete (c := c) hy
    have hh : InteriorAbsVector lo hi c y (fun i => |y i-c i|) v := fun i _ => hv i
    refine ⟨hy,fun i => |y i-c i|,v,hh,?_⟩
    rwa [endpointRow_eq_l1 hy hh]

theorem source_integer_lifted_nogood_iff {N : ℕ} (lo hi : Fin N → ℝ)
    (y c : Fin N → ℤ) :
    (InBox lo hi (fun i => (y i:ℝ)) ∧ ∃ w v,
      InteriorAbsVector lo hi (fun i => (c i:ℝ)) (fun i => (y i:ℝ)) w v ∧
      1 ≤ endpointRow lo hi (fun i => (c i:ℝ)) (fun i => (y i:ℝ)) w) ↔
      InBox lo hi (fun i => (y i:ℝ)) ∧ y ≠ c := by
  rw [source_lifted_nogood_projection_iff,integer_l1_nogood_iff]

/-- The repaired binary row has a PLUS between its lower and upper subsets. -/
def binaryPlusRow {N : ℕ} (y c : Fin N → Bool) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => c i = false), Chapter03.bit (y i)) +
  (∑ i ∈ Finset.univ.filter (fun i => c i = true), (1 - Chapter03.bit (y i)))

theorem binaryPlusRow_eq_row {N : ℕ} (y c : Fin N → Bool) :
    binaryPlusRow y c = Chapter03.binaryRow y c := by
  classical
  simp only [binaryPlusRow,Finset.sum_filter,Chapter03.binaryRow]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hc : c i <;> simp [hc]

theorem binaryPlusRow_eq_l1 {N : ℕ} (y c : Fin N → Bool) :
    binaryPlusRow y c = l1Distance (fun i => Chapter03.bit (y i))
      (fun i => Chapter03.bit (c i)) := by
  rw [binaryPlusRow_eq_row,← Chapter03.binary_repaired_row]
  rfl

theorem binaryPlusRow_nogood_iff {N : ℕ} (y c : Fin N → Bool) :
    1 ≤ binaryPlusRow y c ↔ y ≠ c := by
  rw [binaryPlusRow_eq_row,Chapter03.binary_nogood_iff]

/-- A fixed coordinate contributes zero, even though both endpoint tests hold. -/
theorem fixed_coordinate_zero {a y w : ℝ} {v : Bool}
    (h : Chapter03.AbsLift a a a y w v) : y = a ∧ w = 0 := by
  have hy : y=a := le_antisymm h.2.1 h.1
  refine ⟨hy,?_⟩
  rw [Chapter03.general_abs_lift_sound h,hy]
  simp

def interiorFixedLo : Fin 2 → ℝ := ![0,4]
def interiorFixedHi : Fin 2 → ℝ := ![2,4]
def interiorFixedCenter : Fin 2 → ℤ := ![1,4]

/-- The interior center is excluded, while the fixed second coordinate stays 4. -/
theorem interior_fixed_projection (y : Fin 2 → ℤ) :
    (∃ w v, AbsVector interiorFixedLo interiorFixedHi
      (fun i => (interiorFixedCenter i:ℝ)) (fun i => (y i:ℝ)) w v ∧
      1 ≤ ∑ i, w i) ↔ (y 0 = 0 ∨ y 0 = 2) ∧ y 1 = 4 := by
  rw [integer_lifted_nogood_iff]
  constructor
  · rintro ⟨hb,hn⟩
    have h0 := hb 0
    have h1 := hb 1
    norm_num [interiorFixedLo,interiorFixedHi] at h0 h1
    have ha : 0 ≤ y 0 ∧ y 0 ≤ 2 := by exact_mod_cast h0
    have hb1 : y 1 = 4 := by exact_mod_cast (le_antisymm h1.2 h1.1)
    have hne : y 0 ≠ 1 := by
      intro he
      apply hn
      funext i
      fin_cases i <;> simp [interiorFixedCenter,he,hb1]
    exact ⟨by omega,hb1⟩
  · rintro ⟨hy,hy1⟩
    refine ⟨?_,?_⟩
    · intro i
      fin_cases i
      · rcases hy with h | h <;> norm_num [interiorFixedLo,interiorFixedHi,h]
      · norm_num [interiorFixedLo,interiorFixedHi,hy1]
    · intro he
      have hz := congrFun he (0:Fin 2)
      simp [interiorFixedCenter] at hz
      omega

theorem empty_dimension_l1 (y c : Fin 0 → ℝ) : l1Distance y c = 0 := by
  simp [l1Distance]

theorem empty_dimension_no_exclusion (lo hi c y : Fin 0 → ℝ) :
    ¬ ∃ w v, AbsVector lo hi c y w v ∧ 1 ≤ ∑ i, w i := by
  rw [lifted_nogood_projection_iff,empty_dimension_l1]
  norm_num

end Chapter03.FPFormulation


