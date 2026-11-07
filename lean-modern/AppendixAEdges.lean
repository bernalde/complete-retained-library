module

public import AppendixAAssignment

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AppendixATheory

abbrev OrientedEdge (n : ℕ) := (Fin n × Fin n) × Bool

def edgeOptions {n : ℕ} (E : Finset (Fin n × Fin n)) : Finset (OrientedEdge n) :=
  E.product Finset.univ

def firstEnd {n : ℕ} (x : OrientedEdge n) : Fin n := if x.2 then x.1.2 else x.1.1
def secondEnd {n : ℕ} (x : OrientedEdge n) : Fin n := if x.2 then x.1.1 else x.1.2

@[simp] theorem mem_edgeOptions {n : ℕ} (E : Finset (Fin n × Fin n))
    (e : Fin n × Fin n) (o : Bool) : (e,o) ∈ edgeOptions E ↔ e ∈ E := by
  simp [edgeOptions]

theorem option_adjacent {n : ℕ} (E : Finset (Fin n × Fin n))
    (x : OrientedEdge n) (hx : x ∈ edgeOptions E) :
    AppendixA.adjacent E (firstEnd x) (secondEnd x) := by
  rcases x with ⟨⟨a,b⟩,o⟩
  simp only [mem_edgeOptions] at hx
  cases o <;> simp [firstEnd, secondEnd, AppendixA.adjacent, hx]

def OrientedCoverage {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) : Prop :=
  ∀ l ∈ L, ∃ x ∈ edgeOptions E, A (firstEnd x) l.1 = true ∧ A (secondEnd x) l.2 = true

theorem edgeCoverage_iff_oriented {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) :
    EdgeCoverage E L A ↔ OrientedCoverage E L A := by
  constructor
  · intro h l hl
    obtain ⟨a,ha,b,hb,hab⟩ := h l.1 l.2 (Or.inl hl)
    rcases hab with hab | hba
    · exact ⟨((a,b),false), by simpa using hab, by simpa [firstEnd,secondEnd] using ha,
        by simpa [firstEnd,secondEnd] using hb⟩
    · exact ⟨((b,a),true), by simpa using hba, by simpa [firstEnd,secondEnd] using ha,
        by simpa [firstEnd,secondEnd] using hb⟩
  · intro h j l hjl
    rcases hjl with hjl | hlj
    · obtain ⟨x,hx,ha,hb⟩ := h (j,l) hjl
      exact ⟨firstEnd x, (mem_fiber A _ _).mpr ha, secondEnd x,
        (mem_fiber A _ _).mpr hb, option_adjacent E x hx⟩
    · obtain ⟨x,hx,ha,hb⟩ := h (l,j) hlj
      exact ⟨secondEnd x, (mem_fiber A _ _).mpr hb, firstEnd x,
        (mem_fiber A _ _).mpr ha, AppendixA.adjacent_symmetric E (option_adjacent E x hx)⟩

theorem bit_sum_count {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Bool) :
    (∑ x ∈ s, Chapter10.bit (f x)) = ((s.filter (fun x => f x = true)).card : ℝ) := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [Chapter10.bit, Nat.cast_sum]

theorem bit_sum_ge_one_iff {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Bool) :
    (1 : ℝ) ≤ ∑ x ∈ s, Chapter10.bit (f x) ↔ ∃ x ∈ s, f x = true := by
  rw [bit_sum_count]
  have hc : (1 : ℝ) ≤ ((s.filter (fun x => f x = true)).card : ℝ) ↔
      0 < (s.filter (fun x => f x = true)).card := by
    norm_cast
  rw [hc, Finset.card_pos]
  simp only [Finset.Nonempty, Finset.mem_filter, exists_prop, and_assoc]

def ProductRows (a b g : Bool) : Prop :=
  Chapter10.bit g ≤ Chapter10.bit a ∧ Chapter10.bit g ≤ Chapter10.bit b ∧
    Chapter10.bit a + Chapter10.bit b - 1 ≤ Chapter10.bit g

theorem productRows_iff (a b g : Bool) : ProductRows a b g ↔ g = (a && b) := by
  cases a <;> cases b <;> cases g <;> norm_num [ProductRows, Chapter10.bit]

abbrev EdgeAux (n m : ℕ) := (Fin m × Fin m) → OrientedEdge n → Bool

def DeltaRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) (D : EdgeAux n m) : Prop :=
  (∀ l ∈ L, ∀ x ∈ edgeOptions E,
    ProductRows (A (firstEnd x) l.1) (A (secondEnd x) l.2) (D l x)) ∧
  ∀ l ∈ L, (1 : ℝ) ≤ ∑ x ∈ edgeOptions E, Chapter10.bit (D l x)

theorem delta_projection {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) :
    (∃ D, DeltaRows E L A D) ↔ EdgeCoverage E L A := by
  rw [edgeCoverage_iff_oriented]
  constructor
  · rintro ⟨D,hprod,hcover⟩ l hl
    obtain ⟨x,hx,hd⟩ := (bit_sum_ge_one_iff _ _).mp (hcover l hl)
    have hp := (productRows_iff _ _ _).mp (hprod l hl x hx)
    exact ⟨x,hx,by simpa [hd] using hp.symm⟩
  · intro h
    refine ⟨fun l x => A (firstEnd x) l.1 && A (secondEnd x) l.2, ?_, ?_⟩
    · intro l hl x hx
      exact (productRows_iff _ _ _).mpr rfl
    · intro l hl
      obtain ⟨x,hx,ha,hb⟩ := h l hl
      exact (bit_sum_ge_one_iff _ _).mpr ⟨x,hx,by simp [ha,hb]⟩

theorem oriented_sum_literal {n m : ℕ} (E : Finset (Fin n × Fin n))
    (D : EdgeAux n m) (l : Fin m × Fin m) :
    (∑ x ∈ edgeOptions E, Chapter10.bit (D l x)) =
      ∑ e ∈ E, (Chapter10.bit (D l (e,false)) + Chapter10.bit (D l (e,true))) := by
  simp [edgeOptions, Finset.sum_product, Fintype.sum_bool, add_comm]

def SelectedEdgeRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) (Z : EdgeAux n m) : Prop :=
  ∀ l ∈ L, (∑ x ∈ edgeOptions E, Chapter10.bit (Z l x)) = 1 ∧
    ∀ x ∈ edgeOptions E,
      Chapter10.bit (Z l x) ≤ Chapter10.bit (A (firstEnd x) l.1) ∧
      Chapter10.bit (Z l x) ≤ Chapter10.bit (A (secondEnd x) l.2)

theorem selected_edge_projection {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (A : Alpha n m) :
    (∃ Z, SelectedEdgeRows E L A Z) ↔ EdgeCoverage E L A := by
  classical
  rw [edgeCoverage_iff_oriented]
  constructor
  · rintro ⟨Z,h⟩ l hl
    obtain ⟨x,hx,hz⟩ := (bit_sum_ge_one_iff _ _).mp (by rw [(h l hl).1])
    have hr := (h l hl).2 x hx
    refine ⟨x,hx,?_,?_⟩
    · cases ha : A (firstEnd x) l.1 <;> norm_num [Chapter10.bit, hz, ha] at hr
      all_goals rfl
    · cases hb : A (secondEnd x) l.2 <;> norm_num [Chapter10.bit, hz, hb] at hr
      all_goals rfl
  · intro h
    let Z : EdgeAux n m := fun l x =>
      if hl : l ∈ L then decide (x = Classical.choose (h l hl)) else false
    refine ⟨Z, ?_⟩
    intro l hl
    have hw := Classical.choose_spec (h l hl)
    refine ⟨?_, ?_⟩
    · simp [Z, hl, Chapter10.bit, hw.1]
    · intro x hx
      by_cases heq : x = Classical.choose (h l hl)
      · subst x
        simp [Z,hl,Chapter10.bit,hw.2.1,hw.2.2]
      · simp only [Z, dif_pos hl, heq, decide_false, Chapter10.bit, Bool.false_eq_true, if_false]
        constructor <;> split_ifs <;> norm_num

end AppendixATheory

#print axioms AppendixATheory.edgeCoverage_iff_oriented
#print axioms AppendixATheory.delta_projection
#print axioms AppendixATheory.selected_edge_projection
#print axioms AppendixATheory.oriented_sum_literal
