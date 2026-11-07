module

public import Chapter10ArcRank

@[expose] public section

/-! Constructive finite path decomposition for partial successor/predecessor
maps. The inverse laws and strict rank are established from the literal rows
in the arc adapter; they are not substitutes for those rows. -/
noncomputable section
namespace Chapter10.Routing.FinitePaths

variable {n : ℕ}

inductive Suffix (next : Fin n → Option (Fin n)) : Fin n → List (Fin n) → Prop
  | last {i} : next i = none → Suffix next i [i]
  | step {i j l} : next i = some j → Suffix next j l → Suffix next i (i :: l)

namespace Suffix
variable {next : Fin n → Option (Fin n)}

theorem contains_start {i l} (h : Suffix next i l) : i ∈ l := by
  cases h <;> simp

theorem nonempty {i l} (h : Suffix next i l) : l ≠ [] := by
  cases h <;> simp

theorem unique {i l} (h : Suffix next i l) {m} (g : Suffix next i m) : l = m := by
  induction h generalizing m with
  | last hi =>
    cases g with
    | last => rfl
    | step hg _ => simp_all
  | step hi ht ih =>
    cases g with
    | last hg => simp_all
    | step hg gt =>
      have hj := Option.some.inj (hi.symm.trans hg)
      subst hj
      exact congrArg (List.cons _) (ih gt)

theorem successor_mem {i l} (h : Suffix next i l) {a b} (ha : a ∈ l)
    (hab : next a = some b) : b ∈ l := by
  induction h with
  | last hi =>
    simp only [List.mem_singleton] at ha
    subst ha
    simp_all
  | step hi ht ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst h
      have heq := Option.some.inj (hi.symm.trans hab)
      subst heq
      exact List.mem_cons_of_mem _ ht.contains_start
    · exact List.mem_cons_of_mem _ (ih h)

theorem start_or_predecessor {i l} (h : Suffix next i l) {a} (ha : a ∈ l) :
    a = i ∨ ∃ p ∈ l, next p = some a := by
  induction h with
  | last hi => exact Or.inl (List.mem_singleton.mp ha)
  | @step i j l hi ht ih =>
    rcases List.mem_cons.mp ha with h | h
    · exact Or.inl h
    · rcases ih h with h | ⟨p,hp,hpa⟩
      · subst h
        exact Or.inr ⟨i,by simp,hi⟩
      · exact Or.inr ⟨p,List.mem_cons_of_mem _ hp,hpa⟩

theorem rank_lower (r : Fin n → ℕ) (hr : ∀ i j, next i = some j → r i < r j)
    {i l} (h : Suffix next i l) {a} (ha : a ∈ l) : r i ≤ r a := by
  induction h with
  | last hi =>
    have heq := List.mem_singleton.mp ha
    subst heq
    exact le_rfl
  | step hi ht ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst h; exact le_rfl
    · exact le_trans (Nat.le_of_lt (hr _ _ hi)) (ih h)

theorem nodup (r : Fin n → ℕ) (hr : ∀ i j, next i = some j → r i < r j)
    {i l} (h : Suffix next i l) : l.Nodup := by
  induction h with
  | last => simp
  | @step i j l hi ht ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hm
    have hle := ht.rank_lower r hr hm
    have hlt := hr i j hi
    omega
end Suffix

theorem suffix_exists (next : Fin n → Option (Fin n)) (r : Fin n → ℕ)
    (hr : ∀ i j, next i = some j → r i < r j) (i : Fin n) : ∃ l, Suffix next i l := by
  let B := Finset.univ.sup r
  have hb : ∀ a, r a ≤ B := fun a => Finset.le_sup (f := r) (Finset.mem_univ a)
  suffices ∀ q a, B - r a = q → ∃ l, Suffix next a l by exact this _ i rfl
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro a hq
    cases he : next a with
    | none => exact ⟨[a], Suffix.last he⟩
    | some b =>
      have hlt : B - r b < q := by have := hr a b he; have := hb b; omega
      obtain ⟨l,hl⟩ := ih _ hlt b rfl
      exact ⟨a::l, Suffix.step he hl⟩

def trace (next : Fin n → Option (Fin n)) (r : Fin n → ℕ)
    (hr : ∀ i j, next i = some j → r i < r j) (i : Fin n) : List (Fin n) :=
  Classical.choose (suffix_exists next r hr i)

theorem trace_spec (next : Fin n → Option (Fin n)) (r : Fin n → ℕ)
    (hr : ∀ i j, next i = some j → r i < r j) (i : Fin n) :
    Suffix next i (trace next r hr i) := Classical.choose_spec (suffix_exists next r hr i)

/-- Every customer belongs to exactly one nonempty elementary trace whose first
customer has no customer predecessor. No vehicle-count conclusion is built in. -/
theorem unique_root_cover (next prev : Fin n → Option (Fin n)) (r : Fin n → ℕ)
    (hr : ∀ i j, next i = some j → r i < r j)
    (hnp : ∀ i j, next i = some j → prev j = some i)
    (hpn : ∀ i j, prev j = some i → next i = some j) (i : Fin n) :
    ∃! a, prev a = none ∧ i ∈ trace next r hr a := by
  suffices ∀ q i, r i = q → ∃! a, prev a = none ∧ i ∈ trace next r hr a by exact this _ i rfl
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro i hqi
    cases hp : prev i with
    | none =>
      refine ⟨i,⟨hp,(trace_spec next r hr i).contains_start⟩,?_⟩
      rintro a ⟨ha,hia⟩
      rcases (trace_spec next r hr a).start_or_predecessor hia with heq | ⟨p,_,hpi⟩
      · exact heq.symm
      · have := hnp p i hpi
        simp [hp] at this
    | some p =>
      have hpi := hpn p i hp
      have hlt : r p < q := by simpa [hqi] using hr p i hpi
      obtain ⟨a,⟨ha,hpa⟩,hua⟩ := ih _ hlt p rfl
      refine ⟨a,⟨ha,(trace_spec next r hr a).successor_mem hpa hpi⟩,?_⟩
      rintro b ⟨hb,hib⟩
      apply hua b
      refine ⟨hb,?_⟩
      rcases (trace_spec next r hr b).start_or_predecessor hib with heq | ⟨c,hcb,hci⟩
      · subst heq
        simp [hb] at hp
      · have hc : c = p := Option.some.inj ((hnp c i hci).symm.trans hp)
        simpa [hc] using hcb

end Chapter10.Routing.FinitePaths
