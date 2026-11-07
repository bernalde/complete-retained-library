module

public import Chapter10Sequence
public import Chapter10IntegerPenalty

@[expose] public section

/-! Literal four-family penalty (10.8), retaining every fixed row in its
domain. Flattened finite products are accompanied by the source-sum identity. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.SequencePenalty
open Chapter10.Routing Chapter10.Algebra

abbrev Coord (n v k : ℕ) := Fin v × Fin (k+2) × Node n
abbrev Transition (n v k : ℕ) := Fin v × Fin (k+1) × Node n × Node n
abbrev Absorption (n v k : ℕ) := Fin v × Fin (k+1) × Fin n

def flatten {n v k} (x : Sequence.Array n v k) : Coord n v k → ℝ := fun r => x r.1 r.2.1 r.2.2
def inflate {n v k} (z : Coord n v k → ℝ) : Sequence.Array n v k := fun a p i => z (a,p,i)

theorem flatten_binary {n v k} (x : Sequence.Array n v k) (hx : Sequence.Binary x) :
    Algebra.Binary (flatten x) := fun r => hx r.1 r.2.1 r.2.2

def customerPenalty {n v k} (x : Sequence.Array n v k) : ℝ :=
  ∑ i : Fin n, ((∑ a, ∑ p, x a p (some i)) - 1)^2
def positionTerm {n v k} (x : Sequence.Array n v k) (r : Fin v × Fin (k+2)) : ℝ :=
  ((∑ i, x r.1 r.2 i) - 1)^2
def positionPenalty {n v k} (x : Sequence.Array n v k) : ℝ := ∑ r, positionTerm x r
def forbiddenTerm {n v k} (D : Data n) (x : Sequence.Array n v k) (r : Transition n v k) : ℝ :=
  if D.allowed r.2.2.1 r.2.2.2 then 0 else
    x r.1 (Sequence.left r.2.1) r.2.2.1 * x r.1 (Sequence.right r.2.1) r.2.2.2
def forbiddenPenalty {n v k} (D : Data n) (x : Sequence.Array n v k) : ℝ := ∑ r, forbiddenTerm D x r
def absorbingTerm {n v k} (x : Sequence.Array n v k) (r : Absorption n v k) : ℝ :=
  if 0 < r.2.1.val then x r.1 (Sequence.left r.2.1) none * x r.1 (Sequence.right r.2.1) (some r.2.2) else 0
def absorbingPenalty {n v k} (x : Sequence.Array n v k) : ℝ := ∑ r, absorbingTerm x r
def penalty {n v k} (D : Data n) (x : Sequence.Array n v k) : ℝ :=
  customerPenalty x + positionPenalty x + forbiddenPenalty D x + absorbingPenalty x

def Rows {n v k} (D : Data n) (x : Sequence.Array n v k) : Prop :=
  Sequence.CustomerOnce x ∧ Sequence.PositionOnce x ∧ Sequence.AllowedProducts D x ∧ Sequence.AbsorbingProducts x
def domain {n v k} (D : Data n) : Set (Sequence.Array n v k) :=
  {x | Sequence.Binary x ∧ Sequence.FixedRows D x}
def energy {n v k} (D : Data n) (ρ : ℝ) (x : Sequence.Array n v k) : ℝ :=
  Sequence.objective D x + ρ * penalty D x

theorem source_penalty_sums {n v k} (D : Data n) (x : Sequence.Array n v k) :
    penalty D x =
      (∑ i : Fin n, ((∑ a, ∑ p, x a p (some i)) - 1)^2) +
      (∑ a, ∑ p, ((∑ i, x a p i) - 1)^2) +
      (∑ a, ∑ p : Fin (k+1), ∑ i, ∑ j, if D.allowed i j then 0 else
        x a (Sequence.left p) i * x a (Sequence.right p) j) +
      (∑ a, ∑ p : Fin (k+1), ∑ j : Fin n, if 0 < p.val then
        x a (Sequence.left p) none * x a (Sequence.right p) (some j) else 0) := by
  simp only [penalty, customerPenalty, positionPenalty, positionTerm, forbiddenPenalty,
    forbiddenTerm, absorbingPenalty, absorbingTerm, Fintype.sum_prod_type]

theorem product_binary (a b : ℝ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a * b = 0 ∨ a * b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem forbidden_term_binary {n v k} (D : Data n) (x : Sequence.Array n v k)
    (hx : Sequence.Binary x) (r : Transition n v k) : forbiddenTerm D x r = 0 ∨ forbiddenTerm D x r = 1 := by
  unfold forbiddenTerm
  split_ifs
  · exact Or.inl rfl
  · exact product_binary _ _ (hx _ _ _) (hx _ _ _)

theorem absorbing_term_binary {n v k} (x : Sequence.Array n v k)
    (hx : Sequence.Binary x) (r : Absorption n v k) : absorbingTerm x r = 0 ∨ absorbingTerm x r = 1 := by
  unfold absorbingTerm
  split_ifs
  · exact product_binary _ _ (hx _ _ _) (hx _ _ _)
  · exact Or.inl rfl

theorem customer_nonneg {n v k} (x : Sequence.Array n v k) : 0 ≤ customerPenalty x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
theorem position_nonneg {n v k} (x : Sequence.Array n v k) : 0 ≤ positionPenalty x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
theorem forbidden_nonneg {n v k} (D : Data n) (x : Sequence.Array n v k) (hx : Sequence.Binary x) :
    0 ≤ forbiddenPenalty D x := by
  apply Finset.sum_nonneg
  intro r _
  rcases forbidden_term_binary D x hx r with h | h <;> simp [h]
theorem absorbing_nonneg {n v k} (x : Sequence.Array n v k) (hx : Sequence.Binary x) :
    0 ≤ absorbingPenalty x := by
  apply Finset.sum_nonneg
  intro r _
  rcases absorbing_term_binary x hx r with h | h <;> simp [h]

theorem penalty_nonnegative {n v k} (D : Data n) (x : Sequence.Array n v k) (hx : Sequence.Binary x) :
    0 ≤ penalty D x := by
  have := customer_nonneg x
  have := position_nonneg x
  have := forbidden_nonneg D x hx
  have := absorbing_nonneg x hx
  unfold penalty
  linarith

theorem binary_count_gap {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : Algebra.Binary x)
    (hn : (∑ i, x i) ≠ 1) : (1 : ℝ) ≤ ((∑ i, x i)-1)^2 := by
  have hf : ¬ integerFeasible (fun _ : Unit => fun _ : ι => (1 : ℤ)) (fun _ => (1 : ℤ)) x := by
    intro h
    have hh := h ()
    simp only [Int.cast_one, one_mul] at hh
    exact hn hh
  have h := integer_penalty_gap (fun _ : Unit => fun _ : ι => (1 : ℤ)) (fun _ => (1 : ℤ)) x hx hf
  simpa [integerPenalty, squaredResidual] using h

theorem customer_gap {n v k} (x : Sequence.Array n v k) (hx : Sequence.Binary x)
    (hn : ¬ Sequence.CustomerOnce x) : 1 ≤ customerPenalty x := by
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have hg := binary_count_gap (fun r : Fin v × Fin (k+2) => x r.1 r.2 (some i))
    (fun r => hx r.1 r.2 (some i)) (by simpa only [Fintype.sum_prod_type] using hi)
  simp only [Fintype.sum_prod_type] at hg
  exact hg.trans (Finset.single_le_sum (fun j _ => sq_nonneg ((∑ a, ∑ p, x a p (some j))-1)) (Finset.mem_univ i))

theorem position_gap {n v k} (x : Sequence.Array n v k) (hx : Sequence.Binary x)
    (hn : ¬ Sequence.PositionOnce x) : 1 ≤ positionPenalty x := by
  simp only [Sequence.PositionOnce, not_forall] at hn
  obtain ⟨a, p, hp⟩ := hn
  have hg := binary_count_gap (x a p) (hx a p) hp
  exact hg.trans (Finset.single_le_sum (fun r _ => sq_nonneg ((∑ i, x r.1 r.2 i)-1)) (Finset.mem_univ (a,p)))

theorem forbidden_gap {n v k} (D : Data n) (x : Sequence.Array n v k) (hx : Sequence.Binary x)
    (hn : ¬ Sequence.AllowedProducts D x) : 1 ≤ forbiddenPenalty D x := by
  simp only [Sequence.AllowedProducts, not_forall, Classical.not_imp_iff_and_not] at hn
  obtain ⟨a, p, i, j, ha, hp⟩ := hn
  have hne : forbiddenTerm D x (a,p,i,j) ≠ 0 := by simpa [forbiddenTerm, ha] using hp
  have he := (forbidden_term_binary D x hx (a,p,i,j)).resolve_left hne
  rw [← he]
  apply Finset.single_le_sum _ (Finset.mem_univ (a,p,i,j))
  intro r _
  rcases forbidden_term_binary D x hx r with h | h <;> simp [h]

theorem absorbing_gap {n v k} (x : Sequence.Array n v k) (hx : Sequence.Binary x)
    (hn : ¬ Sequence.AbsorbingProducts x) : 1 ≤ absorbingPenalty x := by
  simp only [Sequence.AbsorbingProducts, not_forall, Classical.not_imp_iff_and_not] at hn
  obtain ⟨a, p, j, hp, hz⟩ := hn
  have hne : absorbingTerm x (a,p,j) ≠ 0 := by simpa [absorbingTerm, hp] using hz
  have he := (absorbing_term_binary x hx (a,p,j)).resolve_left hne
  rw [← he]
  apply Finset.single_le_sum _ (Finset.mem_univ (a,p,j))
  intro r _
  rcases absorbing_term_binary x hx r with h | h <;> simp [h]

theorem rows_penalty_zero {n v k} (D : Data n) (x : Sequence.Array n v k) (h : Rows D x) :
    penalty D x = 0 := by
  rcases h with ⟨hc, hp, hf, ha⟩
  have hfor : ∀ r, forbiddenTerm D x r = 0 := by
    intro r
    cases he : D.allowed r.2.2.1 r.2.2.2 with
    | false => exact by simpa [forbiddenTerm, he] using hf r.1 r.2.1 r.2.2.1 r.2.2.2 he
    | true => simp [forbiddenTerm, he]
  have habs : ∀ r, absorbingTerm x r = 0 := by
    intro r
    by_cases hh : 0 < r.2.1.val
    · simpa [absorbingTerm, hh] using ha r.1 r.2.1 r.2.2 hh
    · simp [absorbingTerm, hh]
  simp only [Sequence.CustomerOnce] at hc
  simp only [Sequence.PositionOnce] at hp
  simp [penalty, customerPenalty, positionPenalty, positionTerm, forbiddenPenalty,
    absorbingPenalty, hc, hp, hfor, habs]

theorem penalty_gap {n v k} (D : Data n) (x : Sequence.Array n v k) (hx : Sequence.Binary x)
    (hn : ¬ Rows D x) : 1 ≤ penalty D x := by
  have hc0 := customer_nonneg x
  have hp0 := position_nonneg x
  have hf0 := forbidden_nonneg D x hx
  have ha0 := absorbing_nonneg x hx
  unfold penalty
  by_cases hc : Sequence.CustomerOnce x
  · by_cases hp : Sequence.PositionOnce x
    · by_cases hf : Sequence.AllowedProducts D x
      · have ha : ¬ Sequence.AbsorbingProducts x := fun h => hn ⟨hc,hp,hf,h⟩
        have := absorbing_gap x hx ha
        linarith
      · have := forbidden_gap D x hx hf
        linarith
    · have := position_gap x hx hp
      linarith
  · have := customer_gap x hx hc
    linarith

theorem penalty_zero_iff {n v k} (D : Data n) (x : Sequence.Array n v k) (hx : Sequence.Binary x) :
    penalty D x = 0 ↔ Rows D x := by
  constructor
  · intro hz
    by_contra hn
    have := penalty_gap D x hx hn
    linarith
  · exact rows_penalty_zero D x

theorem literal_iff_domain_rows {n v k} (D : Data n) (x : Sequence.Array n v k) :
    Sequence.Literal D x ↔ x ∈ domain D ∧ Rows D x := by
  constructor
  · intro h
    exact ⟨⟨h.binary,h.fixed⟩,h.customer_once,h.position_once,h.allowed,h.absorbing⟩
  · rintro ⟨⟨hb,hf⟩,hc,hp,ha,hab⟩
    exact ⟨hb,hc,hp,ha,hab,hf⟩

end Chapter10.SequencePenalty
