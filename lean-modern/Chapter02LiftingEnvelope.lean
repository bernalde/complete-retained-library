module

public import Chapter02Lifting
public import Chapter02PSCEnvelope
public import Mathlib.Tactic

@[expose] public section

/-! Free shared heights and finite nonempty component support lists. These
algebraic rows are not presumed to be derivatives; the OA module supplies that
separate analytic interface. No maximum of an empty family is defined. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

def liftingSupportSet {X I : Type*} {p : ℕ} (D : Set X)
    (row : Fin p → I → X → ℝ) (H : Fin p → List I) (b : ℝ) :
    Set (X × RealVector p) :=
  {z | z.1 ∈ D ∧ (∀ j, pscEnvelopeRows (row j) (H j) z.1 (z.2 j)) ∧
    ∑ j, z.2 j ≤ b}

theorem lifting_envelope_attained {X I : Type*} (row : I → X → ℝ)
    (first : I) (tail : List I) (x : X) :
    ∃ i ∈ first :: tail, pscEnvelope row first tail x = row i x := by
  induction tail with
  | nil => exact ⟨first,by simp,rfl⟩
  | cons i tail ih =>
    obtain ⟨j,hj,heq⟩ := ih
    change ∃ k ∈ first :: i :: tail,
      max (row i x) (pscEnvelope row first tail x) = row k x
    by_cases h : row i x ≤ pscEnvelope row first tail x
    · exact ⟨j,by simp only [List.mem_cons] at hj ⊢; tauto,by rw [max_eq_right h,heq]⟩
    · exact ⟨i,by simp,max_eq_left (le_of_not_ge h)⟩

theorem lifting_support_projection {X I : Type*} {p : ℕ} (D : Set X)
    (row : Fin p → I → X → ℝ) (first : Fin p → I) (tail : Fin p → List I)
    (b : ℝ) (x : X) :
    (∃ y, (x,y) ∈ liftingSupportSet D row (fun j => first j :: tail j) b) ↔
      x ∈ D ∧ (∑ j, pscEnvelope (row j) (first j) (tail j) x) ≤ b := by
  constructor
  · rintro ⟨y,hx,hy,hb⟩
    exact ⟨hx,(Finset.sum_le_sum fun j _ =>
      (psc_envelope_le_iff (row j) (first j) (tail j) x (y j)).mpr (hy j)).trans hb⟩
  · rintro ⟨hx,hb⟩
    refine ⟨fun j => pscEnvelope (row j) (first j) (tail j) x,hx,?_,hb⟩
    intro j
    exact (psc_envelope_le_iff (row j) (first j) (tail j) x _).mp le_rfl

theorem lifting_envelope_mixed_choices {X I : Type*} {p : ℕ}
    (row : Fin p → I → X → ℝ) (first : Fin p → I) (tail : Fin p → List I)
    (b : ℝ) (x : X) :
    (∑ j, pscEnvelope (row j) (first j) (tail j) x) ≤ b ↔
      ∀ choice : Fin p → I, (∀ j, choice j ∈ first j :: tail j) →
        (∑ j, row j (choice j) x) ≤ b := by
  constructor
  · intro hb choice hc
    apply le_trans (Finset.sum_le_sum fun j _ => ?_) hb
    exact (psc_envelope_le_iff (row j) (first j) (tail j) x _).mp le_rfl
      (choice j) (hc j)
  · intro hall
    choose choice hc he using fun j => lifting_envelope_attained (row j) (first j) (tail j) x
    simpa only [he] using hall choice hc

theorem lifting_support_mixed_projection {X I : Type*} {p : ℕ} (D : Set X)
    (row : Fin p → I → X → ℝ) (first : Fin p → I) (tail : Fin p → List I)
    (b : ℝ) (x : X) :
    (∃ y, (x,y) ∈ liftingSupportSet D row (fun j => first j :: tail j) b) ↔
      x ∈ D ∧ ∀ choice : Fin p → I, (∀ j, choice j ∈ first j :: tail j) →
        (∑ j, row j (choice j) x) ≤ b := by
  rw [lifting_support_projection,lifting_envelope_mixed_choices]

def liftingIndependentSupportSet {X : Type*} {p k : ℕ} (D : Set X)
    (row : Fin k → Fin p → X → ℝ) (b : Fin k → ℝ) :
    Set (X × (Fin k → RealVector p)) :=
  {z | z.1 ∈ D ∧ ∀ a, (∀ j, row a j z.1 ≤ z.2 a j) ∧ ∑ j, z.2 a j ≤ b a}

theorem lifting_independent_projection {X : Type*} {p k : ℕ} (D : Set X)
    (row : Fin k → Fin p → X → ℝ) (b : Fin k → ℝ) (x : X) :
    (∃ y, (x,y) ∈ liftingIndependentSupportSet D row b) ↔
      x ∈ D ∧ ∀ a, (∑ j, row a j x) ≤ b a := by
  constructor
  · rintro ⟨y,hx,hy⟩
    exact ⟨hx,fun a => (Finset.sum_le_sum fun j _ => (hy a).1 j).trans (hy a).2⟩
  · rintro ⟨hx,hb⟩
    exact ⟨fun a j => row a j x,hx,fun a => ⟨fun _ => le_rfl,hb a⟩⟩

theorem lifting_single_support_projection {X I : Type*} {p : ℕ} (D : Set X)
    (row : Fin p → I → X → ℝ) (first : Fin p → I) (b : ℝ) (x : X) :
    (∃ y, (x,y) ∈ liftingSupportSet D row (fun j => [first j]) b) ↔
      x ∈ D ∧ (∑ j, row j (first j) x) ≤ b := by
  simpa only [pscEnvelope,pscEnvelopeTail] using
    lifting_support_projection D row first (fun _ => []) b x

theorem lifting_identical_support_projection {X I : Type*} {p : ℕ} (D : Set X)
    (row : Fin p → I → X → ℝ) (first : Fin p → I) (tail : Fin p → List I)
    (v : Fin p → X → ℝ) (he : ∀ j, ∀ i ∈ first j :: tail j, row j i = v j)
    (b : ℝ) (x : X) :
    (∃ y, (x,y) ∈ liftingSupportSet D row (fun j => first j :: tail j) b) ↔
      x ∈ D ∧ (∑ j, v j x) ≤ b := by
  rw [lifting_support_projection]
  have henv : ∀ j, pscEnvelope (row j) (first j) (tail j) x = v j x := by
    intro j
    obtain ⟨i,hi,hei⟩ := lifting_envelope_attained (row j) (first j) (tail j) x
    rw [hei,he j i hi]
  simp only [henv]

theorem lifting_zero_components {X I : Type*} (D : Set X)
    (row : Fin 0 → I → X → ℝ) (H : Fin 0 → List I) (b : ℝ) (x : X) :
    (∃ y, (x,y) ∈ liftingSupportSet D row H b) ↔ x ∈ D ∧ 0 ≤ b := by
  simp [liftingSupportSet]

/-- A genuinely unconstrained component height absorbs the budget. The zero
floor below constructs witnesses for other finite rows; it is not max(empty). -/
theorem lifting_empty_component_projection {X I : Type*} {p : ℕ} (D : Set X)
    (row : Fin p → I → X → ℝ) (H : Fin p → List I) (j₀ : Fin p)
    (hempty : H j₀ = []) (b : ℝ) (x : X) :
    (∃ y, (x,y) ∈ liftingSupportSet D row H b) ↔ x ∈ D := by
  constructor
  · rintro ⟨y,hy⟩; exact hy.1
  · intro hx
    let v : RealVector p := fun j => pscEnvelopeTail (row j) (H j) (fun _ => 0) x
    let y := Function.update v j₀ (b - ∑ j ∈ Finset.univ.erase j₀, v j)
    refine ⟨y,hx,?_,?_⟩
    · intro j
      by_cases hj : j = j₀
      · subst j; rw [hempty]; exact psc_envelope_rows_nil _ _ _
      · have hy : y j = v j := Function.update_of_ne hj _ _
        change pscEnvelopeRows (row j) (H j) x (y j)
        rw [hy]
        exact ((psc_envelope_tail_le_iff (row j) (H j) (fun _ => 0) x (v j)).mp le_rfl).2
    · dsimp [y]
      rw [Finset.sum_update_of_mem (Finset.mem_univ j₀)]
      simp [Finset.sdiff_singleton_eq_erase]

end Chapter02

#print axioms Chapter02.lifting_envelope_attained
#print axioms Chapter02.lifting_support_projection
#print axioms Chapter02.lifting_envelope_mixed_choices
#print axioms Chapter02.lifting_support_mixed_projection
#print axioms Chapter02.lifting_independent_projection
#print axioms Chapter02.lifting_single_support_projection
#print axioms Chapter02.lifting_identical_support_projection
#print axioms Chapter02.lifting_zero_components
#print axioms Chapter02.lifting_empty_component_projection
