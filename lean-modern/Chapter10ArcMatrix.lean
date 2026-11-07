module

public import Chapter10ArcRows

@[expose] public section

/-! The literal integer matrix for (10.3). A fixed-zero row combines the four
possible reasons for fixing one coordinate; flow coefficients subtract in ℤ,
so a self-loop contributes zero rather than two independent coefficients. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing.Arc
open Chapter10.Routing

abbrev Row (n k : ℕ) := Sum (Fin n) (Sum (Fin n × Fin k) (Edge n k))

def edgeValid {n k} (D : Data n) (T : Grid k) (e : Edge n k) : Prop :=
  inWindow D e.2.1 (T.time e.2.2) ∧ inWindow D e.1.1 (T.time e.1.2) ∧
    D.allowed e.1.1 e.2.1 = true ∧ T.time e.1.2 + D.travel e.1.1 e.2.1 ≤ T.time e.2.2

noncomputable def edgeValidDecision {n k} (D : Data n) (T : Grid k) (e : Edge n k) : Decidable (edgeValid D T e) :=
  Classical.propDecidable _

attribute [local instance] edgeValidDecision

def rowMatrix {n k} (D : Data n) (T : Grid k) : Row n k → Edge n k → ℤ := by
  classical
  exact fun r e => match r with
  | .inl i => if e.2.1 = some i then 1 else 0
  | .inr (.inl q) => (if e.2 = (some q.1,q.2) then 1 else 0) -
      (if e.1 = (some q.1,q.2) then 1 else 0)
  | .inr (.inr f) => if edgeValid D T f then 0 else if e = f then 1 else 0

def rowRhs {n k} : Row n k → ℤ
  | .inl _ => 1
  | .inr _ => 0

def rowValue {n k} (D : Data n) (T : Grid k) (x : Assignment n k) (r : Row n k) : ℝ :=
  ∑ e, (rowMatrix D T r e : ℝ) * Chapter10.bit (x e)

def MatrixFeasible {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  ∀ r, rowValue D T x r = (rowRhs r : ℝ)

theorem row_visit {n k} (D : Data n) (T : Grid k) (x : Assignment n k) (i : Fin n) :
    rowValue D T x (.inl i) = displayedSum x (fun e => e.2.1 = some i) := by
  unfold rowValue rowMatrix displayedSum
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all

theorem row_flow {n k} (D : Data n) (T : Grid k) (x : Assignment n k)
    (i : Fin n) (s : Fin k) :
    rowValue D T x (.inr (.inl (i,s))) = displayedSum x (fun e => e.2 = (some i,s)) -
      displayedSum x (fun e => e.1 = (some i,s)) := by
  unfold rowValue rowMatrix displayedSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all

theorem flow_self_cancellation {n k} (D : Data n) (T : Grid k) (i : Fin n) (s : Fin k) :
    rowMatrix D T (.inr (.inl (i,s))) ((some i,s),(some i,s)) = 0 := by
  simp [rowMatrix]

theorem row_fixed {n k} (D : Data n) (T : Grid k) (x : Assignment n k) (f : Edge n k) :
    rowValue D T x (.inr (.inr f)) = if edgeValid D T f then 0 else Chapter10.bit (x f) := by
  classical
  simp only [rowValue, rowMatrix]
  split_ifs with h
  · simp
  · simp [ite_mul]

theorem matrix_iff_literal {n k} (D : Data n) (T : Grid k) (x : Assignment n k) :
    MatrixFeasible D T x ↔ Literal D T x := by
  classical
  rw [literal_iff_feasible]
  constructor
  · intro hm
    have hv : Visit x := by
      intro i
      have h := hm (.inl i)
      rw [row_visit, displayedSum_eq_card] at h
      simpa [arrivals, rowRhs] using h
    have hf : Flow x := by
      intro i s
      have h := hm (.inr (.inl (i,s)))
      rw [row_flow] at h
      have h' := sub_eq_zero.mp (show displayedSum x (fun e => e.2 = (some i,s)) -
        displayedSum x (fun e => e.1 = (some i,s)) = 0 by simpa [rowRhs] using h)
      simpa [displayedSum_eq_card, incoming, outgoing] using h'
    have hg : ∀ e, x e = true → edgeValid D T e := by
      intro e hx
      have h := hm (.inr (.inr e))
      rw [row_fixed] at h
      by_contra hn
      simp [hn, hx, rowRhs, Chapter10.bit] at h
    exact ⟨hv,hf,fun e he => (hg e he).1,fun e he => (hg e he).2.1,
      fun e he => (hg e he).2.2.1,fun e he => (hg e he).2.2.2⟩
  · rintro ⟨hv,hf,ha,hd,hp,ht⟩ r
    rcases r with i | q
    · rw [row_visit, displayedSum_eq_card]
      simpa [rowRhs, arrivals] using congrArg (fun z : ℕ => (z : ℝ)) (hv i)
    · rcases q with ⟨i,s⟩ | e
      · rw [row_flow]
        have h := congrArg (fun z : ℕ => (z : ℝ)) (hf i s)
        have h' : displayedSum x (fun e => e.2 = (some i,s)) =
            displayedSum x (fun e => e.1 = (some i,s)) := by
          simpa [displayedSum_eq_card, incoming, outgoing] using h
        simp [h', rowRhs]
      · rw [row_fixed]
        by_cases he : x e = true
        · have hg : edgeValid D T e := ⟨ha e he,hd e he,hp e he,ht e he⟩
          simp [hg,rowRhs]
        · simp [Chapter10.bit, he, rowRhs]

theorem matrix_iff_feasible {n k} (D : Data n) (T : Grid k) (x : Assignment n k) :
    MatrixFeasible D T x ↔ Feasible D T x :=
  (matrix_iff_literal D T x).trans (literal_iff_feasible D T x)

/-- Flattened costs include every time-indexed copy of each node-pair cost. -/
def coordinateCost {n k} (D : Data n) (e : Edge n k) : ℝ := D.cost e.1.1 e.2.1

theorem actual_objective_flattened {n k} (D : Data n) (x : Assignment n k) :
    objective D x = ∑ e, coordinateCost D e * Chapter10.bit (x e) := rfl

end Chapter10.Routing.Arc
