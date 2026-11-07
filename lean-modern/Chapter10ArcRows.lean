module

public import Chapter10RoutingData

@[expose] public section

/-! Literal Boolean encoding of (10.3), with both real displayed rows and finite
edge counts. The nonnegative distinct grid is an explicit physical convention.
No fleet, load, acyclicity or desired path decomposition is hidden in feasibility. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing.Arc
open Chapter10.Routing

abbrev Event (n k : ℕ) := Node n × Fin k
abbrev Edge (n k : ℕ) := Event n k × Event n k
abbrev Assignment (n k : ℕ) := Edge n k → Bool

structure Grid (k : ℕ) where
  time : Fin k → ℝ
  distinct : Function.Injective time
  nonnegative : ∀ s, 0 ≤ time s

def chosen {n k} (x : Assignment n k) : Finset (Edge n k) :=
  Finset.univ.filter fun e => x e = true

def arrivals {n k} (x : Assignment n k) (i : Fin n) : Finset (Edge n k) :=
  (chosen x).filter fun e => e.2.1 = some i

def incoming {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) : Finset (Edge n k) :=
  (chosen x).filter fun e => e.2 = (some i, s)

def outgoing {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) : Finset (Edge n k) :=
  (chosen x).filter fun e => e.1 = (some i, s)

@[simp] theorem mem_chosen {n k} (x : Assignment n k) (e : Edge n k) :
    e ∈ chosen x ↔ x e = true := by simp [chosen]
@[simp] theorem mem_arrivals {n k} (x : Assignment n k) (i : Fin n) (e : Edge n k) :
    e ∈ arrivals x i ↔ x e = true ∧ e.2.1 = some i := by simp [arrivals]
@[simp] theorem mem_incoming {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) (e : Edge n k) :
    e ∈ incoming x i s ↔ x e = true ∧ e.2 = (some i,s) := by simp [incoming]
@[simp] theorem mem_outgoing {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) (e : Edge n k) :
    e ∈ outgoing x i s ↔ x e = true ∧ e.1 = (some i,s) := by simp [outgoing]

def Visit {n k} (x : Assignment n k) : Prop := ∀ i, (arrivals x i).card = 1
def Flow {n k} (x : Assignment n k) : Prop :=
  ∀ i s, (incoming x i s).card = (outgoing x i s).card

def ArrivalWindows {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  ∀ e, x e = true → inWindow D e.2.1 (T.time e.2.2)
def DepartureWindows {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  ∀ e, x e = true → inWindow D e.1.1 (T.time e.1.2)
def Permitted {n k} (D : Data n) (x : Assignment n k) : Prop :=
  ∀ e, x e = true → D.allowed e.1.1 e.2.1 = true
def Travel {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  ∀ e, x e = true → T.time e.1.2 + D.travel e.1.1 e.2.1 ≤ T.time e.2.2

def Feasible {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  Visit x ∧ Flow x ∧ ArrivalWindows D T x ∧ DepartureWindows D T x ∧
    Permitted D x ∧ Travel D T x

def displayedSum {n k} (x : Assignment n k) (p : Edge n k → Prop) [DecidablePred p] : ℝ :=
  ∑ e, if p e then Chapter10.bit (x e) else 0

theorem displayedSum_eq_card {n k} (x : Assignment n k)
    (p : Edge n k → Prop) [DecidablePred p] :
    displayedSum x p = (((chosen x).filter p).card : ℝ) := by
  unfold displayedSum chosen
  rw [Finset.filter_filter]
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : p e <;> cases hx : x e <;> simp [hp, hx, Chapter10.bit]

def Literal {n k} (D : Data n) (T : Grid k) (x : Assignment n k) : Prop :=
  (∀ i, displayedSum x (fun e => e.2.1 = some i) = 1) ∧
  (∀ i s, displayedSum x (fun e => e.2 = (some i,s)) =
    displayedSum x (fun e => e.1 = (some i,s))) ∧
  (∀ e, ¬ inWindow D e.2.1 (T.time e.2.2) → Chapter10.bit (x e) = 0) ∧
  (∀ e, ¬ inWindow D e.1.1 (T.time e.1.2) → Chapter10.bit (x e) = 0) ∧
  (∀ e, D.allowed e.1.1 e.2.1 ≠ true → Chapter10.bit (x e) = 0) ∧
  (∀ e, T.time e.2.2 < T.time e.1.2 + D.travel e.1.1 e.2.1 → Chapter10.bit (x e) = 0)

theorem bit_binary (b : Bool) : Chapter10.bit b = 0 ∨ Chapter10.bit b = 1 := by
  cases b <;> simp [Chapter10.bit]

theorem zero_rows_iff {α : Type*} (x : α → Bool) (p : α → Prop) :
    (∀ e, ¬ p e → Chapter10.bit (x e) = 0) ↔ (∀ e, x e = true → p e) := by
  constructor
  · intro h e hx
    by_contra hp
    have := h e hp
    simp [Chapter10.bit, hx] at this
  · intro h e hp
    cases hx : x e
    · simp [Chapter10.bit, hx]
    · exact False.elim (hp (h e hx))

theorem literal_iff_feasible {n k} (D : Data n) (T : Grid k) (x : Assignment n k) :
    Literal D T x ↔ Feasible D T x := by
  simp only [Literal, Feasible, Visit, Flow, ArrivalWindows, DepartureWindows, Permitted, Travel,
    displayedSum_eq_card, arrivals, incoming, outgoing, Nat.cast_eq_one, Nat.cast_inj,
    zero_rows_iff, ← not_le]

/-- A real binary source assignment has a unique Boolean encoding, pointwise. -/
theorem real_binary_encoding {α : Type*} (z : α → ℝ) :
    (∀ e, z e = 0 ∨ z e = 1) ↔ ∃! x : α → Bool, ∀ e, Chapter10.bit (x e) = z e := by
  constructor
  · intro hz
    let x : α → Bool := fun e => decide (z e = 1)
    have hx : ∀ e, Chapter10.bit (x e) = z e := by
      intro e
      rcases hz e with h | h <;> simp [x, Chapter10.bit, h]
    refine ⟨x, hx, ?_⟩
    intro y hy
    funext e
    have he : Chapter10.bit (y e) = Chapter10.bit (x e) := (hy e).trans (hx e).symm
    cases hy' : y e <;> cases hx' : x e <;> simp_all [Chapter10.bit]
  · rintro ⟨x, hx, _⟩ e
    rw [← hx e]
    exact bit_binary (x e)

theorem visit_unique {n k} (x : Assignment n k) (h : Visit x) (i : Fin n) :
    ∃! e, x e = true ∧ e.2.1 = some i := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp (h i)
  refine ⟨e, ?_, ?_⟩
  · have : e ∈ arrivals x i := by rw [he]; simp
    simpa using this
  · intro f hf
    have : f ∈ arrivals x i := by simpa using hf
    simpa [he] using this

theorem incoming_subset_arrivals {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) :
    incoming x i s ⊆ arrivals x i := by
  intro e he
  rcases (mem_incoming _ _ _ _).mp he with ⟨hx, hd⟩
  exact (mem_arrivals _ _ _).mpr ⟨hx, congrArg Prod.fst hd⟩

theorem incoming_card_le_one {n k} (x : Assignment n k) (hv : Visit x) (i : Fin n) (s : Fin k) :
    (incoming x i s).card ≤ 1 := by
  simpa [hv i] using Finset.card_le_card (incoming_subset_arrivals x i s)

theorem outgoing_unique_at_arrival {n k} (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i : Fin n) (e : Edge n k) (hx : x e = true) (hd : e.2.1 = some i) :
    ∃! f, x f = true ∧ f.1 = (some i,e.2.2) := by
  have hi : e ∈ incoming x i e.2.2 := (mem_incoming _ _ _ _).mpr ⟨hx, Prod.ext hd rfl⟩
  have hc : (incoming x i e.2.2).card = 1 :=
    Nat.le_antisymm (incoming_card_le_one x hv i _) (Finset.one_le_card.mpr ⟨e,hi⟩)
  obtain ⟨f,hf'⟩ := Finset.card_eq_one.mp ((hf i e.2.2).symm.trans hc)
  refine ⟨f, ?_, ?_⟩
  · have : f ∈ outgoing x i e.2.2 := by rw [hf']; simp
    simpa using this
  · intro g hg
    have : g ∈ outgoing x i e.2.2 := by simpa using hg
    simpa [hf'] using this

theorem no_outgoing_other_event {n k} (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i : Fin n) (e : Edge n k) (hx : x e = true) (hd : e.2.1 = some i)
    (s : Fin k) (hs : s ≠ e.2.2) : outgoing x i s = ∅ := by
  have hem : incoming x i s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hmem
    rcases (mem_incoming _ _ _ _).mp hmem with ⟨hfx, hfd⟩
    obtain ⟨g,hg,hgu⟩ := visit_unique x hv i
    have heq : f = e := (hgu f ⟨hfx, congrArg Prod.fst hfd⟩).trans (hgu e ⟨hx,hd⟩).symm
    exact hs (by simpa [heq] using (congrArg Prod.snd hfd).symm)
  apply Finset.card_eq_zero.mp
  rw [← hf i s, hem, Finset.card_empty]

/-- Customer flow plus valid arrivals supplies departure validity. Depot validity
uses grid nonnegativity. Visit alone is deliberately not the premise. -/
theorem departure_from_flow_arrival {n k} (D : Data n) (T : Grid k) (x : Assignment n k)
    (hf : Flow x) (ha : ArrivalWindows D T x) : DepartureWindows D T x := by
  intro e hx
  cases hnode : e.1.1 with
  | none => simpa [inWindow, hnode] using T.nonnegative e.1.2
  | some i =>
    have ho : e ∈ outgoing x i e.1.2 := (mem_outgoing _ _ _ _).mpr ⟨hx, Prod.ext hnode rfl⟩
    have hp : 0 < (incoming x i e.1.2).card := by
      rw [hf i e.1.2]
      exact Finset.card_pos.mpr ⟨e,ho⟩
    obtain ⟨f,hf'⟩ := Finset.card_pos.mp hp
    rcases (mem_incoming _ _ _ _).mp hf' with ⟨hfx,hfd⟩
    have := ha f hfx
    simpa [hfd, hnode] using this

def objective {n k} (D : Data n) (x : Assignment n k) : ℝ :=
  ∑ e, D.cost e.1.1 e.2.1 * Chapter10.bit (x e)

theorem objective_selected_edges {n k} (D : Data n) (x : Assignment n k) :
    objective D x = ∑ e ∈ chosen x, D.cost e.1.1 e.2.1 := by
  simp only [objective, chosen, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  cases hx : x e <;> simp [Chapter10.bit, hx]

/-- The flattened product index is exactly the displayed three-index visit sum. -/
theorem displayed_visit_nested {n k} (x : Assignment n k) (j : Fin n) :
    displayedSum x (fun e => e.2.1 = some j) =
      ∑ i : Node n, ∑ s : Fin k, ∑ t : Fin k, Chapter10.bit (x ((i,s),(some j,t))) := by
  simp [displayedSum,Fintype.sum_prod_type]

theorem displayed_incoming_nested {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) :
    displayedSum x (fun e => e.2 = (some i,s)) =
      ∑ j : Node n, ∑ t : Fin k, Chapter10.bit (x ((j,t),(some i,s))) := by
  simp [displayedSum,Fintype.sum_prod_type]

theorem displayed_outgoing_nested {n k} (x : Assignment n k) (i : Fin n) (s : Fin k) :
    displayedSum x (fun e => e.1 = (some i,s)) =
      ∑ j : Node n, ∑ t : Fin k, Chapter10.bit (x ((some i,s),(j,t))) := by
  calc
    displayedSum x (fun e => e.1 = (some i,s)) =
        ∑ u : Event n k, if u = (some i,s) then
          (∑ v : Event n k, Chapter10.bit (x (u,v))) else 0 := by
      unfold displayedSum
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : u = (some i,s) <;> simp [hu]
    _ = ∑ v : Event n k, Chapter10.bit (x ((some i,s),v)) := by simp
    _ = ∑ j : Node n, ∑ t : Fin k, Chapter10.bit (x ((some i,s),(j,t))) := by
      rw [Fintype.sum_prod_type]

theorem objective_nested {n k} (D : Data n) (x : Assignment n k) :
    objective D x = ∑ i : Node n, ∑ s : Fin k, ∑ j : Node n, ∑ t : Fin k,
      D.cost i j * Chapter10.bit (x ((i,s),(j,t))) := by
  simp [objective,Fintype.sum_prod_type]

end Chapter10.Routing.Arc
