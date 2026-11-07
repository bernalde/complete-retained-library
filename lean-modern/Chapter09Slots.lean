module

public import Chapter09

@[expose] public section

/-! Literal finite vertex/color slots for thesis Chapter 9, PDF379–382.
The graph stores each undirected edge once, oriented by the vertex order.
No source theorem or optimum existence is assumed. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Source

abbrev Slot (n k : ℕ) := Fin n × Fin k

structure Graph (n : ℕ) where
  edges : Finset (Fin n × Fin n)
  ordered : ∀ e ∈ edges, e.1 < e.2

def Adj {n : ℕ} (G : Graph n) (i j : Fin n) : Prop :=
  (i, j) ∈ G.edges ∨ (j, i) ∈ G.edges

theorem adj_symm {n : ℕ} (G : Graph n) (i j : Fin n) : Adj G i j ↔ Adj G j i :=
  or_comm

theorem adj_irrefl {n : ℕ} (G : Graph n) (i : Fin n) : ¬ Adj G i i := by
  rintro (h | h) <;> exact (lt_irrefl i) (G.ordered _ h)

theorem edge_once {n : ℕ} (G : Graph n) (i j : Fin n) :
    (i, j) ∈ G.edges ↔ Adj G i j ∧ i < j := by
  constructor
  · intro h; exact ⟨Or.inl h, G.ordered _ h⟩
  · rintro ⟨h | h, hij⟩
    · exact h
    · exact False.elim ((not_lt_of_gt hij) (G.ordered _ h))

def flag {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) (r : Fin k) : ℝ :=
  if (i, r) ∈ S then 1 else 0

def row {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun r => (i, r) ∈ S)

def rowCount {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) : ℕ := (row S i).card

def vertices {n k : ℕ} (S : Finset (Slot n k)) : Finset (Fin n) := S.image Prod.fst

def spatialPairs {n : ℕ} (G : Graph n) (k : ℕ) : Finset (Slot n k × Slot n k) :=
  Finset.univ.filter (fun e => (e.1.1, e.2.1) ∈ G.edges ∧ e.1.2 = e.2.2)

def colorPairs (n k : ℕ) : Finset (Slot n k × Slot n k) :=
  Finset.univ.filter (fun e => e.1.1 = e.2.1 ∧ e.1.2 < e.2.2)

def conflictPairs {n : ℕ} (G : Graph n) (k : ℕ) := spatialPairs G k ∪ colorPairs n k

def Feasible {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) : Prop :=
  Chapter09.feasible (conflictPairs G k) S

@[simp] theorem mem_spatialPairs {n k : ℕ} (G : Graph n) (e : Slot n k × Slot n k) :
    e ∈ spatialPairs G k ↔ (e.1.1, e.2.1) ∈ G.edges ∧ e.1.2 = e.2.2 := by
  simp [spatialPairs]

@[simp] theorem mem_colorPairs {n k : ℕ} (e : Slot n k × Slot n k) :
    e ∈ colorPairs n k ↔ e.1.1 = e.2.1 ∧ e.1.2 < e.2.2 := by simp [colorPairs]

@[simp] theorem mem_conflictPairs {n k : ℕ} (G : Graph n) (e : Slot n k × Slot n k) :
    e ∈ conflictPairs G k ↔
      ((e.1.1, e.2.1) ∈ G.edges ∧ e.1.2 = e.2.2) ∨
      (e.1.1 = e.2.1 ∧ e.1.2 < e.2.2) := by simp [conflictPairs]

theorem spatial_color_disjoint {n : ℕ} (G : Graph n) (k : ℕ) :
    Disjoint (spatialPairs G k) (colorPairs n k) := by
  apply Finset.disjoint_left.mpr
  intro e he hc
  have h := G.ordered _ ((mem_spatialPairs G e).mp he).1
  have eq := ((mem_colorPairs e).mp hc).1
  exact (ne_of_lt h) eq

theorem feasible_iff {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    Feasible G S ↔
      (∀ e ∈ G.edges, ∀ r, ¬ ((e.1, r) ∈ S ∧ (e.2, r) ∈ S)) ∧
      (∀ i r p, (i, r) ∈ S → (i, p) ∈ S → r = p) := by
  constructor
  · intro h
    constructor
    · intro e he r; exact h ((e.1,r),(e.2,r)) (by simp [he])
    · intro i r p hr hp
      by_contra hn
      rcases lt_or_gt_of_ne hn with hl | hl
      · exact h ((i,r),(i,p)) (by simp [hl]) ⟨hr,hp⟩
      · exact h ((i,p),(i,r)) (by simp [hl]) ⟨hp,hr⟩
  · rintro ⟨he,hc⟩ ⟨⟨i,r⟩,⟨j,p⟩⟩ hpair ⟨hi,hj⟩
    rcases (mem_conflictPairs G _).mp hpair with ⟨hedge,hrp⟩ | ⟨hij,hrp⟩
    · change r = p at hrp
      subst p; exact he (i,j) hedge r ⟨hi,hj⟩
    · change i = j at hij
      subst j; exact (ne_of_lt hrp) (hc i r p hi hj)

@[simp] theorem feasible_empty {n : ℕ} (G : Graph n) (k : ℕ) :
    Feasible G (∅ : Finset (Slot n k)) := by
  intro e _ h
  exact Finset.notMem_empty e.1 h.1

theorem feasible_rowCount {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (h : Feasible G S) (i : Fin n) : rowCount S i ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr p hp
  exact ((feasible_iff G S).mp h).2 i r p (by simpa [row] using hr) (by simpa [row] using hp)

theorem feasible_vertex_card {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (h : Feasible G S) : (vertices S).card = S.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  apply Prod.ext hab
  exact ((feasible_iff G S).mp h).2 a.1 a.2 b.2 ha (by simpa [hab] using hb)

/-- Partial coloring, with `none` for an unselected vertex. -/
def encode {n k : ℕ} (c : Fin n → Option (Fin k)) : Finset (Slot n k) :=
  Finset.univ.filter (fun u => c u.1 = some u.2)

def Proper {n k : ℕ} (G : Graph n) (c : Fin n → Option (Fin k)) : Prop :=
  ∀ i j, Adj G i j → ∀ r, ¬ (c i = some r ∧ c j = some r)

def decode {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) : Option (Fin k) := by
  classical
  exact if h : ∃ r, (i,r) ∈ S then some (Classical.choose h) else none

@[simp] theorem mem_encode {n k : ℕ} (c : Fin n → Option (Fin k)) (i : Fin n) (r : Fin k) :
    (i,r) ∈ encode c ↔ c i = some r := by simp [encode]

theorem decode_some_iff {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (h : Feasible G S) (i : Fin n) (r : Fin k) : decode S i = some r ↔ (i,r) ∈ S := by
  classical
  by_cases he : ∃ p, (i,p) ∈ S
  · simp only [decode, dif_pos he, Option.some.injEq]
    constructor
    · intro eq; rw [← eq]; exact Classical.choose_spec he
    · intro hr
      exact ((feasible_iff G S).mp h).2 i _ r (Classical.choose_spec he) hr
  · have hn : (i,r) ∉ S := fun hr => he ⟨r,hr⟩
    simp [decode,he,hn]

theorem encode_decode {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (h : Feasible G S) : encode (decode S) = S := by
  ext u; exact (mem_encode _ _ _).trans (decode_some_iff G S h _ _)

theorem decode_encode {n k : ℕ} (c : Fin n → Option (Fin k)) : decode (encode c) = c := by
  classical
  funext i
  cases hc : c i with
  | none => simp [decode, encode, hc]
  | some r =>
    have he : ∃ p, (i,p) ∈ encode c := ⟨r, by simp [hc]⟩
    have hp := Classical.choose_spec he
    have eq : Classical.choose he = r := by simpa [encode,hc] using hp
    simp [decode, he, eq, hc]

theorem proper_encode_iff {n k : ℕ} (G : Graph n) (c : Fin n → Option (Fin k)) :
    Feasible G (encode c) ↔ Proper G c := by
  rw [feasible_iff]
  constructor
  · rintro ⟨he,_⟩ i j (hij|hji) r h
    · exact he (i,j) hij r (by simpa using h)
    · exact he (j,i) hji r (by simpa using And.symm h)
  · intro h
    constructor
    · intro e he r hp; exact h e.1 e.2 (Or.inl he) r (by simpa using hp)
    · intro i r p hr hp
      exact Option.some.inj ((mem_encode c i r).mp hr |>.symm.trans ((mem_encode c i p).mp hp))

theorem feasible_iff_partial_coloring {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    Feasible G S ↔ ∃ c, Proper G c ∧ encode c = S := by
  constructor
  · intro h
    exact ⟨decode S, (proper_encode_iff G _).mp (by simpa [encode_decode G S h] using h), encode_decode G S h⟩
  · rintro ⟨c,hc,rfl⟩; exact (proper_encode_iff G c).mpr hc

/-- The induced vertex set is exactly the vertices on which the partial coloring is defined. -/
theorem vertices_encode {n k : ℕ} (c : Fin n → Option (Fin k)) (i : Fin n) :
    i ∈ vertices (encode c) ↔ ∃ r, c i = some r := by
  simp [vertices, encode, Finset.mem_image, Prod.exists]

def weight {n k : ℕ} (a b : ℝ) (e : Slot n k × Slot n k) : ℝ :=
  if e.1.1 = e.2.1 then b else a

def uScore {n k : ℕ} (G : Graph n) (a b : ℝ) (S : Finset (Slot n k)) : ℝ :=
  Chapter09.score (conflictPairs G k) (weight a b) S

theorem weight_spatial {n k : ℕ} (G : Graph n) (a b : ℝ) (e : Slot n k × Slot n k)
    (he : e ∈ spatialPairs G k) : weight a b e = a := by
  have hn := ne_of_lt (G.ordered _ ((mem_spatialPairs G e).mp he).1)
  simp [weight, hn]

theorem weight_color {n k : ℕ} (a b : ℝ) (e : Slot n k × Slot n k)
    (he : e ∈ colorPairs n k) : weight a b e = b := by
  simp [weight, ((mem_colorPairs e).mp he).1]

theorem weight_ge_one {n k : ℕ} (G : Graph n) (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∀ e ∈ conflictPairs G k, 1 ≤ weight a b e := by
  intro e _; unfold weight; split_ifs <;> assumption

theorem weight_gt_one {n k : ℕ} (G : Graph n) (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    ∀ e ∈ conflictPairs G k, 1 < weight a b e := by
  intro e _; unfold weight; split_ifs <;> assumption

@[simp] theorem colorPairs_one (n : ℕ) : colorPairs n 1 = ∅ := by
  ext e
  have he : e.1.2 = e.2.2 := Subsingleton.elim _ _
  simp [colorPairs, he]

theorem weight_ge_one_k1 {n : ℕ} (G : Graph n) (a b : ℝ) (ha : 1 ≤ a) :
    ∀ e ∈ conflictPairs G 1, 1 ≤ weight a b e := by
  intro e he
  have hs : e ∈ spatialPairs G 1 := by simpa [conflictPairs] using he
  rw [weight_spatial G a b e hs]; exact ha

theorem weight_gt_one_k1 {n : ℕ} (G : Graph n) (a b : ℝ) (ha : 1 < a) :
    ∀ e ∈ conflictPairs G 1, 1 < weight a b e := by
  intro e he
  have hs : e ∈ spatialPairs G 1 := by simpa [conflictPairs] using he
  rw [weight_spatial G a b e hs]; exact ha

theorem feasible_uScore {n k : ℕ} (G : Graph n) (a b : ℝ) (S : Finset (Slot n k))
    (h : Feasible G S) : uScore G a b S = (S.card : ℝ) :=
  Chapter09.feasible_score _ _ _ h

/-- Maximum over an explicit nonempty finite domain; its witness is part of the API. -/
def maxPoint {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ι :=
  Classical.choose (s.exists_max_image f hs)

def maxOn {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ℝ :=
  f (maxPoint s hs f)

theorem maxOn_attained {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    ∃ a ∈ s, f a = maxOn s hs f :=
  ⟨maxPoint s hs f, (Classical.choose_spec (s.exists_max_image f hs)).1, rfl⟩

theorem le_maxOn {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ)
    (a : ι) (ha : a ∈ s) : f a ≤ maxOn s hs f :=
  (Classical.choose_spec (s.exists_max_image f hs)).2 a ha

def finiteMax {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  maxOn Finset.univ Finset.univ_nonempty f

theorem finiteMax_attained {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    ∃ a, f a = finiteMax f := by
  obtain ⟨a,_,ha⟩ := maxOn_attained Finset.univ Finset.univ_nonempty f
  exact ⟨a,ha⟩

theorem le_finiteMax {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (a : ι) :
    f a ≤ finiteMax f := le_maxOn _ _ _ a (Finset.mem_univ _)

def feasibleSelections {n : ℕ} (G : Graph n) (k : ℕ) : Finset (Finset (Slot n k)) := by
  classical
  exact Finset.univ.filter (Feasible G)

@[simp] theorem mem_feasibleSelections {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    S ∈ feasibleSelections G k ↔ Feasible G S := by classical simp [feasibleSelections]

theorem feasibleSelections_nonempty {n : ℕ} (G : Graph n) (k : ℕ) :
    (feasibleSelections G k).Nonempty := ⟨∅, by simp⟩

def alpha {n : ℕ} (G : Graph n) (k : ℕ) : ℝ :=
  maxOn (feasibleSelections G k) (feasibleSelections_nonempty G k) (fun S => ((vertices S).card : ℝ))

theorem alpha_attained {n : ℕ} (G : Graph n) (k : ℕ) :
    ∃ S : Finset (Slot n k), Feasible G S ∧ (S.card : ℝ) = alpha G k := by
  obtain ⟨S,hS,he⟩ := maxOn_attained (feasibleSelections G k) (feasibleSelections_nonempty G k)
    (fun S => ((vertices S).card : ℝ))
  have hf := (mem_feasibleSelections G S).mp hS
  exact ⟨S,hf,by simpa [alpha, feasible_vertex_card G S hf] using he⟩

theorem card_le_alpha {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (h : Feasible G S) : (S.card : ℝ) ≤ alpha G k := by
  have he := le_maxOn (feasibleSelections G k) (feasibleSelections_nonempty G k)
    (fun T => ((vertices T).card : ℝ)) S ((mem_feasibleSelections G S).mpr h)
  simpa [alpha, feasible_vertex_card G S h] using he

end Chapter09.Source
#print axioms Chapter09.Source.edge_once
#print axioms Chapter09.Source.spatial_color_disjoint
#print axioms Chapter09.Source.feasible_iff_partial_coloring
#print axioms Chapter09.Source.feasible_vertex_card
#print axioms Chapter09.Source.alpha_attained
#print axioms Chapter09.Source.card_le_alpha
