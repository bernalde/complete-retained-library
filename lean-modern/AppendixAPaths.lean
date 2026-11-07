module

public import AppendixA
public import Mathlib.Data.Fintype.List
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MigrationListChain
public import Mathlib.Data.List.Chain

@[expose] public section

/-! Complete finite catalogues of actual simple vertex paths. The cap counts
vertices, not edges. Existing AppendixA connectivity remains the target. -/
open scoped BigOperators
namespace AppendixAPaths

abbrev NodupVertices (n : ℕ) := {l : List (Fin n) // l.Nodup}

def PathPredicate {n : ℕ} (E : Finset (Fin n × Fin n)) (k : ℕ)
    (a b : Fin n) (p : NodupVertices n) : Prop :=
  a ≠ b ∧ p.val.head? = some a ∧ p.val.getLast? = some b ∧
    List.IsChain (AppendixA.adjacent E) p.val ∧ p.val.length ≤ k

instance pathPredicateDecidable {n : ℕ} (E : Finset (Fin n × Fin n)) (k : ℕ)
    (a b : Fin n) (p : NodupVertices n) : Decidable (PathPredicate E k a b p) := by
  unfold PathPredicate AppendixA.adjacent
  infer_instance

def catalogue {n : ℕ} (E : Finset (Fin n × Fin n)) (k : ℕ)
    (a b : Fin n) : Finset (NodupVertices n) :=
  Finset.univ.filter (PathPredicate E k a b)

@[simp] theorem mem_catalogue {n : ℕ} (E : Finset (Fin n × Fin n)) (k : ℕ)
    (a b : Fin n) (p : NodupVertices n) :
    p ∈ catalogue E k a b ↔ PathPredicate E k a b p := by
  simp [catalogue]

def Contains {n : ℕ} (S : Finset (Fin n)) (p : NodupVertices n) : Prop :=
  ∀ v ∈ p.val, v ∈ S

def interior {n : ℕ} (a b : Fin n) (p : NodupVertices n) : Finset (Fin n) :=
  p.val.toFinset \ {a,b}

theorem endpoints_mem {n : ℕ} {E : Finset (Fin n × Fin n)} {k : ℕ}
    {a b : Fin n} {p : NodupVertices n} (hp : p ∈ catalogue E k a b) :
    a ∈ p.val ∧ b ∈ p.val := by
  obtain ⟨_,ha,hb,_,_⟩ := (mem_catalogue E k a b p).mp hp
  exact ⟨List.mem_of_mem_head? (by simp [ha]), List.mem_of_mem_getLast? (by simp [hb])⟩

theorem interior_card_add_two_le {n : ℕ} {E : Finset (Fin n × Fin n)} {k : ℕ}
    {a b : Fin n} {p : NodupVertices n} (hp : p ∈ catalogue E k a b) :
    (interior a b p).card + 2 ≤ k := by
  have h := (mem_catalogue E k a b p).mp hp
  have hm := endpoints_mem hp
  have hsub : ({a,b} : Finset (Fin n)) ⊆ p.val.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hm]
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_pair h.1, List.toFinset_card_of_nodup p.property] at hc
  change (interior a b p).card + 2 = p.val.length at hc
  rw [hc]
  exact h.2.2.2.2

theorem contains_iff_interior {n : ℕ} {E : Finset (Fin n × Fin n)} {k : ℕ}
    {a b : Fin n} {p : NodupVertices n} (hp : p ∈ catalogue E k a b)
    (S : Finset (Fin n)) :
    Contains S p ↔ a ∈ S ∧ b ∈ S ∧ ∀ v ∈ interior a b p, v ∈ S := by
  have hm := endpoints_mem hp
  constructor
  · intro h
    exact ⟨h a hm.1,h b hm.2,fun v hv => h v (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)⟩
  · rintro ⟨ha,hb,hi⟩ v hv
    by_cases hmem : v ∈ ({a,b} : Finset (Fin n))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl <;> assumption
    · exact hi v (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hv,hmem⟩)

def restrictedGraph {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ AppendixA.fiberStep E S a b
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,h.2.2.1,h.2.1,AppendixA.adjacent_symmetric E h.2.2.2⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

theorem rtc_restrictedGraph {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    {a b : Fin n} (h : Relation.ReflTransGen (AppendixA.fiberStep E S) a b) :
    Relation.ReflTransGen (restrictedGraph E S).Adj a b := by
  induction h with
  | refl => exact .refl
  | @tail b c hab hbc ih =>
    by_cases he : b = c
    · simpa [he] using ih
    · exact ih.tail ⟨he,hbc⟩

theorem walk_support_contained {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    {a b : Fin n} (w : (restrictedGraph E S).Walk a b) (ha : a ∈ S) :
    ∀ v ∈ w.support, v ∈ S := by
  induction w with
  | nil => simpa using ha
  | @cons a c b h w ih =>
    intro v hv
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact ih h.2.2.1 v hv

theorem bounded_path_complete {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (k : ℕ) (hcard : S.card ≤ k)
    (hc : AppendixA.connected E S) {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S)
    (hne : a ≠ b) : ∃ p ∈ catalogue E k a b, Contains S p := by
  classical
  have hr := rtc_restrictedGraph E S (hc a ha b hb)
  obtain ⟨w⟩ := ((restrictedGraph E S).reachable_iff_reflTransGen a b).mpr hr
  let q := w.toPath
  let p : NodupVertices n := ⟨q.val.support,q.property.support_nodup⟩
  have hcont : Contains S p := walk_support_contained E S q.val ha
  have hlen : p.val.length ≤ k := by
    have hs : p.val.toFinset ⊆ S := by
      intro v hv; exact hcont v (List.mem_toFinset.mp hv)
    have hh := Finset.card_le_card hs
    rw [List.toFinset_card_of_nodup p.property] at hh
    exact hh.trans hcard
  refine ⟨p,(mem_catalogue E k a b p).mpr ⟨hne,?_,?_,?_,hlen⟩,hcont⟩
  · change q.val.support.head? = some a
    rw [List.head?_eq_head (SimpleGraph.Walk.support_ne_nil q.val)]
    simp
  · change q.val.support.getLast? = some b
    rw [List.getLast?_eq_getLast_of_ne_nil (SimpleGraph.Walk.support_ne_nil q.val)]
    simp
  · exact q.val.isChain_adj_support.imp (fun _ _ h => h.2.2.2)

theorem catalogue_path_sound {n : ℕ} {E : Finset (Fin n × Fin n)} {S : Finset (Fin n)}
    {k : ℕ} {a b : Fin n} {p : NodupVertices n}
    (hp : p ∈ catalogue E k a b) (hcont : Contains S p) :
    Relation.ReflTransGen (AppendixA.fiberStep E S) a b := by
  obtain ⟨hne,ha,hb,hchain,hk⟩ := (mem_catalogue E k a b p).mp hp
  have hchain' : List.IsChain (AppendixA.fiberStep E S) p.val :=
    (List.IsChain.iff_mem.mp hchain).imp (fun x y h => ⟨hcont x h.1,hcont y h.2.1,h.2.2⟩)
  cases hv : p.val with
  | nil => simp [hv] at ha
  | cons x xs =>
    have hx : x = a := by simpa [hv] using ha
    subst x
    apply List.relationReflTransGen_of_exists_isChain_cons xs
    · simpa [hv] using hchain'
    · have hl := List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil a xs)
      rw [hv, hl] at hb
      exact Option.some.inj hb

instance containsDecidable {n : ℕ} (S : Finset (Fin n)) (p : NodupVertices n) :
    Decidable (Contains S p) := by unfold Contains; infer_instance

def connectedCheck {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n)) : Bool :=
  decide (∀ a ∈ S, ∀ b ∈ S, a = b ∨
    ∃ p ∈ catalogue E n a b, Contains S p)

theorem connectedCheck_eq_true_iff {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) : connectedCheck E S = true ↔ AppendixA.connected E S := by
  simp only [connectedCheck, decide_eq_true_eq]
  constructor
  · intro h a ha b hb
    rcases h a ha b hb with he | ⟨p,hp,hcont⟩
    · subst b; exact .refl
    · exact catalogue_path_sound hp hcont
  · intro h a ha b hb
    by_cases he : a = b
    · exact Or.inl he
    · exact Or.inr (bounded_path_complete E S n (by simpa using Finset.card_le_univ S) h ha hb he)

end AppendixAPaths
