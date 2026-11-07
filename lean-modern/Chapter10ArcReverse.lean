module

public import Chapter10ArcMatrix

@[expose] public section

/-! Reverse encoding of actual timed customer lists. The customer occurrence
partition covers the whole customer type; disjointness alone is insufficient.
Distinct transitions and one common event clock for each customer are explicit. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing.Arc
open Chapter10.Routing

variable {n k : ℕ}

def timedEdges (clock : Fin n → Fin k) (ret : Fin k) (start : Event n k) :
    List (Fin n) → List (Edge n k)
  | [] => [(start,(none,ret))]
  | j::js => (start,(some j,clock j)) :: timedEdges clock ret (some j,clock j) js

structure TimedPath (n k : ℕ) where
  customers : List (Fin n)
  departure : Fin k
  returnTime : Fin k

def TimedPath.edges (clock : Fin n → Fin k) (p : TimedPath n k) : List (Edge n k) :=
  timedEdges clock p.returnTime (none,p.departure) p.customers

theorem timedEdges_in_count (clock : Fin n → Fin k) (ret : Fin k) (start : Event n k)
    (js : List (Fin n)) (p : Event n k → Bool) (hp : p (none,ret) = false) :
    (timedEdges clock ret start js).countP (fun e => p e.2) =
      js.countP (fun j => p (some j,clock j)) := by
  induction js generalizing start with
  | nil => simp [timedEdges,hp]
  | cons j js ih => simp [timedEdges,List.countP_cons,ih]

theorem timedEdges_out_count (clock : Fin n → Fin k) (ret : Fin k) (start : Event n k)
    (js : List (Fin n)) (p : Event n k → Bool) :
    (timedEdges clock ret start js).countP (fun e => p e.1) =
      js.countP (fun j => p (some j,clock j)) + if p start then 1 else 0 := by
  induction js generalizing start with
  | nil => simp [timedEdges,List.countP_cons]
  | cons j js ih => simp [timedEdges,List.countP_cons,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def encodeEdges (L : List (Edge n k)) : Assignment n k := fun e => decide (e ∈ L)

@[simp] theorem chosen_encode (L : List (Edge n k)) : chosen (encodeEdges L) = L.toFinset := by
  ext e
  simp [encodeEdges]

theorem filter_card_eq_countP {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup)
    (p : α → Prop) [DecidablePred p] :
    (L.toFinset.filter p).card = L.countP (fun e => decide (p e)) := by
  have heq : L.toFinset.filter p = (L.filter (fun e => decide (p e))).toFinset := by
    ext e; simp
  rw [heq, List.toFinset_card_of_nodup (hL.filter _), List.countP_eq_length_filter]

theorem encoded_visit {n k} (clock : Fin n → Fin k) (P : List (TimedPath n k))
    (hL : (P.flatMap (TimedPath.edges clock)).Nodup)
    (hcover : ∀ i, (P.flatMap TimedPath.customers).count i = 1) :
    Visit (encodeEdges (P.flatMap (TimedPath.edges clock))) := by
  intro i
  rw [arrivals, chosen_encode, filter_card_eq_countP _ hL]
  have hsingle : ∀ q : TimedPath n k,
      (q.edges clock).countP (fun e => decide (e.2.1 = some i)) = q.customers.count i := by
    intro q
    rw [TimedPath.edges, timedEdges_in_count clock q.returnTime (none,q.departure) q.customers
      (fun e => decide (e.1 = some i)) (by simp)]
    rw [List.count_eq_countP]
    congr 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Option.some.injEq, beq_iff_eq]
  simpa only [List.countP_flatMap, List.count_flatMap, Function.comp_def,hsingle] using hcover i

theorem encoded_flow (clock : Fin n → Fin k) (P : List (TimedPath n k))
    (hL : (P.flatMap (TimedPath.edges clock)).Nodup) :
    Flow (encodeEdges (P.flatMap (TimedPath.edges clock))) := by
  intro i s
  rw [incoming,outgoing,chosen_encode,filter_card_eq_countP _ hL,filter_card_eq_countP _ hL]
  simp only [List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_def,TimedPath.edges]
  rw [timedEdges_in_count clock q.returnTime (none,q.departure) q.customers
    (fun e => decide (e = (some i,s))) (by simp)]
  rw [timedEdges_out_count clock q.returnTime (none,q.departure) q.customers
    (fun e => decide (e = (some i,s)))]
  simp

/-- Window, allowed-arc and waiting inequalities refer to the actual transitions
of each supplied path; visit and flow are derived from list structure. -/
theorem timed_paths_encode_literal (D : Data n) (T : Grid k) (clock : Fin n → Fin k)
    (P : List (TimedPath n k))
    (hL : (P.flatMap (TimedPath.edges clock)).Nodup)
    (hcover : ∀ i, (P.flatMap TimedPath.customers).count i = 1)
    (hvalid : ∀ q ∈ P, ∀ e ∈ q.edges clock, edgeValid D T e) :
    Literal D T (encodeEdges (P.flatMap (TimedPath.edges clock))) := by
  rw [literal_iff_feasible]
  have hg : ∀ e, encodeEdges (P.flatMap (TimedPath.edges clock)) e = true → edgeValid D T e := by
    intro e he
    have hm : e ∈ P.flatMap (TimedPath.edges clock) := by simpa [encodeEdges] using he
    obtain ⟨q,hq,heq⟩ := List.mem_flatMap.mp hm
    exact hvalid q hq e heq
  exact ⟨encoded_visit clock P hL hcover, encoded_flow clock P hL,
    fun e he => (hg e he).1,fun e he => (hg e he).2.1,
    fun e he => (hg e he).2.2.1,fun e he => (hg e he).2.2.2⟩

theorem timedEdges_no_depot_pair (clock : Fin n → Fin k) (ret : Fin k)
    (start : Event n k) (js : List (Fin n)) (hn : start.1 ≠ none ∨ js ≠ [])
    (e : Edge n k) (he : e ∈ timedEdges clock ret start js) :
    ¬ (e.1.1 = none ∧ e.2.1 = none) := by
  induction js generalizing start with
  | nil =>
    simp only [timedEdges,List.mem_singleton] at he
    subst e
    simp only [ne_eq, not_true_eq_false, or_false] at hn
    simp [hn]
  | cons j js ih =>
    rcases List.mem_cons.mp he with h | h
    · subst e; simp
    · exact ih (some j,clock j) (Or.inl (by simp)) h

theorem encoded_no_depot_pair (clock : Fin n → Fin k) (P : List (TimedPath n k))
    (hne : ∀ q ∈ P, q.customers ≠ []) (e : Edge n k)
    (hs : e.1.1 = none) (hd : e.2.1 = none) :
    encodeEdges (P.flatMap (TimedPath.edges clock)) e = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  have hm : e ∈ P.flatMap (TimedPath.edges clock) := by simpa [encodeEdges] using he
  obtain ⟨q,hq,heq⟩ := List.mem_flatMap.mp hm
  exact timedEdges_no_depot_pair clock q.returnTime (none,q.departure) q.customers
    (Or.inr (hne q hq)) e heq ⟨hs,hd⟩

theorem encoded_objective (D : Data n) (clock : Fin n → Fin k) (P : List (TimedPath n k))
    (hL : (P.flatMap (TimedPath.edges clock)).Nodup) :
    objective D (encodeEdges (P.flatMap (TimedPath.edges clock))) =
      ((P.flatMap (TimedPath.edges clock)).map (fun e => D.cost e.1.1 e.2.1)).sum := by
  rw [objective_selected_edges,chosen_encode]
  exact (List.sum_toFinset (fun e : Edge n k => D.cost e.1.1 e.2.1) hL)

end Chapter10.Routing.Arc
