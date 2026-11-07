module

public import Chapter10FinitePaths

@[expose] public section

/-! Specialize the proved finite successor decomposition to the literal arc
rows. Catalogue roots correspond to selected depot-to-customer departures. -/
noncomputable section
namespace Chapter10.Routing.Arc
open Chapter10.Routing
open Chapter10.Routing.FinitePaths

variable {n k : ℕ}

def departureEdge (x : Assignment n k) (hv : Visit x) (hf : Flow x) (i : Fin n) : Edge n k :=
  Classical.choose (ExistsUnique.exists (outgoing_unique_at_arrival x hv hf i (arrivalEdge x hv i)
    (arrivalEdge_spec x hv i).1 (arrivalEdge_spec x hv i).2))

theorem departureEdge_spec (x : Assignment n k) (hv : Visit x) (hf : Flow x) (i : Fin n) :
    x (departureEdge x hv hf i) = true ∧
    (departureEdge x hv hf i).1 = (some i,(arrivalEdge x hv i).2.2) :=
  Classical.choose_spec (ExistsUnique.exists (outgoing_unique_at_arrival x hv hf i (arrivalEdge x hv i)
    (arrivalEdge_spec x hv i).1 (arrivalEdge_spec x hv i).2))

theorem departureEdge_eq (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i : Fin n) (e : Edge n k) (hx : x e = true) (hs : e.1.1 = some i) :
    departureEdge x hv hf i = e := by
  have hclock := departure_matches_arrival x hv hf i e hx hs
  obtain ⟨g,hg,hgu⟩ := outgoing_unique_at_arrival x hv hf i (arrivalEdge x hv i)
    (arrivalEdge_spec x hv i).1 (arrivalEdge_spec x hv i).2
  exact (hgu _ (departureEdge_spec x hv hf i)).trans (hgu e ⟨hx,Prod.ext hs hclock⟩).symm

def next (x : Assignment n k) (hv : Visit x) (hf : Flow x) (i : Fin n) : Option (Fin n) :=
  (departureEdge x hv hf i).2.1

def prev (x : Assignment n k) (hv : Visit x) (i : Fin n) : Option (Fin n) :=
  (arrivalEdge x hv i).1.1

theorem next_prev (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i j : Fin n) (h : next x hv hf i = some j) : prev x hv j = some i := by
  have heq := arrivalEdge_eq x hv j (departureEdge x hv hf i) (departureEdge_spec x hv hf i).1 h
  have hs := congrArg (fun e : Event n k => e.1) (departureEdge_spec x hv hf i).2
  simpa [prev,heq] using hs

theorem prev_next (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i j : Fin n) (h : prev x hv j = some i) : next x hv hf i = some j := by
  have heq := departureEdge_eq x hv hf i (arrivalEdge x hv j) (arrivalEdge_spec x hv j).1 h
  simpa [next,heq] using (arrivalEdge_spec x hv j).2

theorem next_rank (x : Assignment n k) (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ)
    (hr : StrictRank x r) (i j : Fin n) (h : next x hv hf i = some j) : r i < r j := by
  apply hr i j
  exact ⟨departureEdge x hv hf i,(departureEdge_spec x hv hf i).1,
    congrArg Prod.fst (departureEdge_spec x hv hf i).2,h⟩

def routeTrace (x : Assignment n k) (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ)
    (hr : StrictRank x r) (a : Fin n) : List (Fin n) :=
  trace (next x hv hf) r (next_rank x hv hf r hr) a

theorem routeTrace_spec (x : Assignment n k) (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ)
    (hr : StrictRank x r) (a : Fin n) : Suffix (next x hv hf) a (routeTrace x hv hf r hr a) :=
  trace_spec _ _ _ a

theorem routeTrace_elementary (x : Assignment n k) (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ)
    (hr : StrictRank x r) (a : Fin n) :
    routeTrace x hv hf r hr a ≠ [] ∧ (routeTrace x hv hf r hr a).Nodup :=
  ⟨(routeTrace_spec x hv hf r hr a).nonempty,
    (routeTrace_spec x hv hf r hr a).nodup r (next_rank x hv hf r hr)⟩

theorem route_partition (x : Assignment n k) (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ)
    (hr : StrictRank x r) (i : Fin n) :
    ∃! a, prev x hv a = none ∧ i ∈ routeTrace x hv hf r hr a :=
  unique_root_cover (next x hv hf) (prev x hv) r (next_rank x hv hf r hr)
    (next_prev x hv hf) (prev_next x hv hf) i

def rootSet (x : Assignment n k) (hv : Visit x) : Finset (Fin n) :=
  Finset.univ.filter fun a => prev x hv a = none

/-- Every edge in a customer route is represented by its arrival customer;
only the final return is represented by its departure customer. -/
def routeEdges (x : Assignment n k) (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ)
    (hr : StrictRank x r) (a : Fin n) : Finset (Edge n k) :=
  (routeTrace x hv hf r hr a).toFinset.biUnion fun i =>
    if next x hv hf i = none then {arrivalEdge x hv i, departureEdge x hv hf i}
    else {arrivalEdge x hv i}

theorem mem_routeEdges (x : Assignment n k) (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ)
    (hr : StrictRank x r) (a : Fin n) (e : Edge n k) :
    e ∈ routeEdges x hv hf r hr a ↔
      ∃ i ∈ routeTrace x hv hf r hr a,
        e = arrivalEdge x hv i ∨ next x hv hf i = none ∧ e = departureEdge x hv hf i := by
  simp only [routeEdges, Finset.mem_biUnion, List.mem_toFinset]
  apply exists_congr
  intro i
  by_cases hi : next x hv hf i = none <;> simp [hi]

theorem routeEdges_selected (x : Assignment n k) (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ)
    (hr : StrictRank x r) (a : Fin n) : routeEdges x hv hf r hr a ⊆ chosen x := by
  intro e he
  rcases (mem_routeEdges _ _ _ _ _ _ _).mp he with ⟨i,_,he | ⟨_,he⟩⟩
  · rw [he]; exact (mem_chosen _ _).mpr (arrivalEdge_spec x hv i).1
  · rw [he]; exact (mem_chosen _ _).mpr (departureEdge_spec x hv hf i).1

/-- Full coverage of selected coordinates needs the explicit depot-only
exclusion. Dropping this premise would permit additional depot loops. -/
theorem selected_edge_decomposition (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (r : Fin n → ℕ) (hr : StrictRank x r)
    (hdd : ∀ e, e.1.1 = none → e.2.1 = none → x e = false) :
    chosen x = (rootSet x hv).biUnion (routeEdges x hv hf r hr) := by
  ext e
  constructor
  · intro he
    have hx := (mem_chosen _ _).mp he
    cases hd : e.2.1 with
    | some j =>
      obtain ⟨a,⟨ha,hja⟩,_⟩ := route_partition x hv hf r hr j
      apply Finset.mem_biUnion.mpr
      refine ⟨a,by simpa [rootSet] using ha,?_⟩
      apply (mem_routeEdges _ _ _ _ _ _ _).mpr
      exact ⟨j,hja,Or.inl (arrivalEdge_eq x hv j e hx hd).symm⟩
    | none =>
      cases hs : e.1.1 with
      | none => have := hdd e hs hd; simp [hx] at this
      | some i =>
        obtain ⟨a,⟨ha,hia⟩,_⟩ := route_partition x hv hf r hr i
        have heq := departureEdge_eq x hv hf i e hx hs
        apply Finset.mem_biUnion.mpr
        refine ⟨a,by simpa [rootSet] using ha,?_⟩
        apply (mem_routeEdges _ _ _ _ _ _ _).mpr
        exact ⟨i,hia,Or.inr ⟨by simpa [next,heq] using hd,heq.symm⟩⟩
  · intro he
    obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp he
    exact routeEdges_selected x hv hf r hr a ha

theorem represented_customer_unique (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i j : Fin n) (e : Edge n k)
    (hi : e = arrivalEdge x hv i ∨ next x hv hf i = none ∧ e = departureEdge x hv hf i)
    (hj : e = arrivalEdge x hv j ∨ next x hv hf j = none ∧ e = departureEdge x hv hf j) : i = j := by
  rcases hi with hi | ⟨hi,hei⟩ <;> rcases hj with hj | ⟨hj,hej⟩
  · have hdi := (arrivalEdge_spec x hv i).2
    have hdj := (arrivalEdge_spec x hv j).2
    rw [← hi] at hdi
    rw [← hj] at hdj
    exact Option.some.inj (hdi.symm.trans hdj)
  · have hdi := (arrivalEdge_spec x hv i).2
    have hdj : (departureEdge x hv hf j).2.1 = none := hj
    rw [← hi] at hdi
    rw [← hej] at hdj
    simp [hdi] at hdj
  · have hdj := (arrivalEdge_spec x hv j).2
    have hdi : (departureEdge x hv hf i).2.1 = none := hi
    rw [← hj] at hdj
    rw [← hei] at hdi
    simp [hdj] at hdi
  · have hsi := congrArg Prod.fst (departureEdge_spec x hv hf i).2
    have hsj := congrArg Prod.fst (departureEdge_spec x hv hf j).2
    rw [← hei] at hsi
    rw [← hej] at hsj
    exact Option.some.inj (hsi.symm.trans hsj)

theorem routeEdges_disjoint (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (r : Fin n → ℕ) (hr : StrictRank x r) (a b : Fin n)
    (ha : prev x hv a = none) (hb : prev x hv b = none) (hne : a ≠ b) :
    Disjoint (routeEdges x hv hf r hr a) (routeEdges x hv hf r hr b) := by
  apply Finset.disjoint_left.mpr
  intro e hea heb
  obtain ⟨i,hia,hi⟩ := (mem_routeEdges _ _ _ _ _ _ _).mp hea
  obtain ⟨j,hjb,hj⟩ := (mem_routeEdges _ _ _ _ _ _ _).mp heb
  have hij := represented_customer_unique x hv hf i j e hi hj
  subst j
  obtain ⟨c,hc,hcu⟩ := route_partition x hv hf r hr i
  exact hne ((hcu a ⟨ha,hia⟩).trans (hcu b ⟨hb,hjb⟩).symm)

open scoped BigOperators

theorem objective_route_decomposition (D : Data n) (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (r : Fin n → ℕ) (hr : StrictRank x r)
    (hdd : ∀ e, e.1.1 = none → e.2.1 = none → x e = false) :
    objective D x = ∑ a ∈ rootSet x hv, ∑ e ∈ routeEdges x hv hf r hr a, D.cost e.1.1 e.2.1 := by
  rw [objective_selected_edges, selected_edge_decomposition x hv hf r hr hdd]
  apply Finset.sum_biUnion
  intro a ha b hb hab
  exact routeEdges_disjoint x hv hf r hr a b (by simpa [rootSet] using ha)
    (by simpa [rootSet] using hb) hab

def depotDepartures (x : Assignment n k) : Finset (Edge n k) :=
  (chosen x).filter fun e => e.1.1 = none ∧ e.2.1 ≠ none

theorem root_image_departures (x : Assignment n k) (hv : Visit x) :
    (rootSet x hv).image (arrivalEdge x hv) = depotDepartures x := by
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    have hroot : prev x hv a = none := by simpa [rootSet] using ha
    simp [depotDepartures, (arrivalEdge_spec x hv a).1, (arrivalEdge_spec x hv a).2,
      show (arrivalEdge x hv a).1.1 = none from hroot]
  · intro he
    have he' : x e = true ∧ e.1.1 = none ∧ e.2.1 ≠ none := by simpa [depotDepartures] using he
    cases hd : e.2.1 with
    | none => exact False.elim (he'.2.2 hd)
    | some i =>
      have heq := arrivalEdge_eq x hv i e he'.1 hd
      apply Finset.mem_image.mpr
      refine ⟨i,?_,heq⟩
      change i ∈ Finset.univ.filter (fun a => prev x hv a = none)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (arrivalEdge x hv i).1.1 = none
      rw [heq]
      exact he'.2.1

theorem number_routes_is_departures (x : Assignment n k) (hv : Visit x) :
    (rootSet x hv).card = (depotDepartures x).card := by
  rw [← root_image_departures x hv]
  symm
  apply Finset.card_image_of_injective
  intro i j heq
  have hi := (arrivalEdge_spec x hv i).2
  have hj := (arrivalEdge_spec x hv j).2
  rw [heq] at hi
  exact Option.some.inj (hi.symm.trans hj)

end Chapter10.Routing.Arc
