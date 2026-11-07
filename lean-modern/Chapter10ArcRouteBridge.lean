module

public import Chapter10ArcPaths
public import Chapter10ArcReverse
public import Chapter10Routes

@[expose] public section

/-! Forward bridge from the actual finite successor trace and selected event
coordinates to timed lists and physical position schedules. No edge-list
correspondence or route feasibility is postulated. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing.Arc
open Chapter10.Routing Chapter10.Routing.FinitePaths
variable {n k : ℕ}

def eventClock (x : Assignment n k) (hv : Visit x) (i : Fin n) : Fin k :=
  (arrivalEdge x hv i).2.2

theorem arrival_event (x : Assignment n k) (hv : Visit x) (i : Fin n) :
    (arrivalEdge x hv i).2 = (some i,eventClock x hv i) :=
  Prod.ext (arrivalEdge_spec x hv i).2 rfl

theorem departure_arrival_link (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i j : Fin n) (h : next x hv hf i = some j) :
    departureEdge x hv hf i = arrivalEdge x hv j :=
  (arrivalEdge_eq x hv j (departureEdge x hv hf i) (departureEdge_spec x hv hf i).1 h).symm

theorem next_arrival_source (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i j : Fin n) (h : next x hv hf i = some j) :
    (arrivalEdge x hv j).1 = (some i,eventClock x hv i) := by
  rw [← departure_arrival_link x hv hf i j h]
  exact (departureEdge_spec x hv hf i).2

theorem suffix_terminal_next (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    {i js} (h : Suffix (next x hv hf) i js) :
    next x hv hf (js.getLast h.nonempty) = none := by
  induction h with
  | last hi => simpa using hi
  | step hi ht ih => simpa only [List.getLast_cons ht.nonempty] using ih

theorem suffix_terminal_unique (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    {i js} (h : Suffix (next x hv hf) i js) {j}
    (hm : j ∈ js) (hj : next x hv hf j = none) : j = js.getLast h.nonempty := by
  induction h with
  | last hi => simpa using hm
  | @step i a js hi ht ih =>
    rcases List.mem_cons.mp hm with heq | hmem
    · subst j
      simp [hi] at hj
    · simpa only [List.getLast_cons ht.nonempty] using ih hmem

/-- The actual timed transition list is the arrival edge of each customer in
order followed by precisely the last customer's selected departure edge. -/
theorem suffix_timedEdges (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    {i js} (h : Suffix (next x hv hf) i js) :
    timedEdges (eventClock x hv) (departureEdge x hv hf (js.getLast h.nonempty)).2.2
      (arrivalEdge x hv i).1 js =
    js.map (arrivalEdge x hv) ++ [departureEdge x hv hf (js.getLast h.nonempty)] := by
  induction h with
  | @last i hi =>
    have ha : ((arrivalEdge x hv i).1,(some i,eventClock x hv i)) = arrivalEdge x hv i :=
      Prod.ext rfl (arrival_event x hv i).symm
    have hd : ((some i,eventClock x hv i),(none,(departureEdge x hv hf i).2.2)) =
        departureEdge x hv hf i :=
      Prod.ext (departureEdge_spec x hv hf i).2.symm (Prod.ext hi.symm rfl)
    simp only [List.getLast_singleton, timedEdges, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, ha, hd]
  | @step i j js hi ht ih =>
    have ha : ((arrivalEdge x hv i).1,(some i,eventClock x hv i)) = arrivalEdge x hv i :=
      Prod.ext rfl (arrival_event x hv i).symm
    simp only [List.getLast_cons ht.nonempty, timedEdges, List.map_cons, List.cons_append, ha]
    rw [← next_arrival_source x hv hf i j hi, ih]

/-- Every reconstructed transition is genuinely selected, derived from the
proved equality rather than included as a route-model premise. -/
theorem suffix_timedEdges_selected (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    {i js} (h : Suffix (next x hv hf) i js) (e : Edge n k)
    (he : e ∈ timedEdges (eventClock x hv) (departureEdge x hv hf (js.getLast h.nonempty)).2.2
      (arrivalEdge x hv i).1 js) : x e = true := by
  rw [suffix_timedEdges x hv hf h] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
    exact (arrivalEdge_spec x hv j).1
  · have heq := List.mem_singleton.mp he
    subst e
    exact (departureEdge_spec x hv hf _).1

/-- Validity of actual timed edges entails all allowed arcs and an actual
position schedule, for any finite customer list. -/
theorem timedEdges_valid_schedule (D : Data n) (T : Grid k)
    (clock : Fin n → Fin k) (ret : Fin k) (start : Event n k) (js : List (Fin n))
    (h : ∀ e ∈ timedEdges clock ret start js, edgeValid D T e) :
    AllowedFrom D start.1 js ∧
    ScheduleFrom D start.1 (T.time start.2) js (js.map (fun i => T.time (clock i))) (T.time ret) := by
  induction js generalizing start with
  | nil =>
    have he := h (start,(none,ret)) (by simp [timedEdges])
    exact ⟨he.2.2.1,he.2.2.2⟩
  | cons i js ih =>
    have he := h (start,(some i,clock i)) (by simp [timedEdges])
    have ht := ih (some i,clock i) (fun e hm => h e (List.mem_cons_of_mem _ hm))
    exact ⟨⟨he.2.2.1,ht.1⟩,⟨he.1.1,he.1.2,he.2.2.2,ht.2⟩⟩

/-- Waiting at departure is permitted: the same customer/return clocks remain
feasible when the initial departure time is reduced. -/
theorem schedule_start_le {D : Data n} {prev : Node n} {e s : ℝ} {js ss ret}
    (hes : e ≤ s) (h : ScheduleFrom D prev s js ss ret) :
    ScheduleFrom D prev e js ss ret := by
  cases js with
  | nil =>
    cases ss with
    | nil => exact le_trans (add_le_add hes le_rfl) h
    | cons a as => simp [ScheduleFrom] at h
  | cons j js =>
    cases ss with
    | nil => simp [ScheduleFrom] at h
    | cons a as => exact ⟨h.1,h.2.1,le_trans (add_le_add hes le_rfl) h.2.2.1,h.2.2.2⟩

def extractedPath (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (r : Fin n → ℕ) (hr : StrictRank x r) (a : Fin n) : TimedPath n k where
  customers := routeTrace x hv hf r hr a
  departure := (arrivalEdge x hv a).1.2
  returnTime := (departureEdge x hv hf
    ((routeTrace x hv hf r hr a).getLast (routeTrace_elementary x hv hf r hr a).1)).2.2

theorem extractedPath_edges (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (r : Fin n → ℕ) (hr : StrictRank x r) (a : Fin n) (ha : prev x hv a = none) :
    (extractedPath x hv hf r hr a).edges (eventClock x hv) =
      (routeTrace x hv hf r hr a).map (arrivalEdge x hv) ++
      [departureEdge x hv hf ((routeTrace x hv hf r hr a).getLast
        (routeTrace_elementary x hv hf r hr a).1)] := by
  have hs : (none,(arrivalEdge x hv a).1.2) = (arrivalEdge x hv a).1 := Prod.ext ha.symm rfl
  unfold TimedPath.edges extractedPath
  rw [hs]
  exact suffix_timedEdges x hv hf (routeTrace_spec x hv hf r hr a)

theorem extractedPath_edge_set (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (r : Fin n → ℕ) (hr : StrictRank x r) (a : Fin n) (ha : prev x hv a = none) :
    ((extractedPath x hv hf r hr a).edges (eventClock x hv)).toFinset =
      routeEdges x hv hf r hr a := by
  rw [extractedPath_edges x hv hf r hr a ha]
  ext e
  rw [List.mem_toFinset, mem_routeEdges]
  constructor
  · intro he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i,hi,hei⟩ := List.mem_map.mp he
      exact ⟨i,hi,Or.inl hei.symm⟩
    · have heq := List.mem_singleton.mp he
      exact ⟨_,List.getLast_mem _,Or.inr ⟨suffix_terminal_next x hv hf
        (routeTrace_spec x hv hf r hr a),heq⟩⟩
  · rintro ⟨i,hi,hei | ⟨hnext,hei⟩⟩
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨i,hi,hei.symm⟩
    · have hilast := suffix_terminal_unique x hv hf (routeTrace_spec x hv hf r hr a) hi hnext
      apply List.mem_append_right
      simp [hei,hilast]

/-- Main forward physical endpoint: actual selected customer event clocks and
last selected return define a schedule from zero via the nonnegative grid. -/
theorem extractedPath_realization (D : Data n) (T : Grid k) (x : Assignment n k)
    (h : Feasible D T x) (r : Fin n → ℕ) (hr : StrictRank x r)
    (a : Fin n) (ha : prev x h.1 a = none) :
    let p := extractedPath x h.1 h.2.1 r hr a
    p.customers ≠ [] ∧ p.customers.Nodup ∧ AllowedFrom D none p.customers ∧
    ScheduleFrom D none (T.time p.departure) p.customers
      (p.customers.map (customerClock T x h.1)) (T.time p.returnTime) ∧
    ScheduleFrom D none 0 p.customers
      (p.customers.map (customerClock T x h.1)) (T.time p.returnTime) := by
  dsimp only
  let p := extractedPath x h.1 h.2.1 r hr a
  have hvalid : ∀ e ∈ p.edges (eventClock x h.1), edgeValid D T e := by
    intro e he
    have hx : x e = true := by
      have hm : e ∈ routeEdges x h.1 h.2.1 r hr a := by
        rw [← extractedPath_edge_set x h.1 h.2.1 r hr a ha]
        exact List.mem_toFinset.mpr he
      exact (mem_chosen x e).mp (routeEdges_selected x h.1 h.2.1 r hr a hm)
    exact ⟨h.2.2.1 e hx,h.2.2.2.1 e hx,h.2.2.2.2.1 e hx,h.2.2.2.2.2 e hx⟩
  obtain ⟨hal,hs⟩ := timedEdges_valid_schedule D T (eventClock x h.1) p.returnTime
    (none,p.departure) p.customers hvalid
  exact ⟨(routeTrace_elementary x h.1 h.2.1 r hr a).1,
    (routeTrace_elementary x h.1 h.2.1 r hr a).2,hal,hs,
    schedule_start_le (T.nonnegative p.departure) hs⟩

/-- Actual timed transitions retain multiplicity in the cost sum. -/
theorem timedEdges_cost (D : Data n) (clock : Fin n → Fin k) (ret : Fin k)
    (start : Event n k) (js : List (Fin n)) :
    ((timedEdges clock ret start js).map (fun e => D.cost e.1.1 e.2.1)).sum =
      edgeCostFrom D start.1 js := by
  induction js generalizing start with
  | nil => simp [timedEdges,edgeCostFrom]
  | cons j js ih => simp [timedEdges,edgeCostFrom,ih]

theorem extractedPath_edges_nodup (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (r : Fin n → ℕ) (hr : StrictRank x r) (a : Fin n) (ha : prev x hv a = none) :
    ((extractedPath x hv hf r hr a).edges (eventClock x hv)).Nodup := by
  rw [extractedPath_edges x hv hf r hr a ha]
  apply List.Nodup.append
  · apply List.Nodup.map _ (routeTrace_elementary x hv hf r hr a).2
    intro i j he
    have hi := (arrivalEdge_spec x hv i).2
    have hj := (arrivalEdge_spec x hv j).2
    rw [he] at hi
    exact Option.some.inj (hi.symm.trans hj)
  · simp
  · apply List.disjoint_singleton.mpr
    intro hm
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hm
    have hd := suffix_terminal_next x hv hf (routeTrace_spec x hv hf r hr a)
    have he' : (arrivalEdge x hv i).2.1 = none := by
      rw [he]
      exact hd
    rw [(arrivalEdge_spec x hv i).2] at he'
    cases he'

/-- The selected route-edge set cost is exactly the physical consecutive-edge
cost, because the actual timed list has no repeated transition. -/
theorem routeEdges_cost_eq_physical (D : Data n) (x : Assignment n k)
    (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ) (hr : StrictRank x r)
    (a : Fin n) (ha : prev x hv a = none) :
    (∑ e ∈ routeEdges x hv hf r hr a, D.cost e.1.1 e.2.1) =
      edgeCostFrom D none (routeTrace x hv hf r hr a) := by
  rw [← extractedPath_edge_set x hv hf r hr a ha]
  rw [List.sum_toFinset _ (extractedPath_edges_nodup x hv hf r hr a ha)]
  exact timedEdges_cost D (eventClock x hv) (extractedPath x hv hf r hr a).returnTime
    (none,(extractedPath x hv hf r hr a).departure) (routeTrace x hv hf r hr a)

open scoped BigOperators in
/-- Full physical route-cost equality keeps the source's complete edge domain:
all selected depot-only coordinates are excluded explicitly. -/
theorem objective_physical_route_costs (D : Data n) (x : Assignment n k)
    (hv : Visit x) (hf : Flow x) (r : Fin n → ℕ) (hr : StrictRank x r)
    (hdd : ∀ e, e.1.1 = none → e.2.1 = none → x e = false) :
    objective D x = ∑ a ∈ rootSet x hv, edgeCostFrom D none (routeTrace x hv hf r hr a) := by
  rw [objective_route_decomposition D x hv hf r hr hdd]
  apply Finset.sum_congr rfl
  intro a ha
  exact routeEdges_cost_eq_physical D x hv hf r hr a (by simpa [rootSet] using ha)

end Chapter10.Routing.Arc

