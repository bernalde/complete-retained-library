module

public import Chapter03FPSearchAnalytic

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch
variable {n m l : ℕ}

theorem selectedAt_iff (d : Data n m l) {p : Point n m} (hp : p ∈ d.relaxation)
    (j : Fin l) : selectedAt d p j ↔ ¬OAKKT.AffineRow (d.g j) ∧ d.g j p = 0 := by
  constructor
  · rintro ⟨hn, ha⟩
    exact ⟨hn, le_antisymm (hp.2 j) ha⟩
  · rintro ⟨hn, ha⟩
    exact ⟨hn, le_of_eq ha.symm⟩

theorem initial_valid (d : Data n m l) {p : Point n m} (hp : p ∈ d.relaxation) :
    Valid d (initialState p) := ⟨hp, by simp [initialState]⟩

theorem append_valid (d : Data n m l) {s : State n m} (hs : Valid d s)
    {e : Event n m} (he : EventValid d e) : Valid d (append s e) := by
  refine ⟨hs.seed, ?_⟩
  intro a ha
  simp only [append, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact hs.events a ha
  · exact he

theorem master_rows (d : Data n m l) (mode : Mode) (s : State n m)
    {p : Point n m} (hp : p ∈ master d mode s) : Rows d s p := hp.2.2.1

theorem master_affine_row (d : Data n m l) (h : Analytic d)
    {mode : Mode} {s : State n m} (hs : Valid d s)
    {p : Point n m} (hp : p ∈ master d mode s) (j : Fin l)
    (hj : OAKKT.AffineRow (d.g j)) : d.g j p ≤ 0 := by
  have ht := hp.2.2.1.1 j
  have he := OAKKT.affine_tangent hj (h.derivative_g j s.seed hs.seed.1) p
  change tangent d s.seed j p = d.g j p at he
  rwa [he] at ht

/-- All actual active rows are controlled, even when an affine row is not
selected again at the later anchor: its initial tangent is exact. -/
theorem master_active_tangent (d : Data n m l) (h : Analytic d)
    {mode : Mode} {s : State n m} (hs : Valid d s)
    {p : Point n m} (hp : p ∈ master d mode s)
    {e : Event n m} (he : e ∈ s.history) (j : Fin l)
    (hj : d.g j e.projection = 0) : d.Dg j e.projection (p-e.projection) ≤ 0 := by
  classical
  by_cases ha : OAKKT.AffineRow (d.g j)
  · have hg := master_affine_row d h hs hp j ha
    have ht := OAKKT.affine_tangent ha
      (h.derivative_g j e.projection (hs.events e he).projection_min.1.1) p
    rw [hj, zero_add] at ht
    exact ht.le.trans hg
  · have ht := hp.2.2.1.2 e he j ⟨ha, le_of_eq hj.symm⟩
    simpa only [tangent, hj, zero_add] using ht

theorem original_mem_master (d : Data n m l) (h : Analytic d)
    (mode : Mode) {s : State n m} (hs : Valid d s)
    {p : Point n m} (hp : p ∈ d.original) : p ∈ master d mode s := by
  refine ⟨hp.1.1, hp.2, ⟨?_, ?_⟩, ?_⟩
  · intro j
    exact tangent_cut_valid_on (h.convex_g j) hs.seed.1 hp.1.1
      (h.derivative_g j s.seed hs.seed.1) (hp.1.2 j)
  · intro e he j _
    have hv := (hs.events e he).projection_min
    exact tangent_cut_valid_on (h.convex_g j) hv.1.1 hp.1.1
      (h.derivative_g j e.projection hv.1.1) (hp.1.2 j)
  · intro _ e he
    exact projection_normal d h e.target (hs.events e he).projection_min hp.1

theorem empty_master_infeasible (d : Data n m l) (h : Analytic d)
    {mode : Mode} {s : State n m} (hs : Valid d s)
    (he : ¬(master d mode s).Nonempty) : ¬d.original.Nonempty := by
  rintro ⟨p, hp⟩
  exact he ⟨p, original_mem_master d h mode hs hp⟩

theorem enhanced_normal_law (d : Data n m l) (Q : Finset (IntVector m)) :
    NormalLaw d .enhanced Q := by
  intro s _ _ p hp e he
  exact hp.2.2.2 rfl e he

theorem master_append_subset (d : Data n m l) (mode : Mode) (s : State n m)
    (e : Event n m) : master d mode (append s e) ⊆ master d mode s := by
  intro p hp
  refine ⟨hp.1, hp.2.1, ⟨hp.2.2.1.1, ?_⟩, ?_⟩
  · intro a ha j hj
    exact hp.2.2.1.2 a (List.mem_append_left _ ha) j hj
  · intro hm a ha
    exact hp.2.2.2 hm a (List.mem_append_left _ ha)

end Chapter03.FPSearch
