module

public import Chapter03FPProcedureModel

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02
namespace Chapter03.FP
variable {n m l r : ℕ}

def kept (s : State n m) : List (Event n m) :=
  match s.lastSuccess with | none => s.history | some k => s.history.take k

def belowIncumbent (d : Data n m l r) (s : State n m) (p : Point n m) : Prop :=
  ∀ u, s.incumbent = some u → d.f p ≤ d.f u

structure EventValid (d : Data n m l r) (e : Event n m) : Prop where
  target_box : e.target ∈ d.box
  projection : IsMinimizer (d.region e.generationLevel) (distance e.target) e.projection
  outcome : match e.success with
    | none => distance e.target e.projection ≠ 0
    | some pu => distance e.target e.projection = 0 ∧ IsMinimizer (d.fiber e.target) d.f pu.1

structure Invariant (d : Data n m l r) (s : State n m) : Prop where
  seed : s.seed ∈ d.relaxation
  valid : ∀ e ∈ s.history, EventValid d e
  incumbent : ∀ u, s.incumbent = some u → u ∈ d.original
  best : ∀ e ∈ s.history, ∀ pu, e.success = some pu →
    ∃ u, s.incumbent = some u ∧ d.f u ≤ d.f pu.1
  generation : ∀ e ∈ s.history, d.region (d.level s.incumbent) ⊆ d.region e.generationLevel
  handoff_generation : ∀ e ∈ kept s, e.success = none →
    ∀ p ∈ d.relaxation, belowIncumbent d s p → p ∈ d.region e.generationLevel
  last_bound : ∀ k, s.lastSuccess = some k → k < s.history.length
  synchronized : s.lastSuccess = none ↔ s.incumbent = none
  nodup : (s.history.map Event.target).Nodup

theorem initial_invariant (d : Data n m l r) {p : Point n m} (hp : p ∈ d.relaxation) :
    Invariant d (initialState p) := by
  exact ⟨hp,by simp [initialState],by simp [initialState],by simp [initialState],
    by simp [initialState],by simp [kept,initialState],by simp [initialState],
    by simp [initialState],by simp [initialState]⟩

theorem event_anchor_relaxation (d : Data n m l r) {e : Event n m}
    (h : EventValid d e) : e.anchor ∈ d.relaxation := by
  cases he : e.success with
  | none => simpa [Event.anchor,he] using h.projection.1.1
  | some pu =>
    have ho := h.outcome
    rw [he] at ho
    simpa [Event.anchor,he] using ho.2.1.1

theorem event_target_excluded (d : Data n m l r) {s : State n m}
    (hs : Invariant d s) {z : Point n m × ℝ} (hz : z ∈ master d s)
    {e : Event n m} (he : e ∈ s.history) : z.1.2 ≠ intCast e.target := by
  cases ho : e.success with
  | some pu => exact hz.2.2.1 e he (by simp [ho])
  | none =>
    intro hsame
    have hnormal := hz.2.1 e he ho
    have hne : Chapter03.yMap n m e.projection ≠ intY e.target := by
      intro hy
      have hv := (hs.valid e he).outcome
      rw [ho] at hv
      exact hv ((distance_zero_iff _ _).mpr ((yMap_eq_intY_iff _ _).mp hy))
    have hneg := Chapter03.projection_cut_excludes hne
    have hy := (yMap_eq_intY_iff z.1 e.target).mpr hsame
    unfold Event.normal at hnormal
    rw [hy] at hnormal
    linarith

theorem master_target_fresh (d : Data n m l r) {s : State n m}
    (hs : Invariant d s) {z : Point n m × ℝ} (hz : z ∈ master d s)
    {y : IntVector m} (hy : z.1.2 = intCast y) : y ∉ s.history.map Event.target := by
  intro hm
  obtain ⟨e,he,hey⟩ := List.mem_map.mp hm
  exact event_target_excluded d hs hz he (by simpa [hey] using hy)

theorem reply_valid (d : Data n m l r) {s : State n m}
    {z : Point n m × ℝ} (hz : z ∈ master d s) {e : Event n m}
    (h : EventReply d s z e) : EventValid d e := by
  obtain ⟨y,hy,hye⟩ := master_box_integer d s hz
  have heq : y = e.target := intCast_injective (hye.symm.trans h.target_eq)
  refine ⟨heq ▸ hy,?_,?_⟩
  · rw [h.generation_eq]; exact h.projection_min
  · cases he : e.success with
    | none => simpa [he] using h.outcome
    | some pu =>
      have ho := h.outcome
      rw [he] at ho
      exact ⟨ho.1,ho.2.1⟩

theorem kept_positive_append (s : State n m) (e : Event n m) (he : e.success = none)
    (hbound : ∀ k, s.lastSuccess = some k → k < s.history.length) :
    kept (append s e) = match s.lastSuccess with
      | none => kept s ++ [e]
      | some _ => kept s := by
  cases hk : s.lastSuccess with
  | none => simp [kept,append,he,hk]
  | some k =>
    simp only [kept,append,he,hk]
    exact List.take_append_of_le_length (hbound k hk).le

theorem kept_success_append (s : State n m) (e : Event n m)
    {pu : Point n m × Point n m} (he : e.success = some pu) :
    kept (append s e) = s.history := by
  simp [kept,append,he]

theorem append_invariant (d : Data n m l r) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) {z : Point n m × ℝ}
    (hz : z ∈ master d s) {e : Event n m} (hr : EventReply d s z e) :
    Invariant d (append s e) := by
  have hv := reply_valid d hz hr
  have hnest := append_region_subset d h.delta_nonnegative hr
  have hfresh := master_target_fresh d hs hz hr.target_eq
  refine ⟨hs.seed,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro c hc
    simp only [append,List.mem_append,List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hs.valid c hc
    · exact hv
  · intro u hu
    cases he : e.success with
    | none => exact hs.incumbent u (by simpa [append,he] using hu)
    | some pu =>
      have heu : pu.2 = u := by simpa [append,he] using hu
      have ho := hr.outcome
      rw [he] at ho
      rw [← heu]
      exact best_feasible d ho.2.2 (fiber_original d e.target ho.2.1.1) hs.incumbent
  · intro c hc pc hpc
    simp only [append,List.mem_append,List.mem_singleton] at hc
    cases he : e.success with
    | none =>
      rcases hc with hc | rfl
      · simpa [append,he] using hs.best c hc pc hpc
      · simp [he] at hpc
    | some pu =>
      have ho := hr.outcome
      rw [he] at ho
      refine ⟨pu.2,by simp [append,he],?_⟩
      rcases hc with hc | rfl
      · obtain ⟨u,hu,hle⟩ := hs.best c hc pc hpc
        have hb : BestChoice d (some u) pu.1 pu.2 := by simpa [hu] using ho.2.2
        exact (best_le_old d hb).trans hle
      · have hep : pu = pc := by simpa [he] using hpc
        simpa [← hep] using best_le_new d ho.2.2
  · intro c hc p hp
    simp only [append,List.mem_append,List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hs.generation c hc (hnest hp)
    · rw [hr.generation_eq]; exact hnest hp
  · intro c hc hcn p hp hpu
    cases he : e.success with
    | none =>
      rw [kept_positive_append s e he hs.last_bound] at hc
      have hpu' : belowIncumbent d s p := by simpa [belowIncumbent,append,he] using hpu
      cases hk : s.lastSuccess with
      | none =>
        simp only [hk,List.mem_append,List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact hs.handoff_generation c hc hcn p hp hpu'
        · have hi : s.incumbent = none := hs.synchronized.mp hk
          rw [hr.generation_eq,hi]
          exact ⟨hp,trivial⟩
      | some k =>
        simp only [hk] at hc
        exact hs.handoff_generation c hc hcn p hp hpu'
    | some pu =>
      rw [kept_success_append s e he] at hc
      have hle : d.f p ≤ d.f pu.2 := hpu pu.2 (by simp [append,he])
      exact hs.generation c hc (success_sublevel_subset_old_region d hr he hp hle)
  · intro k hk
    cases he : e.success with
    | none =>
      have hold : s.lastSuccess = some k := by simpa [append,he] using hk
      have hb := hs.last_bound k hold
      simpa [append] using Nat.lt_succ_of_lt hb
    | some pu =>
      have hk' : s.history.length = k := by simpa [append,he] using hk
      simp [append,← hk']
  · cases he : e.success with
    | none => simpa [append,he] using hs.synchronized
    | some pu => simp [append,he]
  · simp [append,List.nodup_append,hs.nodup,List.disjoint_left,hfresh]
    intro a ha he
    exact hfresh (List.mem_map.mpr ⟨a,ha,he⟩)

end Chapter03.FP
