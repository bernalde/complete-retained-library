module

public import Chapter03OASoftStoredPolicy
public import Chapter03OAExecInitialization

@[expose] public section

/-! Qualified soft execution. The neutral OA state is paired with its actual
stored policy. Every append retains the selected KKT certificates and weights.
This is a soft sibling, never a coercion to the accepted hard RawStep. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.OASoftExec
variable {n m l r : ℕ}

abbrev State (d : OAExec.Data n m l r) :=
  Σ s : OAExec.State d, Policy d s.history
abbrev State.core {d : Data n m l r} (s : State d) := s.1
abbrev State.policy {d : Data n m l r} (s : State d) := s.2
abbrev State.history {d : Data n m l r} (s : State d) := s.core.history
abbrev State.incumbent {d : Data n m l r} (s : State d) := s.core.incumbent
abbrev State.lower {d : Data n m l r} (s : State d) := s.core.lower

def initialState (d : Data n m l r) (seed : Point n m) (P0 : Policy d []) : State d :=
  ⟨OAExec.initialState d seed, P0⟩

abbrev loopOpen (d : Data n m l r) (epsilon : ℝ) (s : State d) : Prop :=
  OAExec.loopOpen d epsilon s.core
abbrev Invariant (d : Data n m l r) (seed : Point n m) (s : State d) : Prop :=
  OAExec.Invariant d seed s.core

structure MasterChoice (d : Data n m l r) (seed : Point n m) (s : State d) where
  point : Candidate (family d seed s.history)
  attained : Bool
  valid : if attained then IsMinimizer (historyMaster d seed s.history)
    (cost (s.policy.weight seed)) point else
    point ∈ historyMaster d seed s.history ∧
      ¬ BddBelow (cost (s.policy.weight seed) '' historyMaster d seed s.history)

def MasterChoice.nextLower {d : Data n m l r} {seed : Point n m} {s : State d}
    (q : MasterChoice d seed s) : ℝ := if q.attained then q.point.2.1 else s.lower

theorem MasterChoice.mem {d : Data n m l r} {seed : Point n m} {s : State d}
    (q : MasterChoice d seed s) : q.point ∈ historyMaster d seed s.history := by
  have hv := q.valid
  cases h : q.attained <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hv
  · exact hv.1
  · exact hv.1

def advance {d : Data n m l r} {seed : Point n m} (s : State d)
    (q : MasterChoice d seed s) (e : Event d) (G : Generation d e) : State d :=
  ⟨⟨s.history ++ [e], OAExec.nextIncumbent s.core e, q.nextLower⟩,
    s.policy.append e G⟩

inductive RawStep (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    State d → State d → Prop
  | step {s : State d} (open_gap : loopOpen d epsilon s)
      (q : MasterChoice d seed s) (e : Event d) (generation : Generation d e)
      (same_y : q.point.1.2 = intCast e.target) :
      RawStep d seed epsilon s (advance s q e generation)

inductive Reachable (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :
    State d → Prop
  | initial (P0 : Policy d []) : Reachable d seed epsilon (initialState d seed P0)
  | next {s t : State d} (before : Reachable d seed epsilon s)
      (step : RawStep d seed epsilon s t) : Reachable d seed epsilon t

inductive Decision (d : Data n m l r) (seed : Point n m) (s : State d)
  | empty (valid : historyMaster d seed s.history = ∅)
  | next (q : MasterChoice d seed s) (event : Event d)
      (generation : Generation d event) (same_y : q.point.1.2 = intCast event.target)

/-- Only requested fixed/restoration generations remain local assumptions;
soft polyhedral attainment is derived from the accepted structural theorem. -/
def LocalAvailability (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) : Prop :=
  ∀ s, Reachable d seed epsilon s → loopOpen d epsilon s →
    ∀ q : MasterChoice d seed s, ∃ e : Event d,
      Nonempty (Generation d e) ∧ q.point.1.2 = intCast e.target

def Selector (d : Data n m l r) (seed : Point n m) (epsilon : ℝ) :=
  ∀ s, Reachable d seed epsilon s → loopOpen d epsilon s → Decision d seed s

theorem selector_inhabited {d : Data n m l r} {seed : Point n m} {epsilon : ℝ}
    (availability : LocalAvailability d seed epsilon) :
    Nonempty (Selector d seed epsilon) := by
  classical
  have hd : ∀ s, Reachable d seed epsilon s → loopOpen d epsilon s →
      Nonempty (Decision d seed s) := by
    intro s hs ho
    by_cases he : (historyMaster d seed s.history).Nonempty
    · have hq : Nonempty (MasterChoice d seed s) := by
        by_cases hb : BddBelow (cost (s.policy.weight seed) '' historyMaster d seed s.history)
        · obtain ⟨z,hz⟩ := soft_master_attained_of_bddBelow d seed s.history
            (s.policy.weight seed) he hb
          exact ⟨⟨z,true,hz⟩⟩
        · obtain ⟨z,hz⟩ := he
          exact ⟨⟨z,false,hz,hb⟩⟩
      obtain ⟨q⟩ := hq
      obtain ⟨e,⟨G⟩,hy⟩ := availability s hs ho q
      exact ⟨.next q e G hy⟩
    · exact ⟨.empty (Set.not_nonempty_iff_eq_empty.mp he)⟩
  exact ⟨fun s hs ho => Classical.choice (hd s hs ho)⟩

theorem original_embed_mem {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    {p : Point n m} (hp : p ∈ d.original) :
    embed d.f (family d seed H) p ∈ historyMaster d seed H := by
  have h := OAExec.original_epigraph_mem a hH hp
  exact embed_of_hard_epigraph h.1 ⟨h.2, trivial⟩

theorem master_lower_bound {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {s : State d} (hi : Invariant d seed s)
    {z : Candidate (family d seed s.history)}
    (hm : IsMinimizer (historyMaster d seed s.history) (cost (s.policy.weight seed)) z) :
    IsLowerBound d.original d.f z.2.1 := by
  intro p hp
  have hn := penalty_nonneg (s.policy.weight_nonneg seed) hm.1
  have hb := hm.2 _ (original_embed_mem a hi.history hp)
  rw [cost_embed] at hb
  exact (le_add_of_nonneg_right hn).trans hb

theorem empty_master_original_empty {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    (he : historyMaster d seed H = ∅) : ¬ d.original.Nonempty := by
  rintro ⟨p,hp⟩
  have hm := original_embed_mem a hH hp
  rw [he] at hm
  exact hm

theorem initial_invariant {d : Data n m l r} {seed : Point n m}
    (hs : SeedValid d seed) (P0 : Policy d []) :
    Invariant d seed (initialState d seed P0) := OAExec.initial_invariant hs

theorem advance_invariant {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {s : State d} (hi : Invariant d seed s)
    (q : MasterChoice d seed s) {e : Event d} (G : Generation d e) :
    Invariant d seed (advance s q e G) := by
  classical
  refine ⟨validHistory_append hi.history G.valid,?_,?_,?_,?_⟩
  · change IsLowerBound d.original d.f q.nextLower
    cases hq : q.attained with
    | false => simpa [MasterChoice.nextLower,hq] using hi.lower
    | true =>
      have hv : IsMinimizer (historyMaster d seed s.history) (cost (s.policy.weight seed)) q.point := by
        simpa [hq] using q.valid
      simpa [MasterChoice.nextLower,hq] using master_lower_bound a hi hv
  · intro u hu
    change OAExec.nextIncumbent s.core e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [nextIncumbent,if_pos hn] at hu
      rcases keepBest_cases hu with rfl | hu
      · exact event_feasible G.valid hn
      · exact hi.feasible _ hu
    · exact hi.feasible _ (by simpa [nextIncumbent,hn] using hu)
  · intro u hu
    change OAExec.nextIncumbent s.core e = some u at hu
    by_cases hn : e.restoration = none
    · simp only [nextIncumbent,if_pos hn] at hu
      rcases keepBest_cases hu with rfl | hu
      · exact ⟨e,List.mem_append_right _ (by simp),hn,rfl⟩
      · obtain ⟨v,hv,hnv,ha⟩ := hi.provenance u hu
        exact ⟨v,List.mem_append_left _ hv,hnv,ha⟩
    · obtain ⟨v,hv,hnv,ha⟩ := hi.provenance u
        (by simpa [nextIncumbent,hn] using hu)
      exact ⟨v,List.mem_append_left _ hv,hnv,ha⟩
  · intro v hv hnv
    change v ∈ s.history ++ [e] at hv
    change ∃ u, OAExec.nextIncumbent s.core e = some u ∧ d.f u ≤ d.f v.anchor
    by_cases hn : e.restoration = none
    · obtain ⟨u,hu,hle⟩ := keepBest_some d.f s.incumbent e.anchor
      refine ⟨u,by simpa [nextIncumbent,hn] using hu,?_⟩
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨w,hw,hlew⟩ := hi.dominates v hv hnv
        change s.incumbent = some w at hw
        rw [hw] at hu
        exact (keepBest_le_old hu).trans hlew
      · simpa only [List.mem_singleton.mp hv] using hle
    · rcases List.mem_append.mp hv with hv | hv
      · simpa [nextIncumbent,hn] using hi.dominates v hv hnv
      · exact False.elim (hn ((List.mem_singleton.mp hv) ▸ hnv))

theorem rawStep_invariant {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {epsilon : ℝ} {s t : State d}
    (hi : Invariant d seed s) (h : RawStep d seed epsilon s t) :
    Invariant d seed t := by
  cases h with
  | step _ q e G _ => exact advance_invariant a hi q G

theorem reachable_invariant {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} (hs : SeedValid d seed) {epsilon : ℝ} {s : State d}
    (h : Reachable d seed epsilon s) : Invariant d seed s := by
  induction h with
  | initial P0 => exact initial_invariant hs P0
  | next _ h ih => exact rawStep_invariant a ih h


end Chapter03.OASoftExec
