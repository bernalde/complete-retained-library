module

public import Chapter03PumpSoftModel

@[expose] public section

/-! Actual warm continuation state. The pump prefix is immutable; the suffix
policy and seed agreement travel with the neutral OA state. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.PumpSoft
variable {n m l r : ℕ}

structure State (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) where
  core : OAExec.State d
  policy : Policy d core.history
  agreement : SeedAgreement d delta P W policy

abbrev State.history {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
    {W : Occurrence (prefixFamily d delta P) → ℝ} (s : State d delta P W) := s.core.history
abbrev State.incumbent {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
    {W : Occurrence (prefixFamily d delta P) → ℝ} (s : State d delta P W) := s.core.incumbent
abbrev State.lower {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
    {W : Occurrence (prefixFamily d delta P) → ℝ} (s : State d delta P W) := s.core.lower

def initialState (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (hW : ∀ o, 0 ≤ W o) : State d delta P W :=
  ⟨PumpOA.initialState d P, initialPolicy d delta P W hW,
    initialPolicy_agreement d delta P W hW⟩

abbrev loopOpen (d : OAExec.Data n m l r) {delta : ℝ} {P : FP.State n m}
    {W : Occurrence (prefixFamily d delta P) → ℝ} (epsilon : ℝ)
    (s : State d delta P W) : Prop := OAExec.loopOpen d epsilon s.core

abbrev Invariant (d : OAExec.Data n m l r) {delta : ℝ} (P : FP.State n m)
    {W : Occurrence (prefixFamily d delta P) → ℝ} (s : State d delta P W) : Prop :=
  PumpOA.Invariant d P s.core

structure MasterChoice (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (s : State d delta P W) where
  point : Candidate (family d delta P s.history)
  attained : Bool
  valid : if attained then IsMinimizer (warmMaster d delta P s.history)
    (cost (weight d delta P W s.policy)) point else
    point ∈ warmMaster d delta P s.history ∧
      ¬ BddBelow (cost (weight d delta P W s.policy) '' warmMaster d delta P s.history)

variable {d : OAExec.Data n m l r} {delta : ℝ} {P : FP.State n m}
variable {W : Occurrence (prefixFamily d delta P) → ℝ}

def MasterChoice.nextLower {s : State d delta P W} (q : MasterChoice d delta P W s) : ℝ :=
  if q.attained then q.point.2.1 else s.lower

theorem MasterChoice.mem {s : State d delta P W} (q : MasterChoice d delta P W s) :
    q.point ∈ warmMaster d delta P s.history := by
  have hv := q.valid
  cases h : q.attained <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hv
  · exact hv.1
  · exact hv.1

def advance (s : State d delta P W) (q : MasterChoice d delta P W s)
    (e : OAExec.Event d) (G : Generation d e) : State d delta P W :=
  ⟨⟨s.history ++ [e], OAExec.nextIncumbent s.core e, q.nextLower⟩,
    s.policy.append e G, agreement_append d delta P W s.policy s.agreement e G⟩

inductive RawStep (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (epsilon : ℝ) :
    State d delta P W → State d delta P W → Prop
  | step {s : State d delta P W} (open_gap : loopOpen d epsilon s)
      (q : MasterChoice d delta P W s) (e : OAExec.Event d) (generation : Generation d e)
      (same_y : q.point.1.2 = intCast e.target) :
      RawStep d delta P W epsilon s (advance s q e generation)

inductive Reachable (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (epsilon : ℝ) :
    State d delta P W → Prop
  | initial (hW : ∀ o, 0 ≤ W o) :
      Reachable d delta P W epsilon (initialState d delta P W hW)
  | next {s t : State d delta P W} (before : Reachable d delta P W epsilon s)
      (step : RawStep d delta P W epsilon s t) : Reachable d delta P W epsilon t

inductive Decision (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (s : State d delta P W)
  | empty (valid : warmMaster d delta P s.history = ∅)
  | next (q : MasterChoice d delta P W s) (event : OAExec.Event d)
      (generation : Generation d event) (same_y : q.point.1.2 = intCast event.target)

/-- Local existence obligations are discharged later from data assumptions;
neither progress nor a final return is an availability field. -/
structure LocalAvailability (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (epsilon : ℝ) : Prop where
  master_attainment : ∀ s, Reachable d delta P W epsilon s → loopOpen d epsilon s →
    (warmMaster d delta P s.history).Nonempty →
    BddBelow (cost (weight d delta P W s.policy) '' warmMaster d delta P s.history) →
    ∃ z, IsMinimizer (warmMaster d delta P s.history) (cost (weight d delta P W s.policy)) z
  fixed_or_restoration : ∀ s, Reachable d delta P W epsilon s → loopOpen d epsilon s →
    ∀ q : MasterChoice d delta P W s, ∃ e : OAExec.Event d,
      Nonempty (Generation d e) ∧ q.point.1.2 = intCast e.target

def Selector (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (epsilon : ℝ) :=
  ∀ s, Reachable d delta P W epsilon s → loopOpen d epsilon s → Decision d delta P W s

theorem selector_inhabited {epsilon : ℝ}
    (availability : LocalAvailability d delta P W epsilon) :
    Nonempty (Selector d delta P W epsilon) := by
  classical
  have hd : ∀ s, Reachable d delta P W epsilon s → loopOpen d epsilon s →
      Nonempty (Decision d delta P W s) := by
    intro s hs ho
    by_cases he : (warmMaster d delta P s.history).Nonempty
    · have hq : Nonempty (MasterChoice d delta P W s) := by
        by_cases hb : BddBelow (cost (weight d delta P W s.policy) '' warmMaster d delta P s.history)
        · obtain ⟨z,hz⟩ := availability.master_attainment s hs ho he hb
          exact ⟨⟨z,true,hz⟩⟩
        · obtain ⟨z,hz⟩ := he
          exact ⟨⟨z,false,hz,hb⟩⟩
      obtain ⟨q⟩ := hq
      obtain ⟨e,⟨G⟩,hy⟩ := availability.fixed_or_restoration s hs ho q
      exact ⟨.next q e G hy⟩
    · exact ⟨.empty (Set.not_nonempty_iff_eq_empty.mp he)⟩
  exact ⟨fun s hs ho => Classical.choice (hd s hs ho)⟩

theorem initial_invariant (hs : OAExec.SeedValid d P.seed)
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P) (hW : ∀ o, 0 ≤ W o) :
    Invariant d P (initialState d delta P W hW) := PumpOA.initial_invariant hs hP

theorem improves_before_advance {s : State d delta P W} (q : MasterChoice d delta P W s)
    (e : OAExec.Event d) (G : Generation d e) {p : Point n m}
    (hi : PumpOA.Improves d (advance s q e G).core p) :
    PumpOA.Improves d s.core p := by
  intro u hu
  obtain ⟨v,hv,hle⟩ := PumpOA.nextIncumbent_le_old s.core e hu
  exact (hi v hv).trans_le hle

end Chapter03.PumpSoft
