module

public import Chapter03FPUnboundedInvariant

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02
open Chapter03.FP
namespace Chapter03.FPUnbounded
variable {n m l : ℕ}

theorem anchors_relaxation (d : Data n m l) {s : State n m}
    (hs : Invariant d s) : ∀ a ∈ anchors d s, a.point ∈ d.relaxation := by
  intro a ha
  simp only [anchors,List.mem_cons,List.mem_map] at ha
  rcases ha with rfl | ⟨e,he,rfl⟩
  · exact hs.seed
  · exact event_anchor_relaxation d (hs.valid e he)

theorem epigraph_contains_original (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) {p : Point n m} (hp : p ∈ d.original) :
    (p,d.f p) ∈ epigraph d s := by
  have hpB := relaxation_subset_base d (original_subset_relaxation d hp)
  have ha : ∀ i, (family d s).origin i ∈ d.base := by
    intro i
    exact relaxation_subset_base d (anchors_relaxation d hs _ (List.get_mem _ _))
  refine ⟨hpB,hp.2,?_,?_⟩
  · intro i j _
    exact (tangent_underestimator_on (h.convex_g j) (ha i) hpB
      (h.derivative_g j _ (ha i))).trans (hp.1.2 j)
  · intro i
    exact tangent_underestimator_on h.convex_f (ha i) hpB (h.derivative_f _ (ha i))

theorem current_normals_valid (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) {p : Point n m}
    (hp : p ∈ d.region (d.level s.incumbent)) : retainedNormals s p := by
  intro e he _
  exact projection_normal d h e.generationLevel e.target (hs.valid e he).projection
    (hs.generation e he hp)

theorem kept_subset (s : State n m) : ∀ e ∈ kept s, e ∈ s.history := by
  intro e he
  cases hk : s.lastSuccess with
  | none => simpa [kept,hk] using he
  | some k => exact List.mem_of_mem_take (by simpa [kept,hk] using he)

theorem handoffNormals_iff (s : State n m) (p : Point n m) :
    handoffNormals s p ↔ ∀ e ∈ kept s, e.success = none → 0 ≤ e.normal p := by
  constructor
  · intro hh e he hn
    cases hk : s.lastSuccess with
    | none =>
      have hem : e ∈ s.history := by simpa [kept,hk] using he
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hem
      exact hh i hn (by simp [hk])
    | some k =>
      have hem : e ∈ s.history.take k := by simpa [kept,hk] using he
      obtain ⟨i,hi,hei⟩ := List.mem_take_iff_getElem.mp hem
      have hi' : i < s.history.length := by omega
      have hh' := hh ⟨i,hi'⟩ (by simpa [List.get_eq_getElem,hei] using hn)
        (by
          intro j hj
          have hkj : k=j := by simpa [hk] using hj
          change i < j
          omega)
      simpa [List.get_eq_getElem,hei] using hh'
  · intro hh i hn hi
    apply hh (s.history.get i) _ hn
    cases hk : s.lastSuccess with
    | none => simp [kept,hk]
    | some k =>
      have hik := hi k hk
      simp only [kept,hk]
      exact List.mem_take_iff_getElem.mpr ⟨i.val,by omega,rfl⟩

theorem handoff_normals_valid (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) {p : Point n m}
    (hp : p ∈ d.relaxation) (hpu : belowIncumbent d s p) : handoffNormals s p := by
  apply (handoffNormals_iff s p).mpr
  intro e he hn
  exact projection_normal d h e.generationLevel e.target
    (hs.valid e (kept_subset s e he)).projection (hs.handoff_generation e he hn p hp hpu)

def Improves (d : Data n m l) (s : State n m) (p : Point n m) : Prop :=
  ∀ u, s.incumbent = some u → d.f p < d.f u

theorem master_contains_cutoff (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) {p : Point n m} (hp : p ∈ d.original)
    (hl : Allows (d.level s.incumbent) (d.f p)) : (p,d.f p) ∈ master d s :=
  ⟨epigraph_contains_original d h hs hp,
    current_normals_valid d h hs ⟨original_subset_relaxation d hp,hl⟩,hl⟩

theorem handoff_contains_below (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) {p : Point n m} (hp : p ∈ d.original)
    (hi : belowIncumbent d s p) : (p,d.f p) ∈ handoff d s :=
  ⟨epigraph_contains_original d h hs hp,
    handoff_normals_valid d h hs (original_subset_relaxation d hp) hi⟩

theorem handoff_contains_incumbent (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) {u : Point n m} (hu : s.incumbent = some u) :
    (u,d.f u) ∈ handoff d s := by
  apply handoff_contains_below d h hs (hs.incumbent u hu)
  intro v hv
  have huv : u = v := by simpa [hu] using hv
  simp [huv]

theorem handoff_contains_improving (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) {p : Point n m} (hp : p ∈ d.original)
    (hi : Improves d s p) : (p,d.f p) ∈ handoff d s :=
  handoff_contains_below d h hs hp (fun u hu => (hi u hu).le)

/-- A safe comparison interface, not a finite or attained height lower bound
and not a claim that the OA/DICOPT continuation has been executed. -/
structure SafeHandoff (d : Data n m l) (s : State n m) : Prop where
  embedding : ∀ p ∈ d.original, Improves d s p → (p,d.f p) ∈ handoff d s
  no_incumbent_lower : s.incumbent = none → ∀ L,
    IsLowerBound (handoff d s) Prod.snd L → IsLowerBound d.original d.f L
  merged_lower : ∀ u, s.incumbent = some u → ∀ L,
    IsLowerBound (handoff d s) Prod.snd L → IsLowerBound d.original d.f (min (d.f u) L)
  empty_no_incumbent : s.incumbent = none → ¬(handoff d s).Nonempty → ¬d.original.Nonempty
  empty_with_incumbent : ∀ u, s.incumbent = some u → ¬(handoff d s).Nonempty →
    IsMinimizer d.original d.f u
  bound_closure : ∀ u, s.incumbent = some u → ∀ L,
    IsLowerBound (handoff d s) Prod.snd L → d.f u ≤ L → IsMinimizer d.original d.f u

theorem safe_handoff (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) : SafeHandoff d s := by
  classical
  have embed {p : Point n m} (hp : p ∈ d.original) (hi : Improves d s p) :
      (p,d.f p) ∈ handoff d s := handoff_contains_improving d h hs hp hi
  have merged (u : Point n m) (hu : s.incumbent = some u) (L : ℝ)
      (hL : IsLowerBound (handoff d s) Prod.snd L) :
      IsLowerBound d.original d.f (min (d.f u) L) := by
    intro p hp
    by_cases hi : d.f p < d.f u
    · have hpi : Improves d s p := by
        intro v hv
        have huv : u=v := by simpa [hu] using hv
        simpa [← huv] using hi
      exact (min_le_right _ _).trans (hL (p,d.f p) (embed hp hpi))
    · exact (min_le_left _ _).trans (le_of_not_gt hi)
  refine ⟨fun p hp hi => embed hp hi,?_,merged,?_,?_,?_⟩
  · intro hn L hL p hp
    exact hL (p,d.f p) (embed hp (by simp [Improves,hn]))
  · intro hn he ⟨p,hp⟩
    exact he ⟨(p,d.f p),embed hp (by simp [Improves,hn])⟩
  · intro u hu he
    refine ⟨hs.incumbent u hu,?_⟩
    intro p hp
    by_contra hlt
    have hi : Improves d s p := by
      intro v hv
      have : u=v := by simpa [hu] using hv
      simpa [← this] using lt_of_not_ge hlt
    exact he ⟨(p,d.f p),embed hp hi⟩
  · intro u hu L hL hUL
    refine ⟨hs.incumbent u hu,?_⟩
    simpa only [min_eq_left hUL,IsLowerBound] using merged u hu L hL

/-- Normalized absolute gap; with no incumbent the original mixed set is empty. -/
def TerminalCertificate (d : Data n m l) (s : State n m) : Prop :=
  match s.incumbent with
  | none => ¬d.original.Nonempty
  | some u => u ∈ d.original ∧
      ∀ p ∈ d.original, cutoffValue d.delta (d.f u) ≤ d.f p

theorem empty_master_certificate (d : Data n m l) (h : Analytic d)
    {s : State n m} (hs : Invariant d s) (he : ¬(master d s).Nonempty) :
    TerminalCertificate d s := by
  cases hu : s.incumbent with
  | none =>
    rw [TerminalCertificate,hu]
    rintro ⟨p,hp⟩
    exact he ⟨(p,d.f p),master_contains_cutoff d h hs hp
      (by simp [Data.level,hu,Allows])⟩
  | some u =>
    rw [TerminalCertificate,hu]
    refine ⟨hs.incumbent u hu,?_⟩
    intro p hp
    by_contra hn
    have hlt := lt_of_not_ge hn
    exact he ⟨(p,d.f p),master_contains_cutoff d h hs hp
      (by simpa [Data.level,hu,Allows] using hlt.le)⟩

theorem empty_projection_certificate (d : Data n m l)
    {s : State n m} (hs : Invariant d s)
    (he : ¬(d.region (d.level s.incumbent)).Nonempty) : TerminalCertificate d s := by
  cases hu : s.incumbent with
  | none =>
    rw [TerminalCertificate,hu]
    rintro ⟨p,hp⟩
    exact he ⟨p,original_subset_relaxation d hp,by simp [Data.level,hu,Allows]⟩
  | some u =>
    rw [TerminalCertificate,hu]
    refine ⟨hs.incumbent u hu,?_⟩
    intro p hp
    by_contra hn
    exact he ⟨p,original_subset_relaxation d hp,
      by simpa [Data.level,hu,Allows] using (lt_of_not_ge hn).le⟩

theorem stop_certificate (d : Data n m l) (h : Analytic d)
    {cap : Option ℕ} {s : State n m} (hs : Invariant d s) {reason : StopReason m}
    (ht : Stop d cap s reason) : reason = .handoff ∨ TerminalCertificate d s := by
  cases ht with
  | emptyMaster he => exact Or.inr (empty_master_certificate d h hs he)
  | emptyProjection _ _ _ he => exact Or.inr (empty_projection_certificate d hs he)
  | handoff _ _ _ => exact Or.inl rfl

theorem terminal_gap (d : Data n m l) {s : State n m}
    (h : TerminalCertificate d s) {u : Point n m} (hu : s.incumbent = some u) :
    u ∈ d.original ∧ ∀ p ∈ d.original, d.f u - d.f p ≤ d.delta * max |d.f u| 1 := by
  rw [TerminalCertificate,hu] at h
  refine ⟨h.1,?_⟩
  intro p hp
  have hl := h.2 p hp
  unfold cutoffValue at hl
  linarith

theorem terminal_zero_optimal (d : Data n m l) (hd : d.delta = 0) {s : State n m}
    (h : TerminalCertificate d s) {u : Point n m} (hu : s.incumbent = some u) :
    IsMinimizer d.original d.f u := by
  rw [TerminalCertificate,hu] at h
  exact ⟨h.1,by simpa [cutoffValue,hd] using h.2⟩

/-- At zero tolerance a reachable saved incumbent witnesses both inspected
feasible sets. Thus an uncapped post-success empty stop is impossible. -/
theorem zero_incumbent_witnesses (d : Data n m l) (h : Analytic d)
    (hd : d.delta = 0) {s : State n m} (hs : Invariant d s)
    {u : Point n m} (hu : s.incumbent = some u) :
    u ∈ d.region (d.level s.incumbent) ∧ (u,d.f u) ∈ master d s := by
  have hp := hs.incumbent u hu
  have hl : Allows (d.level s.incumbent) (d.f u) := by
    simp [Data.level,hu,cutoffValue,hd,Allows]
  exact ⟨⟨original_subset_relaxation d hp,hl⟩,master_contains_cutoff d h hs hp hl⟩

theorem zero_incumbent_only_cap (d : Data n m l) (h : Analytic d)
    (hd : d.delta = 0) {s : State n m} (hs : Invariant d s)
    {u : Point n m} (hu : s.incumbent = some u) {cap : Option ℕ}
    {reason : StopReason m} (ht : Stop d cap s reason) : reason = .handoff := by
  have hw := zero_incumbent_witnesses d h hd hs hu
  cases ht with
  | emptyMaster he => exact False.elim (he ⟨(u,d.f u),hw.2⟩)
  | emptyProjection _ _ _ he => exact False.elim (he ⟨u,hw.1⟩)
  | handoff _ _ _ => rfl

end Chapter03.FPUnbounded
