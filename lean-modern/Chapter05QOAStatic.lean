module

public import Chapter05QOAFiber
public import Chapter05QOAAvailability

@[expose] public section

/-! Complete-history equal values and a stored original optimizer.
The master retains all safe token objective rows, including seed/restoration
rows. No theorem makes every optimal master point original feasible. -/
noncomputable section
open Set Chapter02 Chapter03.OAKKT
namespace Chapter05.QOA
variable {n p m r : ℕ} {d : Data n p m r}

def CompleteHistory (d : Data n p m r) (events : List (Event d)) : Prop :=
  ∀ y ∈ d.Y, (d.hardFiber y).Nonempty → ∃ e ∈ events, e.target = y

theorem stored_anchor_below_master (hr : Regularity d)
    {events : List (Event d)} (hv : ∀ e ∈ events, EventValid d e)
    {H : List (Token n p m)} (hrows : ∀ e ∈ events, e.token ∈ H)
    (hc : CompleteHistory d events) {q : Point n p × ℝ} (hq : q ∈ master d H) :
    ∃ e ∈ events, e.restoration = none ∧ e.anchor ∈ d.original ∧ d.f e.anchor ≤ q.2 := by
  obtain ⟨y,hy,hqy,hx⟩ := ((master_mem_iff d H q).mp hq).1
  obtain ⟨e,he,hey⟩ := hc y hy ⟨q.1.1,hx⟩
  have hy' : q.1.2 = intCast e.target := by rw [hey]; exact hqy
  obtain ⟨hn,hf⟩ := event_master_same_fiber hr (hv e he) (hrows e he) hq hy'
  exact ⟨e,he,hn,event_feasible (hv e he) hn,hf⟩

theorem complete_master_nonempty_iff (hr : Regularity d)
    {events : List (Event d)} (hv : ∀ e ∈ events, EventValid d e)
    {H : List (Token n p m)} (hs : SafeRows d H)
    (hrows : ∀ e ∈ events, e.token ∈ H) (hc : CompleteHistory d events) :
    (master d H).Nonempty ↔ d.original.Nonempty := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨e,_,_,he,_⟩ := stored_anchor_below_master hr hv hrows hc hq
    exact ⟨e.anchor,he⟩
  · rintro ⟨z,hz⟩
    exact ⟨(z,d.f z),master_relaxation hr hs ⟨hz,le_rfl⟩⟩

theorem complete_empty_iff (hr : Regularity d)
    {events : List (Event d)} (hv : ∀ e ∈ events, EventValid d e)
    {H : List (Token n p m)} (hs : SafeRows d H)
    (hrows : ∀ e ∈ events, e.token ∈ H) (hc : CompleteHistory d events) :
    d.original = ∅ ↔ master d H = ∅ := by
  have h := not_congr (complete_master_nonempty_iff hr hv hs hrows hc).symm
  simpa only [Set.not_nonempty_iff_eq_empty] using h

theorem original_minimizer_lifts_to_complete_master (hr : Regularity d)
    {events : List (Event d)} (hv : ∀ e ∈ events, EventValid d e)
    {H : List (Token n p m)} (hs : SafeRows d H)
    (hrows : ∀ e ∈ events, e.token ∈ H) (hc : CompleteHistory d events)
    {z : Point n p} (hz : IsMinimizer d.original d.f z) :
    IsMinimizer (master d H) Prod.snd (z,d.f z) := by
  refine ⟨master_relaxation hr hs ⟨hz.1,le_rfl⟩,?_⟩
  intro q hq
  obtain ⟨e,_,_,he,hf⟩ := stored_anchor_below_master hr hv hrows hc hq
  exact (hz.2 e.anchor he).trans hf

theorem complete_master_minimum_stored_optimum (hr : Regularity d)
    {events : List (Event d)} (hv : ∀ e ∈ events, EventValid d e)
    {H : List (Token n p m)} (hs : SafeRows d H)
    (hrows : ∀ e ∈ events, e.token ∈ H) (hc : CompleteHistory d events)
    {q : Point n p × ℝ} (hq : IsMinimizer (master d H) Prod.snd q) :
    ∃ e ∈ events, e.restoration = none ∧
      IsMinimizer d.original d.f e.anchor ∧ d.f e.anchor = q.2 := by
  obtain ⟨e,he,hn,hfeas,hval⟩ := stored_anchor_below_master hr hv hrows hc hq.1
  have hlower := master_lower_bound hr hs hq
  have heq : d.f e.anchor = q.2 := le_antisymm hval (hlower e.anchor hfeas)
  refine ⟨e,he,hn,⟨hfeas,?_⟩,heq⟩
  intro z hz
  rw [heq]
  exact hlower z hz

/-- Compactness supplies an original minimizer; complete history preserves its
lift as a master minimizer at exactly the same attained value. -/
theorem complete_equal_attained_values (hr : Regularity d)
    {events : List (Event d)} (hv : ∀ e ∈ events, EventValid d e)
    {H : List (Token n p m)} (hs : SafeRows d H)
    (hrows : ∀ e ∈ events, e.token ∈ H) (hc : CompleteHistory d events)
    (hne : d.original.Nonempty) :
    ∃ z, IsMinimizer d.original d.f z ∧
      IsMinimizer (master d H) Prod.snd (z,d.f z) := by
  obtain ⟨z,hz⟩ := original_minimum_exists hr hne
  exact ⟨z,hz,original_minimizer_lifts_to_complete_master hr hv hs hrows hc hz⟩

end Chapter05.QOA
