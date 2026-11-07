module

public import Chapter03OAExecState
public import Chapter03OAExecArticleGMaster

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

theorem G_seed_valid : SeedValid Gdata (pt 0 (1/2)) :=
  ⟨G_initial_minimum,Set.mem_univ _,G_initial_fractional⟩

theorem G_reachable_events {epsilon : ℝ} {s : State Gdata}
    (hs : Reachable Gdata (pt 0 (1/2)) epsilon s) :
    ∀ e ∈ s.history, EventValid Gdata e := by
  induction hs with
  | initial => simp [initialState]
  | next hs hstep ih =>
    cases hstep with
    | step ho q e he hy =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact ih a ha
      · simpa only [List.mem_singleton.mp ha] using he

/-- Every named local hypothesis of the generic corrected driver is proved
for G. This proof covers every certificate-bearing fixed selection and every
master tie; it assumes neither progress nor a whole run. -/
theorem G_local_availability (epsilon : ℝ) :
    LocalAvailability Gdata (pt 0 (1/2)) epsilon where
  master_attainment s hs _ _ _ := G_master_attained s.history (G_reachable_events hs)
  fixed_or_restoration s hs ho q := by
    obtain ⟨y,hy,he⟩ := master_integer q.mem
    exact ⟨G_event y hy,G_event_valid y hy,he⟩

theorem G_selectors_exist (epsilon : ℝ) :
    Nonempty (Selector Gdata (pt 0 (1/2)) epsilon) :=
  selector_inhabited (G_local_availability epsilon)

theorem G_event_value (e : Event Gdata) (he : EventValid Gdata e) :
    Gdata.f e.anchor=1/4 := by
  have hx := (G_event_characterization e he).2
  have hy := (binary_box (-1) 1 (xSquareRow 4) e.target).mp e.target_mem
  rcases hy with hy | hy <;>
    norm_num [Gdata,Gf,quadratic,Event.anchor,hx,intCast,hy,scalar]

end Chapter03.OAExec.Article

#print axioms Chapter03.OAExec.Article.G_local_availability
#print axioms Chapter03.OAExec.Article.G_selectors_exist
