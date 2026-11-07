module

public import Chapter03OAExistenceIEvents

@[expose] public section

/-! At epsilon=0 every execution of the article-style I adaptation must
perform restoration. The argument uses the actual master, reachable states,
execution relation and driver, not a separate assumed trace. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.OAExec.ArticleI

theorem domain_product : domain = bounds.region ×ˢ Set.Icc (scalar 0) (scalar 1) := by
  rw [bounds_region]
  ext p
  simp only [Set.mem_prod,Set.mem_univ,true_and,Set.mem_Icc]
  change (0 ≤ p.2 0 ∧ p.2 0 ≤ 1) ↔ (∀ i, 0 ≤ p.2 i) ∧ ∀ i, p.2 i ≤ 1
  simp only [Fin.forall_fin_one]

theorem bounds_unbounded : ¬ Bornology.IsBounded bounds.region := by
  intro hX
  apply domain_unbounded
  rw [domain_product]
  exact hX.prod isCompact_Icc.isBounded

theorem lower_small_without_restoration {s : State spec}
    (hs : Reachable spec I.seed 0 s)
    (hn : ∀ e ∈ s.history, e.restoration = none) : s.lower ≤ 3/16 := by
  induction hs with
  | initial => norm_num [initialState,spec,I.seed,I.objective,pt,scalar]
  | @next s t before step ih =>
    cases step with
    | step ho q e he hy =>
      have hp : ∀ a ∈ s.history, a.restoration = none := by
        intro a ha
        exact hn a (by simp [advance,ha])
      have hl := low_master_point s.history
        (reachable_invariant analytic seed_valid before).history.2 hp
      have hq := q.valid
      cases h : q.attained with
      | false =>
        simpa [advance,MasterChoice.nextLower,h] using ih hp
      | true =>
        simp only [h,↓reduceIte] at hq
        have hh := hq.2 _ hl
        simpa [advance,MasterChoice.nextLower,h] using hh

theorem incumbent_cost {s : State spec} (hs : Reachable spec I.seed 0 s)
    {p : P} (hi : s.incumbent = some p) : spec.f p = 1/4 := by
  have inv := reachable_invariant analytic seed_valid hs
  obtain ⟨e,he,hn,ha⟩ := inv.provenance p hi
  have ee := nonrestoration_event (inv.history.2 e he) hn
  rw [← ha,ee]
  norm_num [spec,I.objective,Event.anchor,event1,intCast,target1,scalar]

theorem execution_requires_restoration {s : State spec} {out : Output 1 1}
    (hx : Execution spec I.seed 0 s out) (hs : Reachable spec I.seed 0 s)
    (hn : ∀ e ∈ s.history, e.restoration = none) : 0 < out.restorations := by
  induction hx with
  | @gap s p hi ht =>
    have hc := incumbent_cost hs hi
    have hl := lower_small_without_restoration hs hn
    rw [hc] at ht
    norm_num at ht ⊢
    linarith
  | @empty s ho he =>
    have hm := original_epigraph_mem analytic
      (reachable_invariant analytic seed_valid hs).history solution_original
    rw [he] at hm
    exact False.elim hm
  | @step s ho q e he hy out tail ih =>
    by_cases hrest : e.restoration = none
    · have hr : Reachable spec I.seed 0 (advance s q e) :=
        .next hs (.step ho q e he hy)
      have hnext : ∀ a ∈ (advance s q e).history, a.restoration = none := by
        intro a ha
        simp only [advance,List.mem_append,List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hn a ha
        · exact hrest
      have hh := ih hr hnext
      simpa [countStep,eventRestorations,hrest] using hh
    · simp [countStep,eventRestorations,hrest]

def initial : Initialization spec := .minimum I.seed seed_minimum seed_valid.2.1

theorem initialization_unique (i : Initialization spec) : i = initial := by
  cases i with
  | empty he =>
    have hh := seed_minimum.1
    rw [he] at hh
    exact False.elim hh
  | minimum p hm hd =>
    have hp := seed_unique hm
    subst p
    rfl

/-- Full source endpoint plus a required positive restoration count at zero
tolerance, for every actual initializer and selector. Counts remain the general
proved bounds; this theorem does not assert the old all-soft exact3/3/1 trace. -/
theorem every_initialized_return_restores :
    Nonempty (Initialization spec) ∧
    (∀ seed, SeedValid spec seed → LocalAvailability spec seed 0) ∧
    Nonempty (InitializedSelectors spec 0) ∧
    ∀ (choose : InitializedSelectors spec 0) (i : Initialization spec),
      ∃ out, execute spec 0 choose i = some out ∧
        ReturnCertificate spec 0 out.result ∧ 0 < out.restorations ∧
        out.masters ≤ spec.box.card+1 ∧ out.fixed ≤ spec.box.card+1 ∧
        out.restorations ≤ spec.box.card := by
  have main := article_source_initialized_finite_return bounds spec encoding analytic
    domain_article relaxation_bounded all_minima_licq (le_refl (0 : ℝ))
  refine ⟨main.1,main.2.1,main.2.2.1,?_⟩
  intro choose i
  obtain ⟨out,hr,hc,hm,hf,hrest⟩ := main.2.2.2 choose i
  have heq := initialization_unique i
  have run : runFuel spec I.seed 0 (choose I.seed seed_valid) (spec.box.card+1)
      (initialState spec I.seed) .initial = some out := by
    simpa only [heq,initial,execute,dif_neg seed_valid.2.2] using hr
  have hex := runFuel_execution spec I.seed 0 (choose I.seed seed_valid) _ _ .initial run
  have hp := execution_requires_restoration hex .initial (by simp [initialState])
  exact ⟨out,hr,hc,hp,hm,hf,hrest⟩

end Chapter03.OAExec.ArticleI
