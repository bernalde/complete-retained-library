module

public import Chapter03OAExistenceIData

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.OAExec.ArticleI

def slack : RealVector 1 := scalar (7/16)

theorem restoration_primal : weightedInsert (scalar 0) slack ∈ restSet model (scalar 0) := by
  rw [restSet_insert_iff]
  refine ⟨fun j => Fin.elim0 j,?_,?_⟩ <;>
    intro j <;> fin_cases j <;> norm_num [soft,model,I.data,scalar,slack]

theorem restoration_minimum : IsMinimizer (restSet model (scalar 0)) restCost
    (weightedInsert (scalar 0) slack) := by
  refine ⟨restoration_primal,?_⟩
  intro q hq
  have hq' : weightedInsert (weightedX (n:=1) (s:=1) q)
      (weightedV (n:=1) (s:=1) q) ∈ restSet model (scalar 0) := by
    rw [weightedInsert_project]; exact hq
  obtain ⟨_,hg,_⟩ := (restSet_insert_iff model (scalar 0) _ _).mp hq'
  have hh := hg 0
  norm_num [soft,model,I.data,scalar] at hh
  change weightedLiftObjective (n:=1) (fun _ : Fin 1 => 1) _ ≤
    weightedLiftObjective (n:=1) (fun _ : Fin 1 => 1) q
  rw [weightedLiftObjective_apply,weightedLiftObjective_apply,weightedV_insert]
  norm_num [slack,scalar,Fin.sum_univ_one]
  nlinarith [sq_nonneg (weightedX (n:=1) (s:=1) q 0)]

theorem restoration_unique {x : V} {s : RealVector 1}
    (hm : IsMinimizer (restSet model (scalar 0)) restCost (weightedInsert x s)) :
    x = scalar 0 ∧ s = slack := by
  obtain ⟨_,hg,_⟩ := (restSet_insert_iff model (scalar 0) x s).mp hm.1
  have hh := hg 0
  have hb := hm.2 _ restoration_primal
  rw [restCost_insert,restCost_insert] at hb
  norm_num [soft,model,I.data,scalar] at hh
  norm_num [slack,scalar,Fin.sum_univ_one] at hb
  have hx : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
  refine ⟨scalar_ext hx,?_⟩
  apply scalar_ext
  change s 0 = 7/16
  nlinarith [sq_nonneg (x 0)]

theorem restoration_value : restCost (weightedInsert (scalar 0) slack) = (7/16:ℝ) := by
  rw [restCost_insert]
  norm_num [slack,scalar,Fin.sum_univ_one]

def event0 : Event spec := ⟨target0,target0_mem,scalar 0,some slack⟩
def event1 : Event spec := ⟨target1,target1_mem,scalar (3/4),none⟩

theorem event0_valid : EventValid spec event0 := by
  exact assumptions.every_exact_restoration_event target0 target0_mem
    (scalar 0) slack (by simpa [spec] using zero_fiber_empty) (by simpa [spec] using restoration_minimum)

theorem event1_valid : EventValid spec event1 := by
  exact assumptions.every_exact_fixed_event target1 target1_mem (scalar (3/4))
    (by simpa [spec] using fixed_minimum)

theorem valid_event_cases {e : Event spec} (he : EventValid spec e) : e = event0 ∨ e = event1 := by
  rcases target_cases e.target e.target_mem with ht | ht
  · cases hr : e.restoration with
    | none =>
      have hm := event_fixed_minimum he hr
      exact False.elim (zero_fiber_empty ⟨e.x,by simpa [spec,ht] using hm.1⟩)
    | some s =>
      have hm := event_restoration_minimum he hr
      have hu := restoration_unique (by simpa [spec,ht] using hm)
      exact Or.inl (event_ext ht hu.1 (by simpa [hu.2,event0] using hr))
  · have hr : e.restoration = none := by
      by_contra hn
      apply event_empty he hn
      exact ⟨scalar (3/4),by simpa [spec,ht] using fixed_minimum.1⟩
    have hm := event_fixed_minimum he hr
    have hx := fixed_unique (by simpa [spec,ht] using hm)
    exact Or.inr (event_ext ht hx hr)

theorem nonrestoration_event {e : Event spec} (he : EventValid spec e)
    (hn : e.restoration = none) : e = event1 := by
  rcases valid_event_cases he with h | h
  · simp [h,event0] at hn
  · exact h

theorem solution_original : pt (3/4) 1 ∈ spec.original := by
  have h := (fiber_original_iff model target1 target1_mem (scalar (3/4))).mp
    (by simpa using fixed_minimum.1)
  simpa [spec,Data.original,pt] using h

/-- Without a restoration event, the y=0 linearized point remains feasible at
height3/16, strictly below the true optimum1/4. This is an actual master point. -/
theorem low_master_point (H : List (Event spec)) (hv : ∀ e ∈ H, EventValid spec e)
    (hn : ∀ e ∈ H, e.restoration = none) :
    (pt (-3/16) 0,(3/16:ℝ)) ∈ master spec I.seed H := by
  apply (master_mem_iff spec I.seed H _).mpr
  refine ⟨hard _,?_,?_,?_,?_,?_⟩
  · exact ⟨target0,target0_mem,by funext i; simp [pt,scalar,target0]⟩
  · intro j
    fin_cases j
    norm_num [spec,model,I.data,I.seed,I.Dg,pt,scalar]
  · norm_num [spec,I.objective,I.Df,I.seed,pt,scalar]
  · intro e he
    have hh := nonrestoration_event (hv e he) (hn e he)
    subst e
    constructor
    · norm_num [spec,Event.anchor,event1,I.objective,I.Df,intCast,target1,pt,scalar]
    · intro j _
      fin_cases j
      norm_num [spec,model,Event.anchor,event1,I.data,I.Dg,intCast,target1,pt,scalar]
  · intro e he hne
    exact False.elim (hne (hn e he))

end Chapter03.OAExec.ArticleI
