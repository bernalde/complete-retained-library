module

public import Chapter03OAExistenceUnboundedSolves

@[expose] public section

/-! Actual retained-history master witnesses of arbitrarily negative height.
The initial and every one-restoration master are genuinely unbounded. Two
distinct empty-fiber no-goods make the next master empty. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec.UnboundedControl

def witness (b : Fin 2) (a : ℝ) : P × ℝ := (pt 0 a (b.val : ℝ),a)

theorem bounds_region : bounds.region = Set.univ := by
  ext x
  simp [Bounds.region,bounds,ExtendedBound.lowerHolds,ExtendedBound.upperHolds]

theorem continuous_domain_unbounded : ¬ Bornology.IsBounded bounds.region := by
  rw [bounds_region]
  exact NormedSpace.unbounded_univ ℝ (RealVector 2)

theorem witness_initial (b : Fin 2) (a : ℝ) : witness b a ∈ master spec seed [] := by
  rw [master_mem_iff]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i; exact Fin.elim0 i
  · refine ⟨target b,target_mem b,?_⟩
    ext i
    simp [witness,pt,target,intCast]
  · intro j
    fin_cases j <;>
      norm_num [spec,model,row,rowD,sign,seed,pt,witness,cx,cz,cy]
  · simp [spec,seed,pt,witness,cz]
  · simp
  · simp [noGoods]

theorem witness_one (b c : Fin 2) (hbc : b ≠ c) (a : ℝ) :
    witness c a ∈ master spec seed [event b] := by
  have hmaster := master_append spec seed [] (event b)
  simp only [List.nil_append] at hmaster
  rw [hmaster]
  refine ⟨witness_initial c a,?_,?_⟩
  · constructor
    · simp [Event.rows,spec,event,Event.anchor,cz,witness,pt]
    · intro j _
      fin_cases b <;> fin_cases c <;> fin_cases j <;>
        norm_num [spec,model,row,rowD,sign,event,Event.anchor,target,intCast,
          witness,pt,cx,cz,cy] at hbc <;>
        norm_num [spec,model,row,rowD,sign,event,Event.anchor,target,intCast,
          witness,pt,cx,cz,cy]
  · intro _ he
    have hc : (witness c a).1.2 = intCast (target c) := by
      ext i
      simp [witness,pt,target,intCast]
    have heq : intCast (target c) = intCast (target b) := hc.symm.trans he
    exact hbc (intCast_target_injective heq).symm

theorem other_target (b : Fin 2) : ∃ c : Fin 2, b ≠ c := by
  fin_cases b
  · exact ⟨1,by decide⟩
  · exact ⟨0,by decide⟩

theorem initial_master_unbounded :
    (master spec seed []).Nonempty ∧ ¬ BddBelow (Prod.snd '' master spec seed []) := by
  refine ⟨⟨witness 0 0,witness_initial 0 0⟩,?_⟩
  rintro ⟨L,hL⟩
  have h := hL ⟨witness 0 (L-1),witness_initial 0 (L-1),rfl⟩
  change L ≤ L-1 at h
  linarith

theorem one_master_unbounded {e : Event spec} (he : EventValid spec e) :
    (master spec seed [e]).Nonempty ∧ ¬ BddBelow (Prod.snd '' master spec seed [e]) := by
  obtain ⟨b,rfl⟩ := valid_event_form he
  obtain ⟨c,hbc⟩ := other_target b
  refine ⟨⟨witness c 0,witness_one b c hbc 0⟩,?_⟩
  rintro ⟨L,hL⟩
  have h := hL ⟨witness c (L-1),witness_one b c hbc (L-1),rfl⟩
  change L ≤ L-1 at h
  linarith

theorem short_master_unbounded (H : List (Event spec))
    (hv : ∀ e ∈ H, EventValid spec e) (hlen : H.length < 2) :
    (master spec seed H).Nonempty ∧ ¬ BddBelow (Prod.snd '' master spec seed H) := by
  cases H with
  | nil => exact initial_master_unbounded
  | cons e H =>
    have hH : H = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
    subst H
    exact one_master_unbounded (hv e (by simp))

theorem both_master_empty (H : List (Event spec))
    (h0 : event 0 ∈ H) (h1 : event 1 ∈ H) : master spec seed H = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨y,hy,he⟩ := master_integer hz
  rcases target_cases y hy with rfl | rfl
  · exact hz.2 (event 0) h0 (by simp [event]) he
  · exact hz.2 (event 1) h1 (by simp [event]) he

theorem short_choice_unbounded {epsilon : ℝ} {s : State spec}
    (hs : Reachable spec seed epsilon s) (hlen : s.history.length < 2)
    (q : MasterChoice spec seed s) : q.attained = false := by
  have hu := (short_master_unbounded s.history
    (reachable_invariant analytic seed_valid hs).history.2 hlen).2
  cases hq : q.attained with
  | false => rfl
  | true =>
    have hm : IsMinimizer (master spec seed s.history) Prod.snd q.point := by
      simpa only [hq,↓reduceIte] using q.valid
    apply False.elim
    apply hu
    refine ⟨q.point.2,?_⟩
    rintro a ⟨z,hz,rfl⟩
    exact hm.2 z hz

end Chapter03.OAExec.UnboundedControl

#print axioms Chapter03.OAExec.UnboundedControl.initial_master_unbounded
#print axioms Chapter03.OAExec.UnboundedControl.one_master_unbounded
#print axioms Chapter03.OAExec.UnboundedControl.short_choice_unbounded
