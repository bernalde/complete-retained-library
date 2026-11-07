module

public import Chapter03FPUnboundedDriver
public import Chapter03FPUnboundedPacking

@[expose] public section

/-! The actual retained history supplies the geometric premises. No target
enclosure is imposed on the master and no progress oracle is an input. -/
noncomputable section
open Chapter02 Chapter03.FP
open scoped RealInnerProductSpace
namespace Chapter03.FPUnbounded
variable {n m l : ℕ}

theorem history_length_bound_of_radius (d : Data n m l) (hd : 0 < d.delta)
    {R : ℝ} (hR : 1 ≤ R) (hr : ∀ p ∈ d.relaxation, ‖Chapter03.yMap n m p‖ ≤ R)
    {P : ℕ} (hP : FarPackingBound m P) {s : State n m} (hs : Invariant d s) :
    s.history.length ≤ (proofLatticeBox m R).card + (proofLatticeBox m (4*R)).card + P := by
  classical
  let fail : Finset (Fin s.history.length) :=
    Finset.univ.filter (fun i => (s.history.get i).success = none)
  let succ : Finset (Fin s.history.length) :=
    Finset.univ.filter (fun i => ¬(s.history.get i).success = none)
  let p := fun i : Fin s.history.length => Chapter03.yMap n m (s.history.get i).projection
  let q := fun i : Fin s.history.length => (s.history.get i).target
  have hc : ∀ i j : Fin s.history.length, i < j →
      PastCompatible d (s.history.get i) (s.history.get j) :=
    List.pairwise_iff_get.mp hs.ordered
  have hfail : fail.card ≤ (proofLatticeBox m (4*R)).card + P := by
    apply failed_subset_card_bound hP hR fail p q
    · intro i _
      exact hr _ (hs.valid _ (List.get_mem _ i)).projection.1.1
    · intro i hi hy
      have hn := (Finset.mem_filter.mp hi).2
      have ho := (hs.valid _ (List.get_mem _ i)).outcome
      rw [hn] at ho
      apply ho
      apply (distance_zero_iff _ _).mpr
      exact (yMap_eq_intY_iff _ _).mp hy
    · intro i hi j _ hij
      exact (hc i j hij).1 (Finset.mem_filter.mp hi).2
  have hsucc : succ.card ≤ (proofLatticeBox m R).card := by
    apply integer_subset_card_bound succ q
    · intro i hi
      obtain ⟨pu,hpu⟩ := Option.ne_none_iff_exists'.mp (Finset.mem_filter.mp hi).2
      have ho := (hs.valid _ (List.get_mem _ i)).outcome
      rw [hpu] at ho
      have hy := (yMap_eq_intY_iff _ _).mpr ((distance_zero_iff _ _).mp ho.1)
      have hp := hr _ (hs.valid _ (List.get_mem _ i)).projection.1.1
      simpa only [hy] using hp
    · intro i hi j hj he
      by_contra hij
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact (hc i j hlt).2 hd hi' hj' he
      · exact (hc j i hgt).2 hd hj' hi' he.symm
  have hsum : fail.card + succ.card = s.history.length := by
    simpa [fail,succ] using Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun i : Fin s.history.length => (s.history.get i).success = none)
  omega

/-- One bound from original data works for all reachable histories and all
admissible choices. Empty feasible and zero-dimensional cases require no choice
of a feasible anchor. -/
theorem uniform_history_bound (d : Data n m l) (h : Analytic d) (hd : 0 < d.delta) :
    ∃ B : ℕ, ∀ s : State n m, Invariant d s → s.history.length ≤ B := by
  obtain ⟨R,hR,hr⟩ := compact_projected_radius (relaxation_compact d h)
  obtain ⟨P,hP⟩ := far_packing_bound_exists m
  exact ⟨(proofLatticeBox m R).card + (proofLatticeBox m (4*R)).card + P,
    fun _ hs => history_length_bound_of_radius d hd hR hr hP hs⟩

def historyBound (d : Data n m l) (h : Analytic d) (hd : 0 < d.delta) : ℕ :=
  Classical.choose (uniform_history_bound d h hd)

theorem history_length_bound (d : Data n m l) (h : Analytic d) (hd : 0 < d.delta)
    {s : State n m} (hs : Invariant d s) : s.history.length ≤ historyBound d h hd :=
  Classical.choose_spec (uniform_history_bound d h hd) s hs

theorem run_sufficient_fuel (d : Data n m l) (h : Analytic d) (hd : 0 < d.delta)
    {cap : Option ℕ} (choose : Selector d cap) (fuel : ℕ) (s : State n m)
    (hs : Invariant d s) (hf : historyBound d h hd < s.history.length+fuel) :
    ∃ out, run d choose fuel s = some out := by
  induction fuel generalizing s with
  | zero => have hb := history_length_bound d h hd hs; omega
  | succ fuel ih =>
    cases hc : choose s with
    | stop reason ht => exact ⟨terminalOutput s reason,by simp [run,hc]⟩
    | next e he =>
      obtain ⟨z,hz,_,hr⟩ := he
      have hs' := append_invariant d h hs hz.1 hr
      have hf' : historyBound d h hd < (append s e).history.length+fuel := by
        simp only [append,List.length_append,List.length_singleton]
        omega
      obtain ⟨out,hout⟩ := ih (append s e) hs' hf'
      exact ⟨out.bump e,by simp [run,hc,hout]⟩

end Chapter03.FPUnbounded
