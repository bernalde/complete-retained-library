module

public import Chapter10ArcRows

@[expose] public section

/-! Derive finite acyclicity ranks from the actual customer clocks and positive
selected customer travel. Zero-time customer cycles are not excluded by (10.3). -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing.Arc
open Chapter10.Routing

def arrivalEdge {n k} (x : Assignment n k) (hv : Visit x) (i : Fin n) : Edge n k :=
  Classical.choose (ExistsUnique.exists (visit_unique x hv i))

theorem arrivalEdge_spec {n k} (x : Assignment n k) (hv : Visit x) (i : Fin n) :
    x (arrivalEdge x hv i) = true ∧ (arrivalEdge x hv i).2.1 = some i :=
  Classical.choose_spec (ExistsUnique.exists (visit_unique x hv i))

theorem arrivalEdge_eq {n k} (x : Assignment n k) (hv : Visit x)
    (i : Fin n) (e : Edge n k) (hx : x e = true) (hd : e.2.1 = some i) :
    arrivalEdge x hv i = e := by
  obtain ⟨g,hg,hgu⟩ := visit_unique x hv i
  exact (hgu _ (arrivalEdge_spec x hv i)).trans (hgu _ ⟨hx,hd⟩).symm

theorem departure_matches_arrival {n k} (x : Assignment n k) (hv : Visit x) (hf : Flow x)
    (i : Fin n) (e : Edge n k) (hx : x e = true) (hs : e.1.1 = some i) :
    e.1.2 = (arrivalEdge x hv i).2.2 := by
  by_contra hn
  have hem := no_outgoing_other_event x hv hf i (arrivalEdge x hv i)
    (arrivalEdge_spec x hv i).1 (arrivalEdge_spec x hv i).2 e.1.2 hn
  have hm : e ∈ outgoing x i e.1.2 := (mem_outgoing _ _ _ _).mpr ⟨hx,Prod.ext hs rfl⟩
  simp [hem] at hm

def customerClock {n k} (T : Grid k) (x : Assignment n k) (hv : Visit x) (i : Fin n) : ℝ :=
  T.time (arrivalEdge x hv i).2.2

def CustomerEdge {n k} (x : Assignment n k) (i j : Fin n) : Prop :=
  ∃ e, x e = true ∧ e.1.1 = some i ∧ e.2.1 = some j

def PositiveCustomerTravel {n k} (D : Data n) (x : Assignment n k) : Prop :=
  ∀ i j, CustomerEdge x i j → 0 < D.travel (some i) (some j)

theorem selected_clock_increases {n k} (D : Data n) (T : Grid k) (x : Assignment n k)
    (hv : Visit x) (hf : Flow x) (ht : Travel D T x) (hp : PositiveCustomerTravel D x)
    (i j : Fin n) (he : CustomerEdge x i j) : customerClock T x hv i < customerClock T x hv j := by
  obtain ⟨e,hx,hs,hd⟩ := he
  have hdep := departure_matches_arrival x hv hf i e hx hs
  have harr := arrivalEdge_eq x hv j e hx hd
  have htravel := ht e hx
  have hpos := hp i j ⟨e,hx,hs,hd⟩
  simp only [customerClock]
  rw [harr]
  rw [← hdep]
  rw [hs,hd] at htravel
  linarith

def clockRank {n} (f : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => f j < f i).card

theorem clockRank_strict {n} (f : Fin n → ℝ) (i j : Fin n) (h : f i < f j) :
    clockRank f i < clockRank f j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact lt_trans ha h
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun a => f a < f j) := by simp [h]
    rw [← heq] at hi
    simpa using hi

def StrictRank {n k} (x : Assignment n k) (rank : Fin n → ℕ) : Prop :=
  ∀ i j, CustomerEdge x i j → rank i < rank j

theorem positive_travel_supplies_rank {n k} (D : Data n) (T : Grid k) (x : Assignment n k)
    (hv : Visit x) (hf : Flow x) (ht : Travel D T x) (hp : PositiveCustomerTravel D x) :
    StrictRank x (clockRank (customerClock T x hv)) := by
  intro i j he
  exact clockRank_strict _ i j (selected_clock_increases D T x hv hf ht hp i j he)

theorem ranked_irreflexive {n k} (x : Assignment n k) (r : Fin n → ℕ) (hr : StrictRank x r)
    (i : Fin n) : ¬ CustomerEdge x i i := by
  intro h
  exact Nat.lt_irrefl _ (hr i i h)

end Chapter10.Routing.Arc
