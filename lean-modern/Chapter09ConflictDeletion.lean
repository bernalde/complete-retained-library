module

public import Chapter09

@[expose] public section

/-! Current-state deletion and two exhaustive scans. These are distinct from
the accepted simultaneous `Chapter09.repair`. Lists may repeat entries. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.ConflictDeletion

variable {α : Type*} [DecidableEq α]

theorem conflicts_mono (E : Finset (α × α)) {S T : Finset α} (h : S ⊆ T) :
    conflicts E S ⊆ conflicts E T := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨he,ha,hb⟩
  exact Finset.mem_filter.mpr ⟨he,h ha,h hb⟩

theorem feasible_subset (E : Finset (α × α)) {S T : Finset α}
    (h : S ⊆ T) (hf : feasible E T) : feasible E S := by
  intro e he hab
  exact hf e he ⟨h hab.1,h hab.2⟩

theorem score_erase_mono (E : Finset (α × α)) (w : α × α → ℝ)
    (S : Finset α) (a : α) (hn : ∀ e ∈ E, 0 ≤ w e)
    (e : α × α) (he : e ∈ E) (ha : e.1 ∈ S) (hb : e.2 ∈ S)
    (hinc : a = e.1 ∨ a = e.2) (hw : 1 ≤ w e) :
    score E w S ≤ score E w (S.erase a) := by
  have ham : a ∈ S := by rcases hinc with rfl | rfl <;> assumption
  have hec : e ∈ conflicts E S := Finset.mem_filter.mpr ⟨he,ha,hb⟩
  have hen : e ∉ conflicts E (S.erase a) := by
    intro h
    have hh := (Finset.mem_filter.mp h).2
    rcases hinc with rfl | rfl
    · exact Finset.notMem_erase e.1 S hh.1
    · exact Finset.notMem_erase e.2 S hh.2
  have hsub : insert e (conflicts E (S.erase a)) ⊆ conflicts E S := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hec
    · exact conflicts_mono E (Finset.erase_subset a S) hf
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun f hf _ => hn f (Finset.mem_filter.mp hf).1)
  rw [Finset.sum_insert hen] at hs
  have hc : ((S.erase a).card : ℝ) + 1 = (S.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one ham
  unfold score
  linarith

def edgeStep (S : Finset α) (e : α × α) : Finset α :=
  if e.1 ∈ S ∧ e.2 ∈ S then S.erase e.1 else S

def edgeScan : List (α × α) → Finset α → Finset α
  | [], S => S
  | e :: es, S => edgeScan es (edgeStep S e)

theorem edgeStep_subset (S : Finset α) (e : α × α) : edgeStep S e ⊆ S := by
  unfold edgeStep
  split_ifs
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

theorem edgeStep_safe (S : Finset α) (e : α × α) :
    ¬ (e.1 ∈ edgeStep S e ∧ e.2 ∈ edgeStep S e) := by
  unfold edgeStep
  split_ifs with h
  · simp
  · exact h

theorem edgeStep_card_bound (S : Finset α) (e : α × α) :
    S.card ≤ (edgeStep S e).card + 1 := by
  unfold edgeStep
  split_ifs with h
  · exact le_of_eq (Finset.card_erase_add_one h.1).symm
  · omega

theorem edgeScan_subset (L : List (α × α)) (S : Finset α) : edgeScan L S ⊆ S := by
  induction L generalizing S with
  | nil => exact Finset.Subset.refl _
  | cons e L ih => exact (ih _).trans (edgeStep_subset S e)

theorem edgeScan_card_bound (L : List (α × α)) (S : Finset α) :
    S.card ≤ (edgeScan L S).card + L.length := by
  induction L generalizing S with
  | nil => simp [edgeScan]
  | cons e L ih =>
    have h₁ := edgeStep_card_bound S e
    have h₂ := ih (edgeStep S e)
    simp only [edgeScan, List.length_cons]
    omega

theorem edgeScan_safe (L : List (α × α)) (S : Finset α)
    (e : α × α) (he : e ∈ L) : ¬ (e.1 ∈ edgeScan L S ∧ e.2 ∈ edgeScan L S) := by
  induction L generalizing S with
  | nil => simp at he
  | cons f L ih =>
    rcases List.mem_cons.mp he with rfl | he
    · intro hab
      exact edgeStep_safe S e ⟨edgeScan_subset L _ hab.1,edgeScan_subset L _ hab.2⟩
    · exact ih (edgeStep S f) he

theorem edgeScan_feasible (E : Finset (α × α)) (L : List (α × α))
    (hc : ∀ e ∈ E, e ∈ L) (S : Finset α) : feasible E (edgeScan L S) :=
  fun e he => edgeScan_safe L S e (hc e he)

theorem edgeStep_score_mono (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 ≤ w e) (S : Finset α) (e : α × α) (he : e ∈ E) :
    score E w S ≤ score E w (edgeStep S e) := by
  unfold edgeStep
  split_ifs with h
  · exact score_erase_mono E w S e.1 (fun f hf => (hw f hf).trans' zero_le_one)
      e he h.1 h.2 (Or.inl rfl) (hw e he)
  · exact le_rfl

theorem edgeScan_score_mono (E : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E, 1 ≤ w e) (L : List (α × α))
    (hs : ∀ e ∈ L, e ∈ E) (S : Finset α) :
    score E w S ≤ score E w (edgeScan L S) := by
  induction L generalizing S with
  | nil => exact le_rfl
  | cons e L ih =>
    exact (edgeStep_score_mono E w hw S e (hs e (by simp))).trans
      (ih (fun f hf => hs f (List.mem_cons_of_mem e hf)) (edgeStep S e))

def vertexStep (C : Finset (α × α)) (S : Finset α) (a : α) : Finset α :=
  if a ∈ S ∧ ∃ b ∈ S, (a,b) ∈ C ∨ (b,a) ∈ C then S.erase a else S

def vertexScan (C : Finset (α × α)) : List α → Finset α → Finset α
  | [], S => S
  | a :: as, S => vertexScan C as (vertexStep C S a)

theorem vertexStep_subset (C : Finset (α × α)) (S : Finset α) (a : α) :
    vertexStep C S a ⊆ S := by
  unfold vertexStep
  split_ifs
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

theorem vertexStep_safe (C : Finset (α × α)) (S : Finset α) (a b : α)
    (he : (a,b) ∈ C) : ¬ (a ∈ vertexStep C S a ∧ b ∈ vertexStep C S a) := by
  unfold vertexStep
  split_ifs with h
  · simp
  · intro hab
    exact h ⟨hab.1,b,hab.2,Or.inl he⟩

theorem vertexStep_card_bound (C : Finset (α × α)) (S : Finset α) (a : α) :
    S.card ≤ (vertexStep C S a).card + 1 := by
  unfold vertexStep
  split_ifs with h
  · exact le_of_eq (Finset.card_erase_add_one h.1).symm
  · omega

theorem vertexScan_subset (C : Finset (α × α)) (L : List α) (S : Finset α) :
    vertexScan C L S ⊆ S := by
  induction L generalizing S with
  | nil => exact Finset.Subset.refl _
  | cons a L ih => exact (ih _).trans (vertexStep_subset C S a)

theorem vertexScan_card_bound (C : Finset (α × α)) (L : List α) (S : Finset α) :
    S.card ≤ (vertexScan C L S).card + L.length := by
  induction L generalizing S with
  | nil => simp [vertexScan]
  | cons a L ih =>
    have h₁ := vertexStep_card_bound C S a
    have h₂ := ih (vertexStep C S a)
    simp only [vertexScan, List.length_cons]
    omega

theorem vertexScan_safe (C : Finset (α × α)) (L : List α) (S : Finset α)
    (a b : α) (ha : a ∈ L) (he : (a,b) ∈ C) :
    ¬ (a ∈ vertexScan C L S ∧ b ∈ vertexScan C L S) := by
  induction L generalizing S with
  | nil => simp at ha
  | cons f L ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · intro hab
      exact vertexStep_safe C S a b he
        ⟨vertexScan_subset C L _ hab.1,vertexScan_subset C L _ hab.2⟩
    · exact ih (vertexStep C S f) ha

theorem vertexScan_feasible (C : Finset (α × α)) (L : List α)
    (hc : ∀ e ∈ C, e.1 ∈ L) (S : Finset α) : feasible C (vertexScan C L S) :=
  fun e he => vertexScan_safe C L S e.1 e.2 (hc e he) he

theorem vertexStep_score_mono (E C : Finset (α × α)) (w : α × α → ℝ)
    (hC : C ⊆ E) (hw : ∀ e ∈ E, 1 ≤ w e) (S : Finset α) (a : α) :
    score E w S ≤ score E w (vertexStep C S a) := by
  unfold vertexStep
  split_ifs with h
  · obtain ⟨ha,b,hb,he⟩ := h
    rcases he with he | he
    · exact score_erase_mono E w S a (fun f hf => (hw f hf).trans' zero_le_one)
        (a,b) (hC he) ha hb (Or.inl rfl) (hw _ (hC he))
    · exact score_erase_mono E w S a (fun f hf => (hw f hf).trans' zero_le_one)
        (b,a) (hC he) hb ha (Or.inr rfl) (hw _ (hC he))
  · exact le_rfl

theorem vertexScan_score_mono (E C : Finset (α × α)) (w : α × α → ℝ)
    (hC : C ⊆ E) (hw : ∀ e ∈ E, 1 ≤ w e) (L : List α) (S : Finset α) :
    score E w S ≤ score E w (vertexScan C L S) := by
  induction L generalizing S with
  | nil => exact le_rfl
  | cons a L ih =>
    exact (vertexStep_score_mono E C w hC hw S a).trans (ih _)

def twoPass (C : Finset (α × α)) (LE : List (α × α)) (LV : List α)
    (S : Finset α) : Finset α := vertexScan C LV (edgeScan LE S)

theorem twoPass_subset (C : Finset (α × α)) (LE : List (α × α)) (LV : List α)
    (S : Finset α) : twoPass C LE LV S ⊆ S :=
  (vertexScan_subset C LV _).trans (edgeScan_subset LE S)

theorem twoPass_card_bound (C : Finset (α × α)) (LE : List (α × α)) (LV : List α)
    (S : Finset α) : S.card ≤ (twoPass C LE LV S).card + LE.length + LV.length := by
  have h₁ := edgeScan_card_bound LE S
  have h₂ := vertexScan_card_bound C LV (edgeScan LE S)
  unfold twoPass
  omega

theorem twoPass_feasible (E C : Finset (α × α)) (LE : List (α × α)) (LV : List α)
    (hE : ∀ e ∈ E, e ∈ LE) (hV : ∀ e ∈ C, e.1 ∈ LV) (S : Finset α) :
    feasible (E ∪ C) (twoPass C LE LV S) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact feasible_subset E (vertexScan_subset C LV _) (edgeScan_feasible E LE hE S) e he
  · exact vertexScan_feasible C LV hV (edgeScan LE S) e he

theorem twoPass_score_mono (E C : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E ∪ C, 1 ≤ w e) (LE : List (α × α)) (LV : List α)
    (hs : ∀ e ∈ LE, e ∈ E) (S : Finset α) :
    score (E ∪ C) w S ≤ score (E ∪ C) w (twoPass C LE LV S) :=
  (edgeScan_score_mono (E ∪ C) w hw LE
    (fun e he => Finset.mem_union_left C (hs e he)) S).trans
    (vertexScan_score_mono (E ∪ C) C w Finset.subset_union_right hw LV _)

theorem twoPass_score_bound (E C : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E ∪ C, 1 ≤ w e) (LE : List (α × α)) (LV : List α)
    (hs : ∀ e ∈ LE, e ∈ E) (hE : ∀ e ∈ E, e ∈ LE)
    (hV : ∀ e ∈ C, e.1 ∈ LV) (S : Finset α) :
    score (E ∪ C) w S ≤ ((twoPass C LE LV S).card : ℝ) := by
  simpa [feasible_score _ w (twoPass C LE LV S) (twoPass_feasible E C LE LV hE hV S)]
    using twoPass_score_mono E C w hw LE LV hs S

theorem twoPass_optimal_return (E C : Finset (α × α)) (w : α × α → ℝ)
    (hw : ∀ e ∈ E ∪ C, 1 ≤ w e) (LE : List (α × α)) (LV : List α)
    (hs : ∀ e ∈ LE, e ∈ E) (hE : ∀ e ∈ E, e ∈ LE)
    (hV : ∀ e ∈ C, e.1 ∈ LV) (S : Finset α) (hm : isScoreMax (E ∪ C) w S) :
    feasible (E ∪ C) (twoPass C LE LV S) ∧
    score (E ∪ C) w S = ((twoPass C LE LV S).card : ℝ) ∧
    ∀ T : Finset α, feasible (E ∪ C) T →
      (T.card : ℝ) ≤ ((twoPass C LE LV S).card : ℝ) := by
  have hf := twoPass_feasible E C LE LV hE hV S
  have hv := feasible_score (E ∪ C) w (twoPass C LE LV S) hf
  have heq : score (E ∪ C) w S = ((twoPass C LE LV S).card : ℝ) :=
    le_antisymm (twoPass_score_bound E C w hw LE LV hs hE hV S)
      (by simpa only [hv] using hm (twoPass C LE LV S))
  refine ⟨hf,heq,?_⟩
  intro T hT
  simpa only [feasible_score (E ∪ C) w T hT,heq] using hm T

end Chapter09.ConflictDeletion

#print axioms Chapter09.ConflictDeletion.score_erase_mono
#print axioms Chapter09.ConflictDeletion.edgeScan_feasible
#print axioms Chapter09.ConflictDeletion.vertexScan_feasible
#print axioms Chapter09.ConflictDeletion.twoPass_subset
#print axioms Chapter09.ConflictDeletion.twoPass_card_bound
#print axioms Chapter09.ConflictDeletion.twoPass_feasible
#print axioms Chapter09.ConflictDeletion.twoPass_score_bound
#print axioms Chapter09.ConflictDeletion.twoPass_optimal_return
