module

public import Chapter09Slots

@[expose] public section

/-! Parametric finite witnesses for the qualified Chapter 9 threshold repairs.
These are explicit assignments on Fin n × Fin k; graph/score bridges follow.
No optimum value is assumed. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Source

/-- A selected-slot family with injective color projection uses at most k slots. -/
theorem card_le_colors_of_injective {n k : ℕ} (S : Finset (Fin n × Fin k))
    (h : Set.InjOn Prod.snd (S : Set (Fin n × Fin k))) : S.card ≤ k := by
  have hc := Finset.card_le_univ (S.image Prod.snd)
  rw [Finset.card_image_of_injOn h] at hc
  simpa using hc

/-- Color r selects vertex r, leaving the final clique vertex unselected. -/
def cliqueBase (k : ℕ) : Finset (Fin (k+1) × Fin k) :=
  Finset.univ.image (fun r : Fin k => (r.castSucc, r))

@[simp] theorem mem_cliqueBase {k : ℕ} (i : Fin (k+1)) (r : Fin k) :
    (i,r) ∈ cliqueBase k ↔ i = r.castSucc := by
  simp [cliqueBase, eq_comm]

@[simp] theorem card_cliqueBase (k : ℕ) : (cliqueBase k).card = k := by
  unfold cliqueBase
  rw [Finset.card_image_of_injective _ (by
    intro a b h
    exact congrArg Prod.snd h)]
  simp

/-- The final clique vertex duplicates color zero; k≥1 is explicit. -/
def cliqueBad (k : ℕ) (hk : 0 < k) : Finset (Fin (k+1) × Fin k) :=
  insert (Fin.last k, ⟨0,hk⟩) (cliqueBase k)

@[simp] theorem last_not_cliqueBase {k : ℕ} (r : Fin k) :
    (Fin.last k,r) ∉ cliqueBase k := by
  simp only [mem_cliqueBase]
  exact (ne_of_lt r.castSucc_lt_last).symm

@[simp] theorem card_cliqueBad (k : ℕ) (hk : 0 < k) :
    (cliqueBad k hk).card = k+1 := by
  rw [cliqueBad, Finset.card_insert_of_notMem (last_not_cliqueBase ⟨0,hk⟩), card_cliqueBase]

@[simp] theorem mem_cliqueBad {k : ℕ} (hk : 0 < k) (i : Fin (k+1)) (r : Fin k) :
    (i,r) ∈ cliqueBad k hk ↔ (i = Fin.last k ∧ r = ⟨0,hk⟩) ∨ i = r.castSucc := by
  simp [cliqueBad, Prod.mk.injEq]


/-- The complete simple graph, with each edge stored in increasing order. -/
def cliqueGraph (n : ℕ) : Graph n where
  edges := Finset.univ.filter (fun e => e.1 < e.2)
  ordered := by intro e he; exact (Finset.mem_filter.mp he).2

@[simp] theorem mem_cliqueGraph {n : ℕ} (i j : Fin n) :
    (i,j) ∈ (cliqueGraph n).edges ↔ i < j := by simp [cliqueGraph]

theorem clique_feasible_color_injective {n k : ℕ} (S : Finset (Slot n k))
    (h : Feasible (cliqueGraph n) S) : Set.InjOn Prod.snd (S : Set (Slot n k)) := by
  rintro ⟨i,r⟩ hi ⟨j,p⟩ hj hrp
  dsimp at hrp
  subst p
  have hij : i = j := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · exact ((feasible_iff _ _).mp h).1 (i,j) (by simpa using hlt) r ⟨hi,hj⟩
    · exact ((feasible_iff _ _).mp h).1 (j,i) (by simpa using hlt) r ⟨hj,hi⟩
  exact Prod.ext hij rfl

theorem clique_feasible_card_le {n k : ℕ} (S : Finset (Slot n k))
    (h : Feasible (cliqueGraph n) S) : S.card ≤ k :=
  card_le_colors_of_injective S (clique_feasible_color_injective S h)

theorem cliqueBase_feasible (k : ℕ) : Feasible (cliqueGraph (k+1)) (cliqueBase k) := by
  rw [feasible_iff]
  constructor
  · rintro ⟨i,j⟩ he r ⟨hi,hj⟩
    have hij : i < j := by simpa using he
    have hi := (mem_cliqueBase i r).mp hi
    have hj := (mem_cliqueBase j r).mp hj
    exact (ne_of_lt hij) (hi.trans hj.symm)
  · intro i r p hr hp
    exact Fin.castSucc_injective k (((mem_cliqueBase i r).mp hr).symm.trans
      ((mem_cliqueBase i p).mp hp))

/-- The full MkCS optimum of K_(k+1) is k, with no hypothetical optimum premise. -/
theorem alpha_clique (k : ℕ) : alpha (cliqueGraph (k+1)) k = (k : ℝ) := by
  apply le_antisymm
  · obtain ⟨S,hS,hcard⟩ := alpha_attained (cliqueGraph (k+1)) k
    rw [← hcard]
    exact_mod_cast clique_feasible_card_le S hS
  · simpa using card_le_alpha (cliqueGraph (k+1)) (cliqueBase k) (cliqueBase_feasible k)

theorem cliqueBad_row_unique {k : ℕ} (hk : 0 < k) (i : Fin (k+1)) (r p : Fin k)
    (hr : (i,r) ∈ cliqueBad k hk) (hp : (i,p) ∈ cliqueBad k hk) : r = p := by
  rcases (mem_cliqueBad hk i r).mp hr with ⟨hi,hr⟩ | hi <;>
    rcases (mem_cliqueBad hk i p).mp hp with ⟨hj,hp⟩ | hj
  · exact hr.trans hp.symm
  · exact False.elim ((ne_of_lt p.castSucc_lt_last) (hj.symm.trans hi))
  · exact False.elim ((ne_of_lt r.castSucc_lt_last) (hi.symm.trans hj))
  · exact Fin.castSucc_injective k (hi.symm.trans hj)

def cliqueConflict (k : ℕ) (hk : 0 < k) : Slot (k+1) k × Slot (k+1) k :=
  (((⟨0,hk⟩ : Fin k).castSucc, ⟨0,hk⟩), (Fin.last k, ⟨0,hk⟩))

/-- There is precisely one spatial conflict and no same-vertex color conflict. -/
theorem cliqueBad_conflicts (k : ℕ) (hk : 0 < k) :
    Chapter09.conflicts (conflictPairs (cliqueGraph (k+1)) k) (cliqueBad k hk) =
      {cliqueConflict k hk} := by
  ext e
  constructor
  · intro h
    obtain ⟨he,hi,hj⟩ := Finset.mem_filter.mp h
    rcases e with ⟨⟨i,r⟩,⟨j,p⟩⟩
    rcases (mem_conflictPairs _ _).mp he with ⟨hedge,hrp⟩ | ⟨hij,hrp⟩
    · dsimp at hrp
      subst p
      have hlt : i < j := by simpa using hedge
      rcases (mem_cliqueBad hk i r).mp hi with ⟨hi,hr⟩ | hi <;>
        rcases (mem_cliqueBad hk j r).mp hj with ⟨hj,hp⟩ | hj
      · exact False.elim ((ne_of_lt hlt) (hi.trans hj.symm))
      · have hf := r.castSucc_lt_last
        rw [hi,hj] at hlt
        exact False.elim ((not_lt_of_gt hf) hlt)
      · subst r
        subst i
        subst j
        simp [cliqueConflict]
      · exact False.elim ((ne_of_lt hlt) (hi.trans hj.symm))
    · dsimp at hij hrp
      subst j
      exact False.elim ((ne_of_lt hrp) (cliqueBad_row_unique hk i r p hi hj))
  · intro h
    have he := Finset.mem_singleton.mp h
    subst e
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_,?_⟩
    · simp [cliqueConflict]
      exact hk
    · simp [cliqueConflict, cliqueBad]
    · simp [cliqueConflict, cliqueBad]

theorem cliqueBad_not_feasible (k : ℕ) (hk : 0 < k) :
    ¬ Feasible (cliqueGraph (k+1)) (cliqueBad k hk) := by
  intro h
  have he := (Chapter09.conflicts_empty_iff _ _).mpr h
  rw [cliqueBad_conflicts k hk] at he
  simp at he

theorem uScore_cliqueBad (k : ℕ) (hk : 0 < k) (a b : ℝ) :
    uScore (cliqueGraph (k+1)) a b (cliqueBad k hk) = (k : ℝ) + 1 - a := by
  have hn := ne_of_lt (⟨0,hk⟩ : Fin k).castSucc_lt_last
  simp [uScore, Chapter09.score, cliqueBad_conflicts, cliqueConflict, weight, hn, Fin.ext_iff, Nat.ne_of_gt hk, ne_of_lt hk]

theorem cliqueBad_uScore_overshoot (k : ℕ) (hk : 0 < k) (a b : ℝ) (ha : a < 1) :
    alpha (cliqueGraph (k+1)) k < uScore (cliqueGraph (k+1)) a b (cliqueBad k hk) := by
  rw [alpha_clique, uScore_cliqueBad]
  linarith

/-- A genuine global infeasible optimum tie at the unit edge penalty. -/
theorem cliqueBad_uScore_global_tie (k : ℕ) (hk : 0 < k) (b : ℝ) (hb : 1 ≤ b) :
    ¬ Feasible (cliqueGraph (k+1)) (cliqueBad k hk) ∧
    uScore (cliqueGraph (k+1)) 1 b (cliqueBad k hk) = alpha (cliqueGraph (k+1)) k ∧
    ∀ T : Finset (Slot (k+1) k),
      uScore (cliqueGraph (k+1)) 1 b T ≤ uScore (cliqueGraph (k+1)) 1 b (cliqueBad k hk) := by
  refine ⟨cliqueBad_not_feasible k hk, ?_, ?_⟩
  · rw [uScore_cliqueBad, alpha_clique]; ring
  · intro T
    have hbound := Chapter09.weighted_repair_bound (conflictPairs (cliqueGraph (k+1)) k)
      (weight 1 b) (weight_ge_one _ 1 b (by norm_num) hb) T
    have hcard := card_le_alpha (cliqueGraph (k+1))
      (Chapter09.repair (conflictPairs (cliqueGraph (k+1)) k) T)
      (Chapter09.repair_feasible _ _)
    change uScore (cliqueGraph (k+1)) 1 b T ≤ _ at hbound
    rw [alpha_clique] at hcard
    rw [uScore_cliqueBad]
    linarith


/-- The edgeless graph used by the single-vertex color witness. -/
def emptyGraph (n : ℕ) : Graph n where
  edges := ∅
  ordered := by simp

/-- A single vertex can contribute at most one selected feasible slot. -/
theorem alpha_one_vertex (k : ℕ) (hk : 0 < k) : alpha (emptyGraph 1) k = 1 := by
  apply le_antisymm
  · obtain ⟨S,hS,hcard⟩ := alpha_attained (emptyGraph 1) k
    have hv : (vertices S).card ≤ 1 := by simpa using Finset.card_le_univ (vertices S)
    rw [feasible_vertex_card _ _ hS] at hv
    rw [← hcard]
    exact_mod_cast hv
  · have hf : Feasible (emptyGraph 1) ({(0,⟨0,hk⟩)} : Finset (Slot 1 k)) := by
      rw [feasible_iff]
      constructor
      · simp [emptyGraph]
      · intro i r p hr hp
        exact congrArg Prod.snd ((Finset.mem_singleton.mp hr).trans (Finset.mem_singleton.mp hp).symm)
    simpa using card_le_alpha (emptyGraph 1) ({(0,⟨0,hk⟩)} : Finset (Slot 1 k)) hf

def doubleColors (k : ℕ) (hk : 2 ≤ k) : Finset (Slot 1 k) :=
  {(0,⟨0,by omega⟩), (0,⟨1,by omega⟩)}

@[simp] theorem mem_doubleColors {k : ℕ} (hk : 2 ≤ k) (i : Fin 1) (r : Fin k) :
    (i,r) ∈ doubleColors k hk ↔ r = ⟨0,by omega⟩ ∨ r = ⟨1,by omega⟩ := by
  simp [doubleColors, Fin.eq_zero i, Prod.mk.injEq]

@[simp] theorem card_doubleColors (k : ℕ) (hk : 2 ≤ k) : (doubleColors k hk).card = 2 := by
  simp [doubleColors, Prod.mk.injEq, Fin.ext_iff]

def doubleConflict (k : ℕ) (hk : 2 ≤ k) : Slot 1 k × Slot 1 k :=
  ((0,⟨0,by omega⟩),(0,⟨1,by omega⟩))

theorem doubleColors_conflicts (k : ℕ) (hk : 2 ≤ k) :
    Chapter09.conflicts (conflictPairs (emptyGraph 1) k) (doubleColors k hk) =
      {doubleConflict k hk} := by
  ext e
  constructor
  · intro h
    obtain ⟨he,hi,hj⟩ := Finset.mem_filter.mp h
    rcases e with ⟨⟨i,r⟩,⟨j,p⟩⟩
    rcases (mem_conflictPairs _ _).mp he with ⟨hedge,_⟩ | ⟨_,hrp⟩
    · simp [emptyGraph] at hedge
    · rcases (mem_doubleColors hk i r).mp hi with hr | hr <;>
        rcases (mem_doubleColors hk j p).mp hj with hp | hp
      · subst r; subst p; exact False.elim ((lt_irrefl _) hrp)
      · subst r; subst p; simp [doubleConflict, Fin.eq_zero i, Fin.eq_zero j]
      · subst r; subst p; have hf : ¬ ((⟨1,by omega⟩ : Fin k) < ⟨0,by omega⟩) := by simp
        exact False.elim (hf hrp)
      · subst r; subst p; exact False.elim ((lt_irrefl _) hrp)
  · intro h
    have he := Finset.mem_singleton.mp h
    subst e
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_,?_⟩ <;> simp [doubleConflict, emptyGraph]

theorem doubleColors_not_feasible (k : ℕ) (hk : 2 ≤ k) :
    ¬ Feasible (emptyGraph 1) (doubleColors k hk) := by
  intro h
  have he := (Chapter09.conflicts_empty_iff _ _).mpr h
  rw [doubleColors_conflicts k hk] at he
  simp at he

theorem uScore_doubleColors (k : ℕ) (hk : 2 ≤ k) (a b : ℝ) :
    uScore (emptyGraph 1) a b (doubleColors k hk) = 2 - b := by
  simp [uScore, Chapter09.score, doubleColors_conflicts, doubleConflict, weight]

theorem doubleColors_uScore_overshoot (k : ℕ) (hk : 2 ≤ k) (a b : ℝ) (hb : b < 1) :
    alpha (emptyGraph 1) k < uScore (emptyGraph 1) a b (doubleColors k hk) := by
  rw [alpha_one_vertex k (by omega), uScore_doubleColors]
  linarith

/-- A genuine globally maximizing infeasible color tie, not just a scalar equality. -/
theorem doubleColors_uScore_global_tie (k : ℕ) (hk : 2 ≤ k) (a : ℝ) :
    ¬ Feasible (emptyGraph 1) (doubleColors k hk) ∧
    uScore (emptyGraph 1) a 1 (doubleColors k hk) = alpha (emptyGraph 1) k ∧
    ∀ T : Finset (Slot 1 k),
      uScore (emptyGraph 1) a 1 T ≤ uScore (emptyGraph 1) a 1 (doubleColors k hk) := by
  have hw : ∀ e ∈ conflictPairs (emptyGraph 1) k, 1 ≤ weight a 1 e := by
    intro e he
    rcases (mem_conflictPairs _ _).mp he with ⟨hedge,_⟩ | hcolor
    · simp [emptyGraph] at hedge
    · simp [weight, hcolor.1]
  refine ⟨doubleColors_not_feasible k hk, ?_, ?_⟩
  · rw [uScore_doubleColors, alpha_one_vertex k (by omega)]; norm_num
  · intro T
    have hbound := Chapter09.weighted_repair_bound (conflictPairs (emptyGraph 1) k) (weight a 1) hw T
    have hcard := card_le_alpha (emptyGraph 1)
      (Chapter09.repair (conflictPairs (emptyGraph 1) k) T) (Chapter09.repair_feasible _ _)
    change uScore (emptyGraph 1) a 1 T ≤ _ at hbound
    rw [alpha_one_vertex k (by omega)] at hcard
    rw [uScore_doubleColors]
    linarith


theorem rowCount_cliqueBad_le_one (k : ℕ) (hk : 0 < k) (i : Fin (k+1)) :
    rowCount (cliqueBad k hk) i ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr p hp
  exact cliqueBad_row_unique hk i r p (by simpa [row] using hr) (by simpa [row] using hp)

@[simp] theorem rowCount_doubleColors (k : ℕ) (hk : 2 ≤ k) (i : Fin 1) :
    rowCount (doubleColors k hk) i = 2 := by
  have he : row (doubleColors k hk) i = {⟨0,by omega⟩,⟨1,by omega⟩} := by
    ext r; simp [row]
  rw [rowCount,he]
  simp [Fin.ext_iff]

end Chapter09.Source
#print axioms Chapter09.Source.card_le_colors_of_injective
#print axioms Chapter09.Source.card_cliqueBase
#print axioms Chapter09.Source.card_cliqueBad

#print axioms Chapter09.Source.alpha_clique
#print axioms Chapter09.Source.cliqueBad_uScore_overshoot
#print axioms Chapter09.Source.cliqueBad_uScore_global_tie

#print axioms Chapter09.Source.alpha_one_vertex
#print axioms Chapter09.Source.doubleColors_uScore_overshoot
#print axioms Chapter09.Source.doubleColors_uScore_global_tie

#print axioms Chapter09.Source.rowCount_cliqueBad_le_one
#print axioms Chapter09.Source.rowCount_doubleColors
