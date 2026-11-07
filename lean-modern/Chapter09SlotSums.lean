module

public import Chapter09Slots

@[expose] public section

/-! Literal source sums and their exact finite conflict representation.
The printed color sum is ordered; its factor two is proved, not absorbed silently. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Source

theorem flag_binary {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) (r : Fin k) :
    flag S i r = 0 ∨ flag S i r = 1 := by unfold flag; split_ifs <;> simp

theorem flag_sq {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) (r : Fin k) :
    flag S i r ^ 2 = flag S i r := by rcases flag_binary S i r with h|h <;> rw [h] <;> norm_num

def Binary {n k : ℕ} (x : Fin n → Fin k → ℝ) : Prop := ∀ i r, x i r = 0 ∨ x i r = 1

def selected {n k : ℕ} (x : Fin n → Fin k → ℝ) : Finset (Slot n k) := by
  classical
  exact Finset.univ.filter (fun u => x u.1 u.2 = 1)

theorem flag_selected {n k : ℕ} (x : Fin n → Fin k → ℝ) (hx : Binary x) :
    flag (selected x) = x := by
  classical
  funext i r
  rcases hx i r with h|h <;> simp [flag,selected,h]

@[simp] theorem selected_flag {n k : ℕ} (S : Finset (Slot n k)) : selected (flag S) = S := by
  classical
  ext u; simp [selected,flag]

theorem rowCount_sum_flag {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) :
    (rowCount S i : ℝ) = ∑ r, flag S i r := by
  simp [rowCount,row,flag,Finset.sum_boole]

def reward {n k : ℕ} (S : Finset (Slot n k)) : ℝ := ∑ i, ∑ r, flag S i r ^ 2

theorem sum_flag_eq_card {n k : ℕ} (S : Finset (Slot n k)) :
    (∑ i, ∑ r, flag S i r) = (S.card : ℝ) := by
  calc
    (∑ i, ∑ r, flag S i r) = ∑ u : Slot n k, if u ∈ S then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]; rfl
    _ = (S.card : ℝ) := by simp

theorem reward_eq_card {n k : ℕ} (S : Finset (Slot n k)) : reward S = (S.card : ℝ) := by
  simp only [reward,flag_sq]; exact sum_flag_eq_card S

def sourceConstraints {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) : Prop :=
  (∀ e ∈ G.edges, ∀ r, flag S e.1 r + flag S e.2 r ≤ 1) ∧
  (∀ i, ∑ r, flag S i r ≤ 1)

theorem feasible_iff_sourceConstraints {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    Feasible G S ↔ sourceConstraints G S := by
  rw [feasible_iff]
  have he : ∀ (i j : Fin n) (r : Fin k),
      (¬ ((i,r) ∈ S ∧ (j,r) ∈ S)) ↔ flag S i r + flag S j r ≤ 1 := by
    intro i j r
    by_cases hi : (i,r) ∈ S <;> by_cases hj : (j,r) ∈ S <;> simp [flag,hi,hj]
  have hr : (∀ i r p, (i,r) ∈ S → (i,p) ∈ S → r=p) ↔ ∀ i, ∑ r, flag S i r ≤ 1 := by
    constructor
    · intro h i
      rw [← rowCount_sum_flag]
      have hc : rowCount S i ≤ 1 := Finset.card_le_one.mpr (by
        intro r hr p hp; exact h i r p (by simpa [row] using hr) (by simpa [row] using hp))
      exact_mod_cast hc
    · intro h i r p hr hp
      have hc : rowCount S i ≤ 1 := by exact_mod_cast (by simpa [← rowCount_sum_flag] using h i : (rowCount S i : ℝ) ≤ 1)
      exact Finset.card_le_one.mp hc r (by simpa [row] using hr) p (by simpa [row] using hp)
  simp only [he,hr,sourceConstraints]

def edgeProducts {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) : ℝ :=
  ∑ e ∈ G.edges, ∑ r, flag S e.1 r * flag S e.2 r

def orderedProducts {n k : ℕ} (S : Finset (Slot n k)) : ℝ :=
  ∑ i, ∑ r, ∑ p, if p ≠ r then flag S i r * flag S i p else 0

def colorProducts {n k : ℕ} (S : Finset (Slot n k)) : ℝ :=
  ∑ i, ∑ r, ∑ p, if r < p then flag S i r * flag S i p else 0

def pairProducts {n k : ℕ} (P : Finset (Slot n k × Slot n k)) (S : Finset (Slot n k)) : ℝ :=
  ∑ e ∈ P, flag S e.1.1 e.1.2 * flag S e.2.1 e.2.2

theorem sum_spatialPairs {n k : ℕ} (G : Graph n) (f : Slot n k × Slot n k → ℝ) :
    (∑ e ∈ spatialPairs G k, f e) = ∑ e ∈ G.edges, ∑ r, f ((e.1,r),(e.2,r)) := by
  have hexp : (∑ q ∈ G.edges.product (Finset.univ : Finset (Fin k)),
      f ((q.1.1,q.2),(q.1.2,q.2))) = ∑ e ∈ G.edges, ∑ r, f ((e.1,r),(e.2,r)) := by
    exact Finset.sum_product G.edges Finset.univ (fun q => f ((q.1.1,q.2),(q.1.2,q.2)))
  rw [← hexp]
  symm
  apply Finset.sum_bij (fun e _ => ((e.1.1,e.2),(e.1.2,e.2)))
  · intro e he
    have he1 := (Finset.mem_product.mp he).1
    exact (mem_spatialPairs G _).mpr ⟨he1,rfl⟩
  · rintro ⟨⟨i,j⟩,r⟩ ha ⟨⟨u,v⟩,p⟩ hb h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨⟨h.1.1,h.2.1⟩,h.1.2⟩
  · rintro ⟨⟨i,r⟩,⟨j,p⟩⟩ he
    obtain ⟨hij,hrp⟩ := (mem_spatialPairs G _).mp he
    change r = p at hrp
    subst p
    exact ⟨((i,j),r),by simp [hij],rfl⟩
  · intro a ha; rfl

theorem sum_colorPairs {n k : ℕ} (f : Slot n k × Slot n k → ℝ) :
    (∑ e ∈ colorPairs n k, f e) =
      ∑ i, ∑ r, ∑ p, if r<p then f ((i,r),(i,p)) else 0 := by
  let C : Finset (Fin k × Fin k) := Finset.univ.filter (fun e => e.1 < e.2)
  have hs : (∑ e ∈ colorPairs n k, f e) =
      ∑ q ∈ (Finset.univ : Finset (Fin n)).product C, f ((q.1,q.2.1),(q.1,q.2.2)) := by
    symm
    apply Finset.sum_bij (fun q _ => ((q.1,q.2.1),(q.1,q.2.2)))
    · intro q hq; simpa [C] using hq
    · intro a ha b hb h
      obtain ⟨i,⟨r,p⟩⟩ := a
      obtain ⟨j,⟨s,t⟩⟩ := b
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1.1,h.1.2,h.2.2⟩
    · rintro ⟨⟨i,r⟩,⟨j,p⟩⟩ he
      obtain ⟨hij,hrp⟩ := (mem_colorPairs _).mp he
      change i = j at hij
      subst j
      exact ⟨(i,(r,p)),by simp [C,hrp],rfl⟩
    · intro q hq; rfl
  rw [hs]
  simp [Finset.sum_product,C,Finset.sum_filter,Fintype.sum_prod_type]

theorem spatial_pairProducts {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    pairProducts (spatialPairs G k) S = edgeProducts G S :=
  sum_spatialPairs G _

theorem color_pairProducts {n k : ℕ} (S : Finset (Slot n k)) :
    pairProducts (colorPairs n k) S = colorProducts S := sum_colorPairs _

theorem orderedProducts_eq_twice {n k : ℕ} (S : Finset (Slot n k)) :
    orderedProducts S = 2 * colorProducts S := by
  have split : ∀ (i : Fin n) (r p : Fin k),
      (if p ≠ r then flag S i r * flag S i p else 0) =
      (if r < p then flag S i r * flag S i p else 0) +
      (if p < r then flag S i r * flag S i p else 0) := by
    intro i r p; rcases lt_trichotomy r p with h|h|h <;> simp [h,ne_of_lt,ne_of_gt,not_lt_of_ge,le_of_lt]
  have swap : (∑ i, ∑ r, ∑ p, if p<r then flag S i r * flag S i p else 0) = colorProducts S := by
    unfold colorProducts
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r hr
    apply Finset.sum_congr rfl; intro p hp
    simp [mul_comm]
  simp only [orderedProducts,split,Finset.sum_add_distrib]
  rw [swap]
  change colorProducts S + colorProducts S = 2 * colorProducts S
  ring

theorem orderedProducts_eq_rows {n k : ℕ} (S : Finset (Slot n k)) :
    orderedProducts S = ∑ i, (rowCount S i : ℝ) * ((rowCount S i : ℝ) - 1) := by
  unfold orderedProducts
  apply Finset.sum_congr rfl
  intro i hi
  have term : ∀ (r p : Fin k),
      (if p ≠ r then flag S i r * flag S i p else 0) =
      flag S i r * flag S i p - (if p=r then flag S i r else 0) := by
    intro r p
    by_cases h : p=r
    · subst p; simp [← pow_two,flag_sq]
    · simp [h]
  simp only [term,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [← Finset.sum_mul_sum,← rowCount_sum_flag]
  ring

theorem colorProducts_eq_rows {n k : ℕ} (S : Finset (Slot n k)) :
    colorProducts S = ∑ i, (rowCount S i : ℝ) * ((rowCount S i : ℝ)-1) / 2 := by
  have h := orderedProducts_eq_twice S
  rw [orderedProducts_eq_rows] at h
  rw [← Finset.sum_div]
  linarith

theorem pairProducts_eq_conflicts {n k : ℕ} (P : Finset (Slot n k × Slot n k))
    (S : Finset (Slot n k)) : pairProducts P S = ((Chapter09.conflicts P S).card : ℝ) := by
  rw [pairProducts,Chapter09.conflicts,Finset.card_eq_sum_ones, Nat.cast_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S <;> simp [flag,h1,h2]

theorem uScore_eq_products {n k : ℕ} (G : Graph n) (a b : ℝ) (S : Finset (Slot n k)) :
    uScore G a b S = (S.card : ℝ) - a*edgeProducts G S - b*colorProducts S := by
  have term : ∀ e : Slot n k × Slot n k,
      (if e.1∈S ∧ e.2∈S then weight a b e else 0) =
      weight a b e * (flag S e.1.1 e.1.2 * flag S e.2.1 e.2.2) := by
    intro e
    by_cases h1 : e.1∈S <;> by_cases h2 : e.2∈S <;> simp [flag,h1,h2]
  unfold uScore Chapter09.score Chapter09.conflicts
  rw [Finset.sum_filter]
  simp only [term]
  rw [conflictPairs,Finset.sum_union (spatial_color_disjoint G k)]
  have h1 : (∑ e ∈ spatialPairs G k, weight a b e * (flag S e.1.1 e.1.2 * flag S e.2.1 e.2.2)) = a*edgeProducts G S := by
    rw [← spatial_pairProducts G S, pairProducts,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e he; rw [weight_spatial G a b e he]
  have h2 : (∑ e ∈ colorPairs n k, weight a b e * (flag S e.1.1 e.1.2 * flag S e.2.1 e.2.2)) = b*colorProducts S := by
    rw [← color_pairProducts S,pairProducts,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e he; rw [weight_color a b e he]
  rw [h1,h2]; ring

theorem uScore_eq_counts {n k : ℕ} (G : Graph n) (a b : ℝ) (S : Finset (Slot n k)) :
    uScore G a b S = (S.card : ℝ) - a*edgeProducts G S -
      b * ∑ i, (rowCount S i : ℝ) * ((rowCount S i : ℝ)-1) / 2 := by
  rw [uScore_eq_products,colorProducts_eq_rows]

def nScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) : ℝ :=
  reward S - c1 * edgeProducts G S - c2 * orderedProducts S

theorem nScore_eq_uScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) :
    nScore G c1 c2 S = uScore G c1 (2*c2) S := by
  rw [nScore,reward_eq_card,orderedProducts_eq_twice,uScore_eq_products]; ring

end Chapter09.Source
#print axioms Chapter09.Source.flag_selected
#print axioms Chapter09.Source.reward_eq_card
#print axioms Chapter09.Source.feasible_iff_sourceConstraints
#print axioms Chapter09.Source.orderedProducts_eq_twice
#print axioms Chapter09.Source.uScore_eq_counts
#print axioms Chapter09.Source.nScore_eq_uScore
