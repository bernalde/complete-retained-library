module

public import Chapter02FBBTOperator

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter02FBBT

 theorem within_refl {ι} (q : Bounds ι) : Within q q := fun _ => ⟨le_rfl, le_rfl⟩
 theorem within_trans {ι} {p q r : Bounds ι} (h : Within p q) (k : Within q r) :
    Within p r := fun i => ⟨(k i).1.trans (h i).1, (h i).2.trans (k i).2⟩
 theorem within_antisymm {ι} {p q : Bounds ι} (h : Within p q) (k : Within q p) : p = q := by
  apply Prod.ext <;> funext i
  · exact le_antisymm (k i).1 (h i).1
  · exact le_antisymm (h i).2 (k i).2
 theorem ordered_of_within {ι} {p q : Bounds ι} (hp : Ordered p) (h : Within p q) :
    Ordered q := fun i => (h i).1.trans ((hp i).trans (h i).2)
 theorem members_mono {ι} {p q : Bounds ι} (h : Within p q) : members p ⊆ members q :=
  fun _ hx i => ⟨(h i).1.trans (hx i).1, (hx i).2.trans (h i).2⟩
 theorem clip_left {ι} (p q : Bounds ι) : Within (clip p q) p :=
  fun _ => ⟨le_max_left _ _, min_le_left _ _⟩
 theorem clip_right {ι} (p q : Bounds ι) : Within (clip p q) q :=
  fun _ => ⟨le_max_right _ _, min_le_right _ _⟩
 theorem clip_mono {ι} {p q : Bounds ι} (h : Within p q) (r : Bounds ι) :
    Within (clip p r) (clip q r) :=
  fun i => ⟨max_le_max (h i).1 le_rfl, min_le_min (h i).2 le_rfl⟩
 theorem clip_eq_left {ι} {p q : Bounds ι} (h : Within p q) : clip p q = p := by
  apply Prod.ext <;> funext i
  · exact max_eq_left (h i).1
  · exact min_eq_left (h i).2

 theorem seededMax_le {m} (s c : ℝ) (v : Fin m → ℝ) :
    seededMax s v ≤ c ↔ s ≤ c ∧ ∀ i, v i ≤ c := by
  unfold seededMax
  constructor
  · intro h
    have hh := (Finset.sup'_le_iff _ _).mp h
    exact ⟨hh none (Finset.mem_univ _), fun i => hh (some i) (Finset.mem_univ _)⟩
  · rintro ⟨hs, hv⟩
    apply (Finset.sup'_le_iff _ _).mpr
    intro o _
    cases o with
    | none => exact hs
    | some i => exact hv i
 theorem le_seededMin {m} (s c : ℝ) (v : Fin m → ℝ) :
    c ≤ seededMin s v ↔ c ≤ s ∧ ∀ i, c ≤ v i := by
  unfold seededMin
  constructor
  · intro h
    have hh := (Finset.le_inf'_iff _ _).mp h
    exact ⟨hh none (Finset.mem_univ _), fun i => hh (some i) (Finset.mem_univ _)⟩
  · rintro ⟨hs, hv⟩
    apply (Finset.le_inf'_iff _ _).mpr
    intro o _
    cases o with
    | none => exact hs
    | some i => exact hv i
 theorem seed_le_max {m} (s : ℝ) (v : Fin m → ℝ) : s ≤ seededMax s v :=
  (seededMax_le _ _ _).1 le_rfl |>.1
 theorem value_le_max {m} (s : ℝ) (v : Fin m → ℝ) (i) : v i ≤ seededMax s v :=
  (seededMax_le _ _ _).1 le_rfl |>.2 i
 theorem min_le_seed {m} (s : ℝ) (v : Fin m → ℝ) : seededMin s v ≤ s :=
  (le_seededMin _ _ _).1 le_rfl |>.1
 theorem min_le_value {m} (s : ℝ) (v : Fin m → ℝ) (i) : seededMin s v ≤ v i :=
  (le_seededMin _ _ _).1 le_rfl |>.2 i
 theorem seededMax_mono {m} {s t : ℝ} {v w : Fin m → ℝ}
    (h : s ≤ t) (k : ∀ i, v i ≤ w i) : seededMax s v ≤ seededMax t w :=
  (seededMax_le _ _ _).2 ⟨h.trans (seed_le_max _ _),
    fun i => (k i).trans (value_le_max _ _ _)⟩
 theorem seededMin_mono {m} {s t : ℝ} {v w : Fin m → ℝ}
    (h : s ≤ t) (k : ∀ i, v i ≤ w i) : seededMin s v ≤ seededMin t w :=
  (le_seededMin _ _ _).2 ⟨(min_le_seed _ _).trans h,
    fun i => (min_le_value _ _ _).trans (k i)⟩

 theorem products_mono {n m} (A : Matrix n m) {p q : JointBounds n m}
    (h : Within p q) (i j) :
    productLo A q i j ≤ productLo A p i j ∧ productHi A p i j ≤ productHi A q i j := by
  by_cases ha : 0 ≤ A i j
  · simp only [productLo, productHi, Chapter02.affineProductLo, Chapter02.affineProductHi, if_pos ha]
    exact ⟨mul_le_mul_of_nonneg_left (h (.inl j)).1 ha,
      mul_le_mul_of_nonneg_left (h (.inl j)).2 ha⟩
  · simp only [productLo, productHi, Chapter02.affineProductLo, Chapter02.affineProductHi, if_neg ha]
    exact ⟨mul_le_mul_of_nonpos_left (h (.inl j)).2 (le_of_not_ge ha),
      mul_le_mul_of_nonpos_left (h (.inl j)).1 (le_of_not_ge ha)⟩
 theorem images_mono {n m} (A : Matrix n m) {p q : JointBounds n m}
    (h : Within p q) (i) : imageLo A q i ≤ imageLo A p i ∧ imageHi A p i ≤ imageHi A q i :=
  ⟨Finset.sum_le_sum (fun j _ => (products_mono A h i j).1),
   Finset.sum_le_sum (fun j _ => (products_mono A h i j).2)⟩
 theorem rests_mono {n m} (A : Matrix n m) {p q : JointBounds n m}
    (h : Within p q) (i j) : restLo A q i j ≤ restLo A p i j ∧ restHi A p i j ≤ restHi A q i j :=
  ⟨Finset.sum_le_sum (fun k _ => (products_mono A h i k).1),
   Finset.sum_le_sum (fun k _ => (products_mono A h i k).2)⟩
 theorem inverses_mono {n m} (A : Matrix n m) {p q : JointBounds n m}
    (h : Within p q) (i j) : inverseLo A q i j ≤ inverseLo A p i j ∧
      inverseHi A p i j ≤ inverseHi A q i j := by
  by_cases hz : A i j = 0
  · simpa [inverseLo, inverseHi, hz] using h (.inl j)
  have hr := rests_mono A h i j
  by_cases hp : 0 < A i j
  · simp only [inverseLo, inverseHi, if_neg hz, if_pos hp]
    exact ⟨div_le_div_of_nonneg_right (sub_le_sub (h (.inr i)).1 hr.2) hp.le,
      div_le_div_of_nonneg_right (sub_le_sub (h (.inr i)).2 hr.1) hp.le⟩
  · have hn : A i j ≤ 0 := le_of_not_gt hp
    simp only [inverseLo, inverseHi, if_neg hz, if_neg hp]
    exact ⟨div_le_div_of_nonpos_of_le hn (sub_le_sub (h (.inr i)).2 hr.1),
      div_le_div_of_nonpos_of_le hn (sub_le_sub (h (.inr i)).1 hr.2)⟩

 theorem upward_contract {n m} (A : Matrix n m) (q : JointBounds n m) : Within (upward A q) q := by
  intro s; cases s with
  | inl j => exact ⟨le_rfl, le_rfl⟩
  | inr i => exact ⟨le_max_left _ _, min_le_left _ _⟩
 theorem downward_contract {n m} (A : Matrix n m) (q : JointBounds n m) : Within (downward A q) q := by
  intro s; cases s with
  | inl j => exact ⟨seed_le_max _ _, min_le_seed _ _⟩
  | inr i => exact ⟨le_rfl, le_rfl⟩
 theorem upward_mono {n m} (A : Matrix n m) {p q : JointBounds n m} (h : Within p q) :
    Within (upward A p) (upward A q) := by
  intro s; cases s with
  | inl j => exact h (.inl j)
  | inr i => exact ⟨max_le_max (h (.inr i)).1 (images_mono A h i).1,
      min_le_min (h (.inr i)).2 (images_mono A h i).2⟩
 theorem downward_mono {n m} (A : Matrix n m) {p q : JointBounds n m} (h : Within p q) :
    Within (downward A p) (downward A q) := by
  intro s; cases s with
  | inl j => exact ⟨seededMax_mono (h (.inl j)).1 (fun i => (inverses_mono A h i j).1),
      seededMin_mono (h (.inl j)).2 (fun i => (inverses_mono A h i j).2)⟩
  | inr i => exact h (.inr i)
 theorem rawF_contract {n m} (A : Matrix n m) (q0 q : JointBounds n m) : Within (rawF A q0 q) q :=
  within_trans (downward_contract _ _) (within_trans (upward_contract _ _) (clip_left _ _))
 theorem rawF_within_initial {n m} (A : Matrix n m) (q0 q : JointBounds n m) : Within (rawF A q0 q) q0 :=
  within_trans (downward_contract _ _) (within_trans (upward_contract _ _) (clip_right _ _))
 theorem rawF_mono {n m} (A : Matrix n m) (q0 : JointBounds n m)
    {p q : JointBounds n m} (h : Within p q) : Within (rawF A q0 p) (rawF A q0 q) :=
  downward_mono _ (upward_mono _ (clip_mono h q0))

 theorem rawF_fixed_iff {n m} (A : Matrix n m) (q0 q : JointBounds n m) :
    rawF A q0 q = q ↔ Within q q0 ∧ upward A q = q ∧ downward A q = q := by
  constructor
  · intro h
    have hc : clip q q0 = q := within_antisymm (clip_left _ _)
      (by have ht := within_trans (downward_contract A (upward A (clip q q0))) (upward_contract A (clip q q0)); change Within (rawF A q0 q) (clip q q0) at ht; rw [h] at ht; exact ht)
    have hu : upward A q = q := within_antisymm (upward_contract _ _)
      (by have ht := downward_contract A (upward A (clip q q0)); change Within (rawF A q0 q) (upward A (clip q q0)) at ht; rw [h, hc] at ht; exact ht)
    refine ⟨h ▸ rawF_within_initial A q0 q, hu, ?_⟩
    simpa only [rawF, hc, hu] using h
  · rintro ⟨hq, hu, hd⟩
    simp only [rawF, clip_eq_left hq, hu, hd]

end Chapter02FBBT
