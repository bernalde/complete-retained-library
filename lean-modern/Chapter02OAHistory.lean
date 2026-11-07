module

public import Chapter02MultiplierExistence
public import Mathlib.Data.List.Basic

@[expose] public section

/-! Literal retained OA tangent histories. Raw batch validity records exact
optimizer facts, not multipliers, cut validity, fiber exclusion or progress.
Rows are all constraints after a feasible NLP and all originally violated
constraints at a restoration anchor. Derivatives are the actual fderiv there. -/

noncomputable section
open scoped BigOperators
namespace Chapter02

structure OABatch (n m : ℕ) where
  integer : IntVector m
  anchor : Point n m
  restoration : Option ℝ

def oaIntCast {m : ℕ} (y : IntVector m) : RealVector m := fun i => (y i : ℝ)

theorem oaIntCast_injective {m : ℕ} : Function.Injective (@oaIntCast m) := by
  intro y z h
  funext i
  exact Int.cast_injective (congrFun h i)

def oaBatchDerivative {n m l r : ℕ} (d : ModelData n m l r) (b : OABatch n m) :
    Fin l → Point n m →L[ℝ] ℝ := fun j => fderiv ℝ (d.g j) b.anchor

def oaBatchRows {n m l r : ℕ} (d : ModelData n m l r) (b : OABatch n m) : Set (Fin l) :=
  match b.restoration with
  | none => Set.univ
  | some _ => {j | 0 < d.g j b.anchor}

def oaBatchCuts {n m l r : ℕ} (d : ModelData n m l r) (b : OABatch n m)
    (q : Point n m) : Prop :=
  SelectedOARows d (oaBatchDerivative d b) b.anchor (oaBatchRows d b) q

def oaBatchValid {n m l r : ℕ} (d : ModelData n m l r) (b : OABatch n m) : Prop :=
  b.integer ∈ IntegerBox d.lo d.hi ∧ b.anchor.2 = oaIntCast b.integer ∧
  match b.restoration with
  | none => IsMinimizer (d.fixedNonlinearFiber (oaIntCast b.integer)) d.objective b.anchor
  | some rho => ¬ (d.fixedNonlinearFiber (oaIntCast b.integer)).Nonempty ∧
      IsMinimizer (RestorationPairs (d.fixedLinearFiber (oaIntCast b.integer)) d.g)
        Prod.snd (b.anchor,rho)

def OAFiberSlater {n m l r : ℕ} (d : ModelData n m l r) : Prop :=
  ∀ y ∈ IntegerBox d.lo d.hi,
    (d.fixedNonlinearFiber (oaIntCast y)).Nonempty →
    ∃ z ∈ d.fixedLinearFiber (oaIntCast y), ∀ j, d.g j z < 0

def oaHistoryFamily {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m)) : TangentFamily n m l H.length where
  origin i := (H.get i).anchor
  selected i := oaBatchRows d (H.get i)
  derivative i := oaBatchDerivative d (H.get i)

def oaMaster {n m l r : ℕ} (d : ModelData n m l r) (H : List (OABatch n m)) :=
  d.masterOn (oaHistoryFamily d H) Set.univ

theorem oa_history_cutRegion_iff {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m)) (q : Point n m) :
    q ∈ (oaHistoryFamily d H).cutRegion d ↔ ∀ b ∈ H, oaBatchCuts d b q := by
  constructor
  · intro h b hb
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
    subst b
    exact h i
  · intro h i
    exact h (H.get i) (List.get_mem H i)

theorem oa_master_mem_iff {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m)) (q : Point n m) :
    q ∈ oaMaster d H ↔ q ∈ d.linearRegion ∧
      q ∈ IntegerCylinder (n := n) d.lo d.hi ∧ ∀ b ∈ H, oaBatchCuts d b q := by
  change ((q ∈ Set.univ ∧ q ∈ (oaHistoryFamily d H).cutRegion d) ∧
    q ∈ d.linearRegion) ∧ q ∈ IntegerCylinder d.lo d.hi ↔ _
  rw [oa_history_cutRegion_iff]
  simp only [Set.mem_univ, true_and, and_comm, and_left_comm, and_assoc]

theorem oa_master_nil {n m l r : ℕ} (d : ModelData n m l r) :
    oaMaster d [] = d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi := by
  ext q
  simp [oa_master_mem_iff]

theorem oa_master_append {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m)) (b : OABatch n m) :
    oaMaster d (H ++ [b]) = oaMaster d H ∩ {q | oaBatchCuts d b q} := by
  ext q
  simp [oa_master_mem_iff, and_assoc, or_imp, forall_and]

theorem oa_master_subset_of_history_subset {n m l r : ℕ} (d : ModelData n m l r)
    {H K : List (OABatch n m)} (h : H ⊆ K) : oaMaster d K ⊆ oaMaster d H := by
  intro q hq
  obtain ⟨hL,hY,hrows⟩ := (oa_master_mem_iff d K q).mp hq
  exact (oa_master_mem_iff d H q).mpr ⟨hL,hY,fun b hb => hrows b (h hb)⟩

theorem oaBatch_derivatives {n m l r : ℕ} (d : ModelData n m l r) (b : OABatch n m)
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    ∀ j, HasFDerivAt (d.g j) (oaBatchDerivative d b j) b.anchor :=
  fun j => (hdiff j b.anchor).hasFDerivAt

theorem oa_master_contains_feasible {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m)) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    d.feasibleOn Set.univ ⊆ oaMaster d H := by
  apply source_feasible_subset_master d (oaHistoryFamily d H) Set.univ hconv
  · exact fun _ => Set.mem_univ _
  · intro i j _
    exact oaBatch_derivatives d (H.get i) hdiff j

theorem oa_master_compact {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m))
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi)) :
    IsCompact (oaMaster d H) := source_master_compact d (oaHistoryFamily d H) hbase

theorem oa_master_reply {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m))
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi)) :
    oaMaster d H = ∅ ∨ ∃ q, IsMinimizer (oaMaster d H) d.objective q := by
  rcases (oaMaster d H).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (source_master_minimum_attained d (oaHistoryFamily d H) hbase h)

theorem oa_master_integer_witness {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m)) (q : Point n m) (hq : q ∈ oaMaster d H) :
    ∃ y ∈ IntegerBox d.lo d.hi, q.2 = oaIntCast y ∧
      (d.fixedLinearFiber (oaIntCast y)).Nonempty := by
  obtain ⟨hL,⟨y,hy,hqy⟩,_⟩ := (oa_master_mem_iff d H q).mp hq
  exact ⟨y,hy,hqy,q,hL,hqy⟩

theorem oaBatch_feasible_minimizer {n m l r : ℕ} (d : ModelData n m l r)
    (b : OABatch n m) (hb : oaBatchValid d b) (hnone : b.restoration = none) :
    IsMinimizer (d.fixedNonlinearFiber (oaIntCast b.integer)) d.objective b.anchor := by
  simpa only [hnone] using hb.2.2

theorem oaBatch_restoration_minimizer {n m l r : ℕ} (d : ModelData n m l r)
    (b : OABatch n m) (hb : oaBatchValid d b) {rho : ℝ}
    (hsome : b.restoration = some rho) :
    ¬ (d.fixedNonlinearFiber (oaIntCast b.integer)).Nonempty ∧
      IsMinimizer (RestorationPairs (d.fixedLinearFiber (oaIntCast b.integer)) d.g)
        Prod.snd (b.anchor,rho) := by
  simpa only [hsome] using hb.2.2

theorem oaBatch_feasible_original {n m l r : ℕ} (d : ModelData n m l r)
    (b : OABatch n m) (hb : oaBatchValid d b) (hnone : b.restoration = none) :
    b.anchor ∈ d.feasibleOn Set.univ := by
  have hmin := oaBatch_feasible_minimizer d b hb hnone
  exact ⟨⟨⟨Set.mem_univ _,hmin.1.2⟩,hmin.1.1.1⟩,b.integer,hb.1,hb.2.1⟩

theorem oaBatch_anchor_linear {n m l r : ℕ} (d : ModelData n m l r)
    (b : OABatch n m) (hb : oaBatchValid d b) : b.anchor ∈ d.linearRegion := by
  cases h : b.restoration with
  | none => exact (oaBatch_feasible_minimizer d b hb h).1.1.1
  | some rho => exact (oaBatch_restoration_minimizer d b hb h).2.1.1.1

theorem oa_infeasible_fiber_has_rows {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (hne : (d.fixedLinearFiber y).Nonempty)
    (hinfeas : ¬ (d.fixedNonlinearFiber y).Nonempty) : Nonempty (Fin l) := by
  classical
  obtain ⟨p,hp⟩ := hne
  have hn : ¬ ∀ j, d.g j p ≤ 0 := by
    intro hg
    exact hinfeas ⟨p,hp,hg⟩
  push_neg at hn
  obtain ⟨j,_⟩ := hn
  exact ⟨j⟩

theorem oaBatch_feasible_lowerBound {n m l r : ℕ} (d : ModelData n m l r)
    (b : OABatch n m) (hb : oaBatchValid d b) (hnone : b.restoration = none)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d)
    {q : Point n m} (hqL : q ∈ d.linearRegion)
    (hys : q.2 = oaIntCast b.integer) (hcuts : oaBatchCuts d b q) :
    d.objective b.anchor ≤ d.objective q := by
  have hmin := oaBatch_feasible_minimizer d b hb hnone
  have hs := hCQ b.integer hb.1 ⟨b.anchor,hmin.1⟩
  obtain ⟨lambda,mu,hkkt⟩ := exists_fixedNLPKKT d b.anchor (oaBatchDerivative d b)
    hconv (oaBatch_derivatives d b hdiff) (by simpa only [hb.2.1] using hmin)
    (by simpa only [hb.2.1] using hs)
  have hrows : SelectedOARows d (oaBatchDerivative d b) b.anchor Set.univ q := by
    simpa only [oaBatchCuts, oaBatchRows, hnone] using hcuts
  have hbound := optimality_cut_of_all_oa_rows hkkt hqL hrows
  rw [hys, ← hb.2.1, optimality_cut_at_anchor] at hbound
  exact hbound

theorem oaBatch_restoration_excludes {n m l r : ℕ} (d : ModelData n m l r)
    (b : OABatch n m) (hb : oaBatchValid d b) {rho : ℝ}
    (hsome : b.restoration = some rho)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    {q : Point n m} (hqL : q ∈ d.linearRegion)
    (hys : q.2 = oaIntCast b.integer) (hcuts : oaBatchCuts d b q) : False := by
  obtain ⟨hinfeas,hmin⟩ := oaBatch_restoration_minimizer d b hb hsome
  letI : Nonempty (Fin l) := oa_infeasible_fiber_has_rows d (oaIntCast b.integer)
    ⟨b.anchor,hmin.1.1⟩ hinfeas
  obtain ⟨lambda,mu,hkkt⟩ := exists_restorationKKT d b.anchor rho (oaBatchDerivative d b)
    hconv (oaBatch_derivatives d b hdiff) (by simpa only [hb.2.1] using hmin)
  have hi : ¬ (d.fixedNonlinearFiber b.anchor.2).Nonempty := by
    simpa only [hb.2.1] using hinfeas
  have hpos := (restoration_positive_iff_fiber_infeasible hkkt hconv).mpr hi
  apply restoration_oa_fiber_excluded_violated hkkt hpos
  refine ⟨q,⟨hqL,hys.trans hb.2.1.symm⟩,?_⟩
  simpa only [oaBatchCuts, oaBatchRows, hsome] using hcuts

theorem oa_fiber_reply_exists {n m l r : ℕ} (d : ModelData n m l r)
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hne : (d.fixedLinearFiber (oaIntCast y)).Nonempty)
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    ∃ b : OABatch n m, oaBatchValid d b ∧ b.integer = y := by
  classical
  by_cases hN : (d.fixedNonlinearFiber (oaIntCast y)).Nonempty
  · obtain ⟨p,hp⟩ := source_fixedNLP_minimum_attained d y hy hbase hN
      (fun j => (hdiff j).continuous)
    exact ⟨⟨y,p,none⟩,⟨hy,hp.1.1.2,hp⟩,rfl⟩
  · letI : Nonempty (Fin l) := oa_infeasible_fiber_has_rows d (oaIntCast y) hne hN
    obtain ⟨p,hp⟩ := restorationPairs_minimum_attained
      (source_fixedLinearFiber_compact d y hy hbase) hne
      (fun j => (hdiff j).continuous)
    exact ⟨⟨y,p.1,some p.2⟩,⟨hy,hp.1.1.2,hN,hp⟩,rfl⟩

theorem oaBatch_feasible_iff_nonlinear_nonempty {n m l r : ℕ}
    (d : ModelData n m l r) (b : OABatch n m) (hb : oaBatchValid d b) :
    b.restoration = none ↔ (d.fixedNonlinearFiber (oaIntCast b.integer)).Nonempty := by
  constructor
  · intro h
    exact ⟨b.anchor,(oaBatch_feasible_minimizer d b hb h).1⟩
  · intro hne
    cases h : b.restoration with
    | none => rfl
    | some rho => exact False.elim ((oaBatch_restoration_minimizer d b hb h).1 hne)

theorem oaBatch_restoration_positive {n m l r : ℕ} (d : ModelData n m l r)
    (b : OABatch n m) (hb : oaBatchValid d b) {rho : ℝ}
    (hsome : b.restoration = some rho) : 0 < rho := by
  obtain ⟨hinfeas,hmin⟩ := oaBatch_restoration_minimizer d b hb hsome
  letI : Nonempty (Fin l) := oa_infeasible_fiber_has_rows d (oaIntCast b.integer)
    ⟨b.anchor,hmin.1.1⟩ hinfeas
  have hp := (restorationPairs_minimizer_iff
    (d.fixedLinearFiber (oaIntCast b.integer)) d.g (b.anchor,rho)).mp hmin
  dsimp only at hp
  rw [hp.2]
  exact (signedMinimum_pos_iff hp.1).mpr hinfeas

theorem oa_zero_rows_batch_not_restoration {n m r : ℕ} (d : ModelData n m 0 r)
    (b : OABatch n m) (hb : oaBatchValid d b) : b.restoration = none := by
  apply (oaBatch_feasible_iff_nonlinear_nonempty d b hb).mpr
  exact ⟨b.anchor,⟨oaBatch_anchor_linear d b hb,hb.2.1⟩,fun j => Fin.elim0 j⟩

theorem oa_zero_rows_master_eq_feasible {n m r : ℕ} (d : ModelData n m 0 r)
    (H : List (OABatch n m)) : oaMaster d H = d.feasibleOn Set.univ := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨hL,hY,_⟩ := (oa_master_mem_iff d H q).mp hq
    exact ⟨⟨⟨Set.mem_univ _,fun j => Fin.elim0 j⟩,hL⟩,hY⟩
  · exact oa_master_contains_feasible d H (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)

theorem oa_master_lowerBound {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m)) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {q : Point n m}
    (hq : IsMinimizer (oaMaster d H) d.objective q) :
    IsLowerBound (d.feasibleOn Set.univ) d.objective (d.objective q) :=
  lowerBound_of_relaxation (oa_master_contains_feasible d H hconv hdiff)
    (minimizer_is_lowerBound hq)

theorem oa_master_feasible_minimizer {n m l r : ℕ} (d : ModelData n m l r)
    (H : List (OABatch n m)) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {q : Point n m}
    (hq : IsMinimizer (oaMaster d H) d.objective q)
    (hfeas : q ∈ d.feasibleOn Set.univ) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective q :=
  minimizer_of_relaxation_feasible (oa_master_contains_feasible d H hconv hdiff) hq hfeas

#print axioms oaIntCast_injective
#print axioms oa_history_cutRegion_iff
#print axioms oa_master_mem_iff
#print axioms oa_master_nil
#print axioms oa_master_append
#print axioms oa_master_subset_of_history_subset
#print axioms oaBatch_derivatives
#print axioms oa_master_contains_feasible
#print axioms oa_master_compact
#print axioms oa_master_reply
#print axioms oa_master_integer_witness
#print axioms oaBatch_feasible_minimizer
#print axioms oaBatch_restoration_minimizer
#print axioms oaBatch_feasible_original
#print axioms oaBatch_anchor_linear
#print axioms oa_infeasible_fiber_has_rows
#print axioms oaBatch_feasible_lowerBound
#print axioms oaBatch_restoration_excludes
#print axioms oa_fiber_reply_exists
#print axioms oaBatch_feasible_iff_nonlinear_nonempty
#print axioms oaBatch_restoration_positive
#print axioms oa_zero_rows_batch_not_restoration
#print axioms oa_zero_rows_master_eq_feasible
#print axioms oa_master_lowerBound
#print axioms oa_master_feasible_minimizer

end Chapter02
