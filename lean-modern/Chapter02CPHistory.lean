module

public import Chapter02ESH
public import Mathlib.Tactic

@[expose] public section

/-! Literal ECP/ESH retained canonical tangent histories. Trial and origin differ
for ESH. Source policies contain no progress, separation or oracle-success field.
Positive constraint tolerance is not an objective-gap or feasibility certificate.
Seeds are arbitrary finite canonical tangent families; this does not encode an
LP preprocessing execution. All global source hypotheses are explicit. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

structure CPBatch (n m l : ℕ) where
  trial : Point n m
  origin : Point n m
  rows : Finset (Fin l)

inductive CPMode (n m : ℕ)
  | ecpMost
  | ecpAll
  | esh (interior : Point n m)

def cpBase (d : ModelData n m l r) :=
  d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi

def cpBatchCuts (d : ModelData n m l r) (b : CPBatch n m l) (q : Point n m) :=
  ∀ j ∈ b.rows, d.g j b.origin + fderiv ℝ (d.g j) b.origin (q - b.origin) ≤ 0

def cpHistoryFamily (d : ModelData n m l r) (H : List (CPBatch n m l)) :
    TangentFamily n m l H.length where
  origin i := (H.get i).origin
  selected i := ↑(H.get i).rows
  derivative i j := fderiv ℝ (d.g j) (H.get i).origin

def cpMaster (d : ModelData n m l r) (H : List (CPBatch n m l)) :=
  d.masterOn (cpHistoryFamily d H) Set.univ

def CPFeasibleWithin (d : ModelData n m l r) (eps : ℝ) (q : Point n m) :=
  ∀ j, d.g j q ≤ eps

def CPInterior (d : ModelData n m l r) : CPMode n m → Prop
  | .ecpMost => True
  | .ecpAll => True
  | .esh a => a ∈ d.linearRegion ∧ ∀ j, d.g j a < 0

def CPBatchValid (d : ModelData n m l r) (mode : CPMode n m)
    (b : CPBatch n m l) : Prop :=
  match mode with
  | .ecpMost => b.origin = b.trial ∧ b.rows.Nonempty ∧
      ∀ j ∈ b.rows, ∀ k, d.g k b.trial ≤ d.g j b.trial
  | .ecpAll => b.origin = b.trial ∧ ∀ j, j ∈ b.rows ↔ 0 < d.g j b.trial
  | .esh a => ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      b.origin = AffineMap.lineMap a b.trial t ∧
      (∀ j, d.g j b.origin ≤ 0) ∧ b.rows.Nonempty ∧
      ∀ j, j ∈ b.rows ↔ d.g j b.origin = 0

def CPStep (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (H : List (CPBatch n m l)) (b : CPBatch n m l) : Prop :=
  IsMinimizer (cpMaster d H) d.objective b.trial ∧
  ¬ CPFeasibleWithin d eps b.trial ∧ CPBatchValid d mode b

def CPContinue (d : ModelData n m l r) (mode : CPMode n m) (eps : ℝ)
    (H K : List (CPBatch n m l)) : Prop :=
  ∃ b, K = H ++ [b] ∧ CPStep d mode eps H b

inductive CPResult (n m : ℕ)
  | infeasible
  | point (q : Point n m)

inductive CPStop (d : ModelData n m l r) (eps : ℝ)
    (H : List (CPBatch n m l)) : CPResult n m → Prop
  | empty (h : cpMaster d H = ∅) : CPStop d eps H .infeasible
  | point (q : Point n m) (minimum : IsMinimizer (cpMaster d H) d.objective q)
      (tolerance : CPFeasibleWithin d eps q) : CPStop d eps H (.point q)

def CPReturnCertificate (d : ModelData n m l r) (eps : ℝ) : CPResult n m → Prop
  | .infeasible => d.feasibleOn Set.univ = ∅
  | .point q => q ∈ cpBase d ∧ CPFeasibleWithin d eps q ∧
      IsLowerBound (d.feasibleOn Set.univ) d.objective (d.objective q)

theorem cp_history_cutRegion_iff (d : ModelData n m l r)
    (H : List (CPBatch n m l)) (q : Point n m) :
    q ∈ (cpHistoryFamily d H).cutRegion d ↔ ∀ b ∈ H, cpBatchCuts d b q := by
  constructor
  · intro h b hb
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
    subst b
    exact h i
  · intro h i
    exact h (H.get i) (List.get_mem H i)

theorem cp_master_mem_iff (d : ModelData n m l r)
    (H : List (CPBatch n m l)) (q : Point n m) :
    q ∈ cpMaster d H ↔ q ∈ cpBase d ∧ ∀ b ∈ H, cpBatchCuts d b q := by
  change ((q ∈ Set.univ ∧ q ∈ (cpHistoryFamily d H).cutRegion d) ∧
    q ∈ d.linearRegion) ∧ q ∈ IntegerCylinder d.lo d.hi ↔ _
  rw [cp_history_cutRegion_iff]
  simp only [cpBase, Set.mem_univ, true_and, Set.mem_inter_iff, and_comm,
    and_left_comm, and_assoc]

theorem cp_master_nil (d : ModelData n m l r) : cpMaster d [] = cpBase d := by
  ext q; simp [cp_master_mem_iff]

theorem cp_master_append (d : ModelData n m l r)
    (H : List (CPBatch n m l)) (b : CPBatch n m l) :
    cpMaster d (H ++ [b]) = cpMaster d H ∩ {q | cpBatchCuts d b q} := by
  ext q; simp [cp_master_mem_iff, and_assoc, or_imp, forall_and]

theorem cp_master_antitone (d : ModelData n m l r)
    {H K : List (CPBatch n m l)} (h : H ⊆ K) : cpMaster d K ⊆ cpMaster d H := by
  intro q hq
  obtain ⟨hb,hcuts⟩ := (cp_master_mem_iff d K q).mp hq
  exact (cp_master_mem_iff d H q).mpr ⟨hb,fun b hmem => hcuts b (h hmem)⟩

theorem cp_master_contains_feasible (d : ModelData n m l r)
    (H : List (CPBatch n m l)) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    d.feasibleOn Set.univ ⊆ cpMaster d H := by
  apply source_feasible_subset_master d (cpHistoryFamily d H) Set.univ hconv
  · exact fun _ => Set.mem_univ _
  · intro i j _
    exact (hdiff j _).hasFDerivAt

theorem cp_master_compact (d : ModelData n m l r)
    (H : List (CPBatch n m l)) (hbase : IsCompact (cpBase d)) :
    IsCompact (cpMaster d H) :=
  source_master_compact d (cpHistoryFamily d H) hbase

theorem cp_master_reply (d : ModelData n m l r)
    (H : List (CPBatch n m l)) (hbase : IsCompact (cpBase d)) :
    cpMaster d H = ∅ ∨ ∃ q, IsMinimizer (cpMaster d H) d.objective q := by
  rcases (cpMaster d H).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (source_master_minimum_attained d (cpHistoryFamily d H) hbase h)

theorem cp_master_lowerBound (d : ModelData n m l r)
    (H : List (CPBatch n m l)) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {q : Point n m}
    (hq : IsMinimizer (cpMaster d H) d.objective q) :
    IsLowerBound (d.feasibleOn Set.univ) d.objective (d.objective q) :=
  lowerBound_of_relaxation (cp_master_contains_feasible d H hconv hdiff)
    (minimizer_is_lowerBound hq)

theorem cp_master_values_monotone (d : ModelData n m l r)
    {H K : List (CPBatch n m l)} (hHK : H ⊆ K) {p q : Point n m}
    (hp : IsMinimizer (cpMaster d H) d.objective p)
    (hq : IsMinimizer (cpMaster d K) d.objective q) : d.objective p ≤ d.objective q :=
  hp.2 q (cp_master_antitone d hHK hq.1)

theorem cp_failed_test_row (d : ModelData n m l r) {eps : ℝ} {q : Point n m}
    (h : ¬ CPFeasibleWithin d eps q) : ∃ j, eps < d.g j q := by
  simpa only [CPFeasibleWithin, not_forall, not_le] using h

theorem cp_ecp_selected_violation (d : ModelData n m l r) {eps : ℝ}
    (heps : 0 ≤ eps) {b : CPBatch n m l}
    (hfail : ¬ CPFeasibleWithin d eps b.trial)
    (hvalid : CPBatchValid d .ecpMost b ∨ CPBatchValid d .ecpAll b) :
    b.origin = b.trial ∧ ∃ j ∈ b.rows, eps < d.g j b.trial := by
  obtain ⟨k,hk⟩ := cp_failed_test_row d hfail
  rcases hvalid with h | h
  · obtain ⟨horg,hne,hmax⟩ := h
    obtain ⟨j,hj⟩ := hne
    exact ⟨horg,j,hj,hk.trans_le (hmax j hj k)⟩
  · exact ⟨h.1,k,(h.2 k).mpr (heps.trans_lt hk),hk⟩

theorem cp_batch_origin_linearRegion (d : ModelData n m l r) (mode : CPMode n m)
    (ha : CPInterior d mode) {b : CPBatch n m l}
    (hvalid : CPBatchValid d mode b) (htrial : b.trial ∈ cpBase d) :
    b.origin ∈ d.linearRegion := by
  cases mode with
  | ecpMost => exact hvalid.1 ▸ htrial.1
  | ecpAll => exact hvalid.1 ▸ htrial.1
  | esh a =>
    obtain ⟨t,ht,horg,_⟩ := hvalid
    rw [horg]
    exact (source_linearRegion_convex d).lineMap_mem ha.1 htrial.1 ⟨ht.1.le,ht.2.le⟩

theorem cp_policy_reply_exists (d : ModelData n m l r) (mode : CPMode n m)
    (hcontinuous : ∀ j, Continuous (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 ≤ eps) (q : Point n m)
    (hfail : ¬ CPFeasibleWithin d eps q) :
    ∃ b : CPBatch n m l, b.trial = q ∧ CPBatchValid d mode b := by
  classical
  obtain ⟨k,hk⟩ := cp_failed_test_row d hfail
  letI : Nonempty (Fin l) := ⟨k⟩
  cases mode with
  | ecpMost =>
    obtain ⟨j,hj⟩ := eshMaximum_attained d.g q
    refine ⟨⟨q,q,{j}⟩,rfl,rfl,by simp,?_⟩
    intro i hi t
    have hij : i = j := by simpa using hi
    subst i
    rw [← hj]
    exact (eshMaximum_le_iff d.g q _).mp le_rfl t
  | ecpAll =>
    exact ⟨⟨q,q,Finset.univ.filter (fun j => 0 < d.g j q)⟩,rfl,rfl,by simp⟩
  | esh a =>
    obtain ⟨t,ht,hrows,j,hj⟩ := esh_boundary_exists hcontinuous ha.2
      ⟨k,heps.trans_lt hk⟩
    let z := AffineMap.lineMap a q t
    let rows := Finset.univ.filter (fun i => d.g i z = 0)
    refine ⟨⟨q,z,rows⟩,rfl,t,ht,rfl,hrows,?_,?_⟩
    · exact ⟨j,by simp [rows,z,hj]⟩
    · intro i; simp [rows]

theorem cp_step_total (d : ModelData n m l r) (mode : CPMode n m)
    {eps : ℝ} (heps : 0 ≤ eps) (hbase : IsCompact (cpBase d))
    (hcontinuous : ∀ j, Continuous (d.g j)) (ha : CPInterior d mode)
    (H : List (CPBatch n m l)) :
    (∃ out, CPStop d eps H out) ∨ ∃ b, CPStep d mode eps H b := by
  classical
  rcases cp_master_reply d H hbase with hempty | ⟨q,hmin⟩
  · exact Or.inl ⟨.infeasible,.empty hempty⟩
  · by_cases hpass : CPFeasibleWithin d eps q
    · exact Or.inl ⟨.point q,.point q hmin hpass⟩
    · obtain ⟨b,hb,hvalid⟩ := cp_policy_reply_exists d mode hcontinuous ha heps q hpass
      exact Or.inr ⟨b,by simpa only [hb] using hmin,by simpa only [hb] using hpass,hvalid⟩

theorem cp_nonterminal_successor (d : ModelData n m l r) (mode : CPMode n m)
    {eps : ℝ} (heps : 0 ≤ eps) (hbase : IsCompact (cpBase d))
    (hcontinuous : ∀ j, Continuous (d.g j)) (ha : CPInterior d mode)
    (H : List (CPBatch n m l)) (hnone : ¬ ∃ out, CPStop d eps H out) :
    ∃ K, CPContinue d mode eps H K := by
  obtain h | ⟨b,h⟩ := cp_step_total d mode heps hbase hcontinuous ha H
  · exact (hnone h).elim
  · exact ⟨H ++ [b],b,rfl,h⟩

theorem cp_stop_sound (d : ModelData n m l r)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) {eps : ℝ}
    {H : List (CPBatch n m l)} {out : CPResult n m}
    (hstop : CPStop d eps H out) : CPReturnCertificate d eps out := by
  cases hstop with
  | empty h =>
    exact Set.eq_empty_of_subset_empty (h ▸ cp_master_contains_feasible d H hconv hdiff)
  | point q hmin htol =>
    exact ⟨((cp_master_mem_iff d H q).mp hmin.1).1,htol,
      cp_master_lowerBound d H hconv hdiff hmin⟩

theorem cp_zero_certificate_optimal (d : ModelData n m l r) {q : Point n m}
    (h : CPReturnCertificate d 0 (.point q)) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective q := by
  refine ⟨?_,h.2.2⟩
  exact ⟨⟨⟨Set.mem_univ _,h.2.1⟩,h.1.1⟩,h.1.2⟩

theorem cp_feasible_certificate_optimal (d : ModelData n m l r) {eps : ℝ}
    {q : Point n m} (h : CPReturnCertificate d eps (.point q))
    (hfeas : q ∈ d.feasibleOn Set.univ) :
    IsMinimizer (d.feasibleOn Set.univ) d.objective q := ⟨hfeas,h.2.2⟩

theorem cp_empty_base_stop (d : ModelData n m l r) (eps : ℝ)
    (H : List (CPBatch n m l)) (h : cpBase d = ∅) : CPStop d eps H .infeasible := by
  apply CPStop.empty
  apply Set.eq_empty_of_subset_empty
  intro q hq
  have := ((cp_master_mem_iff d H q).mp hq).1
  simp only [h, Set.mem_empty_iff_false] at this

theorem cp_zero_rows_pass (d : ModelData n m 0 r) (eps : ℝ) (q : Point n m) :
    CPFeasibleWithin d eps q := by intro j; exact Fin.elim0 j

#print axioms cp_history_cutRegion_iff
#print axioms cp_master_mem_iff
#print axioms cp_master_nil
#print axioms cp_master_append
#print axioms cp_master_antitone
#print axioms cp_master_contains_feasible
#print axioms cp_master_compact
#print axioms cp_master_reply
#print axioms cp_master_lowerBound
#print axioms cp_master_values_monotone
#print axioms cp_failed_test_row
#print axioms cp_ecp_selected_violation
#print axioms cp_batch_origin_linearRegion
#print axioms cp_policy_reply_exists
#print axioms cp_step_total
#print axioms cp_nonterminal_successor
#print axioms cp_stop_sound
#print axioms cp_zero_certificate_optimal
#print axioms cp_feasible_certificate_optimal
#print axioms cp_empty_base_stop
#print axioms cp_zero_rows_pass
end Chapter02
