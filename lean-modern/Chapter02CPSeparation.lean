module

public import Chapter02CPHistory
public import Chapter02ECPAnalysis
public import Chapter02ESHAnalysis

@[expose] public section

/-! Separation is derived for the literal source batch policies, at every
positive threshold. It is not assumed as an oracle or a progress field. -/
noncomputable section
namespace Chapter02
variable {n m l r : ℕ}

theorem cp_policy_uniform_separation (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {theta : ℝ} (htheta : 0 < theta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ b : CPBatch n m l,
      CPBatchValid d mode b → b.trial ∈ cpBase d →
      (∃ j, theta < d.g j b.trial) →
      ∀ w, cpBatchCuts d b w → delta ≤ dist b.trial w := by
  have hecp (mode : CPMode n m)
      (hmode : mode = .ecpMost ∨ mode = .ecpAll) :
      ∃ delta : ℝ, 0 < delta ∧ ∀ b : CPBatch n m l,
        CPBatchValid d mode b → b.trial ∈ cpBase d →
        (∃ j, theta < d.g j b.trial) →
        ∀ w, cpBatchCuts d b w → delta ≤ dist b.trial w := by
    obtain ⟨delta,hd,hsep⟩ := ecp_uniform_separation hbase hC1 htheta
    refine ⟨delta,hd,?_⟩
    intro b hv hb hbad w hw
    have hf : ¬ CPFeasibleWithin d theta b.trial := by
      intro hpass
      obtain ⟨j,hj⟩ := hbad
      exact (not_lt_of_ge (hpass j)) hj
    have hpolicy : CPBatchValid d .ecpMost b ∨ CPBatchValid d .ecpAll b := by
      rcases hmode with h | h
      · exact Or.inl (h ▸ hv)
      · exact Or.inr (h ▸ hv)
    obtain ⟨horg,j,hj,hviol⟩ := cp_ecp_selected_violation d htheta.le hf hpolicy
    exact hsep b.trial hb w j hviol (by simpa only [horg] using hw j hj)
  cases mode with
  | ecpMost => exact hecp .ecpMost (Or.inl rfl)
  | ecpAll => exact hecp .ecpAll (Or.inr rfl)
  | esh a =>
    obtain ⟨delta,hd,hsep⟩ := esh_uniform_separation hbase hconv hC1 ha.2 htheta
    refine ⟨delta,hd,?_⟩
    intro b hv hb hbad w hw
    obtain ⟨t,ht,horg,hrows,hne,hactive⟩ := hv
    obtain ⟨j,hj⟩ := hne
    apply hsep b.trial hb (by obtain ⟨k,hk⟩ := hbad; exact ⟨k,hk.le⟩)
      t ⟨ht.1.le,ht.2.le⟩
    · simpa only [← horg] using hrows
    · simpa only [← horg] using (hactive j).mp hj
    · simpa only [← horg] using hw j hj

theorem cp_step_excludes_trial (d : ModelData n m l r) (mode : CPMode n m)
    (hbase : IsCompact (cpBase d))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hC1 : ∀ j, ContDiff ℝ 1 (d.g j)) (ha : CPInterior d mode)
    {eps : ℝ} (heps : 0 ≤ eps) {H : List (CPBatch n m l)}
    {b : CPBatch n m l} (hstep : CPStep d mode eps H b) :
    b.trial ∉ cpMaster d (H ++ [b]) := by
  obtain ⟨j,hj⟩ := cp_failed_test_row d hstep.2.1
  have hpos : 0 < d.g j b.trial := heps.trans_lt hj
  obtain ⟨delta,hd,hsep⟩ := cp_policy_uniform_separation d mode hbase hconv hC1 ha
    (half_pos hpos)
  intro hmem
  have hold := (cp_master_mem_iff d H b.trial).mp hstep.1.1
  have hcut := ((cp_master_mem_iff d (H ++ [b]) b.trial).mp hmem).2 b (by simp)
  have hh := hsep b hstep.2.2 hold.1 ⟨j,half_lt_self hpos⟩ b.trial hcut
  exact (not_le_of_gt hd) (by simpa using hh)

#print axioms cp_policy_uniform_separation
#print axioms cp_step_excludes_trial
end Chapter02
