module

public import Chapter04TrialHistory

@[expose] public section

/-! Subsequent exact-master availability before an optimal polish.
The seed is empty and the processed history is nonempty. A retained nonzero
normal, an upper radius bound and an actual radius-zero competitor are derived.
The radius remains unrestricted in the master; a compact nonnegative slice is
only a proof device. This is existence, not exactness of a selected trial or a
solver policy. It supplies no empty-initial or post-discovery master guarantee.
Infeasible events retain Algorithm 2.b strict violations, as in the accepted
history definition; the broader printed active-and-violated rule is not added. -/

noncomputable section
open Chapter02
namespace Chapter04.CenterCut

/-- Historical anchors and normals are constants: each selected ball row is
continuous in the new center/radius, even when its normal is zero. -/
theorem eventRows_isClosed {n m l k : ℕ} (d : ModelData n m l k)
    (e : TrialEvent n m) :
    IsClosed {w : Point n m × ℝ | eventRows d e w.1 w.2} := by
  cases hp : e.polished with
  | none =>
      have heq : {w : Point n m × ℝ | eventRows d e w.1 w.2} =
          ⋂ j, ⋂ (_ : 0 < d.g j e.trial),
            {w : Point n m × ℝ |
              d.g j e.trial + inner ℝ (euclideanGradient (d.g j) e.trial)
                (coordinates n m w.1 - coordinates n m e.trial) +
                w.2 * ‖euclideanGradient (d.g j) e.trial‖ ≤ 0} := by
        ext w
        simp [eventRows, hp]
      rw [heq]
      refine isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
      exact (continuous_const.add (continuous_const.inner
        (((coordinates n m).continuous.comp continuous_fst).sub continuous_const))).add
        (continuous_snd.mul continuous_const)
  | some p =>
      have heq : {w : Point n m × ℝ | eventRows d e w.1 w.2} =
          (⋂ j, ⋂ (_ : d.g j p = 0),
            {w : Point n m × ℝ |
              d.g j p + inner ℝ (euclideanGradient (d.g j) p)
                (coordinates n m w.1 - coordinates n m p) +
                w.2 * ‖euclideanGradient (d.g j) p‖ ≤ 0}) ∩
          {w : Point n m × ℝ |
            d.objective w.1 + w.2 * ‖coordinates n m (d.c1, d.c2)‖ ≤ d.objective p} := by
        ext w
        simp [eventRows, hp]
      rw [heq]
      apply IsClosed.inter
      · refine isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
        exact (continuous_const.add (continuous_const.inner
          (((coordinates n m).continuous.comp continuous_fst).sub continuous_const))).add
          (continuous_snd.mul continuous_const)
      · exact isClosed_le (((linearForm_continuous d.c1 d.c2).comp continuous_fst).add
          (continuous_snd.mul continuous_const)) continuous_const

/-- Every nonempty valid empty-seed history before optimal discovery has an
exact free-radius master. No Slater, nonzero-objective, radius bound or prior
master-existence hypothesis is assumed. Post-discovery and initial empty
masters are outside this conclusion. The direct universal-polish premise is
the negation of an actually stored global optimizer, without importing the
finite-discovery theorem. -/
theorem source_master_attained_before_optimal_polish {n m l k : ℕ}
    (d : ModelData n m l k)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hfeas : (d.feasibleOn Set.univ).Nonempty)
    (H : List (TrialEvent n m)) (hne : H ≠ [])
    (hvalid : ∀ e ∈ H, eventValid d e)
    (hbefore : ∀ e ∈ H, ∀ p, e.polished = some p →
      ¬ IsMinimizer (d.feasibleOn Set.univ) d.objective p) :
    ∃ w : Point n m × ℝ, ExactRadiusMax (sourceMaster d [] H) w := by
  obtain ⟨pStar, hmin⟩ := source_minimum_attained d hcompact
    (fun j => (hdiff j).continuous) hfeas
  have hzero : (pStar, 0) ∈ sourceMaster d [] H := by
    apply optimizer_mem_sourceMaster d hconv hdiff [] _ H hvalid pStar hmin
    intro p hp row hrow
    simp at hrow
  have hrow : ∃ a : EuclideanPoint n m, ∃ b : ℝ, a ≠ 0 ∧
      ∀ w ∈ sourceMaster d [] H,
        inner ℝ a (coordinates n m w.1) + w.2 * ‖a‖ ≤ b := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil H hne
    have hv := hvalid e he
    cases hp : e.polished with
    | none =>
        have hinfeas : ¬ e.trial ∈ d.nonlinearRegion := by
          simpa only [hp] using hv.2
        change ¬ (∀ j, d.g j e.trial ≤ 0) at hinfeas
        push_neg at hinfeas
        obtain ⟨j, hj⟩ := hinfeas
        have hstar := ((source_feasible_iff d Set.univ pStar).mp hmin.1).2.1 j
        have ha := euclideanGradient_ne_zero_of_violation (hconv j)
          (hdiff j e.trial) hj hstar
        refine ⟨euclideanGradient (d.g j) e.trial,
          inner ℝ (euclideanGradient (d.g j) e.trial) (coordinates n m e.trial) -
            d.g j e.trial, ha, ?_⟩
        intro w hw
        have hrows := hw.2.2 e he
        simp only [eventRows, hp] at hrows
        have h := hrows j hj
        rw [inner_sub_right] at h
        linarith
    | some p =>
        have hpf := event_polished_feasible d e hv p hp
        have hc : coordinates n m (d.c1, d.c2) ≠ 0 := by
          intro hc
          apply hbefore e he p hp
          refine ⟨hpf, ?_⟩
          intro q hq
          simp only [objective_eq_inner_coordinates, hc, inner_zero_left, le_refl]
        refine ⟨coordinates n m (d.c1, d.c2), d.objective p, hc, ?_⟩
        intro w hw
        have hrows := hw.2.2 e he
        simp only [eventRows, hp] at hrows
        rw [← objective_eq_inner_coordinates]
        exact hrows.2
  obtain ⟨a, b, ha, hrow⟩ := hrow
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hcont : Continuous (fun q : Point n m =>
      (b - inner ℝ a (coordinates n m q)) / ‖a‖) :=
    (continuous_const.sub (continuous_const.inner (coordinates n m).continuous)).div_const _
  obtain ⟨U, hU⟩ := hcompact.bddAbove_image hcont.continuousOn
  have hbound : ∀ w ∈ sourceMaster d [] H, w.2 ≤ max U 0 := by
    intro w hw
    have h := hrow w hw
    have hdiv : w.2 ≤ (b - inner ℝ a (coordinates n m w.1)) / ‖a‖ := by
      apply (le_div_iff₀ hanorm).mpr
      linarith
    exact hdiv.trans ((hU ⟨w.1, hw.1, rfl⟩).trans (le_max_left _ _))
  have hclosedRows : IsClosed {w : Point n m × ℝ | ∀ e ∈ H, eventRows d e w.1 w.2} := by
    have heq : {w : Point n m × ℝ | ∀ e ∈ H, eventRows d e w.1 w.2} =
        ⋂ e, ⋂ (_ : e ∈ H), {w : Point n m × ℝ | eventRows d e w.1 w.2} := by
      ext w
      simp
    rw [heq]
    exact isClosed_iInter fun e => isClosed_iInter fun _ => eventRows_isClosed d e
  have hclosed : IsClosed (sourceMaster d [] H) := by
    have heq : sourceMaster d [] H =
        {w : Point n m × ℝ | w.1 ∈ d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi} ∩
        {w : Point n m × ℝ | ∀ e ∈ H, eventRows d e w.1 w.2} := by
      ext w
      simp [sourceMaster]
    rw [heq]
    exact (hcompact.isClosed.preimage continuous_fst).inter hclosedRows
  let S := sourceMaster d [] H ∩
    ((d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) ×ˢ Set.Icc 0 (max U 0))
  have hS : IsCompact S :=
    (hcompact.prod isCompact_Icc).inter_left hclosed
  have hSne : S.Nonempty := ⟨(pStar, 0), hzero, hzero.1, le_rfl, le_max_right _ _⟩
  obtain ⟨w, hw, hmax⟩ := hS.exists_isMaxOn hSne continuous_snd.continuousOn
  refine ⟨w, hw.1, ?_⟩
  intro z hz
  by_cases hnonneg : 0 ≤ z.2
  · exact hmax ⟨hz, hz.1, hnonneg, hbound z hz⟩
  · exact (le_of_not_ge hnonneg).trans hw.2.2.1

end Chapter04.CenterCut
