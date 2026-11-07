module

public import Chapter03OAKKTSource

@[expose] public section

/-! Two KKT-conditional source ingredients, not full OA execution or LICQ
existence. The master is the hard epigraph master, not penalized rMIP. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter03.OAKKT

variable {n m l r k : ℕ} {d : ModelData n m l r} {f : Point n m → ℝ}
  {N : Set (Fin l)} {c : TangentFamily n m l k}
  {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {y : RealVector m}

theorem History.current_g_derivative_eq (H : History d f N c df x y)
    (D : Fin l → Point n m →L[ℝ] ℝ)
    (hD : ∀ j, HasFDerivAt (d.g j) (D j) (x,y)) (j : Fin l) :
    c.derivative H.current j = D j := by
  have hh := H.g_derivative H.current j
  rw [H.current_origin] at hh
  exact hh.unique (hD j)

theorem History.current_f_derivative_eq (H : History d f N c df x y)
    (D : Point n m →L[ℝ] ℝ) (hD : HasFDerivAt f D (x,y)) :
    df H.current = D := by
  have hh := H.f_derivative H.current
  rw [H.current_origin] at hh
  exact hh.unique hD

theorem History.affine_row_retained (H : History d f N c df x y)
    {q : Point n m} (hq : q ∈ d.masterOn c Set.univ)
    (j : Fin l) (hj : j ∉ N) : d.g j q ≤ 0 := by
  have hc := hq.1.1.2 H.seed j (by rw [H.initial_all]; trivial)
  rw [affine_tangent (H.affine j hj) (H.g_derivative H.seed j) q] at hc
  exact hc

theorem History.supported_tangent (H : History d f N c df x y)
    (D : Fin l → Point n m →L[ℝ] ℝ)
    (hD : ∀ j, HasFDerivAt (d.g j) (D j) (x,y))
    {q : Point n m} (hq : q ∈ d.masterOn c Set.univ)
    (j : Fin l) (hres : 0 ≤ d.g j (x,y)) :
    d.g j (x,y) + D j (q-(x,y)) ≤ 0 := by
  by_cases hj : j ∈ N
  · have hc := hq.1.1.2 H.current j (by rw [H.current_selected]; exact ⟨hj,hres⟩)
    rw [H.current_origin, H.current_g_derivative_eq D hD j] at hc
    exact hc
  · rw [affine_tangent (H.affine j hj) (hD j) q]
    exact H.affine_row_retained hq j hj

theorem History.objective_tangent (H : History d f N c df x y)
    (D : Point n m →L[ℝ] ℝ) (hD : HasFDerivAt f D (x,y))
    {z : Point n m × ℝ} (hz : z ∈ Chapter06.EpigraphMaster d f c df Set.univ) :
    f (x,y) + D (z.1-(x,y)) ≤ z.2 := by
  have hh := hz.2 H.current
  rw [H.current_origin,H.current_f_derivative_eq D hD] at hh
  exact hh

theorem FixedKKT.supported_residual (K : FixedKKT d f x y)
    (j : Fin l) (hj : K.lambda j ≠ 0) : d.g j (x,y) = 0 :=
  (mul_eq_zero.mp (K.soft_compl j)).resolve_left hj

/-- Qualified endpoint 1: actual source retained rows and KKT equations give
the fiber objective comparison. No master minimum or global convexity is used. -/
theorem fixed_kkt_master_lower (H : History d f N c df x y)
    (K : FixedKKT d f x y) {z : Point n m × ℝ}
    (hz : z ∈ Chapter06.EpigraphMaster d f c df Set.univ)
    (hy : z.1.2 = y) : f (x,y) ≤ z.2 := by
  have hpoint : z.1 = (z.1.1,y) := Prod.ext rfl hy
  have hcoord (D : RealVector n →L[ℝ] ℝ) (v : RealVector n) :
      (fun i => D (Pi.single i 1)) ⬝ᵥ v = D v :=
    (coneFunctional_coordinates D v).symm
  apply Chapter06.fixed_fiber_kkt_master_lower_bound (f (x,y)) z.2
    (fun i => restrict K.Df (Pi.single i 1)) (fun j => soft d y j x)
    (fun j i => restrict (K.Dg j) (Pi.single i 1))
    (fun i => hard d y i x) (fun i a => fiberLinearRow d i (Pi.single a 1))
    K.lambda K.mu (z.1.1-x) K.lambda_nonneg K.mu_nonneg
    K.soft_compl K.hard_compl
  · intro i
    have hh := congrArg (fun D : RealVector n →L[ℝ] ℝ => D (Pi.single i 1)) K.stationarity
    simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.zero_apply] using hh
  · intro j hj
    rw [hcoord]
    have hh := H.supported_tangent K.Dg K.derivative_g hz.1 j
      (le_of_eq (K.supported_residual j hj).symm)
    rw [hpoint,derivative_fiber_action] at hh
    exact hh
  · intro i
    rw [hcoord,hard_tangent]
    have hh := hz.1.1.2 i
    rw [hpoint] at hh
    exact sub_nonpos.mpr hh
  · rw [hcoord]
    have hh := H.objective_tangent K.Df K.derivative_f hz
    rw [hpoint,derivative_fiber_action] at hh
    exact hh

theorem fixed_solution_master_lower (H : History d f N c df x y)
    (_hmin : IsMinimizer (fiber d y) (fiberObjective f y) x)
    (K : FixedKKT d f x y) {z : Point n m × ℝ}
    (hz : z ∈ Chapter06.EpigraphMaster d f c df Set.univ)
    (hy : z.1.2 = y) : f (x,y) ≤ z.2 :=
  fixed_kkt_master_lower H K hz hy

/-- Additional rows only restrict the master. This transfers a consequence,
not the validity of no-good cuts or any other additional restriction. -/
theorem fixed_kkt_restricted_lower (H : History d f N c df x y)
    (K : FixedKKT d f x y) (R : Set (Point n m × ℝ))
    (hR : R ⊆ Chapter06.EpigraphMaster d f c df Set.univ)
    {z : Point n m × ℝ} (hz : z ∈ R) (hy : z.1.2 = y) : f (x,y) ≤ z.2 :=
  fixed_kkt_master_lower H K (hR hz) hy

variable {s : RealVector l}

theorem SumKKT.slack_nonneg (K : SumKKT d x y s) (j : Fin l) : 0 ≤ s j :=
  ((restSet_insert_iff d y x s).mp K.primal).2.2 j

theorem SumKKT.soft_le_slack (K : SumKKT d x y s) (j : Fin l) :
    soft d y j x ≤ s j :=
  ((restSet_insert_iff d y x s).mp K.primal).2.1 j

theorem SumKKT.lambda_le_one (K : SumKKT d x y s) (j : Fin l) :
    K.lambda j ≤ 1 := by linarith [K.nu_nonneg j,K.slack_stationarity j]

theorem SumKKT.slacks_tight (K : SumKKT d x y s) (j : Fin l) :
    s j = max (soft d y j x) 0 := by
  by_cases hs : s j = 0
  · rw [hs]
    exact (max_eq_right (by simpa [hs] using K.soft_le_slack j)).symm
  · have hn : K.nu j = 0 := (mul_eq_zero.mp (K.slack_compl j)).resolve_right hs
    have hl : K.lambda j = 1 := by linarith [K.slack_stationarity j]
    have hv : soft d y j x = s j := by
      have hh := K.soft_compl j
      rw [hl,one_mul] at hh
      exact sub_eq_zero.mp hh
    rw [hv,max_eq_left (K.slack_nonneg j)]

theorem SumKKT.soft_value (K : SumKKT d x y s) (j : Fin l) :
    K.lambda j * soft d y j x = s j := by
  have hh := congrArg (fun a : ℝ => a*s j) (K.slack_stationarity j)
  nlinarith [K.soft_compl j,K.slack_compl j]

theorem SumKKT.total_value (K : SumKKT d x y s) :
    (∑ j, K.lambda j * soft d y j x) = ∑ j, s j := by
  simp only [K.soft_value]

theorem SumKKT.supported_residual (K : SumKKT d x y s)
    (j : Fin l) (hj : K.lambda j ≠ 0) : 0 ≤ d.g j (x,y) := by
  have hh := (mul_eq_zero.mp (K.soft_compl j)).resolve_left hj
  have he := sub_eq_zero.mp hh
  change 0 ≤ soft d y j x
  rw [he]
  exact K.slack_nonneg j

def SumKKT.toWeighted (K : SumKKT d x y s) :
    WeightedHardKKT Set.univ (hard d y) (soft d y) (fun _ => 1) x
      (fiberLinearRow d) (fun j => restrict (K.Dg j)) K.mu K.lambda 0 where
  mem := ⟨Set.mem_univ _,((restSet_insert_iff d y x s).mp K.primal).1⟩
  hard_nonneg := K.mu_nonneg
  soft_nonneg := K.lambda_nonneg
  soft_le_weight := K.lambda_le_one
  hard_compl := K.hard_compl
  soft_compl := by intro j; rw [← K.slacks_tight]; exact K.soft_compl j
  slack_compl := by
    intro j
    rw [← K.slacks_tight]
    have hh := K.slack_stationarity j
    have he : 1-K.lambda j = K.nu j := by linarith
    rw [he]
    exact K.slack_compl j
  normal_le := by simp
  stationarity := by simpa only [add_zero,zero_add,add_comm] using K.stationarity

theorem SumKKT.positive_value_eq (K : SumKKT d x y s) :
    weightedPositive (fun _ : Fin l => 1) (soft d y) x = ∑ j, s j := by
  simp only [weightedPositive,one_mul,← K.slacks_tight]

/-- Qualified endpoint 2: positive total separate slack, actual KKT equations,
and the literal retained row policy exclude this entire fixed fiber. -/
theorem sum_kkt_master_exclusion (H : History d f N c df x y)
    (K : SumKKT d x y s) (hpos : 0 < ∑ j, s j) :
    ¬ ∃ z ∈ Chapter06.EpigraphMaster d f c df Set.univ, z.1.2 = y := by
  rintro ⟨z,hz,hy⟩
  have hpoint : z.1 = (z.1.1,y) := Prod.ext rfl hy
  have hlo := weighted_hard_tangent_lower K.toWeighted (Set.mem_univ z.1.1)
  rw [K.positive_value_eq] at hlo
  have hhard : (∑ i, K.mu i *
      (hard d y i x + fiberLinearRow d i (z.1.1-x))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply mul_nonpos_of_nonneg_of_nonpos (K.mu_nonneg i)
    rw [hard_tangent]
    have hh := hz.1.1.2 i
    rw [hpoint] at hh
    exact sub_nonpos.mpr hh
  have hsoft : (∑ j, K.lambda j *
      (soft d y j x + restrict (K.Dg j) (z.1.1-x))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : K.lambda j = 0
    · simp [hj]
    · apply mul_nonpos_of_nonneg_of_nonpos (K.lambda_nonneg j)
      have hh := H.supported_tangent K.Dg K.derivative_g hz.1 j
        (K.supported_residual j hj)
      rw [hpoint,derivative_fiber_action] at hh
      exact hh
  linarith

theorem sum_kkt_restricted_exclusion (H : History d f N c df x y)
    (K : SumKKT d x y s) (hpos : 0 < ∑ j, s j)
    (R : Set (Point n m × ℝ))
    (hR : R ⊆ Chapter06.EpigraphMaster d f c df Set.univ) :
    ¬ ∃ z ∈ R, z.1.2 = y := by
  rintro ⟨z,hz,hy⟩
  exact sum_kkt_master_exclusion H K hpos ⟨z,hR hz,hy⟩

theorem rest_minimizer_iff (d : ModelData n m l r) (y : RealVector m)
    (x : RealVector n) (s : RealVector l) :
    IsMinimizer (restSet d y) restCost (weightedInsert x s) ↔
      IsMinimizer (weightedHardRegion Set.univ (hard d y))
        (weightedPositive (fun _ : Fin l => 1) (soft d y)) x ∧
      ∀ j, s j = max (soft d y j x) 0 := by
  simpa only [restSet,restCost,weightedX_insert,weightedV_insert] using
    weighted_lift_minimizer_iff Set.univ (hard d y) (soft d y)
      (fun _ : Fin l => 1) (by intro j; norm_num) (weightedInsert x s)

theorem rest_primal_zero_feasible (d : ModelData n m l r) (y : RealVector m)
    (x : RealVector n) (s : RealVector l)
    (hp : weightedInsert x s ∈ restSet d y) (hs : (∑ j, s j) = 0) :
    x ∈ fiber d y := by
  obtain ⟨hh,hg,hn⟩ := (restSet_insert_iff d y x s).mp hp
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hs
  apply (fiber_iff d y x).mpr
  exact ⟨hh,fun j => by simpa [hzero j (Finset.mem_univ j)] using hg j⟩

theorem rest_minimum_nonneg (d : ModelData n m l r) (y : RealVector m)
    (x : RealVector n) (s : RealVector l)
    (hm : IsMinimizer (restSet d y) restCost (weightedInsert x s)) :
    0 ≤ ∑ j, s j :=
  Finset.sum_nonneg fun j _ => ((restSet_insert_iff d y x s).mp hm.1).2.2 j

theorem rest_minimum_positive_iff_empty (d : ModelData n m l r) (y : RealVector m)
    (x : RealVector n) (s : RealVector l)
    (hm : IsMinimizer (restSet d y) restCost (weightedInsert x s)) :
    0 < (∑ j, s j) ↔ ¬ (fiber d y).Nonempty := by
  obtain ⟨hmin,ht⟩ := (rest_minimizer_iff d y x s).mp hm
  have hv : weightedPositive (fun _ : Fin l => 1) (soft d y) x = ∑ j, s j := by
    simp only [weightedPositive,one_mul,← ht]
  have hh := weighted_hard_value_pos_iff_empty Set.univ (hard d y) (soft d y)
    (fun _ : Fin l => 1) (by intro j; norm_num) hmin
  rw [hv] at hh
  have he : (∃ a ∈ weightedHardRegion Set.univ (hard d y), ∀ j, soft d y j a ≤ 0) ↔
      (fiber d y).Nonempty := by
    constructor
    · rintro ⟨a,ha,hg⟩
      exact ⟨a,(fiber_iff d y a).mpr ⟨ha.2,hg⟩⟩
    · rintro ⟨a,ha⟩
      obtain ⟨hh,hg⟩ := (fiber_iff d y a).mp ha
      exact ⟨a,⟨Set.mem_univ _,hh⟩,hg⟩
  rw [he] at hh
  exact hh

theorem rest_minimum_zero_iff_nonempty (d : ModelData n m l r) (y : RealVector m)
    (x : RealVector n) (s : RealVector l)
    (hm : IsMinimizer (restSet d y) restCost (weightedInsert x s)) :
    (∑ j, s j) = 0 ↔ (fiber d y).Nonempty := by
  constructor
  · intro hz
    exact ⟨x,rest_primal_zero_feasible d y x s hm.1 hz⟩
  · intro hne
    have hn := rest_minimum_nonneg d y x s hm
    have hnp : ¬ 0 < ∑ j, s j := by
      intro hp
      exact (rest_minimum_positive_iff_empty d y x s hm).mp hp hne
    linarith

/-- Actual source infeasible branch: the attained minimum and empty fiber
derive positive slack. Attainment is supplied, never inferred from A3. -/
theorem infeasible_restoration_master_exclusion (H : History d f N c df x y)
    (hempty : ¬ (fiber d y).Nonempty)
    (hmin : IsMinimizer (restSet d y) restCost (weightedInsert x s))
    (K : SumKKT d x y s) :
    ¬ ∃ z ∈ Chapter06.EpigraphMaster d f c df Set.univ, z.1.2 = y :=
  sum_kkt_master_exclusion H K
    ((rest_minimum_positive_iff_empty d y x s hmin).mpr hempty)

theorem infeasible_restoration_restricted_exclusion (H : History d f N c df x y)
    (hempty : ¬ (fiber d y).Nonempty)
    (hmin : IsMinimizer (restSet d y) restCost (weightedInsert x s))
    (K : SumKKT d x y s) (R : Set (Point n m × ℝ))
    (hR : R ⊆ Chapter06.EpigraphMaster d f c df Set.univ) :
    ¬ ∃ z ∈ R, z.1.2 = y := by
  rintro ⟨z,hz,hy⟩
  exact infeasible_restoration_master_exclusion H hempty hmin K ⟨z,hR hz,hy⟩

end Chapter03.OAKKT

#print axioms Chapter03.OAKKT.fixed_kkt_master_lower
#print axioms Chapter03.OAKKT.sum_kkt_master_exclusion
