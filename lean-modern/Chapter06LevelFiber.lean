module

public import Chapter06LevelModel

@[expose] public section

/-! Actual nonlinear-objective Slater/normal derivation and the literal
nonnegative common-slack problem. The original nonlinear objective never passes
through the linear-objective fixed-NLP adapter. That adapter is used transitively
only by the accepted lifted-slack restoration theorem. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter06.Level
variable {n m l r : ℕ}

structure FeasibleKKT (d : Data n m l r) (hr : Regularity d) (a : Point n m) where
  lambda : Fin l → ℝ
  mu : Fin r → ℝ
  lambda_nonneg : ∀ j, 0 ≤ lambda j
  mu_nonneg : ∀ i, 0 ≤ mu i
  soft_compl : ∀ j, lambda j * d.g j a = 0
  hard_compl : ∀ i, mu i * linearResidual (boxedModel d hr) i a = 0
  stationarity : restrict (fderiv ℝ d.f a) +
    (∑ j, lambda j • restrict (fderiv ℝ (d.g j) a)) +
    (∑ i, mu i • fiberLinearRow (boxedModel d hr) i) = 0

/-- Generic Slater is applied to the actual nonlinear restricted objective.
Every hard affine row remains in the polyhedral normal representation. -/
theorem feasibleKKT_exists (d : Data n m l r) (hr : Regularity d)
    (y : IntVector m) {a : Point n m}
    (ha : IsMinimizer (d.feasibleFiber y) d.f a) : Nonempty (FeasibleKKT d hr a) := by
  let md := boxedModel d hr
  have hay : a.2 = intCast y := ha.1.1.2
  have hmin : IsMinimizer
      {x ∈ fiberPolyhedron md a.2 | ∀ j, d.g j (x,a.2) ≤ 0}
      (fun x => d.f (x,a.2)) a.1 := by
    refine ⟨⟨(fiberPolyhedron_mem_iff md a.2 a.1).mpr ha.1.1.1,ha.1.2⟩,?_⟩
    intro x hx
    exact ha.2 (x,a.2) ⟨⟨(fiberPolyhedron_mem_iff md a.2 x).mp hx.1,hay⟩,hx.2⟩
  have hs : ∃ x ∈ fiberPolyhedron md a.2, ∀ j, d.g j (x,a.2) < 0 := by
    obtain ⟨p,hp,hg⟩ := hr.fiber_slater y ⟨a,ha.1⟩
    have hpy : p.2 = a.2 := hp.2.trans hay.symm
    have he : (p.1,a.2) = p := Prod.ext rfl hpy.symm
    refine ⟨p.1,(fiberPolyhedron_mem_iff md a.2 p.1).mpr ?_,?_⟩
    · change (p.1,a.2) ∈ d.hard
      simpa only [he] using hp.1
    · simpa only [he] using hg
  have hf : ConvexOn ℝ (fiberPolyhedron md a.2) (fun x => d.f (x,a.2)) := by
    refine ⟨fiberPolyhedron_convex md a.2,?_⟩
    intro x _ z _ s t hs ht hst
    dsimp only
    rw [fiber_mix x z a.2 s t hst]
    exact hr.objective_convex.2 (Set.mem_univ _) (Set.mem_univ _) hs ht hst
  obtain ⟨lambda,hl,hcomp,hpartial⟩ := convex_slater_partialLagrangian_minimum
    (fiberPolyhedron md a.2) (fun x => d.f (x,a.2))
    (fun j x => d.g j (x,a.2)) a.1 (fiberPolyhedron_convex md a.2)
    hf (fiberRows_convex md a.2 hr.constraint_convex) hmin hs
  have hdf : HasFDerivAt d.f (fderiv ℝ d.f a) a :=
    ((hr.objective_C1.differentiable (by norm_num)) a).hasFDerivAt
  have hdg : ∀ j, HasFDerivAt (d.g j) (fderiv ℝ (d.g j) a) a :=
    fun j => (((hr.constraint_C1 j).differentiable (by norm_num)) a).hasFDerivAt
  have hd : HasFDerivAt (fun x => d.f (x,a.2) + ∑ j, lambda j * d.g j (x,a.2))
      (restrict (fderiv ℝ d.f a) + ∑ j, lambda j • restrict (fderiv ℝ (d.g j) a)) a.1 :=
    (fiber_derivative hdf).fun_add
      (HasFDerivAt.fun_sum fun j _ => (fiber_derivative (hdg j)).const_mul (lambda j))
  obtain ⟨mu,hm,hmc,hstation⟩ := polyhedral_minimum_multipliers
    (fiberLinearRow md) (fiberLinearBound md a.2) hpartial hd
  refine ⟨⟨lambda,mu,hl,hm,hcomp,?_,hstation⟩⟩
  intro i
  simpa only [fiberLinearResidual_eq] using hmc i

/-- The actual feasible minimum and its selected active rows give a same-fiber
lower bound on the actual objective tangent, without supplied multipliers. -/
theorem feasible_selected_lower (d : Data n m l r) (hr : Regularity d)
    (y : IntVector m) {a q : Point n m}
    (ha : IsMinimizer (d.feasibleFiber y) d.f a)
    (hq : q ∈ d.hardFiber y) (hrows : selectedRows d a 0 q) :
    d.f a ≤ tangent d.f a q := by
  obtain ⟨K⟩ := feasibleKKT_exists d hr y ha
  have hqa : q.2 = a.2 := hq.2.trans ha.1.1.2.symm
  have heq : q = (q.1,a.2) := Prod.ext rfl hqa
  have hcoord (D : RealVector n →L[ℝ] ℝ) (v : RealVector n) :
      (fun i => D (Pi.single i 1)) ⬝ᵥ v = D v :=
    (coneFunctional_coordinates D v).symm
  apply Chapter06.fixed_fiber_kkt_master_lower_bound (d.f a) (tangent d.f a q)
    (fun i => restrict (fderiv ℝ d.f a) (Pi.single i 1)) (fun j => d.g j a)
    (fun j i => restrict (fderiv ℝ (d.g j) a) (Pi.single i 1))
    (fun i => hard (boxedModel d hr) a.2 i a.1)
    (fun i v => fiberLinearRow (boxedModel d hr) i (Pi.single v 1))
    K.lambda K.mu (q.1-a.1) K.lambda_nonneg K.mu_nonneg K.soft_compl K.hard_compl
  · intro i
    have hh := congrArg (fun D : RealVector n →L[ℝ] ℝ => D (Pi.single i 1)) K.stationarity
    simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.zero_apply] using hh
  · intro j hj
    rw [hcoord]
    have hh := hrows j ((mul_eq_zero.mp (K.soft_compl j)).resolve_left hj)
    unfold tangent at hh
    rw [heq,derivative_fiber_action] at hh
    exact hh
  · intro i
    rw [hcoord,hard_tangent]
    have hh := hq.1 i
    rw [heq] at hh
    exact sub_nonpos.mpr hh
  · rw [hcoord]
    unfold tangent
    rw [heq,derivative_fiber_action]

/-- An infeasible nonempty hard fiber itself forces at least one soft row. -/
theorem infeasible_has_row (d : Data n m l r) (y : IntVector m)
    (hne : (d.hardFiber y).Nonempty) (hi : ¬ (d.feasibleFiber y).Nonempty) :
    Nonempty (Fin l) := by
  by_contra hn
  have hempty : IsEmpty (Fin l) := not_nonempty_iff.mp hn
  obtain ⟨p,hp⟩ := hne
  exact hi ⟨p,hp,fun j => (hempty.false j).elim⟩

theorem free_restoration_positive (d : Data n m l r) (y : IntVector m)
    (hi : ¬ (d.feasibleFiber y).Nonempty) {z : Point n m × ℝ}
    (hz : z ∈ RestorationPairs (d.hardFiber y) d.g) : 0 < z.2 := by
  by_contra hn
  exact hi ⟨z.1,hz.1,fun j => (hz.2 j).trans (le_of_not_gt hn)⟩

theorem restoration_eq_free_of_infeasible (d : Data n m l r) (y : IntVector m)
    (hi : ¬ (d.feasibleFiber y).Nonempty) :
    d.restoration y = RestorationPairs (d.hardFiber y) d.g := by
  ext z
  constructor
  · exact fun hz => ⟨hz.1,hz.2.1⟩
  · exact fun hz => ⟨hz.1,hz.2,(free_restoration_positive d y hi hz).le⟩

theorem restoration_minimizer_iff_free (d : Data n m l r) (y : IntVector m)
    (hi : ¬ (d.feasibleFiber y).Nonempty) (z : Point n m × ℝ) :
    IsMinimizer (d.restoration y) Prod.snd z ↔
      IsMinimizer (RestorationPairs (d.hardFiber y) d.g) Prod.snd z := by
  rw [restoration_eq_free_of_infeasible d y hi]

theorem infeasible_restoration_positive (d : Data n m l r) (y : IntVector m)
    (hi : ¬ (d.feasibleFiber y).Nonempty) {a : Point n m} {rho : ℝ}
    (ha : IsMinimizer (d.restoration y) Prod.snd (a,rho)) : 0 < rho :=
  free_restoration_positive d y hi ⟨ha.1.1,ha.1.2.1⟩

/-- Literal nonnegative restoration always attains on a nonempty hard fiber,
including an empty soft family. -/
theorem restoration_attained (d : Data n m l r) (hr : Regularity d)
    (y : IntVector m) (hne : (d.hardFiber y).Nonempty) :
    ∃ a rho, IsMinimizer (d.restoration y) Prod.snd (a,rho) := by
  by_cases hf : (d.feasibleFiber y).Nonempty
  · obtain ⟨p,hp⟩ := hf
    exact ⟨p,0,⟨hp.1,hp.2,le_rfl⟩,fun z hz => hz.2.2⟩
  · letI := infeasible_has_row d y hne hf
    obtain ⟨z,hz⟩ := restorationPairs_minimum_attained (hardFiber_compact d hr y) hne
      (fun j => (hr.constraint_C1 j).continuous)
    exact ⟨z.1,z.2,(restoration_minimizer_iff_free d y hf z).mpr hz⟩

theorem zero_rows_restoration_minimum (d : Data n m 0 r) (y : IntVector m)
    {a : Point n m} (ha : a ∈ d.hardFiber y) :
    IsMinimizer (d.restoration y) Prod.snd (a,0) :=
  ⟨⟨ha,fun j => Fin.elim0 j,le_rfl⟩,fun _ hz => hz.2.2⟩

theorem zero_rows_free_unbounded (d : Data n m 0 r) (y : IntVector m)
    (hne : (d.hardFiber y).Nonempty) :
    ∀ v : ℝ, ∃ z ∈ RestorationPairs (d.hardFiber y) d.g, z.2 < v :=
  restorationPairs_unbounded_empty_rows d.g hne

/-- The permitted lifted auxiliary objective is exactly the common slack and
is independent of both original linear-objective adapter coefficients. -/
theorem restoration_objective_exact (d : Data n m l r) (hr : Regularity d)
    (p : Point (n+1) m) : (boxedModel d hr).restorationModel.objective p = epiHeight p :=
  restorationModel_objective _ _

theorem restoration_independent_objective (md : ModelData n m l r)
    (c1 : RealVector n) (c2 : RealVector m) :
    ({md with c1 := c1, c2 := c2}).restorationModel = md.restorationModel := rfl

/-- The same actual all-row derivative family occurs in the derived restoration
KKT and the selected rows. Selection is by g_j(a)=rho, not by g_j(a)=0. -/
theorem restoration_selected_excludes (d : Data n m l r) (hr : Regularity d)
    (y : IntVector m) {a q : Point n m} {rho : ℝ}
    (hi : ¬ (d.feasibleFiber y).Nonempty)
    (ha : IsMinimizer (d.restoration y) Prod.snd (a,rho))
    (hq : q ∈ d.hardFiber y) (hrows : selectedRows d a rho q) : False := by
  letI := infeasible_has_row d y ⟨a,ha.1.1⟩ hi
  have hay : a.2 = intCast y := ha.1.1.2
  have hfree := (restoration_minimizer_iff_free d y hi (a,rho)).mp ha
  have hmin : IsMinimizer
      (RestorationPairs ((boxedModel d hr).fixedLinearFiber a.2) (boxedModel d hr).g)
      Prod.snd (a,rho) := by
    change IsMinimizer (RestorationPairs ((boxedModel d hr).fixedLinearFiber a.2) d.g)
      Prod.snd (a,rho)
    simpa only [hay,boxed_hardFiber_eq] using hfree
  obtain ⟨lambda,mu,hkkt⟩ := exists_restorationKKT (boxedModel d hr) a rho
    (fun j => fderiv ℝ (d.g j) a) hr.constraint_convex
    (fun j => (((hr.constraint_C1 j).differentiable (by norm_num)) a).hasFDerivAt) hmin
  apply restoration_oa_fiber_excluded_active hkkt (infeasible_restoration_positive d y hi ha)
  refine ⟨q,?_,hrows⟩
  simpa only [hay,boxed_hardFiber_eq] using hq

theorem event_exists (d : Data n m l r) (hr : Regularity d) (y : IntVector m)
    (hne : (d.hardFiber y).Nonempty) :
    (∃ a, IsMinimizer (d.feasibleFiber y) d.f a) ∨
    (¬ (d.feasibleFiber y).Nonempty ∧
      ∃ a rho, IsMinimizer (d.restoration y) Prod.snd (a,rho)) := by
  by_cases hf : (d.feasibleFiber y).Nonempty
  · exact Or.inl (feasibleFiber_attained d hr y hf)
  · exact Or.inr ⟨hf,restoration_attained d hr y hne⟩

end Chapter06.Level
