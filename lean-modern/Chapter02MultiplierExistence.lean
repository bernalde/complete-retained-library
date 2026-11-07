module

public import Chapter02KKTCuts
public import Chapter02Slater
public import Chapter02PolyhedralNormal

@[expose] public section

/-! Actual fixed-fiber restriction for the refined-Slater multiplier existence
composition. Candidate work; acceptance and scope are recorded separately. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

def fiberInclusionDerivative (n m : ℕ) : RealVector n →L[ℝ] Point n m :=
  ContinuousLinearMap.inl ℝ (RealVector n) (RealVector m)

@[simp] theorem fiberInclusionDerivative_apply {n m : ℕ} (v : RealVector n) :
    fiberInclusionDerivative n m v = (v,0) := rfl

theorem fiberInclusion_hasFDerivAt {n m : ℕ} (y : RealVector m) (x : RealVector n) :
    HasFDerivAt (fun z : RealVector n => (z,y)) (fiberInclusionDerivative n m) x := by
  simpa only [fiberInclusionDerivative_apply, Prod.mk_add_mk, add_zero, zero_add]
    using (fiberInclusionDerivative n m).hasFDerivAt.add_const (0,y)

def fiberLinearRow {n m l r : ℕ} (d : ModelData n m l r) (i : Fin r) :
    RealVector n →L[ℝ] ℝ :=
  (linearFormCLM (d.A i) (d.B i)).comp (fiberInclusionDerivative n m)

def fiberLinearBound {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (i : Fin r) : ℝ :=
  d.rhs i - LinearForm (d.A i) (d.B i) (0,y)

def fiberPolyhedron {n m l r : ℕ} (d : ModelData n m l r) (y : RealVector m) :
    Set (RealVector n) := {x | ∀ i, fiberLinearRow d i x ≤ fiberLinearBound d y i}

@[simp] theorem fiberLinearRow_apply {n m l r : ℕ} (d : ModelData n m l r)
    (i : Fin r) (x : RealVector n) :
    fiberLinearRow d i x = LinearForm (d.A i) (d.B i) (x,0) := rfl

theorem fiberLinearResidual_eq {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (i : Fin r) (x : RealVector n) :
    fiberLinearRow d i x - fiberLinearBound d y i = linearResidual d i (x,y) := by
  simp [fiberLinearRow_apply, fiberLinearBound, linearResidual, LinearForm]
  ring

theorem fiberPolyhedron_mem_iff {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (x : RealVector n) :
    x ∈ fiberPolyhedron d y ↔ (x,y) ∈ d.linearRegion := by
  change (∀ i, fiberLinearRow d i x ≤ fiberLinearBound d y i) ↔ _
  constructor
  · intro h i
    have hi := sub_nonpos.mpr (h i)
    rw [fiberLinearResidual_eq] at hi
    exact sub_nonpos.mp hi
  · intro h i
    apply sub_nonpos.mp
    rw [fiberLinearResidual_eq]
    exact sub_nonpos.mpr (h i)

theorem fiberPolyhedron_convex {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) : Convex ℝ (fiberPolyhedron d y) := by
  intro x hx z hz a b ha hb hab i
  change fiberLinearRow d i (a • x + b • z) ≤ fiberLinearBound d y i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a * fiberLinearRow d i x + b * fiberLinearRow d i z ≤
        a * fiberLinearBound d y i + b * fiberLinearBound d y i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hz i) hb)
    _ = fiberLinearBound d y i := by rw [← add_mul, hab, one_mul]

theorem fiber_mix {n m : ℕ} (x z : RealVector n) (y : RealVector m)
    (a b : ℝ) (hab : a+b=1) :
    (a • x + b • z,y) = a • (x,y) + b • (z,y) := by
  apply Prod.ext
  · rfl
  change y = a • y + b • y
  rw [← add_smul, hab, one_smul]

theorem fiberObjective_convex {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) :
    ConvexOn ℝ (fiberPolyhedron d y) (fun x => d.objective (x,y)) := by
  refine ⟨fiberPolyhedron_convex d y, ?_⟩
  intro x _ z _ a b _ _ hab
  dsimp only
  rw [fiber_mix x z y a b hab]
  exact le_of_eq (linearForm_affine d.c1 d.c2 _ _ a b)

theorem fiberRows_convex {n m l r : ℕ} (d : ModelData n m l r)
    (y : RealVector m) (hg : ∀ j, ConvexOn ℝ Set.univ (d.g j)) :
    ∀ j, ConvexOn ℝ (fiberPolyhedron d y) (fun x => d.g j (x,y)) := by
  intro j
  refine ⟨fiberPolyhedron_convex d y, ?_⟩
  intro x _ z _ a b ha hb hab
  dsimp only
  rw [fiber_mix x z y a b hab]
  exact (hg j).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem fiber_minimizer_iff {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) :
    IsMinimizer (d.fixedNonlinearFiber p.2) d.objective p ↔
    IsMinimizer {x ∈ fiberPolyhedron d p.2 | ∀ j, d.g j (x,p.2) ≤ 0}
      (fun x => d.objective (x,p.2)) p.1 := by
  constructor
  · rintro ⟨hp,hmin⟩
    have hp' := (mem_fixedNonlinearFiber d p.2 p).mp hp
    refine ⟨⟨(fiberPolyhedron_mem_iff d p.2 p.1).mpr hp'.1, hp'.2.2⟩, ?_⟩
    intro x hx
    exact hmin (x,p.2) ((mem_fixedNonlinearFiber d p.2 _).mpr
      ⟨(fiberPolyhedron_mem_iff d p.2 x).mp hx.1, rfl, hx.2⟩)
  · rintro ⟨hp,hmin⟩
    refine ⟨(mem_fixedNonlinearFiber d p.2 p).mpr
      ⟨(fiberPolyhedron_mem_iff d p.2 p.1).mp hp.1, rfl, hp.2⟩, ?_⟩
    intro q hq
    obtain ⟨hL,hy,hg⟩ := (mem_fixedNonlinearFiber d p.2 q).mp hq
    have hq' : q = (q.1,p.2) := Prod.ext rfl hy
    rw [hq'] at hL hg ⊢
    exact hmin q.1 ⟨(fiberPolyhedron_mem_iff d p.2 q.1).mpr hL,hg⟩

theorem fiber_partialLagrangian_hasFDerivAt {n m l r : ℕ}
    (d : ModelData n m l r) (p : Point n m)
    (D : Fin l → Point n m →L[ℝ] ℝ) (lambda : Fin l → ℝ)
    (hd : ∀ j, HasFDerivAt (d.g j) (D j) p) :
    HasFDerivAt (fun x => d.objective (x,p.2) + ∑ j, lambda j * d.g j (x,p.2))
      ((linearFormCLM d.c1 d.c2).comp (fiberInclusionDerivative n m) +
        ∑ j, lambda j • (D j).comp (fiberInclusionDerivative n m)) p.1 := by
  have hi := fiberInclusion_hasFDerivAt p.2 p.1
  exact ((objective_hasFDerivAt d p).comp p.1 hi).add
    (HasFDerivAt.fun_sum fun j _ => ((hd j).comp p.1 hi).const_mul (lambda j))

theorem source_fixedNonlinearFiber_compact {n m l r : ℕ} (d : ModelData n m l r)
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j)) :
    IsCompact (d.fixedNonlinearFiber (fun i => (y i : ℝ))) := by
  have hN : IsClosed d.nonlinearRegion := by
    have heq : d.nonlinearRegion = ⋂ j, {p | d.g j p ≤ 0} := by
      ext p
      simp [ModelData.nonlinearRegion]
    rw [heq]
    exact isClosed_iInter fun j => isClosed_le (hg j) continuous_const
  exact (source_fixedLinearFiber_compact d y hy hbase).inter_right hN

theorem source_fixedNLP_minimum_attained {n m l r : ℕ} (d : ModelData n m l r)
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hne : (d.fixedNonlinearFiber (fun i => (y i : ℝ))).Nonempty)
    (hg : ∀ j, Continuous (d.g j)) :
    ∃ p, IsMinimizer (d.fixedNonlinearFiber (fun i => (y i : ℝ))) d.objective p :=
  compact_feasible_attainment (source_fixedNonlinearFiber_compact d y hy hbase hg)
    hne (linearForm_continuous d.c1 d.c2).continuousOn

/-- Refined fiberwise Slater yields actual multipliers for each fixed-NLP
minimizer. All affine inequalities may be tight. Full-space derivatives
are supplied at that optimizer; only their x-parts enter stationarity. -/
theorem exists_fixedNLPKKT {n m l r : ℕ} (d : ModelData n m l r)
    (p : Point n m) (D : Fin l → Point n m →L[ℝ] ℝ)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hd : ∀ j, HasFDerivAt (d.g j) (D j) p)
    (hmin : IsMinimizer (d.fixedNonlinearFiber p.2) d.objective p)
    (hslater : ∃ z ∈ d.fixedLinearFiber p.2, ∀ j, d.g j z < 0) :
    ∃ lambda mu, FixedNLPKKT d p D lambda mu := by
  have hs : ∃ z ∈ fiberPolyhedron d p.2, ∀ j, d.g j (z,p.2) < 0 := by
    obtain ⟨z,⟨hL,hy⟩,hz⟩ := hslater
    have heq : z = (z.1,p.2) := Prod.ext rfl hy
    refine ⟨z.1,(fiberPolyhedron_mem_iff d p.2 z.1).mpr ?_,?_⟩
    · simpa only [← heq] using hL
    · simpa only [← heq] using hz
  obtain ⟨lambda,hlambda,hcomp,hpartial⟩ :=
    convex_slater_partialLagrangian_minimum (fiberPolyhedron d p.2)
      (fun x => d.objective (x,p.2)) (fun j x => d.g j (x,p.2)) p.1
      (fiberPolyhedron_convex d p.2) (fiberObjective_convex d p.2)
      (fiberRows_convex d p.2 hconv) ((fiber_minimizer_iff d p).mp hmin) hs
  obtain ⟨mu,hmu,hlincomp,hstat⟩ := polyhedral_minimum_multipliers
    (fiberLinearRow d) (fiberLinearBound d p.2) hpartial
    (fiber_partialLagrangian_hasFDerivAt d p D lambda hd)
  have hp := (mem_fixedNonlinearFiber d p.2 p).mp hmin.1
  refine ⟨lambda,mu,hp.1,hp.2.2,hd,hlambda,hmu,hcomp,?_,?_⟩
  · intro i
    simpa only [fiberLinearResidual_eq] using hlincomp i
  · intro dx
    have h := congrArg (fun L : RealVector n →L[ℝ] ℝ => L dx) hstat
    simpa [ModelData.objective, fiberLinearRow_apply] using h

/-- Literal free-slack restoration has nonlinear Slater whenever its linear
fiber is nonempty. Normalization follows from the lifted slack stationarity.
The empty nonlinear family is excluded here and remains the unbounded branch. -/
theorem exists_restorationKKT {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (p : Point n m) (rho : ℝ)
    (D : Fin l → Point n m →L[ℝ] ℝ)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hd : ∀ j, HasFDerivAt (d.g j) (D j) p)
    (hmin : IsMinimizer (RestorationPairs (d.fixedLinearFiber p.2) d.g)
      Prod.snd (p,rho)) :
    ∃ lambda mu, RestorationKKT d p rho D lambda mu := by
  have hlift : IsMinimizer (d.restorationModel.fixedNonlinearFiber p.2)
      d.restorationModel.objective (epiInsert p rho) := by
    apply (restorationModel_pairMinimizer_iff d p.2 _).mpr
    simpa only [epiProject_insert, epiHeight_insert] using hmin
  have hc : ∀ j, ConvexOn ℝ Set.univ (d.restorationModel.g j) := by
    simpa only [Set.preimage_univ] using restorationModel_rows_convex d Set.univ hconv
  have hder : ∀ j, HasFDerivAt (d.restorationModel.g j)
      (epigraphDerivative (D j)) (epiInsert p rho) := by
    intro j
    apply restorationModel_row_hasFDerivAt
    simpa only [epiProject_insert] using hd j
  obtain ⟨lambda,mu,hkkt⟩ := exists_fixedNLPKKT d.restorationModel (epiInsert p rho)
    (fun j => epigraphDerivative (D j)) hc hder hlift
    (source_restoration_strict_slack_exists d p.2 ⟨p,hmin.1.1⟩)
  exact ⟨lambda,mu,restorationKKT_of_lifted_fixedNLPKKT hd hkkt⟩

/-- At least one actual fixed-NLP optimizer and its actual derivatives have
KKT multipliers under the source compactness assumptions plus fiber Slater. -/
theorem source_fixedNLP_KKT_attained {n m l r : ℕ} (d : ModelData n m l r)
    (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hslater : ∃ z ∈ d.fixedLinearFiber (fun i => (y i : ℝ)), ∀ j, d.g j z < 0) :
    ∃ p lambda mu, p.2 = (fun i => (y i : ℝ)) ∧
      IsMinimizer (d.fixedNonlinearFiber (fun i => (y i : ℝ))) d.objective p ∧
      FixedNLPKKT d p (fun j => fderiv ℝ (d.g j) p) lambda mu := by
  have hne : (d.fixedNonlinearFiber (fun i => (y i : ℝ))).Nonempty := by
    obtain ⟨z,hz,hg⟩ := hslater
    exact ⟨z,hz,fun j => (hg j).le⟩
  obtain ⟨p,hp⟩ := source_fixedNLP_minimum_attained d y hy hbase hne
    (fun j => (hdiff j).continuous)
  have hpy := ((mem_fixedNonlinearFiber d _ p).mp hp.1).2.1
  obtain ⟨lambda,mu,hkkt⟩ := exists_fixedNLPKKT d p (fun j => fderiv ℝ (d.g j) p)
    hconv (fun j => (hdiff j p).hasFDerivAt) (by simpa only [hpy] using hp)
    (by simpa only [hpy] using hslater)
  exact ⟨p,lambda,mu,hpy,hp,hkkt⟩

/-- Source compactness, smoothness and a nonempty fixed linear fiber produce
an attained restoration point and its normalized multipliers, without a KKT input. -/
theorem source_restoration_KKT_attained {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hne : (d.fixedLinearFiber (fun i => (y i : ℝ))).Nonempty)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    ∃ p rho lambda mu, p.2 = (fun i => (y i : ℝ)) ∧
      IsMinimizer (RestorationPairs (d.fixedLinearFiber (fun i => (y i : ℝ))) d.g)
        Prod.snd (p,rho) ∧
      RestorationKKT d p rho (fun j => fderiv ℝ (d.g j) p) lambda mu := by
  obtain ⟨q,hq⟩ := source_restoration_minimum_attained d y hy hbase hne
    (fun j => (hdiff j).continuous)
  have hpair := (restorationModel_pairMinimizer_iff d _ q).mp hq
  have hpy : (epiProject q).2 = (fun i => (y i : ℝ)) := hpair.1.1.2
  obtain ⟨lambda,mu,hkkt⟩ := exists_restorationKKT d (epiProject q) (epiHeight q)
    (fun j => fderiv ℝ (d.g j) (epiProject q)) hconv
    (fun j => (hdiff j _).hasFDerivAt) (by simpa only [hpy] using hpair)
  exact ⟨epiProject q,epiHeight q,lambda,mu,hpy,hpair,hkkt⟩

/-- Existence, normalization and a valid anchored GBD feasibility cut at the
given restoration optimizer, with no supplied multiplier certificate. -/
theorem restoration_cut_exists_of_minimum {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (p : Point n m) (rho : ℝ)
    (D : Fin l → Point n m →L[ℝ] ℝ)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hd : ∀ j, HasFDerivAt (d.g j) (D j) p)
    (hmin : IsMinimizer (RestorationPairs (d.fixedLinearFiber p.2) d.g)
      Prod.snd (p,rho)) :
    ∃ lambda mu, RestorationKKT d p rho D lambda mu ∧
      (∑ j, lambda j = 1) ∧
      anchoredFeasibilityCut d p D lambda mu p.2 = rho ∧
      (0 < rho ↔ ¬ (d.fixedNonlinearFiber p.2).Nonempty) ∧
      ∀ q ∈ d.linearRegion, q ∈ d.nonlinearRegion →
        anchoredFeasibilityCut d p D lambda mu q.2 ≤ 0 := by
  obtain ⟨lambda,mu,hkkt⟩ := exists_restorationKKT d p rho D hconv hd hmin
  exact ⟨lambda,mu,hkkt,hkkt.normalization,restoration_cut_at_anchor hkkt,
    restoration_positive_iff_fiber_infeasible hkkt hconv,
    fun _ hL hN => restoration_cut_valid hkkt hconv hL hN⟩

/-- All restoration-active rows exclude the whole infeasible affine fiber.
The source optimizer and actual derivatives suffice; no KKT input is required. -/
theorem restoration_active_oa_exclusion_of_minimum {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (p : Point n m) (rho : ℝ)
    (D : Fin l → Point n m →L[ℝ] ℝ)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hd : ∀ j, HasFDerivAt (d.g j) (D j) p)
    (hmin : IsMinimizer (RestorationPairs (d.fixedLinearFiber p.2) d.g)
      Prod.snd (p,rho))
    (hinfeas : ¬ (d.fixedNonlinearFiber p.2).Nonempty) :
    ¬ ∃ q, q ∈ d.fixedLinearFiber p.2 ∧
      SelectedOARows d D p {j | d.g j p = rho} q := by
  obtain ⟨lambda,mu,hkkt⟩ := exists_restorationKKT d p rho D hconv hd hmin
  exact restoration_oa_fiber_excluded_active hkkt
    ((restoration_positive_iff_fiber_infeasible hkkt hconv).mpr hinfeas)

/-- Source attainment plus smooth convex data supplies an actual restoration
anchor whose active linearizations exclude the infeasible fixed fiber. -/
theorem source_restoration_oa_exclusion_attained {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r) (y : IntVector m) (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hne : (d.fixedLinearFiber (fun i => (y i : ℝ))).Nonempty)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j))
    (hinfeas : ¬ (d.fixedNonlinearFiber (fun i => (y i : ℝ))).Nonempty) :
    ∃ p rho, p.2 = (fun i => (y i : ℝ)) ∧
      IsMinimizer (RestorationPairs (d.fixedLinearFiber (fun i => (y i : ℝ))) d.g)
        Prod.snd (p,rho) ∧ 0 < rho ∧
      ¬ ∃ q, q ∈ d.fixedLinearFiber (fun i => (y i : ℝ)) ∧
        SelectedOARows d (fun j => fderiv ℝ (d.g j) p) p
          {j | d.g j p = rho} q := by
  obtain ⟨p,rho,lambda,mu,hpy,hmin,hkkt⟩ :=
    source_restoration_KKT_attained d y hy hbase hne hconv hdiff
  have hi : ¬ (d.fixedNonlinearFiber p.2).Nonempty := by simpa only [hpy] using hinfeas
  have hpos := (restoration_positive_iff_fiber_infeasible hkkt hconv).mpr hi
  refine ⟨p,rho,hpy,hmin,hpos,?_⟩
  simpa only [hpy] using restoration_oa_fiber_excluded_active hkkt hpos

end Chapter02

#print axioms Chapter02.fiberInclusionDerivative_apply
#print axioms Chapter02.fiberInclusion_hasFDerivAt
#print axioms Chapter02.fiberLinearRow_apply
#print axioms Chapter02.fiberLinearResidual_eq
#print axioms Chapter02.fiberPolyhedron_mem_iff
#print axioms Chapter02.fiberPolyhedron_convex
#print axioms Chapter02.fiber_mix
#print axioms Chapter02.fiberObjective_convex
#print axioms Chapter02.fiberRows_convex
#print axioms Chapter02.fiber_minimizer_iff
#print axioms Chapter02.fiber_partialLagrangian_hasFDerivAt
#print axioms Chapter02.source_fixedNonlinearFiber_compact
#print axioms Chapter02.source_fixedNLP_minimum_attained
#print axioms Chapter02.exists_fixedNLPKKT
#print axioms Chapter02.exists_restorationKKT
#print axioms Chapter02.source_fixedNLP_KKT_attained
#print axioms Chapter02.source_restoration_KKT_attained
#print axioms Chapter02.restoration_cut_exists_of_minimum
#print axioms Chapter02.restoration_active_oa_exclusion_of_minimum
#print axioms Chapter02.source_restoration_oa_exclusion_attained
