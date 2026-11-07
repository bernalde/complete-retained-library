module

public import Chapter02KKTExamples
public import Chapter02MultiplierExistence

@[expose] public section

/-! Source-model controls for actual multiplier existence. Positive multiplier
conclusions will be obtained by applying the new general existence theorems. -/
noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02MultiplierExamples

def pt2 (x z : ℝ) : Point 2 0 := (fun i => if i = 0 then x else z,0)

def pinnedDisk : ModelData 2 0 1 2 where
  g := fun _ p => (p.1 0)^2 + (p.1 1)^2 - 1
  A := fun row i => if i = 0 then (if row = 0 then 1 else -1) else 0
  B := fun _ _ => 0
  rhs := fun _ => 0
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0

def diskCoord (i : Fin 2) : Point 2 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (RealVector 2) (RealVector 0))

theorem pinnedDisk_linear_iff (p : Point 2 0) :
    p ∈ pinnedDisk.linearRegion ↔ p.1 0 = 0 := by
  simp [ModelData.linearRegion, pinnedDisk, LinearForm, Fin.forall_fin_succ,
    Fin.sum_univ_succ]
  constructor <;> intro h
  · linarith [h.1,h.2]
  · simp [h]

theorem pinnedDisk_no_strict_affine :
    ¬ ∃ p : Point 2 0, ∀ row,
      LinearForm (pinnedDisk.A row) (pinnedDisk.B row) p < pinnedDisk.rhs row := by
  rintro ⟨p,h⟩
  have h0 := h 0
  have h1 := h 1
  norm_num [pinnedDisk, LinearForm, Fin.sum_univ_succ] at h0 h1
  linarith

theorem pinnedDisk_convex : ∀ j, ConvexOn ℝ Set.univ (pinnedDisk.g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  have h0 : 0 ≤ a*b*(p.1 0-q.1 0)^2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  have h1 : 0 ≤ a*b*(p.1 1-q.1 1)^2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  simp only [pinnedDisk, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  nlinarith [sq_nonneg (p.1 0-q.1 0),sq_nonneg (p.1 1-q.1 1)]

theorem pinnedDisk_derivative (j : Fin 1) :
    HasFDerivAt (pinnedDisk.g j) (-((2:ℝ) • diskCoord 1)) (pt2 0 (-1)) := by
  have h0 := (hasDerivAt_pow 2 ((pt2 0 (-1)).1 0)).comp_hasFDerivAt
    (pt2 0 (-1)) (diskCoord 0).hasFDerivAt
  have h1 := (hasDerivAt_pow 2 ((pt2 0 (-1)).1 1)).comp_hasFDerivAt
    (pt2 0 (-1)) (diskCoord 1).hasFDerivAt
  simpa [pinnedDisk, diskCoord, pt2, Function.comp_def] using (h0.add h1).sub_const 1

theorem pinnedDisk_slater : ∃ z ∈ pinnedDisk.fixedLinearFiber (pt2 0 (-1)).2,
    ∀ j, pinnedDisk.g j z < 0 := by
  refine ⟨pt2 0 0,⟨(pinnedDisk_linear_iff _).mpr (by simp [pt2]),rfl⟩,?_⟩
  intro j
  norm_num [pinnedDisk,pt2]

theorem pinnedDisk_minimum :
    IsMinimizer (pinnedDisk.fixedNonlinearFiber (pt2 0 (-1)).2)
      pinnedDisk.objective (pt2 0 (-1)) := by
  refine ⟨⟨⟨(pinnedDisk_linear_iff _).mpr (by simp [pt2]),rfl⟩,?_⟩,?_⟩
  · intro j
    norm_num [pinnedDisk,pt2]
  · intro q hq
    have hx := (pinnedDisk_linear_iff q).mp hq.1.1
    have hsq := hq.2 (0 : Fin 1)
    change (q.1 0)^2+(q.1 1)^2-1 ≤ 0 at hsq
    simp [ModelData.objective,pinnedDisk,LinearForm,pt2,Fin.sum_univ_succ,hx]
    nlinarith [sq_nonneg (q.1 1+1)]

def pt (x y : ℝ) : Point 1 1 := (fun _ => x,fun _ => y)

def pinnedRestoration : ModelData 1 1 1 2 where
  g := fun _ p => (p.1 0-1)^2
  A := fun row _ => if row = 0 then 1 else -1
  B := fun row _ => if row = 0 then -1 else 1
  rhs := fun _ => 0
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

theorem pinnedRestoration_linear_iff (p : Point 1 1) :
    p ∈ pinnedRestoration.linearRegion ↔ p.1 0 = p.2 0 := by
  simp [ModelData.linearRegion,pinnedRestoration,LinearForm,Fin.forall_fin_succ,
    Fin.sum_univ_one]
  constructor <;> intro h
  · linarith [h.1,h.2]
  · simp [h]

theorem pinnedRestoration_no_strict_affine :
    ¬ ∃ p : Point 1 1, ∀ row,
      LinearForm (pinnedRestoration.A row) (pinnedRestoration.B row) p <
        pinnedRestoration.rhs row := by
  rintro ⟨p,h⟩
  have h0 := h 0
  have h1 := h 1
  norm_num [pinnedRestoration,LinearForm,Fin.sum_univ_one] at h0 h1
  linarith

theorem pinnedRestoration_convex :
    ∀ j, ConvexOn ℝ Set.univ (pinnedRestoration.g j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro p _ q _ a b ha hb hab
  have h : 0 ≤ a*b*(p.1 0-q.1 0)^2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  simp only [pinnedRestoration,Prod.fst_add,Prod.smul_fst,Pi.add_apply,Pi.smul_apply,
    smul_eq_mul]
  have hm : a*p.1 0+b*q.1 0-1 = a*(p.1 0-1)+b*(q.1 0-1) := by nlinarith
  rw [hm]
  nlinarith [sq_nonneg (p.1 0-q.1 0)]

theorem pinnedRestoration_derivative (p : Point 1 1) (j : Fin 1) :
    HasFDerivAt (pinnedRestoration.g j)
      ((2*(p.1 0-1)) • Chapter02Examples.coordX) p := by
  have h := (hasDerivAt_pow 2 (p.1 0-1)).comp_hasFDerivAt p
    (Chapter02Examples.coordX.hasFDerivAt.sub_const 1)
  simpa [pinnedRestoration,Chapter02Examples.coordX,Function.comp_def] using h

theorem pinnedRestoration_smooth :
    ∀ j, ContDiff ℝ 1 (pinnedRestoration.g j) := by
  intro j
  exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).sub contDiff_const).pow 2

theorem pinnedRestoration_pair_minimum :
    IsMinimizer (RestorationPairs (pinnedRestoration.fixedLinearFiber (pt 0 0).2)
      pinnedRestoration.g) Prod.snd (pt 0 0,1) := by
  refine ⟨⟨⟨(pinnedRestoration_linear_iff _).mpr rfl,rfl⟩,?_⟩,?_⟩
  · intro j
    norm_num [pinnedRestoration,pt]
  · rintro ⟨q,rho⟩ ⟨⟨hq,hy⟩,hg⟩
    have hxy := (pinnedRestoration_linear_iff q).mp hq
    have hy0 : q.2 0 = 0 := congrFun hy 0
    have h := hg (0 : Fin 1)
    simpa [pinnedRestoration,hxy,hy0] using h

theorem pinnedRestoration_original_fiber_infeasible :
    ¬ (pinnedRestoration.fixedNonlinearFiber (pt 0 0).2).Nonempty := by
  rintro ⟨q,⟨hq,hy⟩,hg⟩
  have hxy := (pinnedRestoration_linear_iff q).mp hq
  have hy0 : q.2 0 = 0 := congrFun hy 0
  have h := hg (0 : Fin 1)
  norm_num [pinnedRestoration,hxy,hy0] at h

/-- The theorem must work despite impossible strict affine feasibility and
must supply a nonzero nonlinear multiplier and a nonzero affine normal. -/
theorem pinnedDisk_multipliers_from_existence :
    ∃ lambda mu, FixedNLPKKT pinnedDisk (pt2 0 (-1))
      (fun _ => -((2:ℝ) • diskCoord 1)) lambda mu ∧
      lambda 0 = 1/2 ∧ mu 1 - mu 0 = 1 := by
  obtain ⟨lambda,mu,h⟩ := exists_fixedNLPKKT pinnedDisk (pt2 0 (-1))
    (fun _ => -((2:ℝ) • diskCoord 1)) pinnedDisk_convex pinnedDisk_derivative
    pinnedDisk_minimum pinnedDisk_slater
  have hx := h.stationarity ((pt2 1 0).1)
  have hz := h.stationarity ((pt2 0 1).1)
  norm_num [ModelData.objective,pinnedDisk,pt2,diskCoord,LinearForm,Fin.sum_univ_succ]
    at hx hz
  exact ⟨lambda,mu,h,by linarith,by linarith⟩

def restorationD (_ : Fin 1) : Point 1 1 →L[ℝ] ℝ :=
  (2*((pt 0 0).1 0-1)) • Chapter02Examples.coordX

theorem pinnedRestoration_multipliers_from_existence :
    ∃ lambda mu, RestorationKKT pinnedRestoration (pt 0 0) 1 restorationD lambda mu ∧
      lambda 0 = 1 ∧ mu 0 - mu 1 = 2 := by
  obtain ⟨lambda,mu,h⟩ := exists_restorationKKT pinnedRestoration (pt 0 0) 1
    restorationD pinnedRestoration_convex (pinnedRestoration_derivative (pt 0 0))
    pinnedRestoration_pair_minimum
  have hl : lambda 0 = 1 := by simpa only [Fin.sum_univ_one] using h.normalization
  have hs := h.stationarity (fun _ => 1)
  norm_num [restorationD,pinnedRestoration,pt,Chapter02Examples.coordX,
    LinearForm,Fin.sum_univ_succ,hl] at hs
  exact ⟨lambda,mu,h,hl,by linarith⟩

theorem pinnedRestoration_exclusion_from_minimum :
    ¬ ∃ q, q ∈ pinnedRestoration.fixedLinearFiber (pt 0 0).2 ∧
      SelectedOARows pinnedRestoration restorationD (pt 0 0)
        {j | pinnedRestoration.g j (pt 0 0) = 1} q :=
  restoration_active_oa_exclusion_of_minimum pinnedRestoration (pt 0 0) 1
    restorationD pinnedRestoration_convex (pinnedRestoration_derivative (pt 0 0))
    pinnedRestoration_pair_minimum pinnedRestoration_original_fiber_infeasible

theorem pinnedRestoration_base_compact :
    IsCompact (pinnedRestoration.linearRegion ∩
      IntegerCylinder (n := 1) pinnedRestoration.lo pinnedRestoration.hi) := by
  have hL : IsClosed pinnedRestoration.linearRegion := by
    have heq : pinnedRestoration.linearRegion = {p : Point 1 1 | p.1 0 = p.2 0} := by
      ext p
      exact pinnedRestoration_linear_iff p
    rw [heq]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hY : IsClosed (IntegerCylinder (n := 1) pinnedRestoration.lo pinnedRestoration.hi) := by
    have hfin := (integerBox_finite pinnedRestoration.lo pinnedRestoration.hi).image
      (fun y : IntVector 1 => fun i => (y i : ℝ))
    have heq : IntegerCylinder (n := 1) pinnedRestoration.lo pinnedRestoration.hi =
        Prod.snd ⁻¹' ((fun y : IntVector 1 => fun i => (y i : ℝ)) ''
          IntegerBox pinnedRestoration.lo pinnedRestoration.hi) := by
      ext p
      simp [IntegerCylinder,eq_comm]
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  apply (isCompact_Icc : IsCompact (Set.Icc (pt 0 0) (pt 1 1))).of_isClosed_subset
    (hL.inter hY)
  rintro p ⟨hL,y,hy,hpy⟩
  have hxy := (pinnedRestoration_linear_iff p).mp hL
  have hy0 : 0 ≤ p.2 0 := by rw [hpy]; exact (hy 0).1
  have hy1 : p.2 0 ≤ 1 := by rw [hpy]; exact (hy 0).2
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i; change 0 ≤ p.1 0; rw [hxy]; exact hy0
  · intro i; fin_cases i; exact hy0
  · intro i; fin_cases i; change p.1 0 ≤ 1; rw [hxy]; exact hy1
  · intro i; fin_cases i; exact hy1

/-- The compact source-model wrapper yields an actual point, actual fderiv,
and multipliers together. No optimizer or multiplier is supplied to this call. -/
theorem pinnedRestoration_source_attained :
    ∃ p rho lambda mu, p.2 = (fun _ => (0:ℝ)) ∧
      IsMinimizer (RestorationPairs (pinnedRestoration.fixedLinearFiber (fun _ => 0))
        pinnedRestoration.g) Prod.snd (p,rho) ∧
      RestorationKKT pinnedRestoration p rho
        (fun j => fderiv ℝ (pinnedRestoration.g j) p) lambda mu := by
  have hy : (fun _ => (0:ℤ)) ∈ IntegerBox pinnedRestoration.lo pinnedRestoration.hi := by
    intro i; norm_num [pinnedRestoration]
  have hne : (pinnedRestoration.fixedLinearFiber (fun _ => ((0:ℤ):ℝ))).Nonempty := by
    refine ⟨pt 0 0,⟨(pinnedRestoration_linear_iff _).mpr rfl,?_⟩⟩
    simp [pt]
  simpa only [Int.cast_zero] using source_restoration_KKT_attained pinnedRestoration
    (fun _ => (0:ℤ)) hy pinnedRestoration_base_compact hne pinnedRestoration_convex
    (fun j => (pinnedRestoration_smooth j).differentiable (by norm_num))

end Chapter02MultiplierExamples

#print axioms Chapter02MultiplierExamples.pinnedDisk_linear_iff
#print axioms Chapter02MultiplierExamples.pinnedDisk_no_strict_affine
#print axioms Chapter02MultiplierExamples.pinnedDisk_convex
#print axioms Chapter02MultiplierExamples.pinnedDisk_derivative
#print axioms Chapter02MultiplierExamples.pinnedDisk_slater
#print axioms Chapter02MultiplierExamples.pinnedDisk_minimum
#print axioms Chapter02MultiplierExamples.pinnedRestoration_linear_iff
#print axioms Chapter02MultiplierExamples.pinnedRestoration_no_strict_affine
#print axioms Chapter02MultiplierExamples.pinnedRestoration_convex
#print axioms Chapter02MultiplierExamples.pinnedRestoration_derivative
#print axioms Chapter02MultiplierExamples.pinnedRestoration_smooth
#print axioms Chapter02MultiplierExamples.pinnedRestoration_pair_minimum
#print axioms Chapter02MultiplierExamples.pinnedRestoration_original_fiber_infeasible
#print axioms Chapter02MultiplierExamples.pinnedDisk_multipliers_from_existence
#print axioms Chapter02MultiplierExamples.pinnedRestoration_multipliers_from_existence
#print axioms Chapter02MultiplierExamples.pinnedRestoration_exclusion_from_minimum
#print axioms Chapter02MultiplierExamples.pinnedRestoration_base_compact
#print axioms Chapter02MultiplierExamples.pinnedRestoration_source_attained
