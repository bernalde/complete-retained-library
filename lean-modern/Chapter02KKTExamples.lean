module

public import Chapter02ModelExamples
public import Chapter02CompletionExamples
public import Chapter02KKTCuts

@[expose] public section

/-! Actual source-model witnesses for the Chapter 2 restoration/KKT continuation:
printed-cut refutations, signed restoration margins, absent KKT multipliers,
and explicit limits of source hypotheses. Independent acceptance is recorded
outside this candidate module. Original and accepted proof files are unchanged.
-/
noncomputable section
open Chapter02 Chapter02Examples
open scoped BigOperators
namespace Chapter02KKTExamples

def pt (x y : ℝ) : Point 1 1 := (fun _ => x, fun _ => y)
def coordY : Point 1 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.snd ℝ (RealVector 1) (RealVector 1))

/-- Source linear rows: 0 ≤ x ≤ 2 and y ≤ x; integer y is 0 or 1. -/
def linkedModel (c : ℝ) : ModelData 1 1 1 3 where
  g := fun _ p => (p.1 0)^2 - c
  A := fun row _ => if row = 1 then 1 else -1
  B := fun row _ => if row = 2 then 1 else 0
  rhs := fun row => if row = 1 then 2 else 0
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

theorem linked_linear_iff (c : ℝ) (p : Point 1 1) :
    p ∈ (linkedModel c).linearRegion ↔ 0 ≤ p.1 0 ∧ p.1 0 ≤ 2 ∧ p.2 0 ≤ p.1 0 := by
  simp [ModelData.linearRegion, linkedModel, LinearForm, Fin.forall_fin_succ,
    Fin.sum_univ_one]

theorem linked_objective (c : ℝ) (p : Point 1 1) :
    (linkedModel c).objective p = p.1 0 := by
  simp [ModelData.objective, linkedModel, LinearForm, Fin.sum_univ_one]

theorem linked_convex (c : ℝ) : ∀ j, ConvexOn ℝ Set.univ ((linkedModel c).g j) := by
  intro j
  convert (sample_convex (0 : Fin 2)).add_const (1-c) using 1
  ext p
  simp [sample, linkedModel]

theorem linked_derivative (c : ℝ) (p : Point 1 1) (j : Fin 1) :
    HasFDerivAt ((linkedModel c).g j) ((2*p.1 0) • coordX) p := by
  have h := ((hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p
    coordX.hasFDerivAt).sub_const c
  convert h using 1 <;> norm_num [linkedModel, coordX, Function.comp_def]

theorem linked_smooth (c : ℝ) : ∀ j, ContDiff ℝ 1 ((linkedModel c).g j) := by
  intro j
  exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).sub contDiff_const

/-- Compactness of the actual source linear/integer base, for every c. -/
theorem linked_base_compact (c : ℝ) :
    IsCompact ((linkedModel c).linearRegion ∩
      IntegerCylinder (n := 1) (linkedModel c).lo (linkedModel c).hi) := by
  have hL : IsClosed (linkedModel c).linearRegion := by
    have heq : (linkedModel c).linearRegion =
        ⋂ row, {p | LinearForm ((linkedModel c).A row) ((linkedModel c).B row) p ≤
          (linkedModel c).rhs row} := by
      ext p
      simp [ModelData.linearRegion]
    rw [heq]
    exact isClosed_iInter fun row => isClosed_le (linearForm_continuous _ _) continuous_const
  have hY : IsClosed (IntegerCylinder (n := 1) (linkedModel c).lo (linkedModel c).hi) := by
    have hfin := (integerBox_finite (linkedModel c).lo (linkedModel c).hi).image
      (fun y : IntVector 1 => fun i => (y i : ℝ))
    have heq : IntegerCylinder (n := 1) (linkedModel c).lo (linkedModel c).hi =
        Prod.snd ⁻¹' ((fun y : IntVector 1 => fun i => (y i : ℝ)) ''
          IntegerBox (linkedModel c).lo (linkedModel c).hi) := by
      ext p
      simp [IntegerCylinder, eq_comm]
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  apply (isCompact_Icc : IsCompact (Set.Icc (pt 0 0) (pt 2 1))).of_isClosed_subset
    (hL.inter hY)
  rintro p ⟨hL,y,hy,hp⟩
  obtain ⟨hxlo,hxhi,_⟩ := (linked_linear_iff c p).mp hL
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i; fin_cases i; exact hxlo
  · intro i; rw [hp]; exact (hy i).1
  · intro i; fin_cases i; exact hxhi
  · intro i; rw [hp]; exact (hy i).2

theorem linked_zero_feasible (c : ℝ) (hc : 0 ≤ c) :
    pt 0 0 ∈ (linkedModel c).feasibleOn Set.univ := by
  rw [source_feasible_iff]
  refine ⟨Set.mem_univ _, ?_, ?_, fun _ => (0:ℤ), ?_, by simp [pt]⟩
  · intro j; change 0^2-c ≤ 0; nlinarith
  · exact (linked_linear_iff c _).mpr (by norm_num [pt])
  · intro i; norm_num [linkedModel]

theorem linked_zero_global_minimizer (c : ℝ) (hc : 0 ≤ c) :
    IsMinimizer ((linkedModel c).feasibleOn Set.univ) (linkedModel c).objective (pt 0 0) := by
  refine ⟨linked_zero_feasible c hc, ?_⟩
  intro p hp
  have hL := ((source_feasible_iff (linkedModel c) Set.univ p).mp hp).2.2.1
  simpa [linked_objective, pt] using ((linked_linear_iff c p).mp hL).1

/-- Source ESH preprocessing drops the integer bounds: this affine g=y has no
minimum over L even though the original linear/integer base is compact. -/
def eshUnboundedModel : ModelData 1 1 1 3 :=
  {linkedModel 4 with g := fun _ p => p.2 0}

theorem esh_unbounded_source_base_compact :
    IsCompact (eshUnboundedModel.linearRegion ∩
      IntegerCylinder (n := 1) eshUnboundedModel.lo eshUnboundedModel.hi) :=
  linked_base_compact 4

theorem esh_unbounded_convex :
    ∀ j, ConvexOn ℝ Set.univ (eshUnboundedModel.g j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ s t _ _ _
  simp [eshUnboundedModel, smul_eq_mul]

theorem esh_unbounded_smooth :
    ∀ j, ContDiff ℝ 1 (eshUnboundedModel.g j) := by
  intro j
  exact (contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd

theorem esh_unbounded_no_minimizer : ¬ ∃ z,
    IsMinimizer (RestorationPairs eshUnboundedModel.linearRegion eshUnboundedModel.g)
      Prod.snd z := by
  rintro ⟨z,_,hmin⟩
  let s : ℝ := min (z.2-1) 0
  have hs0 : s ≤ 0 := min_le_right _ _
  have hs : s < z.2 := (min_le_left _ _).trans_lt (by linarith)
  have hL : pt 0 s ∈ eshUnboundedModel.linearRegion := by
    exact (linked_linear_iff 4 _).mpr (by norm_num [pt]; exact hs0)
  have hq : (pt 0 s,s) ∈ RestorationPairs eshUnboundedModel.linearRegion
      eshUnboundedModel.g := ⟨hL, fun _ => le_rfl⟩
  exact (not_le_of_gt hs) (hmin _ hq)

theorem esh_unbounded_complete_witness :
    IsCompact (eshUnboundedModel.linearRegion ∩
      IntegerCylinder (n := 1) eshUnboundedModel.lo eshUnboundedModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (eshUnboundedModel.g j)) ∧
    (∀ j, ContDiff ℝ 1 (eshUnboundedModel.g j)) ∧
    (∃ a ∈ eshUnboundedModel.linearRegion, ∀ j, eshUnboundedModel.g j a < 0) ∧
    ¬ ∃ z, IsMinimizer (RestorationPairs eshUnboundedModel.linearRegion
      eshUnboundedModel.g) Prod.snd z := by
  refine ⟨esh_unbounded_source_base_compact, esh_unbounded_convex,
    esh_unbounded_smooth, ?_, esh_unbounded_no_minimizer⟩
  refine ⟨pt 0 (-1), ?_, ?_⟩
  · exact (linked_linear_iff 4 _).mpr (by norm_num [pt])
  · intro j; norm_num [eshUnboundedModel, pt]

/-- Signed-margin minimization and absolute infinity norm already disagree for
one affine constraint. Neither optimum is an infimum-only assertion. -/
theorem signed_margin_not_absolute_norm :
    IsMinimizer (Set.Icc (-2:ℝ) 2) (fun x => x-1) (-2) ∧
    IsMinimizer (Set.Icc (-2:ℝ) 2) (fun x => |x-1|) 1 ∧
    ((-2:ℝ)-1 < 0) ∧ ((1:ℝ)-1=0) := by
  refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩, by norm_num, by norm_num⟩
  · intro x hx; dsimp only; linarith [hx.1]
  · intro x _; change |1-1| ≤ |x-1|; simp

def anchor : Point 1 1 := pt 1 1
def anchorD (_ : Fin 1) : Point 1 1 →L[ℝ] ℝ := (2:ℝ) • coordX
def linkMu (v : ℝ) (row : Fin 3) : ℝ := if row=2 then v else 0

theorem linked_optimality_kkt :
    FixedNLPKKT (linkedModel 4) anchor anchorD (fun _ => 0) (linkMu 1) := by
  constructor
  · exact (linked_linear_iff 4 _).mpr (by norm_num [anchor, pt])
  · intro j; norm_num [linkedModel, anchor, pt]
  · intro j; simpa [anchorD, anchor, pt] using linked_derivative 4 anchor j
  · intro j; norm_num
  · intro row; unfold linkMu; split_ifs <;> norm_num
  · intro j; simp
  · intro row
    fin_cases row <;> norm_num [linkMu, linearResidual, linkedModel, anchor, pt,
      LinearForm, Fin.sum_univ_one, Fin.ext_iff]
  · intro dx
    simp [ModelData.objective, linkedModel, LinearForm, linkMu, Fin.sum_univ_succ,
      Fin.sum_univ_one]

theorem linked_restoration_kkt :
    RestorationKKT (linkedModel (1/2)) anchor (1/2) anchorD (fun _ => 1) (linkMu 2) := by
  constructor
  · exact (linked_linear_iff (1/2) _).mpr (by norm_num [anchor, pt])
  · intro j; norm_num [linkedModel, anchor, pt]
  · intro j; simpa [anchorD, anchor, pt] using linked_derivative (1/2) anchor j
  · intro j; norm_num
  · intro row; unfold linkMu; split_ifs <;> norm_num
  · intro j; norm_num [linkedModel, anchor, pt]
  · intro row
    fin_cases row <;> norm_num [linkMu, linearResidual, linkedModel, anchor, pt,
      LinearForm, Fin.sum_univ_one, Fin.ext_iff]
  · intro dx
    simp [linkedModel, LinearForm, linkMu, anchorD, coordX, Fin.sum_univ_succ,
      Fin.sum_univ_one, smul_eq_mul]
  · norm_num [Fin.sum_univ_one]

theorem printed_optimality_excludes_global_minimizer :
    IsMinimizer ((linkedModel 4).feasibleOn Set.univ) (linkedModel 4).objective (pt 0 0) ∧
    FixedNLPKKT (linkedModel 4) anchor anchorD (fun _ => 0) (linkMu 1) ∧
    (linkedModel 4).objective (pt 0 0) <
      printedOptimalityCut (linkedModel 4) anchor anchorD (fun _ => 0) (linkMu 1) (pt 0 0).2 ∧
    anchoredOptimalityCut (linkedModel 4) anchor anchorD (fun _ => 0) (linkMu 1) (pt 0 0).2 =
      (linkedModel 4).objective (pt 0 0) := by
  refine ⟨linked_zero_global_minimizer 4 (by norm_num), linked_optimality_kkt, ?_, ?_⟩ <;>
    norm_num [printedOptimalityCut, anchoredOptimalityCut, ModelData.objective,
      linkedModel, LinearForm, linkMu, anchor, pt, Fin.sum_univ_succ, Fin.sum_univ_one]

theorem printed_feasibility_excludes_feasible_assignment :
    pt 0 0 ∈ (linkedModel (1/2)).feasibleOn Set.univ ∧
    RestorationKKT (linkedModel (1/2)) anchor (1/2) anchorD (fun _ => 1) (linkMu 2) ∧
    0 < printedFeasibilityCut (linkedModel (1/2)) anchor anchorD (fun _ => 1) (linkMu 2) (pt 0 0).2 ∧
    anchoredFeasibilityCut (linkedModel (1/2)) anchor anchorD (fun _ => 1) (linkMu 2) (pt 0 0).2 ≤ 0 := by
  refine ⟨linked_zero_feasible (1/2) (by norm_num), linked_restoration_kkt, ?_, ?_⟩ <;>
    norm_num [printedFeasibilityCut, anchoredFeasibilityCut, linkedModel, LinearForm,
      linkMu, anchor, pt, anchorD, coordX, Fin.sum_univ_succ, Fin.sum_univ_one, smul_eq_mul]

/-- Zero-margin source model: x in [-1,1], integer y=0, g=x²-y,
objective x. The fixed nonlinear fiber consists only of (0,0). -/
def zeroMarginModel : ModelData 1 1 1 2 where
  g := fun _ p => (p.1 0)^2 - p.2 0
  A := fun row _ => if row = 0 then 1 else -1
  B := fun _ _ => 0
  rhs := fun _ => 1
  c1 := fun _ => 1
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 0

theorem zeroMargin_linear_iff (p : Point 1 1) :
    p ∈ zeroMarginModel.linearRegion ↔ -1 ≤ p.1 0 ∧ p.1 0 ≤ 1 := by
  simp [ModelData.linearRegion, zeroMarginModel, LinearForm, Fin.forall_fin_succ,
    Fin.sum_univ_one]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem zeroMargin_convex : ∀ j, ConvexOn ℝ Set.univ (zeroMarginModel.g j) := by
  intro j
  have hlinear : ConvexOn ℝ Set.univ (fun p : Point 1 1 => -p.2 0) := by
    refine ⟨convex_univ, ?_⟩
    intro p _ q _ s t _ _ _
    change -(s*p.2 0+t*q.2 0) ≤ s*(-p.2 0)+t*(-q.2 0)
    linarith
  apply ((linked_convex 0 j).add hlinear).congr
  intro p hp
  simp [zeroMarginModel, linkedModel, sub_eq_add_neg, Pi.add_apply]

theorem zeroMargin_smooth : ∀ j, ContDiff ℝ 1 (zeroMarginModel.g j) := by
  intro j
  exact (((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_fst).pow 2).sub
    ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).comp contDiff_snd)

theorem zeroMargin_derivative (p : Point 1 1) (j : Fin 1) :
    HasFDerivAt (zeroMarginModel.g j) ((2*p.1 0) • coordX - coordY) p := by
  have h := ((hasDerivAt_pow 2 (p.1 0)).comp_hasFDerivAt p
    coordX.hasFDerivAt).sub coordY.hasFDerivAt
  convert h using 1 <;> (try ext w) <;>
    norm_num [zeroMarginModel, coordX, coordY, Function.comp_def, Pi.sub_apply]

theorem zeroMargin_base_compact :
    IsCompact (zeroMarginModel.linearRegion ∩
      IntegerCylinder (n := 1) zeroMarginModel.lo zeroMarginModel.hi) := by
  have heq : zeroMarginModel.linearRegion ∩
      IntegerCylinder (n := 1) zeroMarginModel.lo zeroMarginModel.hi =
      Set.Icc (pt (-1) 0) (pt 1 0) := by
    ext p
    constructor
    · rintro ⟨hpL, y, hy, hpy⟩
      have hx := (zeroMargin_linear_iff p).mp hpL
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro i; fin_cases i; exact hx.1
      · intro i; rw [hpy]; exact (hy i).1
      · intro i; fin_cases i; exact hx.2
      · intro i; rw [hpy]; exact (hy i).2
    · intro hp
      refine ⟨(zeroMargin_linear_iff p).mpr ⟨hp.1.1 0, hp.2.1 0⟩,
        fun _ => (0 : ℤ), ?_, ?_⟩
      · intro i; norm_num [zeroMarginModel]
      · funext i
        simpa [pt] using le_antisymm (hp.2.2 i) (hp.1.2 i)
  rw [heq]
  exact isCompact_Icc

theorem zeroMargin_fiber_iff (p : Point 1 1) :
    p ∈ zeroMarginModel.fixedNonlinearFiber (fun _ => 0) ↔ p = pt 0 0 := by
  constructor
  · rintro ⟨⟨_, hpy⟩, hg⟩
    have hy : p.2 0 = 0 := congrFun hpy 0
    have hsq := hg (0 : Fin 1)
    change (p.1 0)^2 - p.2 0 ≤ 0 at hsq
    have hx : p.1 0 = 0 := by nlinarith [sq_nonneg (p.1 0)]
    apply Prod.ext
    · funext i; fin_cases i; exact hx
    · exact hpy
  · rintro rfl
    refine ⟨⟨(zeroMargin_linear_iff _).mpr (by norm_num [pt]), rfl⟩, ?_⟩
    intro j; norm_num [zeroMarginModel, pt]

theorem zeroMargin_fixed_optimum :
    IsMinimizer (zeroMarginModel.fixedNonlinearFiber (fun _ => 0))
      zeroMarginModel.objective (pt 0 0) := by
  refine ⟨(zeroMargin_fiber_iff _).mpr rfl, ?_⟩
  intro p hp
  rw [(zeroMargin_fiber_iff p).mp hp]

theorem zeroMargin_original_feasible : pt 0 0 ∈ zeroMarginModel.feasibleOn Set.univ := by
  rw [source_feasible_iff]
  refine ⟨Set.mem_univ _, ?_, (zeroMargin_linear_iff _).mpr (by norm_num [pt]),
    fun _ => (0 : ℤ), ?_, by simp [pt]⟩
  · intro j; norm_num [zeroMarginModel, pt]
  · intro i; norm_num [zeroMarginModel]

theorem zeroMargin_restoration_optimum :
    IsMinimizer (zeroMarginModel.restorationModel.fixedNonlinearFiber (fun _ => 0))
      zeroMarginModel.restorationModel.objective (epiInsert (pt 0 0) 0) := by
  apply (restorationModel_pairMinimizer_iff zeroMarginModel (fun _ => 0) _).mpr
  simp only [epiProject_insert, epiHeight_insert]
  refine ⟨⟨⟨(zeroMargin_linear_iff _).mpr (by norm_num [pt]), rfl⟩, ?_⟩, ?_⟩
  · intro j; norm_num [zeroMarginModel, pt]
  · rintro ⟨p,v⟩ ⟨⟨_, hpy⟩, hpg⟩
    have hy : p.2 0 = 0 := congrFun hpy 0
    have hgv := hpg (0 : Fin 1)
    change (p.1 0)^2 - p.2 0 ≤ v at hgv
    change 0 ≤ v
    nlinarith [sq_nonneg (p.1 0)]

/-- Arbitrary derivative and multiplier families are ruled out: derivative
uniqueness forces the actual zero continuous derivative, and both inactive
affine rows have zero multipliers by complementarity. -/
theorem zeroMargin_no_kkt :
    ¬ ∃ (D : Fin 1 → Point 1 1 →L[ℝ] ℝ) (lambda : Fin 1 → ℝ) (mu : Fin 2 → ℝ),
      FixedNLPKKT zeroMarginModel (pt 0 0) D lambda mu := by
  rintro ⟨D, lambda, mu, h⟩
  have hD : D 0 = -coordY := by
    have hcanon : HasFDerivAt (zeroMarginModel.g 0) (-coordY) (pt 0 0) := by
      simpa [pt] using zeroMargin_derivative (pt 0 0) 0
    exact (h.derivatives 0).unique hcanon
  have hmu0 : mu 0 = 0 := by
    have hm := h.linear_complementarity 0
    simpa [linearResidual, zeroMarginModel, pt, LinearForm, Fin.sum_univ_one] using hm
  have hmu1 : mu 1 = 0 := by
    have hm := h.linear_complementarity 1
    simpa [linearResidual, zeroMarginModel, pt, LinearForm, Fin.sum_univ_one] using hm
  have hstat := h.stationarity (fun _ => 1)
  norm_num [ModelData.objective, zeroMarginModel, LinearForm, Fin.sum_univ_one,
    Fin.sum_univ_succ, hD, hmu0, hmu1, coordY] at hstat

theorem zeroMargin_oa_strict_improvement :
    pt (-1) 0 ∈ zeroMarginModel.fixedLinearFiber (fun _ => 0) ∧
    (∀ j, tangentRow zeroMarginModel (fun _ => -coordY) (pt 0 0) j (pt (-1) 0) ≤ 0) ∧
    zeroMarginModel.objective (pt (-1) 0) < zeroMarginModel.objective (pt 0 0) := by
  refine ⟨⟨(zeroMargin_linear_iff _).mpr (by norm_num [pt]), rfl⟩, ?_, ?_⟩
  · intro j; norm_num [tangentRow, zeroMarginModel, pt, coordY]
  · norm_num [ModelData.objective, zeroMarginModel, LinearForm, pt, Fin.sum_univ_one]

theorem zeroMargin_complete_witness :
    IsCompact (zeroMarginModel.linearRegion ∩
      IntegerCylinder (n := 1) zeroMarginModel.lo zeroMarginModel.hi) ∧
    (∀ j, ConvexOn ℝ Set.univ (zeroMarginModel.g j)) ∧
    (∀ j, ContDiff ℝ 1 (zeroMarginModel.g j)) ∧
    (∀ j, HasFDerivAt (zeroMarginModel.g j) (-coordY) (pt 0 0)) ∧
    pt 0 0 ∈ zeroMarginModel.feasibleOn Set.univ ∧
    IsMinimizer (zeroMarginModel.fixedNonlinearFiber (fun _ => 0))
      zeroMarginModel.objective (pt 0 0) ∧
    IsMinimizer (zeroMarginModel.restorationModel.fixedNonlinearFiber (fun _ => 0))
      zeroMarginModel.restorationModel.objective (epiInsert (pt 0 0) 0) ∧
    (¬ ∃ (D : Fin 1 → Point 1 1 →L[ℝ] ℝ) (lambda : Fin 1 → ℝ) (mu : Fin 2 → ℝ),
      FixedNLPKKT zeroMarginModel (pt 0 0) D lambda mu) ∧
    (pt (-1) 0 ∈ zeroMarginModel.fixedLinearFiber (fun _ => 0) ∧
      (∀ j, tangentRow zeroMarginModel (fun _ => -coordY) (pt 0 0) j (pt (-1) 0) ≤ 0) ∧
      zeroMarginModel.objective (pt (-1) 0) < zeroMarginModel.objective (pt 0 0)) := by
  refine ⟨zeroMargin_base_compact, zeroMargin_convex, zeroMargin_smooth,
    ?_, zeroMargin_original_feasible, zeroMargin_fixed_optimum, zeroMargin_restoration_optimum,
    zeroMargin_no_kkt, zeroMargin_oa_strict_improvement⟩
  intro j
  simpa [pt] using zeroMargin_derivative (pt 0 0) j

theorem linked_source_regularity (c : ℝ) :
    IsCompact ((linkedModel c).linearRegion ∩
      IntegerCylinder (n := 1) (linkedModel c).lo (linkedModel c).hi) ∧
    (∀ j, ConvexOn ℝ Set.univ ((linkedModel c).g j)) ∧
    (∀ j, ContDiff ℝ 1 ((linkedModel c).g j)) ∧
    (∀ p j, HasFDerivAt ((linkedModel c).g j) ((2*p.1 0) • coordX) p) :=
  ⟨linked_base_compact c, linked_convex c, linked_smooth c, linked_derivative c⟩

/-- The actual source restoration optimizer for every signed margin 1-c,
including negative and zero slack. There is no r≥0 constraint. -/
theorem linked_restoration_literal_optimum (c : ℝ) :
    IsMinimizer ((linkedModel c).restorationModel.fixedNonlinearFiber anchor.2)
      (linkedModel c).restorationModel.objective (epiInsert anchor (1-c)) := by
  apply (restorationModel_pairMinimizer_iff (linkedModel c) anchor.2 _).mpr
  simp only [epiProject_insert, epiHeight_insert]
  refine ⟨⟨⟨(linked_linear_iff c _).mpr (by norm_num [anchor, pt]), rfl⟩,
    ?_⟩, ?_⟩
  · intro j; norm_num [linkedModel, anchor, pt]
  · rintro ⟨p,v⟩ ⟨⟨hpL,hpy⟩,hpg⟩
    have hp := (linked_linear_iff c p).mp hpL
    have hpy1 : p.2 0 = 1 := by simpa [anchor, pt] using congrFun hpy 0
    have hgv := hpg (0 : Fin 1)
    change (p.1 0)^2 - c ≤ v at hgv
    change 1-c ≤ v
    nlinarith [hp.2.2]

theorem negative_margin_literal_witness :
    IsMinimizer ((linkedModel 4).restorationModel.fixedNonlinearFiber anchor.2)
      (linkedModel 4).restorationModel.objective (epiInsert anchor (-3)) ∧
    ∃ p ∈ (linkedModel 4).fixedLinearFiber anchor.2, ∀ j, (linkedModel 4).g j p < 0 := by
  refine ⟨?_, ?_⟩
  · convert linked_restoration_literal_optimum 4 using 1
    norm_num
  · exact (source_restoration_negative_iff (linkedModel 4) anchor.2
      (linked_restoration_literal_optimum 4)).mp (by norm_num)

theorem zero_margin_literal_witness :
    IsMinimizer ((linkedModel 1).restorationModel.fixedNonlinearFiber anchor.2)
      (linkedModel 1).restorationModel.objective (epiInsert anchor 0) ∧
    ((linkedModel 1).fixedNonlinearFiber anchor.2).Nonempty ∧
    ¬ ∃ p ∈ (linkedModel 1).fixedLinearFiber anchor.2, ∀ j, (linkedModel 1).g j p < 0 := by
  refine ⟨?_, ?_⟩
  · convert linked_restoration_literal_optimum 1 using 1
    norm_num
  · exact (source_restoration_zero_iff (linkedModel 1) anchor.2
      (linked_restoration_literal_optimum 1)).mp (by norm_num)

theorem positive_margin_literal_witness :
    IsMinimizer ((linkedModel (1/2)).restorationModel.fixedNonlinearFiber anchor.2)
      (linkedModel (1/2)).restorationModel.objective (epiInsert anchor (1/2)) ∧
    ¬ ((linkedModel (1/2)).fixedNonlinearFiber anchor.2).Nonempty := by
  refine ⟨?_, ?_⟩
  · convert linked_restoration_literal_optimum (1/2) using 1
    norm_num
  · exact (source_restoration_positive_iff (linkedModel (1/2)) anchor.2
      (linked_restoration_literal_optimum (1/2))).mp (by norm_num)

/-- Drop only nonlinear complementarity from the proposed optimality KKT
conditions. The retained true source hypotheses no longer justify elimination:
the Lagrangian tangent at the anchor is -2, while the purported cut is 1. -/
theorem nonlinear_complementarity_ablation_witness :
    anchor ∈ (linkedModel 4).linearRegion ∧
    (∀ j, (linkedModel 4).g j anchor ≤ 0) ∧
    (∀ j, HasFDerivAt ((linkedModel 4).g j) (anchorD j) anchor) ∧
    (∀ j : Fin 1, (0 : ℝ) ≤ (fun _ => 1) j) ∧
    (∀ row, 0 ≤ linkMu 3 row) ∧
    (∀ row, linkMu 3 row * linearResidual (linkedModel 4) row anchor = 0) ∧
    (∀ dx : RealVector 1, (linkedModel 4).objective (dx,0) +
      (∑ j : Fin 1, (1 : ℝ) * anchorD j (dx,0)) +
      (∑ row, linkMu 3 row * LinearForm ((linkedModel 4).A row)
        ((linkedModel 4).B row) (dx,0)) = 0) ∧
    (1 : ℝ) * (linkedModel 4).g 0 anchor ≠ 0 ∧
    ((linkedModel 4).objective anchor +
      (∑ j : Fin 1, (1 : ℝ) * tangentRow (linkedModel 4) anchorD anchor j anchor) +
      (∑ row, linkMu 3 row * linearResidual (linkedModel 4) row anchor) = -2) ∧
    anchoredOptimalityCut (linkedModel 4) anchor anchorD (fun _ => 1)
      (linkMu 3) anchor.2 = 1 := by
  have hcomp : ∀ row, linkMu 3 row * linearResidual (linkedModel 4) row anchor = 0 := by
    intro row
    fin_cases row <;> norm_num [linkMu, linearResidual, linkedModel, anchor, pt,
      LinearForm, Fin.sum_univ_one, Fin.ext_iff]
  refine ⟨(linked_linear_iff 4 _).mpr (by norm_num [anchor, pt]), ?_, ?_, ?_,
    ?_, hcomp, ?_, ?_, ?_, ?_⟩
  · intro j; norm_num [linkedModel, anchor, pt]
  · intro j; simpa [anchorD, anchor, pt] using linked_derivative 4 anchor j
  · intro j; norm_num
  · intro row; unfold linkMu; split_ifs <;> norm_num
  · intro dx
    simp [ModelData.objective, linkedModel, LinearForm, linkMu, anchorD, coordX,
      Fin.sum_univ_succ, Fin.sum_univ_one, smul_eq_mul]
    ring
  · norm_num [linkedModel, anchor, pt]
  · have hsum : (∑ row, linkMu 3 row * linearResidual (linkedModel 4) row anchor) = 0 :=
      Finset.sum_eq_zero (fun row _ => hcomp row)
    rw [hsum]
    norm_num [ModelData.objective, linkedModel, LinearForm, anchorD, coordX,
      tangentRow, anchor, pt, Fin.sum_univ_one]
  · norm_num [anchoredOptimalityCut, ModelData.objective, linkedModel, LinearForm,
      linkMu, anchor, pt, Fin.sum_univ_succ, Fin.sum_univ_one]
    exact (anchorD 0).map_zero

end Chapter02KKTExamples

#print axioms Chapter02KKTExamples.linked_source_regularity
#print axioms Chapter02KKTExamples.printed_optimality_excludes_global_minimizer
#print axioms Chapter02KKTExamples.printed_feasibility_excludes_feasible_assignment
#print axioms Chapter02KKTExamples.esh_unbounded_complete_witness
#print axioms Chapter02KKTExamples.signed_margin_not_absolute_norm
#print axioms Chapter02KKTExamples.zeroMargin_complete_witness
#print axioms Chapter02KKTExamples.linked_restoration_literal_optimum
#print axioms Chapter02KKTExamples.negative_margin_literal_witness
#print axioms Chapter02KKTExamples.zero_margin_literal_witness
#print axioms Chapter02KKTExamples.positive_margin_literal_witness
#print axioms Chapter02KKTExamples.nonlinear_complementarity_ablation_witness
