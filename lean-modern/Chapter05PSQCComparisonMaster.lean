module

public import Chapter05PSQCComparisonAnalytic
public import Chapter05QuadraticExact

@[expose] public section

/-! Compatible quadratic OA/PSC rows on the very same KKT entries and
occurrences. Every retained W/V/Y/coupling restriction is preserved. -/
noncomputable section
open Set Chapter02
open scoped BigOperators
namespace Chapter05.PSQC.Comparison
open Quadratic
variable {p q m l s nw nv : ℕ}

theorem unit_lagrangian_safeScale (d : PSCData p q m l s nw nv)
    (e : PSCEntry d) (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (hru : ∀ v ∈ d.V, cut d.r e.data.v 1 v ≤ d.r v)
    (htu : ∀ j v, v ∈ d.V → cut (d.t j) e.data.v 1 v ≤ d.t j v) :
    safeScale (lagrangian d e.data) e.data.v d.V = 1 :=
  unit_underestimation_safeScale_eq_one (unit_lagrangian_underestimation d e hr ht hru htu)

theorem quadratic_components_unit (d : PSCData p q m l s nw nv) (e : PSCEntry d)
    (R : QuadraticFormData (RealVector q)) (T : Fin l → QuadraticFormData (RealVector q))
    (hr : d.r = R.eval) (ht : ∀ j, d.t j = (T j).eval) :
    safeScale (lagrangian d e.data) e.data.v d.V = 1 := by
  apply unit_lagrangian_safeScale d e
    (hr ▸ R.contDiff) (fun j => ht j ▸ (T j).contDiff)
  · intro v _
    rw [hr,R.cut_one_eq]
  · intro j v _
    rw [ht j,(T j).cut_one_eq]

def objectiveRow (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (a : ℝ) (w : RealVector p) (v : RealVector q) (y : RealVector m) : ℝ :=
  d.a w + d.c y + cut d.r e.v a v
def constraintRow (d : PSCData p q m l s nw nv) (e : PSCAnchor d)
    (b : Fin l → ℝ) (j : Fin l) (w : RealVector p) (v : RealVector q)
    (y : RealVector m) : ℝ := d.C j y + d.D j w + cut (d.t j) e.v (b j) v

theorem compatible_row_identity (d : PSCData p q m l s nw nv) (e : PSCEntry d)
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (af as : ℝ) (b : Fin l → ℝ) (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    objectiveRow d e.data af w v y - fullCut d e.data as w v y =
      -(∑ j, e.data.lambda j * constraintRow d e.data b j w v y) -
        e.data.normalV (v-e.data.v) +
        ((af-as) * curvature d.r e.data.v v +
          ∑ j, e.data.lambda j * (b j-as) * curvature (d.t j) e.data.v v)/2 := by
  have hi := psc_oa_surrogate_identity d e.data e.kkt w v y
  have he : ∀ j, constraintRow d e.data b j w v y =
      pscConstraintTangent d e.data j w v y + (b j/2)*curvature (d.t j) e.data.v v := by
    intro j
    simp only [constraintRow, cut, tangent, (e.kkt.derivative_t j).fderiv,
      pscConstraintTangent, PSCData.nonlinear]
    ring
  have ho : objectiveRow d e.data af w v y =
      d.a w + d.c y + pscObjectiveTangent d e.data v + (af/2)*curvature d.r e.data.v v := by
    simp only [objectiveRow, cut, tangent, e.kkt.derivative_r.fderiv, pscObjectiveTangent]
    ring
  have hs : (∑ j, e.data.lambda j * (b j / 2 * curvature (d.t j) e.data.v v)) =
      (∑ j, e.data.lambda j * b j * curvature (d.t j) e.data.v v)/2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrows : (∑ j, e.data.lambda j * constraintRow d e.data b j w v y) =
      (∑ j, e.data.lambda j * pscConstraintTangent d e.data j w v y) +
        (∑ j, e.data.lambda j * b j * curvature (d.t j) e.data.v v)/2 := by
    simp_rw [he,mul_add]
    rw [Finset.sum_add_distrib,hs]
  have hdiff : (∑ j, e.data.lambda j * (b j-as) * curvature (d.t j) e.data.v v) =
      (∑ j, e.data.lambda j * b j * curvature (d.t j) e.data.v v) -
        as*(∑ j, e.data.lambda j * curvature (d.t j) e.data.v v) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ho, fullCut, psqcRow, lagrangian_curvature d e.data hr ht,hrows,hdiff]
  nlinarith

theorem compatible_row (d : PSCData p q m l s nw nv) (e : PSCEntry d)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (af as : ℝ) (b : Fin l → ℝ) (hfa : as ≤ af) (hba : ∀ j, as ≤ b j)
    (w : RealVector p) (v : RealVector q) (y : RealVector m) (eta : ℝ)
    (hv : v ∈ d.V) (hobj : objectiveRow d e.data af w v y ≤ eta)
    (hcon : ∀ j, constraintRow d e.data b j w v y ≤ 0) :
    psqcRow d e.data as w v y ≤ eta-d.a w-d.c y := by
  have hi := compatible_row_identity d e hr ht af as b w v y
  have hn := e.kkt.normalV_nonpos hv
  have hc : (∑ j, e.data.lambda j * constraintRow d e.data b j w v y) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (e.kkt.lambda_nonneg j) (hcon j)
  have hp : 0 ≤ (af-as)*curvature d.r e.data.v v :=
    mul_nonneg (sub_nonneg.mpr hfa) (curvature_nonneg hcr hr _ _)
  have hs : 0 ≤ ∑ j, e.data.lambda j * (b j-as) * curvature (d.t j) e.data.v v :=
    Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (e.kkt.lambda_nonneg j) (sub_nonneg.mpr (hba j)))
      (curvature_nonneg (hct j) (ht j) _ _)
  dsimp [fullCut] at hi
  linarith

theorem common_scale_row (d : PSCData p q m l s nw nv) (e : PSCEntry d)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (a : ℝ) (w : RealVector p) (v : RealVector q) (y : RealVector m) (eta : ℝ)
    (hv : v ∈ d.V) (hobj : objectiveRow d e.data a w v y ≤ eta)
    (hcon : ∀ j, constraintRow d e.data (fun _ => a) j w v y ≤ 0) :
    psqcRow d e.data a w v y ≤ eta-d.a w-d.c y :=
  compatible_row d e hcr hct hr ht a a (fun _ => a) le_rfl (fun _ => le_rfl)
    w v y eta hv hobj hcon

structure Occurrence (d : PSCData p q m l s nw nv) where
  entry : PSCEntry d
  objectiveScale : ℝ
  constraintScale : Fin l → ℝ
  pscScale : ℝ

def pscProjection {d : PSCData p q m l s nw nv} (H : List (Occurrence d)) :
    List (PSCEntry d × ℝ) := H.map fun o => (o.entry,o.pscScale)

def jointMasterData (d : PSCData p q m l s nw nv) (H : List (Occurrence d)) :
    MasterData (PSCCoordinates p q m) (Fin H.length) (Fin l) where
  f := jointObjective d
  g := jointConstraint d
  anchor i := jointAnchor (H.get i).entry.data
  objectiveScale i := (H.get i).objectiveScale
  constraintScale i := (H.get i).constraintScale
  base := pscRetainedBase d

theorem projection_occurrence {d : PSCData p q m l s nw nv}
    (H : List (Occurrence d)) (i : Fin H.length) :
    (pscProjection H).get ⟨i.val,by simp [pscProjection]⟩ =
      ((H.get i).entry,(H.get i).pscScale) := by
  simp [pscProjection]

theorem joint_occurrence_anchor (d : PSCData p q m l s nw nv)
    (H : List (Occurrence d)) (i : Fin H.length) :
    (jointMasterData d H).anchor i = jointAnchor (H.get i).entry.data ∧
      (jointMasterData d H).objectiveScale i = (H.get i).objectiveScale ∧
      (jointMasterData d H).constraintScale i = (H.get i).constraintScale :=
  ⟨rfl,rfl,rfl⟩

def Compatible {d : PSCData p q m l s nw nv} (H : List (Occurrence d)) : Prop :=
  ∀ o ∈ H, o.pscScale ≤ o.objectiveScale ∧ ∀ j, o.pscScale ≤ o.constraintScale j

/-- Source-facing scale validity is separate from compatibility. -/
def ValidScales (d : PSCData p q m l s nw nv) (H : List (Occurrence d)) : Prop :=
  SafeHistory (jointMasterData d H) Finset.univ ∧ scalesValid d (pscProjection H)

def epigraphToPSC (d : PSCData p q m l s nw nv) (z : PSCCoordinates p q m × ℝ) :
    PSCPoint p q m := ⟨z.1.1.1,z.1.1.2,z.1.2,z.2-d.a z.1.1.1-d.c z.1.2,z.2⟩
def pscToEpigraph (z : PSCPoint p q m) : PSCCoordinates p q m × ℝ :=
  (((z.w,z.v),z.y),z.alpha)

theorem epigraph_psc_inverse (d : PSCData p q m l s nw nv)
    (z : PSCCoordinates p q m × ℝ) : pscToEpigraph (epigraphToPSC d z) = z := by
  rcases z with ⟨⟨⟨w,v⟩,y⟩,eta⟩
  rfl
theorem psc_epigraph_inverse (d : PSCData p q m l s nw nv)
    (z : PSCPoint p q m) (hz : pscPointBase d z) :
    epigraphToPSC d (pscToEpigraph z) = z := by
  rcases z with ⟨w,v,y,beta,alpha⟩
  have he : alpha-d.a w-d.c y = beta := by have := hz.2; dsimp at this; linarith
  simp only [epigraphToPSC,pscToEpigraph,he]
theorem epigraph_psc_value (d : PSCData p q m l s nw nv)
    (z : PSCCoordinates p q m × ℝ) : (epigraphToPSC d z).alpha = z.2 := rfl
theorem epigraph_psc_base (d : PSCData p q m l s nw nv)
    (z : PSCCoordinates p q m × ℝ) :
    pscPointBase d (epigraphToPSC d z) ↔ z.1 ∈ pscRetainedBase d := by
  simp only [pscPointBase, epigraphToPSC, pscRetainedBase, mem_setOf_eq]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, by ring⟩

theorem quadratic_oa_to_psc (d : PSCData p q m l s nw nv)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (Occurrence d)) (hH : Compatible H) :
    epigraphToPSC d '' quadraticMaster (jointMasterData d H) Finset.univ ⊆
      psqcMaster d (pscProjection H) := by
  rintro _ ⟨z,hz,rfl⟩
  refine ⟨(epigraph_psc_base d z).mpr hz.1, ?_⟩
  intro ea hea
  obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hea
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ho
  subst o
  have hobj := hz.2.1 i (Finset.mem_univ i)
  have hcon := hz.2.2 i (Finset.mem_univ i)
  change cut (jointObjective d) (jointAnchor (H.get i).entry.data) _ z.1 ≤ z.2 at hobj
  rw [joint_objective_cut d _ hr] at hobj
  have hcons : ∀ j, constraintRow d (H.get i).entry.data (H.get i).constraintScale j
      z.1.1.1 z.1.1.2 z.1.2 ≤ 0 := by
    intro j
    have hj := hcon j
    change cut (jointConstraint d j) (jointAnchor (H.get i).entry.data) _ z.1 ≤ 0 at hj
    rw [joint_constraint_cut d _ ht] at hj
    exact hj
  exact compatible_row d (H.get i).entry hcr hct hr ht _ _ _
    (hH _ ho).1 (hH _ ho).2 _ _ _ _ hz.1.2.1 hobj hcons

theorem attained_comparison (d : PSCData p q m l s nw nv)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (Occurrence d)) (hH : Compatible H)
    (oa : PSCCoordinates p q m × ℝ) (ps : PSCPoint p q m)
    (hoa : IsMinimizer (quadraticMaster (jointMasterData d H) Finset.univ) Prod.snd oa)
    (hps : IsMinimizer (psqcMaster d (pscProjection H)) PSCPoint.alpha ps) :
    ps.alpha ≤ oa.2 :=
  hps.2 (epigraphToPSC d oa) (quadratic_oa_to_psc d hcr hct hr ht H hH ⟨oa,hoa.1,rfl⟩)

theorem joint_regularity (d : PSCData p q m l s nw nv)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (Occurrence d)) : MasterRegularity (jointMasterData d H) := by
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x _ z _ a b ha hb hab
    have hh := hcr.2 (mem_univ x.1.2) (mem_univ z.1.2) ha hb hab
    change d.a (a • x.1.1+b • z.1.1) + d.r (a • x.1.2+b • z.1.2) +
      d.c (a • x.2+b • z.2) ≤
      a*(d.a x.1.1+d.r x.1.2+d.c x.2)+b*(d.a z.1.1+d.r z.1.2+d.c z.2)
    simp only [map_add,map_smul,smul_eq_mul] at *
    nlinarith
  · change ContDiff ℝ 2 (fun z : PSCCoordinates p q m => d.a z.1.1 + d.r z.1.2 + d.c z.2)
    exact (((d.a.comp jointW).contDiff).add (hr.comp jointV.contDiff)).add
      (d.c.comp jointY).contDiff
  · intro j
    refine ⟨convex_univ, ?_⟩
    intro x _ z _ a b ha hb hab
    have hh := (hct j).2 (mem_univ x.1.2) (mem_univ z.1.2) ha hb hab
    change d.C j (a • x.2+b • z.2) + d.D j (a • x.1.1+b • z.1.1) +
      d.t j (a • x.1.2+b • z.1.2) ≤
      a*(d.C j x.2+d.D j x.1.1+d.t j x.1.2)+b*(d.C j z.2+d.D j z.1.1+d.t j z.1.2)
    simp only [map_add,map_smul,smul_eq_mul] at *
    nlinarith
  · intro j
    change ContDiff ℝ 2 (fun z : PSCCoordinates p q m => d.C j z.2 + d.D j z.1.1 + d.t j z.1.2)
    exact (((d.C j).comp jointY).contDiff.add ((d.D j).comp jointW).contDiff).add
      ((ht j).comp jointV.contDiff)

/-- Validity and comparison are both explicit; validity does not imply the
coefficient compatibility inequalities. Empty histories retain their literal sets. -/
theorem valid_coefficients_unit (d : PSCData p q m l s nw nv)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (Occurrence d)) (hv : ValidScales d H) (i : Fin H.length) :
    (0 ≤ (H.get i).objectiveScale ∧ (H.get i).objectiveScale ≤ 1) ∧
      (∀ j, 0 ≤ (H.get i).constraintScale j ∧ (H.get i).constraintScale j ≤ 1) ∧
      (0 ≤ (H.get i).pscScale ∧ (H.get i).pscScale ≤ 1) := by
  let R := joint_regularity d hcr hct hr ht H
  have hi := hv.1 i (Finset.mem_univ i)
  have hs := hv.2 ((H.get i).entry,(H.get i).pscScale)
    (List.mem_map.mpr ⟨H.get i,List.get_mem H i,rfl⟩)
  refine ⟨⟨hi.1.1,hi.1.2.trans (safeScale_bounds R.objective_convex R.objective_C2 _ _).2⟩,
    fun j => ⟨(hi.2 j).1,(hi.2 j).2.trans
      (safeScale_bounds (R.constraint_convex j) (R.constraint_C2 j) _ _).2⟩,
    hs.1,hs.2.trans ?_⟩
  exact (safeScale_bounds (lagrangian_convex d _ (H.get i).entry.kkt hcr hct)
    (lagrangian_contDiff d _ hr ht) _ _).2

theorem valid_master_comparison (d : PSCData p q m l s nw nv)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (H : List (Occurrence d)) (hc : Compatible H) (hv : ValidScales d H) :
    trueEpigraph (jointMasterData d H) ⊆ quadraticMaster (jointMasterData d H) Finset.univ ∧
      epigraphToPSC d '' quadraticMaster (jointMasterData d H) Finset.univ ⊆
        psqcMaster d (pscProjection H) :=
  ⟨trueEpigraph_subset_quadraticMaster (joint_regularity d hcr hct hr ht H) hv.1,
    quadratic_oa_to_psc d hcr hct hr ht H hc⟩

structure SourceOccurrence (d : PSCData p q m l s nw nv) where
  anchor : PSCSourceAnchor d
  objectiveScale : ℝ
  constraintScale : Fin l → ℝ
  pscScale : ℝ

def selectedOccurrences (d : PSCData p q m l s nw nv)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (S : List (SourceOccurrence d)) : List (Occurrence d) :=
  S.map fun a => ⟨sourceEntry d hcr hct a.anchor,a.objectiveScale,a.constraintScale,a.pscScale⟩

theorem selected_projection (d : PSCData p q m l s nw nv)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (S : List (SourceOccurrence d)) :
    pscProjection (selectedOccurrences d hcr hct S) =
      sourceHistory d hcr hct (S.map fun a => (a.anchor,a.pscScale)) := by
  simp [pscProjection,selectedOccurrences,sourceHistory,List.map_map]

/-- Uses exactly the multipliers selected by the accepted KKT necessity
interface from each source minimum and its local Slater data. -/
theorem source_selected_comparison (d : PSCData p q m l s nw nv)
    (hcr : ConvexOn ℝ univ d.r) (hct : ∀ j, ConvexOn ℝ univ (d.t j))
    (hr : ContDiff ℝ 2 d.r) (ht : ∀ j, ContDiff ℝ 2 (d.t j))
    (S : List (SourceOccurrence d))
    (hc : Compatible (selectedOccurrences d hcr hct S))
    (hv : ValidScales d (selectedOccurrences d hcr hct S)) :
    let H := selectedOccurrences d hcr hct S
    List.Forall₂ pscSourceMatches (S.map SourceOccurrence.anchor)
      (matchedHistory (pscProjection H)) ∧
      trueEpigraph (jointMasterData d H) ⊆ quadraticMaster (jointMasterData d H) Finset.univ ∧
      epigraphToPSC d '' quadraticMaster (jointMasterData d H) Finset.univ ⊆
        psqcMaster d (pscProjection H) := by
  dsimp only
  refine ⟨?_,valid_master_comparison d hcr hct hr ht _ hc hv⟩
  rw [selected_projection]
  simpa [List.map_map] using
    source_history_matches d hcr hct (S.map fun a => (a.anchor,a.pscScale))

end Chapter05.PSQC.Comparison
