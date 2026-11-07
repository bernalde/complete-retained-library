module

public import Chapter02InitializerSource
public import Chapter02CPDomainExamples
public import Chapter02ExteriorTangentAffineExample
public import Mathlib.Tactic

@[expose] public section

/-! Full ModelData controls for continuous initialization and evidence routing.
The accepted F1/F3 models are reused; their old cut theorems receive no new credit.
Neither a fractional strict reference nor a feasible objective trial is a solver
optimality certificate. Empty nonlinear rows bypass the signed maximum. -/

noncomputable section
open Chapter02 Chapter02CPDomainExamples
namespace Chapter02InitializerSourceExamples

private theorem mixed_zero_domain : mixedPoint 0 0 ∈ mixedDomain :=
  (source_feasible_iff _ _ _).mp mixed_feasible_endpoints.1 |>.1

private theorem mixed_zero_affine : mixedPoint 0 0 ∈ mixedModel.linearRegion :=
  (source_feasible_iff _ _ _).mp mixed_feasible_endpoints.1 |>.2.2.1

/-- Both continuous domain selectors attain their signed and tight lifted minima
on the same actual full mixed model. No integer restriction enters the minimum. -/
theorem mixed_initializer_attainment (retainAffine : Bool) :
    ∃ p, IsMinimizer (sourceInitializerDomain mixedModel mixedDomain retainAffine)
        (eshMaximum mixedModel.g) p ∧
      IsMinimizer (RestorationPairs
        (sourceInitializerDomain mixedModel mixedDomain retainAffine) mixedModel.g)
        Prod.snd (p, eshMaximum mixedModel.g p) := by
  apply source_initializer_minimum_attained mixedModel mixedDomain retainAffine
    mixed_domain_geometry.1
  · refine ⟨mixedPoint 0 0, ?_⟩
    cases retainAffine
    · exact mixed_zero_domain
    · exact ⟨mixed_zero_domain, mixed_zero_affine⟩
  · exact mixed_source_compact_control.1

/-- The new strict initializer is (0,1/2), distinct from the old F1 cut origin.
Height -1/8 is feasible and nonoptimal; its strictness does not restore integrality. -/
theorem mixed_fractional_initializer :
    mixedModel.g 0 (mixedPoint 0 (1/2)) = -(1/4 : ℝ) ∧
    (mixedPoint 0 (1/2), -(1/8 : ℝ)) ∈ RestorationPairs
      (sourceInitializerDomain mixedModel mixedDomain false) mixedModel.g ∧
    (∀ j, mixedModel.g j (mixedPoint 0 (1/2)) < 0) ∧
    ¬ IsMinimizer (RestorationPairs
      (sourceInitializerDomain mixedModel mixedDomain false) mixedModel.g)
      Prod.snd (mixedPoint 0 (1/2), -(1/8 : ℝ)) ∧
    mixedPoint 0 (1/2) ∉ IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi ∧
    mixedPoint 0 (1/2) ∉ mixedModel.feasibleOn mixedDomain := by
  have hp : mixedPoint 0 (1/2) ∈ sourceInitializerDomain mixedModel mixedDomain false :=
    (mixed_domain_geometry.2.2 _).mpr (by norm_num [mixedPoint])
  have hpair : (mixedPoint 0 (1/2), -(1/8 : ℝ)) ∈ RestorationPairs
      (sourceInitializerDomain mixedModel mixedDomain false) mixedModel.g := by
    refine ⟨hp, ?_⟩
    intro j; norm_num [mixedModel, mixedPoint]
  have hY : mixedPoint 0 (1/2) ∉ IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi := by
    rintro ⟨y, _, hy⟩
    have heq : (y 0 : ℝ) = 1/2 := by simpa [mixedPoint] using (congrFun hy 0).symm
    have h0 : (0 : ℤ) < y 0 := by exact_mod_cast (show (0 : ℝ) < y 0 by linarith)
    have h1 : y 0 < (1 : ℤ) := by exact_mod_cast (show (y 0 : ℝ) < 1 by linarith)
    omega
  refine ⟨by norm_num [mixedModel, mixedPoint], hpair,
    (initializer_feasible_height hpair).2.1 (by norm_num), ?_, hY, ?_⟩
  · intro hm
    have hbetter : (mixedPoint 0 (1/2), -(1/4 : ℝ)) ∈ RestorationPairs
        (sourceInitializerDomain mixedModel mixedDomain false) mixedModel.g := by
      refine ⟨hp, ?_⟩
      intro j; norm_num [mixedModel, mixedPoint]
    have hbad := hm.2 _ hbetter
    norm_num at hbad
  · intro hf
    exact hY ((source_feasible_iff _ _ _).mp hf).2.2.2

/-- An actual nonpositive pair at the integer endpoint passes the full source
consumer with the affine rows and bounded integer vector proved explicitly. -/
theorem mixed_restored_feasibility :
    (mixedPoint 0 0, (0 : ℝ)) ∈ RestorationPairs
      (sourceInitializerDomain mixedModel mixedDomain true) mixedModel.g ∧
    mixedPoint 0 0 ∈ mixedModel.feasibleOn mixedDomain := by
  have hp : (mixedPoint 0 0, (0 : ℝ)) ∈ RestorationPairs
      (sourceInitializerDomain mixedModel mixedDomain true) mixedModel.g := by
    refine ⟨⟨mixed_zero_domain, mixed_zero_affine⟩, ?_⟩
    intro j; norm_num [mixedModel, mixedPoint]
  have hy : mixedPoint 0 0 ∈ IntegerCylinder (n := 1) mixedModel.lo mixedModel.hi := by
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i; norm_num [IntegerBox, mixedModel]
    · funext i; norm_num [mixedPoint]
  exact ⟨hp, source_initializer_feasible mixedModel mixedDomain true hp le_rfl
    mixed_zero_affine hy⟩

/-- The X-only strict reference may violate L; the distinct feasible point
(0,1) restores every original restriction through the nonpositive-height consumer. -/
theorem affine_initializer_routing :
    (Chapter02ExteriorTangentAffineExample.point 0 0, -(1 : ℝ)) ∈ RestorationPairs
      (sourceInitializerDomain Chapter02ExteriorTangentAffineExample.model
        Chapter02ExteriorTangentAffineExample.domain false)
      Chapter02ExteriorTangentAffineExample.model.g ∧
    Chapter02ExteriorTangentAffineExample.point 0 0 ∉ sourceInitializerDomain
      Chapter02ExteriorTangentAffineExample.model Chapter02ExteriorTangentAffineExample.domain true ∧
    Chapter02ExteriorTangentAffineExample.point 0 0 ∉
      Chapter02ExteriorTangentAffineExample.model.feasibleOn Chapter02ExteriorTangentAffineExample.domain ∧
    (Chapter02ExteriorTangentAffineExample.point 0 1, (0 : ℝ)) ∈ RestorationPairs
      (sourceInitializerDomain Chapter02ExteriorTangentAffineExample.model
        Chapter02ExteriorTangentAffineExample.domain true)
      Chapter02ExteriorTangentAffineExample.model.g ∧
    Chapter02ExteriorTangentAffineExample.point 0 1 ∈
      Chapter02ExteriorTangentAffineExample.model.feasibleOn Chapter02ExteriorTangentAffineExample.domain := by
  let d := Chapter02ExteriorTangentAffineExample.model
  let K := Chapter02ExteriorTangentAffineExample.domain
  let p := Chapter02ExteriorTangentAffineExample.point 0 1
  have href := Chapter02ExteriorTangentAffineExample.affine_reference_control
  have hfeas := (source_feasible_iff d K p).mp
    Chapter02ExteriorTangentAffineExample.affine_feasible_witness
  have hp : (p, (0 : ℝ)) ∈ RestorationPairs (sourceInitializerDomain d K true) d.g :=
    ⟨⟨hfeas.1, hfeas.2.2.1⟩, hfeas.2.1⟩
  refine ⟨⟨href.1, ?_⟩, ?_, ?_, hp, ?_⟩
  · intro j
    norm_num [Chapter02ExteriorTangentAffineExample.model,
      Chapter02ExteriorTangentAffineExample.point]
  · intro h
    exact href.2.1 h.2
  · intro h
    exact href.2.1 ((source_feasible_iff _ _ _).mp h).2.2.1
  · exact source_initializer_feasible d K true hp le_rfl hfeas.2.2.1 hfeas.2.2.2

/-- Empty X reaches the empty-domain consumer without signed attainment. -/
theorem empty_initializer_routing (retainAffine : Bool) :
    sourceInitializerDomain mixedModel ∅ retainAffine = ∅ ∧
    mixedModel.feasibleOn ∅ = ∅ := by
  have he : sourceInitializerDomain mixedModel ∅ retainAffine = ∅ := by
    cases retainAffine <;> simp [sourceInitializerDomain]
  exact ⟨he, source_initializer_empty mixedModel ∅ retainAffine (Or.inl he)⟩

def scalarPoint (x : ℝ) : Point 1 0 := (fun _ => x, fun i => Fin.elim0 i)
def scalarDomain : Set (Point 1 0) := Set.Icc (scalarPoint 0) (scalarPoint 1)
def scalarModel (rowHeight : ℝ) : ModelData 1 0 1 0 where
  g := fun _ _ => rowHeight
  A := fun i => Fin.elim0 i
  B := fun i => Fin.elim0 i
  rhs := fun i => Fin.elim0 i
  c1 := ![1]
  c2 := fun i => Fin.elim0 i
  lo := fun i => Fin.elim0 i
  hi := fun i => Fin.elim0 i

private theorem scalar_affine (h : ℝ) (p : Point 1 0) :
    p ∈ (scalarModel h).linearRegion := by intro i; exact Fin.elim0 i

private theorem scalar_integer (h : ℝ) (p : Point 1 0) :
    p ∈ IntegerCylinder (n := 1) (scalarModel h).lo (scalarModel h).hi := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · funext i; exact Fin.elim0 i

/-- A proved positive universal height bound, not a positive feasible height,
excludes the original feasible set of an actual full model for either selector. -/
theorem positive_bound_original_empty (retainAffine : Bool) :
    IsLowerBound (RestorationPairs
      (sourceInitializerDomain (scalarModel 1) scalarDomain retainAffine) (scalarModel 1).g)
      Prod.snd 1 ∧ (scalarModel 1).feasibleOn scalarDomain = ∅ := by
  have hb : IsLowerBound (RestorationPairs
      (sourceInitializerDomain (scalarModel 1) scalarDomain retainAffine) (scalarModel 1).g)
      Prod.snd 1 := by
    intro q hq
    exact hq.2 0
  exact ⟨hb, source_initializer_empty (scalarModel 1) scalarDomain retainAffine
    (Or.inr ⟨1, by norm_num, hb⟩)⟩

def zeroRowModel : ModelData 1 0 0 0 where
  g := fun i => Fin.elim0 i
  A := fun i => Fin.elim0 i
  B := fun i => Fin.elim0 i
  rhs := fun i => Fin.elim0 i
  c1 := ![1]
  c2 := fun i => Fin.elim0 i
  lo := fun i => Fin.elim0 i
  hi := fun i => Fin.elim0 i

/-- With zero nonlinear rows the original model has a feasible point, while
free height is unbounded below and has no minimizer. No maximum is assigned. -/
theorem zero_row_initializer_bypass :
    scalarPoint 0 ∈ zeroRowModel.feasibleOn scalarDomain ∧
    (∀ v : ℝ, ∃ q ∈ RestorationPairs
      (sourceInitializerDomain zeroRowModel scalarDomain false) zeroRowModel.g, q.2 < v) ∧
    ¬ ∃ q, IsMinimizer (RestorationPairs
      (sourceInitializerDomain zeroRowModel scalarDomain false) zeroRowModel.g) Prod.snd q := by
  have hK : scalarPoint 0 ∈ scalarDomain := by
    norm_num [scalarDomain, scalarPoint, Set.mem_Icc, Prod.le_def, Pi.le_def]
  have hp : (scalarPoint 0, (0 : ℝ)) ∈ RestorationPairs
      (sourceInitializerDomain zeroRowModel scalarDomain false) zeroRowModel.g :=
    ⟨hK, fun j => Fin.elim0 j⟩
  refine ⟨source_initializer_feasible zeroRowModel scalarDomain false hp le_rfl
    (fun i => Fin.elim0 i) ?_,
    restorationPairs_unbounded_empty_rows zeroRowModel.g ⟨scalarPoint 0, hK⟩,
    restorationPairs_no_minimizer_empty_rows _ _⟩
  refine ⟨fun i => Fin.elim0 i, (fun i => Fin.elim0 i), ?_⟩
  funext i; exact Fin.elim0 i

/-- Full-model feasible trial1 has objective1, while feasible0 has objective0.
The actual trial objective is neither a universal lower bound nor a minimum. -/
theorem feasible_only_objective_control :
    scalarPoint 1 ∈ (scalarModel (-1)).feasibleOn scalarDomain ∧
    scalarPoint 0 ∈ (scalarModel (-1)).feasibleOn scalarDomain ∧
    (scalarModel (-1)).objective (scalarPoint 1) = 1 ∧
    (scalarModel (-1)).objective (scalarPoint 0) = 0 ∧
    ¬ IsLowerBound ((scalarModel (-1)).feasibleOn scalarDomain)
      (scalarModel (-1)).objective ((scalarModel (-1)).objective (scalarPoint 1)) ∧
    ¬ IsMinimizer ((scalarModel (-1)).feasibleOn scalarDomain)
      (scalarModel (-1)).objective (scalarPoint 1) := by
  have hf (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
      scalarPoint x ∈ (scalarModel (-1)).feasibleOn scalarDomain := by
    apply source_initializer_feasible (scalarModel (-1)) scalarDomain false
      (h := (-1 : ℝ))
    · refine ⟨?_, fun _ => le_rfl⟩
      simpa [sourceInitializerDomain, scalarDomain, scalarPoint, Set.mem_Icc,
        Prod.le_def, Pi.le_def] using hx
    · norm_num
    · exact scalar_affine _ _
    · exact scalar_integer _ _
  have hzero := hf 0 (by norm_num)
  have hone := hf 1 (by norm_num)
  have ho (x : ℝ) : (scalarModel (-1)).objective (scalarPoint x) = x := by
    simp [ModelData.objective, scalarModel, scalarPoint, LinearForm, Fin.sum_univ_succ]
  refine ⟨hone, hzero, ho 1, ho 0, ?_, ?_⟩
  · intro hb
    have hbad := hb _ hzero
    rw [ho 1, ho 0] at hbad
    norm_num at hbad
  · intro hm
    have hbad := hm.2 _ hzero
    rw [ho 1, ho 0] at hbad
    norm_num at hbad

end Chapter02InitializerSourceExamples

#print axioms Chapter02InitializerSourceExamples.mixed_initializer_attainment
#print axioms Chapter02InitializerSourceExamples.mixed_fractional_initializer
#print axioms Chapter02InitializerSourceExamples.mixed_restored_feasibility
#print axioms Chapter02InitializerSourceExamples.affine_initializer_routing
#print axioms Chapter02InitializerSourceExamples.empty_initializer_routing
#print axioms Chapter02InitializerSourceExamples.positive_bound_original_empty
#print axioms Chapter02InitializerSourceExamples.zero_row_initializer_bypass
#print axioms Chapter02InitializerSourceExamples.feasible_only_objective_control
