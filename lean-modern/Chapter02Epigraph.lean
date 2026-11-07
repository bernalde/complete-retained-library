module

public import Chapter02Model
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Literal finite-dimensional epigraph construction for a nonlinear objective.
The original ModelData objective coefficients are irrelevant to feasibility;
`f` is the objective to be replaced. The extra coordinate is continuous, at
index zero. Bounded-height variants are explicit repairs, not an assertion
that the usual unbounded epigraph preserves compactness. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

def epiProject {n m : ℕ} (p : Point (n+1) m) : Point n m := (Fin.tail p.1, p.2)
def epiHeight {n m : ℕ} (p : Point (n+1) m) : ℝ := p.1 0
def epiInsert {n m : ℕ} (p : Point n m) (t : ℝ) : Point (n+1) m :=
  (Fin.cons t p.1, p.2)

@[simp] theorem epiProject_insert {n m : ℕ} (p : Point n m) (t : ℝ) :
    epiProject (epiInsert p t) = p := by simp [epiProject, epiInsert]
@[simp] theorem epiHeight_insert {n m : ℕ} (p : Point n m) (t : ℝ) :
    epiHeight (epiInsert p t) = t := by simp [epiHeight, epiInsert]
@[simp] theorem epiInsert_project_height {n m : ℕ} (p : Point (n+1) m) :
    epiInsert (epiProject p) (epiHeight p) = p := by
  rcases p with ⟨x,y⟩
  simp [epiInsert, epiProject, epiHeight]

def ModelData.epigraphModel {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) : ModelData (n+1) m (l+1) r where
  g := Fin.cons (fun p => f (epiProject p) - epiHeight p) (fun j p => d.g j (epiProject p))
  A := fun row => Fin.cons 0 (d.A row)
  B := d.B
  rhs := d.rhs
  c1 := Fin.cons 1 (fun _ => 0)
  c2 := fun _ => 0
  lo := d.lo
  hi := d.hi

@[simp] theorem linearForm_prepend_zero {n m : ℕ}
    (a : RealVector n) (b : RealVector m) (p : Point (n+1) m) :
    LinearForm (Fin.cons 0 a) b p = LinearForm a b (epiProject p) := by
  simp [LinearForm, Fin.sum_univ_succ, epiProject, Fin.tail]

@[simp] theorem epigraphModel_objective {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (p : Point (n+1) m) :
    (d.epigraphModel f).objective p = epiHeight p := by
  simp [ModelData.objective, ModelData.epigraphModel, LinearForm,
    Fin.sum_univ_succ, epiHeight]

theorem epigraphModel_feasible_iff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (p : Point (n+1) m) :
    p ∈ (d.epigraphModel f).feasibleOn (epiProject ⁻¹' S) ↔
      epiProject p ∈ d.feasibleOn S ∧ f (epiProject p) ≤ epiHeight p := by
  rw [source_feasible_iff, source_feasible_iff]
  simp only [Set.mem_preimage, ModelData.epigraphModel, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, sub_nonpos, linearForm_prepend_zero]
  simp only [epiProject]
  tauto

theorem epigraphModel_nonempty_iff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) :
    ((d.epigraphModel f).feasibleOn (epiProject ⁻¹' S)).Nonempty ↔
      (d.feasibleOn S).Nonempty := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨epiProject p, ((epigraphModel_feasible_iff d f S p).mp hp).1⟩
  · rintro ⟨p,hp⟩
    refine ⟨epiInsert p (f p), (epigraphModel_feasible_iff d f S _).mpr ?_⟩
    simpa using And.intro hp (le_refl (f p))

theorem epigraphModel_minimizer_iff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (p : Point (n+1) m) :
    IsMinimizer ((d.epigraphModel f).feasibleOn (epiProject ⁻¹' S))
        (d.epigraphModel f).objective p ↔
      IsMinimizer (d.feasibleOn S) f (epiProject p) ∧
        epiHeight p = f (epiProject p) := by
  constructor
  · rintro ⟨hp,hmin⟩
    obtain ⟨hproj,hheight⟩ := (epigraphModel_feasible_iff d f S p).mp hp
    have hgraph (x : Point n m) (hx : x ∈ d.feasibleOn S) :
        epiInsert x (f x) ∈ (d.epigraphModel f).feasibleOn (epiProject ⁻¹' S) := by
      apply (epigraphModel_feasible_iff d f S _).mpr
      simpa using And.intro hx (le_refl (f x))
    have htight : epiHeight p = f (epiProject p) := by
      have hh := hmin _ (hgraph _ hproj)
      simp only [epigraphModel_objective, epiHeight_insert] at hh
      exact le_antisymm hh hheight
    refine ⟨⟨hproj, fun x hx => ?_⟩, htight⟩
    have hh := hmin _ (hgraph x hx)
    simpa only [epigraphModel_objective, epiHeight_insert, htight] using hh
  · rintro ⟨⟨hp,hmin⟩, htight⟩
    refine ⟨(epigraphModel_feasible_iff d f S _).mpr ⟨hp, le_of_eq htight.symm⟩, ?_⟩
    intro q hq
    obtain ⟨hqproj,hqheight⟩ := (epigraphModel_feasible_iff d f S q).mp hq
    simpa only [epigraphModel_objective, htight] using (hmin _ hqproj).trans hqheight

theorem epigraphModel_lift_minimizer {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) {p : Point n m}
    (hp : IsMinimizer (d.feasibleOn S) f p) :
    IsMinimizer ((d.epigraphModel f).feasibleOn (epiProject ⁻¹' S))
      (d.epigraphModel f).objective (epiInsert p (f p)) := by
  apply (epigraphModel_minimizer_iff d f S _).mpr
  simpa using And.intro hp (rfl : f p = f p)

/-- Two additional literal linear rows are -t ≤ -low and t ≤ high. -/
def ModelData.boundedEpigraphModel {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (low high : ℝ) : ModelData (n+1) m (l+1) (r+2) where
  g := (d.epigraphModel f).g
  A := Fin.cons (Fin.cons (-1) (fun _ => 0))
    (Fin.cons (Fin.cons 1 (fun _ => 0)) (d.epigraphModel f).A)
  B := Fin.cons (fun _ => 0) (Fin.cons (fun _ => 0) d.B)
  rhs := Fin.cons (-low) (Fin.cons high d.rhs)
  c1 := (d.epigraphModel f).c1
  c2 := (d.epigraphModel f).c2
  lo := d.lo
  hi := d.hi

@[simp] theorem linearForm_height {n m : ℕ} (a : ℝ) (p : Point (n+1) m) :
    LinearForm (Fin.cons a (fun _ => 0)) (fun _ => 0) p = a * epiHeight p := by
  simp [LinearForm, Fin.sum_univ_succ, epiHeight]

@[simp] theorem boundedEpigraphModel_objective {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (low high : ℝ) (p : Point (n+1) m) :
    (d.boundedEpigraphModel f low high).objective p = epiHeight p :=
  epigraphModel_objective d f p

theorem boundedEpigraphModel_feasible_iff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (low high : ℝ) (p : Point (n+1) m) :
    p ∈ (d.boundedEpigraphModel f low high).feasibleOn (epiProject ⁻¹' S) ↔
      epiProject p ∈ d.feasibleOn S ∧ f (epiProject p) ≤ epiHeight p ∧
        low ≤ epiHeight p ∧ epiHeight p ≤ high := by
  rw [source_feasible_iff, source_feasible_iff]
  simp only [Set.mem_preimage, ModelData.boundedEpigraphModel, ModelData.epigraphModel,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, sub_nonpos,
    linearForm_prepend_zero, linearForm_height, neg_one_mul, one_mul, neg_le_neg_iff]
  simp only [epiProject]
  tauto

theorem boundedEpigraphModel_minimizer_iff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (low high : ℝ)
    (hb : ∀ x ∈ d.feasibleOn S, low ≤ f x ∧ f x ≤ high) (p : Point (n+1) m) :
    IsMinimizer ((d.boundedEpigraphModel f low high).feasibleOn (epiProject ⁻¹' S))
        (d.boundedEpigraphModel f low high).objective p ↔
      IsMinimizer (d.feasibleOn S) f (epiProject p) ∧ epiHeight p = f (epiProject p) := by
  constructor
  · rintro ⟨hp,hmin⟩
    obtain ⟨hproj,hheight,_⟩ := (boundedEpigraphModel_feasible_iff d f S low high p).mp hp
    have hgraph (x : Point n m) (hx : x ∈ d.feasibleOn S) :
        epiInsert x (f x) ∈
          (d.boundedEpigraphModel f low high).feasibleOn (epiProject ⁻¹' S) := by
      apply (boundedEpigraphModel_feasible_iff d f S low high _).mpr
      simpa using And.intro hx (And.intro (le_refl (f x)) (hb x hx))
    have htight : epiHeight p = f (epiProject p) := by
      have hh := hmin _ (hgraph _ hproj)
      simp only [boundedEpigraphModel_objective, epiHeight_insert] at hh
      exact le_antisymm hh hheight
    refine ⟨⟨hproj, fun x hx => ?_⟩, htight⟩
    have hh := hmin _ (hgraph x hx)
    simpa only [boundedEpigraphModel_objective, epiHeight_insert, htight] using hh
  · rintro ⟨⟨hp,hmin⟩, htight⟩
    refine ⟨(boundedEpigraphModel_feasible_iff d f S low high _).mpr ?_, ?_⟩
    · exact ⟨hp, le_of_eq htight.symm, by simpa only [htight] using hb _ hp⟩
    · intro q hq
      obtain ⟨hqproj,hqheight,_⟩ :=
        (boundedEpigraphModel_feasible_iff d f S low high q).mp hq
      simpa only [boundedEpigraphModel_objective, htight] using (hmin _ hqproj).trans hqheight


theorem epiProject_affine {n m : ℕ} (p q : Point (n+1) m) (a b : ℝ) :
    epiProject (a • p + b • q) = a • epiProject p + b • epiProject q := by
  rfl

theorem epiHeight_affine {n m : ℕ} (p q : Point (n+1) m) (a b : ℝ) :
    epiHeight (a • p + b • q) = a * epiHeight p + b * epiHeight q := by
  rfl

theorem epiProject_preimage_convex {n m : ℕ} {S : Set (Point n m)}
    (hS : Convex ℝ S) : Convex ℝ (epiProject ⁻¹' S) := by
  intro p hp q hq a b ha hb hab
  change epiProject (a • p + b • q) ∈ S
  rw [epiProject_affine]
  exact hS hp hq ha hb hab

theorem epigraphModel_rows_convex {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m))
    (hf : ConvexOn ℝ S f) (hg : ∀ j, ConvexOn ℝ S (d.g j)) :
    ∀ j, ConvexOn ℝ (epiProject ⁻¹' S) ((d.epigraphModel f).g j) := by
  intro j
  refine ⟨epiProject_preimage_convex hf.1, ?_⟩
  intro p hp q hq a b ha hb hab
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [ModelData.epigraphModel, Fin.cons_zero, epiProject_affine, epiHeight_affine,
      smul_eq_mul]
    have h := hf.2 hp hq ha hb hab
    simp only [smul_eq_mul] at h
    nlinarith
  · simpa only [ModelData.epigraphModel, Fin.cons_succ, epiProject_affine] using
      (hg j).2 hp hq ha hb hab

theorem epigraphModel_relaxation_convex {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m))
    (hf : ConvexOn ℝ S f) (hg : ∀ j, ConvexOn ℝ S (d.g j)) :
    Convex ℝ ((d.epigraphModel f).relaxationOn (epiProject ⁻¹' S)) :=
  source_relaxation_convex_on _ _ (epiProject_preimage_convex hf.1)
    (epigraphModel_rows_convex d f S hf hg)

theorem boundedEpigraphModel_rows_convex {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (low high : ℝ)
    (hf : ConvexOn ℝ S f) (hg : ∀ j, ConvexOn ℝ S (d.g j)) :
    ∀ j, ConvexOn ℝ (epiProject ⁻¹' S) ((d.boundedEpigraphModel f low high).g j) :=
  epigraphModel_rows_convex d f S hf hg

theorem boundedEpigraphModel_relaxation_convex {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (low high : ℝ)
    (hf : ConvexOn ℝ S f) (hg : ∀ j, ConvexOn ℝ S (d.g j)) :
    Convex ℝ ((d.boundedEpigraphModel f low high).relaxationOn (epiProject ⁻¹' S)) :=
  source_relaxation_convex_on _ _ (epiProject_preimage_convex hf.1)
    (boundedEpigraphModel_rows_convex d f S low high hf hg)

theorem epiProject_contDiff {n m : ℕ} (k : WithTop ℕ∞) :
    ContDiff ℝ k (@epiProject n m) := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    exact (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) i.succ).comp contDiff_fst
  · exact contDiff_snd

theorem epiHeight_contDiff {n m : ℕ} (k : WithTop ℕ∞) :
    ContDiff ℝ k (@epiHeight n m) := by
  exact (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) 0).comp contDiff_fst

theorem epiInsert_continuous {n m : ℕ} :
    Continuous (fun q : Point n m × ℝ => epiInsert q.1 q.2) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [epiInsert, Function.comp_def] using (continuous_snd : Continuous (Prod.snd : Point n m × ℝ → ℝ))
    · simpa [epiInsert, Function.comp_def] using
        ((continuous_apply j).comp (continuous_fst.comp continuous_fst) :
          Continuous (fun q : Point n m × ℝ => q.1.1 j))
  · exact continuous_snd.comp continuous_fst

theorem epigraphModel_rows_contDiff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (k : WithTop ℕ∞)
    (hf : ContDiff ℝ k f) (hg : ∀ j, ContDiff ℝ k (d.g j)) :
    ∀ j, ContDiff ℝ k ((d.epigraphModel f).g j) := by
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact (hf.comp (epiProject_contDiff k)).sub (epiHeight_contDiff k)
  · exact (hg j).comp (epiProject_contDiff k)

theorem boundedEpigraphModel_rows_contDiff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (low high : ℝ) (k : WithTop ℕ∞)
    (hf : ContDiff ℝ k f) (hg : ∀ j, ContDiff ℝ k (d.g j)) :
    ∀ j, ContDiff ℝ k ((d.boundedEpigraphModel f low high).g j) :=
  epigraphModel_rows_contDiff d f k hf hg

/-- The feasible set is the continuous insertion-image of the generic bounded
 epigraph. This is a typed-model equality, not a relabeling of the objective. -/
theorem boundedEpigraphModel_feasible_eq_image {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (low high : ℝ) :
    (d.boundedEpigraphModel f low high).feasibleOn (epiProject ⁻¹' S) =
      (fun q : Point n m × ℝ => epiInsert q.1 q.2) ''
        BoundedEpigraph (d.feasibleOn S) f low high := by
  ext p
  constructor
  · intro hp
    have hh := (boundedEpigraphModel_feasible_iff d f S low high p).mp hp
    exact ⟨(epiProject p, epiHeight p), hh, epiInsert_project_height p⟩
  · rintro ⟨⟨q,t⟩,hq,rfl⟩
    apply (boundedEpigraphModel_feasible_iff d f S low high _).mpr
    simpa only [BoundedEpigraph, Set.mem_setOf_eq, epiProject_insert, epiHeight_insert] using hq

theorem boundedEpigraphModel_feasible_compact {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (low high : ℝ)
    (hS : IsCompact (d.feasibleOn S)) (hf : ContinuousOn f (d.feasibleOn S)) :
    IsCompact ((d.boundedEpigraphModel f low high).feasibleOn (epiProject ⁻¹' S)) := by
  rw [boundedEpigraphModel_feasible_eq_image]
  exact (bounded_epigraph_compact hS hf low high).image epiInsert_continuous

theorem boundedEpigraphModel_nonempty_iff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (S : Set (Point n m)) (low high : ℝ)
    (hb : ∀ x ∈ d.feasibleOn S, low ≤ f x ∧ f x ≤ high) :
    ((d.boundedEpigraphModel f low high).feasibleOn (epiProject ⁻¹' S)).Nonempty ↔
      (d.feasibleOn S).Nonempty := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨epiProject p, ((boundedEpigraphModel_feasible_iff d f S low high p).mp hp).1⟩
  · rintro ⟨p,hp⟩
    refine ⟨epiInsert p (f p), (boundedEpigraphModel_feasible_iff d f S low high _).mpr ?_⟩
    simpa only [epiProject_insert, epiHeight_insert] using
      And.intro hp (And.intro (le_refl (f p)) (hb p hp))


theorem boundedEpigraphModel_linearRegion_iff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (low high : ℝ) (p : Point (n+1) m) :
    p ∈ (d.boundedEpigraphModel f low high).linearRegion ↔
      epiProject p ∈ d.linearRegion ∧ low ≤ epiHeight p ∧ epiHeight p ≤ high := by
  simp only [ModelData.linearRegion, Set.mem_setOf_eq, ModelData.boundedEpigraphModel,
    ModelData.epigraphModel, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    linearForm_prepend_zero, linearForm_height, neg_one_mul, one_mul, neg_le_neg_iff]
  tauto

/-- Compactness preservation concerns the literal lifted linear/integer base,
not only its subset satisfying the nonlinear rows. Integer coordinates and
integer bounds are identical; the added height is continuous. -/
theorem boundedEpigraphModel_base_eq_image {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (low high : ℝ) :
    (d.boundedEpigraphModel f low high).linearRegion ∩
        IntegerCylinder (n := n+1) d.lo d.hi =
      (fun q : Point n m × ℝ => epiInsert q.1 q.2) ''
        ((d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) ×ˢ Set.Icc low high) := by
  ext p
  constructor
  · rintro ⟨hL,hY⟩
    obtain ⟨hL,hlo,hhi⟩ := (boundedEpigraphModel_linearRegion_iff d f low high p).mp hL
    exact ⟨(epiProject p, epiHeight p), ⟨⟨hL,hY⟩,hlo,hhi⟩, epiInsert_project_height p⟩
  · rintro ⟨⟨q,t⟩,⟨⟨hL,hY⟩,hlo,hhi⟩,rfl⟩
    refine ⟨(boundedEpigraphModel_linearRegion_iff d f low high _).mpr ?_, hY⟩
    simpa only [epiProject_insert, epiHeight_insert] using And.intro hL (And.intro hlo hhi)

theorem boundedEpigraphModel_base_compact {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (low high : ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi)) :
    IsCompact ((d.boundedEpigraphModel f low high).linearRegion ∩
      IntegerCylinder (n := n+1) (d.boundedEpigraphModel f low high).lo
        (d.boundedEpigraphModel f low high).hi) := by
  change IsCompact ((d.boundedEpigraphModel f low high).linearRegion ∩
    IntegerCylinder (n := n+1) d.lo d.hi)
  rw [boundedEpigraphModel_base_eq_image]
  exact (hbase.prod isCompact_Icc).image epiInsert_continuous

/-- A continuous nonlinear objective on the original nonempty compact feasible
set admits finite valid height bounds. The resulting literal ModelData has a
compact linear/integer base, is nonempty, and has exactly the original
minimizers with tight auxiliary height. No computable bounds are asserted. -/
theorem boundedEpigraphModel_exists {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j)) (hf : ContinuousOn f (d.feasibleOn Set.univ))
    (hne : (d.feasibleOn Set.univ).Nonempty) :
    ∃ low high : ℝ,
      (∀ x ∈ d.feasibleOn Set.univ, low ≤ f x ∧ f x ≤ high) ∧
      IsCompact ((d.boundedEpigraphModel f low high).linearRegion ∩
        IntegerCylinder (n := n+1) (d.boundedEpigraphModel f low high).lo
          (d.boundedEpigraphModel f low high).hi) ∧
      IsCompact ((d.boundedEpigraphModel f low high).feasibleOn Set.univ) ∧
      ((d.boundedEpigraphModel f low high).feasibleOn Set.univ).Nonempty ∧
      (∀ p, IsMinimizer ((d.boundedEpigraphModel f low high).feasibleOn Set.univ)
          (d.boundedEpigraphModel f low high).objective p ↔
        IsMinimizer (d.feasibleOn Set.univ) f (epiProject p) ∧
          epiHeight p = f (epiProject p)) := by
  have hc := source_feasible_compact d hbase hg
  obtain ⟨low,high,hb⟩ := compact_objective_bounds hc hne hf
  refine ⟨low,high,hb,boundedEpigraphModel_base_compact d f low high hbase, ?_, ?_, ?_⟩
  · simpa only [Set.preimage_univ] using
      boundedEpigraphModel_feasible_compact d f Set.univ low high hc hf
  · simpa only [Set.preimage_univ] using
      (boundedEpigraphModel_nonempty_iff d f Set.univ low high hb).mpr hne
  · intro p
    simpa only [Set.preimage_univ] using
      boundedEpigraphModel_minimizer_iff d f Set.univ low high hb p


/-- The coordinate deletion map as an actual continuous linear map, so
Fréchet derivatives of new rows can be used directly by tangent families. -/
def epiProjectCLM {n m : ℕ} : Point (n+1) m →L[ℝ] Point n m where
  toFun := epiProject
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := (epiProject_contDiff 1).continuous

def epiHeightCLM {n m : ℕ} : Point (n+1) m →L[ℝ] ℝ where
  toFun := epiHeight
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := (epiHeight_contDiff 1).continuous

def epigraphDerivative {n m : ℕ} (D : Point n m →L[ℝ] ℝ) :
    Point (n+1) m →L[ℝ] ℝ := D.comp epiProjectCLM - epiHeightCLM

theorem epigraphModel_hasFDerivAt {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (p : Point (n+1) m) (D : Point n m →L[ℝ] ℝ)
    (hf : HasFDerivAt f D (epiProject p)) :
    HasFDerivAt ((d.epigraphModel f).g 0) (epigraphDerivative D) p :=
  (hf.comp p epiProjectCLM.hasFDerivAt).sub epiHeightCLM.hasFDerivAt

theorem epigraphModel_oldRow_hasFDerivAt {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (p : Point (n+1) m) (j : Fin l) (D : Point n m →L[ℝ] ℝ)
    (hg : HasFDerivAt (d.g j) D (epiProject p)) :
    HasFDerivAt ((d.epigraphModel f).g j.succ) (D.comp epiProjectCLM) p :=
  hg.comp p epiProjectCLM.hasFDerivAt

theorem boundedEpigraphModel_hasFDerivAt {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (low high : ℝ) (p : Point (n+1) m)
    (D : Point n m →L[ℝ] ℝ) (hf : HasFDerivAt f D (epiProject p)) :
    HasFDerivAt ((d.boundedEpigraphModel f low high).g 0) (epigraphDerivative D) p :=
  epigraphModel_hasFDerivAt d f p D hf

theorem epigraphDerivative_apply {n m : ℕ} (D : Point n m →L[ℝ] ℝ)
    (v : Point (n+1) m) : epigraphDerivative D v = D (epiProject v) - epiHeight v := rfl

theorem epigraphDerivative_insert {n m : ℕ} (D : Point n m →L[ℝ] ℝ)
    (v : Point n m) (dt : ℝ) : epigraphDerivative D (epiInsert v dt) = D v - dt := by
  simp only [epigraphDerivative_apply, epiProject_insert, epiHeight_insert]

theorem epigraphModel_tangent_identity {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (D : Point n m →L[ℝ] ℝ) (p q : Point (n+1) m) :
    (d.epigraphModel f).g 0 p + epigraphDerivative D (q - p) =
      f (epiProject p) + D (epiProject q - epiProject p) - epiHeight q := by
  change f (epiProject p) - epiHeight p +
    (D (epiProject (q-p)) - epiHeight (q-p)) = _
  have hproj : epiProject (q-p) = epiProject q - epiProject p := rfl
  have hheight : epiHeight (q-p) = epiHeight q - epiHeight p := rfl
  rw [hproj, hheight]
  ring

theorem epigraphModel_tangent_insert {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (D : Point n m →L[ℝ] ℝ)
    (q x : Point n m) (s t : ℝ) :
    (d.epigraphModel f).g 0 (epiInsert q s) +
        epigraphDerivative D (epiInsert x t - epiInsert q s) = f q + D (x-q) - t := by
  simpa only [epiProject_insert, epiHeight_insert] using
    epigraphModel_tangent_identity d f D (epiInsert q s) (epiInsert x t)

theorem epigraphModel_linearRegion_iff {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (p : Point (n+1) m) :
    p ∈ (d.epigraphModel f).linearRegion ↔ epiProject p ∈ d.linearRegion := by
  simp only [ModelData.linearRegion, Set.mem_setOf_eq, ModelData.epigraphModel,
    linearForm_prepend_zero]

/-- The particular lift with unrestricted height has a noncompact linear/integer
base whenever the original base is nonempty. This does not refute the existence
of an equivalent linear-objective formulation with valid height bounds. -/
theorem epigraphModel_base_not_compact {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ)
    (hne : (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi).Nonempty) :
    ¬ IsCompact ((d.epigraphModel f).linearRegion ∩
      IntegerCylinder (n := n+1) (d.epigraphModel f).lo (d.epigraphModel f).hi) := by
  intro hc
  obtain ⟨z,hzL,hzY⟩ := hne
  obtain ⟨u,hu⟩ := (hc.image (epiHeight_contDiff 1).continuous).bddAbove
  have hL : epiInsert z (u+1) ∈ (d.epigraphModel f).linearRegion := by
    apply (epigraphModel_linearRegion_iff d f _).mpr
    simpa only [epiProject_insert] using hzL
  have hY : epiInsert z (u+1) ∈
      IntegerCylinder (n := n+1) (d.epigraphModel f).lo (d.epigraphModel f).hi := hzY
  have hbound : epiHeight (epiInsert z (u+1)) ≤ u := hu ⟨_, ⟨hL,hY⟩, rfl⟩
  simp only [epiHeight_insert] at hbound
  linarith

/-- Strict nonlinear feasibility of an ESH starting point requires an upper
height strictly larger than its objective, even if it lies outside the integer
box. Bounds merely preserving original mixed-feasible points do not imply this. -/
theorem boundedEpigraphModel_strict_start {n m l r : ℕ} (d : ModelData n m l r)
    (f : Point n m → ℝ) (low high : ℝ) (z : Point n m)
    (hL : z ∈ d.linearRegion) (hg : ∀ j, d.g j z < 0)
    (hlohi : low ≤ high) (hf : f z < high) :
    epiInsert z high ∈ (d.boundedEpigraphModel f low high).linearRegion ∧
      ∀ j, (d.boundedEpigraphModel f low high).g j (epiInsert z high) < 0 := by
  constructor
  · apply (boundedEpigraphModel_linearRegion_iff d f low high _).mpr
    simpa only [epiProject_insert, epiHeight_insert] using
      And.intro hL (And.intro hlohi (le_refl high))
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [ModelData.boundedEpigraphModel, ModelData.epigraphModel, Fin.cons_zero,
        epiProject_insert, epiHeight_insert, sub_neg] using hf
    · simpa only [ModelData.boundedEpigraphModel, ModelData.epigraphModel, Fin.cons_succ,
        epiProject_insert] using hg j


/-- Full linear-objective representation in the source's compact, jointly
convex, C¹ model class, including infeasible models. Valid finite height bounds
are selected classically; in the empty-feasible case zero bounds suffice.
The new nonlinear rows retain joint convexity and C¹ regularity. -/
theorem boundedEpigraphModel_representation_exists {n m l r : ℕ}
    (d : ModelData n m l r) (f : Point n m → ℝ)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hfconv : ConvexOn ℝ Set.univ f)
    (hgconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hfC1 : ContDiff ℝ 1 f) (hgC1 : ∀ j, ContDiff ℝ 1 (d.g j)) :
    ∃ low high : ℝ,
      low ≤ high ∧
      (∀ x ∈ d.feasibleOn Set.univ, low ≤ f x ∧ f x ≤ high) ∧
      IsCompact ((d.boundedEpigraphModel f low high).linearRegion ∩
        IntegerCylinder (n := n+1) (d.boundedEpigraphModel f low high).lo
          (d.boundedEpigraphModel f low high).hi) ∧
      IsCompact ((d.boundedEpigraphModel f low high).feasibleOn Set.univ) ∧
      (((d.boundedEpigraphModel f low high).feasibleOn Set.univ).Nonempty ↔
        (d.feasibleOn Set.univ).Nonempty) ∧
      (∀ p, IsMinimizer ((d.boundedEpigraphModel f low high).feasibleOn Set.univ)
          (d.boundedEpigraphModel f low high).objective p ↔
        IsMinimizer (d.feasibleOn Set.univ) f (epiProject p) ∧
          epiHeight p = f (epiProject p)) ∧
      (∀ j, ConvexOn ℝ Set.univ ((d.boundedEpigraphModel f low high).g j)) ∧
      (∀ j, ContDiff ℝ 1 ((d.boundedEpigraphModel f low high).g j)) := by
  have hc := source_feasible_compact d hbase (fun j => (hgC1 j).continuous)
  have hf := hfC1.continuous.continuousOn (s := d.feasibleOn Set.univ)
  obtain ⟨low,high,horder,hb⟩ : ∃ low high : ℝ,
      low ≤ high ∧ ∀ x ∈ d.feasibleOn Set.univ, low ≤ f x ∧ f x ≤ high := by
    by_cases hne : (d.feasibleOn Set.univ).Nonempty
    · obtain ⟨low,high,hb⟩ := compact_objective_bounds hc hne hf
      obtain ⟨x,hx⟩ := hne
      exact ⟨low,high,(hb x hx).1.trans (hb x hx).2,hb⟩
    · exact ⟨0,0,le_rfl,fun x hx => False.elim (hne ⟨x,hx⟩)⟩
  refine ⟨low,high,horder,hb,boundedEpigraphModel_base_compact d f low high hbase,
    ?_, ?_, ?_, ?_, boundedEpigraphModel_rows_contDiff d f low high 1 hfC1 hgC1⟩
  · simpa only [Set.preimage_univ] using
      boundedEpigraphModel_feasible_compact d f Set.univ low high hc hf
  · simpa only [Set.preimage_univ] using
      boundedEpigraphModel_nonempty_iff d f Set.univ low high hb
  · intro p
    simpa only [Set.preimage_univ] using
      boundedEpigraphModel_minimizer_iff d f Set.univ low high hb p
  · simpa only [Set.preimage_univ] using
      boundedEpigraphModel_rows_convex d f Set.univ low high hfconv hgconv

end Chapter02

#print axioms Chapter02.epiProject_insert
#print axioms Chapter02.epiHeight_insert
#print axioms Chapter02.epiInsert_project_height
#print axioms Chapter02.linearForm_prepend_zero
#print axioms Chapter02.epigraphModel_objective
#print axioms Chapter02.epigraphModel_feasible_iff
#print axioms Chapter02.epigraphModel_nonempty_iff
#print axioms Chapter02.epigraphModel_minimizer_iff
#print axioms Chapter02.epigraphModel_lift_minimizer
#print axioms Chapter02.linearForm_height
#print axioms Chapter02.boundedEpigraphModel_objective
#print axioms Chapter02.boundedEpigraphModel_feasible_iff
#print axioms Chapter02.boundedEpigraphModel_minimizer_iff
#print axioms Chapter02.epiProject_affine
#print axioms Chapter02.epiHeight_affine
#print axioms Chapter02.epiProject_preimage_convex
#print axioms Chapter02.epigraphModel_rows_convex
#print axioms Chapter02.epigraphModel_relaxation_convex
#print axioms Chapter02.boundedEpigraphModel_rows_convex
#print axioms Chapter02.boundedEpigraphModel_relaxation_convex
#print axioms Chapter02.epiProject_contDiff
#print axioms Chapter02.epiHeight_contDiff
#print axioms Chapter02.epiInsert_continuous
#print axioms Chapter02.epigraphModel_rows_contDiff
#print axioms Chapter02.boundedEpigraphModel_rows_contDiff
#print axioms Chapter02.boundedEpigraphModel_feasible_eq_image
#print axioms Chapter02.boundedEpigraphModel_feasible_compact
#print axioms Chapter02.boundedEpigraphModel_nonempty_iff
#print axioms Chapter02.boundedEpigraphModel_linearRegion_iff
#print axioms Chapter02.boundedEpigraphModel_base_eq_image
#print axioms Chapter02.boundedEpigraphModel_base_compact
#print axioms Chapter02.boundedEpigraphModel_exists
#print axioms Chapter02.epigraphModel_hasFDerivAt
#print axioms Chapter02.epigraphModel_oldRow_hasFDerivAt
#print axioms Chapter02.boundedEpigraphModel_hasFDerivAt
#print axioms Chapter02.epigraphDerivative_apply
#print axioms Chapter02.epigraphDerivative_insert
#print axioms Chapter02.epigraphModel_tangent_identity
#print axioms Chapter02.epigraphModel_tangent_insert
#print axioms Chapter02.epigraphModel_linearRegion_iff
#print axioms Chapter02.epigraphModel_base_not_compact
#print axioms Chapter02.boundedEpigraphModel_strict_start

#print axioms Chapter02.boundedEpigraphModel_representation_exists
