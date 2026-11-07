module

public import Chapter02Lifting
public import Chapter02WeightedRestoration
public import Mathlib.Tactic

@[expose] public section

/-! Literal finite ModelData adapter for separable constraints. Original affine
rows, integer box and objective are retained; heights are appended to the
continuous coordinates with zero objective coefficients and no new bounds.
Each component can occur in overlapping original-variable arguments. -/
noncomputable section
open scoped BigOperators
namespace Chapter02

def liftingSourceProject {n m q : ℕ} (z : Point (n+q) m) : Point n m :=
  (weightedX z.1,z.2)
def liftingSourceHeight {n m q : ℕ} (z : Point (n+q) m) : RealVector q := weightedV z.1
def liftingSourceInsert {n m q : ℕ} (x : Point n m) (y : RealVector q) : Point (n+q) m :=
  (weightedInsert x.1 y,x.2)

@[simp] theorem lifting_source_project_insert {n m q : ℕ} (x : Point n m) (y : RealVector q) :
    liftingSourceProject (liftingSourceInsert x y) = x := by simp [liftingSourceProject,liftingSourceInsert]
@[simp] theorem lifting_source_height_insert {n m q : ℕ} (x : Point n m) (y : RealVector q) :
    liftingSourceHeight (liftingSourceInsert x y) = y := by simp [liftingSourceHeight,liftingSourceInsert]

theorem lifting_linearForm_append {n m q : ℕ} (a : RealVector n)
    (c : RealVector q) (b : RealVector m) (z : Point (n+q) m) :
    LinearForm (Fin.addCases a c) b z =
      LinearForm a b (liftingSourceProject z) + ∑ j, c j * liftingSourceHeight z j := by
  simp [LinearForm,Fin.sum_univ_add,liftingSourceProject,liftingSourceHeight,weightedX,weightedV]
  ring

def ModelData.separableLift {n m l r q : ℕ} (d : ModelData n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → RealVector q) :
    ModelData (n+q) m q (r+l) where
  g := fun j z => component j (liftingSourceProject z) - liftingSourceHeight z j
  A := Fin.addCases (fun i => Fin.addCases (d.A i) (fun _ => 0))
    (fun i => Fin.addCases (fun _ => 0) (weight i))
  B := Fin.addCases d.B (fun _ _ => 0)
  rhs := Fin.addCases d.rhs (fun _ => 0)
  c1 := Fin.addCases d.c1 (fun _ => 0)
  c2 := d.c2
  lo := d.lo
  hi := d.hi

@[simp] theorem lifting_source_objective {n m l r q : ℕ} (d : ModelData n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → RealVector q)
    (z : Point (n+q) m) : (d.separableLift component weight).objective z =
      d.objective (liftingSourceProject z) := by
  simp [ModelData.objective,ModelData.separableLift,lifting_linearForm_append]

theorem lifting_source_affine_rows {n m l r q : ℕ} (d : ModelData n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → RealVector q)
    (z : Point (n+q) m) :
    z ∈ (d.separableLift component weight).linearRegion ↔
      liftingSourceProject z ∈ d.linearRegion ∧
        ∀ i, (∑ j, weight i j * liftingSourceHeight z j) ≤ 0 := by
  constructor
  · intro hz
    constructor
    · intro i
      simpa [ModelData.separableLift,lifting_linearForm_append] using hz (i.castAdd l)
    · intro i
      simpa [ModelData.separableLift,lifting_linearForm_append,LinearForm,Fin.sum_univ_add,
        liftingSourceHeight,weightedV] using hz (i.natAdd r)
  · rintro ⟨hl,hb⟩ row
    refine Fin.addCases (fun i => ?_) (fun i => ?_) row
    · simpa [ModelData.separableLift,lifting_linearForm_append] using hl i
    · simpa [ModelData.separableLift,lifting_linearForm_append,LinearForm,Fin.sum_univ_add,
        liftingSourceHeight,weightedV] using hb i

theorem lifting_source_feasible_rows {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (component : Fin q → Point n m → ℝ)
    (weight : Fin l → RealVector q) (z : Point (n+q) m) :
    z ∈ (d.separableLift component weight).feasibleOn (liftingSourceProject ⁻¹' S) ↔
      liftingSourceProject z ∈ S ∧
      (∀ j, component j (liftingSourceProject z) ≤ liftingSourceHeight z j) ∧
      liftingSourceProject z ∈ d.linearRegion ∧
      (∀ i, (∑ j, weight i j * liftingSourceHeight z j) ≤ 0) ∧
      liftingSourceProject z ∈ IntegerCylinder d.lo d.hi := by
  change (((liftingSourceProject z ∈ S ∧
    ∀ j, component j (liftingSourceProject z) - liftingSourceHeight z j ≤ 0) ∧
    z ∈ (d.separableLift component weight).linearRegion) ∧
    liftingSourceProject z ∈ IntegerCylinder d.lo d.hi) ↔ _
  rw [lifting_source_affine_rows]
  simp only [sub_nonpos]
  tauto

theorem lifting_source_project_feasible {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (component : Fin q → Point n m → ℝ)
    (weight : Fin l → RealVector q)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x)
    {z : Point (n+q) m}
    (hz : z ∈ (d.separableLift component weight).feasibleOn (liftingSourceProject ⁻¹' S)) :
    liftingSourceProject z ∈ d.feasibleOn S := by
  obtain ⟨hs,hc,hl,hb,hi⟩ := (lifting_source_feasible_rows d S component weight z).mp hz
  refine ⟨⟨⟨hs,?_⟩,hl⟩,hi⟩
  intro i
  rw [hg]
  exact (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hc j) (hw i j)).trans (hb i)

theorem lifting_source_graph_feasible {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (component : Fin q → Point n m → ℝ)
    (weight : Fin l → RealVector q)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x)
    {x : Point n m} (hx : x ∈ d.feasibleOn S) :
    liftingSourceInsert x (fun j => component j x) ∈
      (d.separableLift component weight).feasibleOn (liftingSourceProject ⁻¹' S) := by
  apply (lifting_source_feasible_rows d S component weight _).mpr
  simp only [lifting_source_project_insert,lifting_source_height_insert]
  exact ⟨hx.1.1.1,fun _ => le_rfl,hx.1.2,fun i => by rw [← hg]; exact hx.1.1.2 i,hx.2⟩

theorem lifting_source_mixed_projection {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (component : Fin q → Point n m → ℝ)
    (weight : Fin l → RealVector q)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) :
    liftingSourceProject '' (d.separableLift component weight).feasibleOn
      (liftingSourceProject ⁻¹' S) = d.feasibleOn S := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩; exact lifting_source_project_feasible d S component weight hw hg hz
  · intro hx
    exact ⟨liftingSourceInsert x (fun j => component j x),
      lifting_source_graph_feasible d S component weight hg hx,lifting_source_project_insert _ _⟩

theorem lifting_source_minimizer_iff {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (component : Fin q → Point n m → ℝ)
    (weight : Fin l → RealVector q)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x)
    (z : Point (n+q) m) :
    IsMinimizer ((d.separableLift component weight).feasibleOn (liftingSourceProject ⁻¹' S))
      (d.separableLift component weight).objective z ↔
      z ∈ (d.separableLift component weight).feasibleOn (liftingSourceProject ⁻¹' S) ∧
      IsMinimizer (d.feasibleOn S) d.objective (liftingSourceProject z) := by
  constructor
  · intro hz
    refine ⟨hz.1,lifting_source_project_feasible d S component weight hw hg hz.1,?_⟩
    intro x hx
    simpa using hz.2 _ (lifting_source_graph_feasible d S component weight hg hx)
  · rintro ⟨hz,hm⟩
    refine ⟨hz,fun z' hz' => ?_⟩
    simpa using hm.2 _ (lifting_source_project_feasible d S component weight hw hg hz')

theorem lifting_source_relaxation_rows {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (component : Fin q → Point n m → ℝ)
    (weight : Fin l → RealVector q) (z : Point (n+q) m) :
    z ∈ (d.separableLift component weight).relaxationOn (liftingSourceProject ⁻¹' S) ↔
      liftingSourceProject z ∈ S ∧
      (∀ j, component j (liftingSourceProject z) ≤ liftingSourceHeight z j) ∧
      liftingSourceProject z ∈ d.linearRegion ∧
      (∀ i, (∑ j, weight i j * liftingSourceHeight z j) ≤ 0) ∧
      (∀ j, d.lo j ≤ z.2 j ∧ z.2 j ≤ d.hi j) := by
  change ((liftingSourceProject z ∈ S ∧
    (∀ j, component j (liftingSourceProject z) - liftingSourceHeight z j ≤ 0)) ∧
    z ∈ (d.separableLift component weight).linearRegion ∧ _) ↔ _
  rw [lifting_source_affine_rows]
  simp only [sub_nonpos]
  tauto

theorem lifting_source_relaxation_projection {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (component : Fin q → Point n m → ℝ)
    (weight : Fin l → RealVector q)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) :
    liftingSourceProject '' (d.separableLift component weight).relaxationOn
      (liftingSourceProject ⁻¹' S) = d.relaxationOn S := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨hs,hc,hl,hb,hi⟩ := (lifting_source_relaxation_rows d S component weight z).mp hz
    refine ⟨⟨hs,fun i => ?_⟩,hl,hi⟩
    rw [hg]
    exact (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hc j) (hw i j)).trans (hb i)
  · intro hx
    refine ⟨liftingSourceInsert x (fun j => component j x),?_,lifting_source_project_insert _ _⟩
    apply (lifting_source_relaxation_rows d S component weight _).mpr
    simp only [lifting_source_project_insert,lifting_source_height_insert]
    exact ⟨hx.1.1,fun _ => le_rfl,hx.2.1,fun i => by rw [← hg]; exact hx.1.2 i,hx.2.2⟩

def liftingAffineArgument {n m : ℕ} (a : RealVector n) (b : RealVector m)
    (offset : ℝ) (x : Point n m) : ℝ := LinearForm a b x + offset

/-- Component differentiability is an explicit premise at the affine argument;
it is not inferred from differentiability of an aggregate constraint. -/
theorem lifting_affine_component_derivative {n m : ℕ} (a : RealVector n)
    (b : RealVector m) (offset : ℝ) (phi : ℝ → ℝ) (slope : ℝ) (x : Point n m)
    (hd : HasDerivAt phi slope (liftingAffineArgument a b offset x)) :
    HasFDerivAt (fun z => phi (liftingAffineArgument a b offset z))
      (slope • linearFormCLM a b) x := by
  have harg : HasFDerivAt (liftingAffineArgument a b offset) (linearFormCLM a b) x :=
    (linearFormCLM a b).hasFDerivAt.add_const offset
  exact hd.comp_hasFDerivAt x harg

def ModelData.normalizedLift {n m l r q : ℕ} (d : ModelData n m l r)
    (a : Fin q → RealVector n) (b : Fin q → RealVector m) (offset : RealVector q)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → RealVector q) :
    ModelData (n+q) m l (r+(q+q)) where
  g := fun i z => ∑ j, weight i j * phi j (liftingSourceHeight z j)
  A := Fin.addCases (fun i => Fin.addCases (d.A i) (fun _ => 0))
    (Fin.addCases (fun j => Fin.addCases (-a j) (Pi.single j 1))
      (fun j => Fin.addCases (a j) (Pi.single j (-1))))
  B := Fin.addCases d.B (Fin.addCases (fun j => -b j) b)
  rhs := Fin.addCases d.rhs (Fin.addCases offset (-offset))
  c1 := Fin.addCases d.c1 (fun _ => 0)
  c2 := d.c2
  lo := d.lo
  hi := d.hi

theorem lifting_normalization_pos_row {n m q : ℕ} (a : RealVector n)
    (b : RealVector m) (j : Fin q) (z : Point (n+q) m) :
    LinearForm (Fin.addCases (-a) (Pi.single j 1)) (-b) z =
      -LinearForm a b (liftingSourceProject z) + liftingSourceHeight z j := by
  rw [lifting_linearForm_append]
  simp [LinearForm,Pi.single_apply,Finset.sum_neg_distrib,neg_add,add_comm]

theorem lifting_normalization_neg_row {n m q : ℕ} (a : RealVector n)
    (b : RealVector m) (j : Fin q) (z : Point (n+q) m) :
    LinearForm (Fin.addCases a (Pi.single j (-1))) b z =
      LinearForm a b (liftingSourceProject z) - liftingSourceHeight z j := by
  rw [lifting_linearForm_append]
  simp [Pi.single_apply,sub_eq_add_neg]

theorem lifting_normalization_affine_rows {n m l r q : ℕ} (d : ModelData n m l r)
    (a : Fin q → RealVector n) (b : Fin q → RealVector m) (offset : RealVector q)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → RealVector q) (z : Point (n+q) m) :
    z ∈ (d.normalizedLift a b offset phi weight).linearRegion ↔
      liftingSourceProject z ∈ d.linearRegion ∧
      ∀ j, liftingSourceHeight z j = liftingAffineArgument (a j) (b j) (offset j) (liftingSourceProject z) := by
  constructor
  · intro hz
    constructor
    · intro i
      simpa [ModelData.normalizedLift,lifting_linearForm_append] using hz (i.castAdd (q+q))
    · intro j
      have hp := hz ((j.castAdd q).natAdd r)
      have hn := hz ((j.natAdd q).natAdd r)
      simp only [ModelData.normalizedLift,Fin.addCases_left,Fin.addCases_right,
        lifting_normalization_pos_row,lifting_normalization_neg_row,Pi.neg_apply] at hp hn
      dsimp [liftingAffineArgument]
      linarith
  · rintro ⟨hl,he⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [ModelData.normalizedLift,lifting_linearForm_append] using hl j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [ModelData.normalizedLift,Fin.addCases_left,Fin.addCases_right,
          lifting_normalization_pos_row]
        rw [he]; dsimp [liftingAffineArgument]; linarith
      · simp only [ModelData.normalizedLift,Fin.addCases_left,Fin.addCases_right,
          lifting_normalization_neg_row,Pi.neg_apply]
        rw [he]; dsimp [liftingAffineArgument]; linarith

@[simp] theorem lifting_normalization_objective {n m l r q : ℕ} (d : ModelData n m l r)
    (a : Fin q → RealVector n) (b : Fin q → RealVector m) (offset : RealVector q)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → RealVector q) (z : Point (n+q) m) :
    (d.normalizedLift a b offset phi weight).objective z = d.objective (liftingSourceProject z) := by
  simp [ModelData.objective,ModelData.normalizedLift,lifting_linearForm_append]

theorem lifting_normalization_feasible_iff {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (a : Fin q → RealVector n) (b : Fin q → RealVector m)
    (offset : RealVector q) (phi : Fin q → ℝ → ℝ) (weight : Fin l → RealVector q)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (liftingAffineArgument (a j) (b j) (offset j) x))
    (z : Point (n+q) m) :
    z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (liftingSourceProject ⁻¹' S) ↔
      liftingSourceProject z ∈ d.feasibleOn S ∧
      ∀ j, liftingSourceHeight z j = liftingAffineArgument (a j) (b j) (offset j) (liftingSourceProject z) := by
  constructor
  · intro hz
    obtain ⟨hl,he⟩ := (lifting_normalization_affine_rows d a b offset phi weight z).mp hz.1.2
    refine ⟨⟨⟨⟨hz.1.1.1,?_⟩,hl⟩,hz.2⟩,he⟩
    intro i
    rw [hg]
    have hi := hz.1.1.2 i
    change (∑ j, weight i j * phi j (liftingSourceHeight z j)) ≤ 0 at hi
    simpa only [he] using hi
  · rintro ⟨hx,he⟩
    refine ⟨⟨⟨hx.1.1.1,?_⟩,(lifting_normalization_affine_rows d a b offset phi weight z).mpr ⟨hx.1.2,he⟩⟩,hx.2⟩
    intro i
    change (∑ j, weight i j * phi j (liftingSourceHeight z j)) ≤ 0
    simpa only [he,← hg] using hx.1.1.2 i

theorem lifting_normalization_projection {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (a : Fin q → RealVector n) (b : Fin q → RealVector m)
    (offset : RealVector q) (phi : Fin q → ℝ → ℝ) (weight : Fin l → RealVector q)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (liftingAffineArgument (a j) (b j) (offset j) x)) :
    liftingSourceProject '' (d.normalizedLift a b offset phi weight).feasibleOn
      (liftingSourceProject ⁻¹' S) = d.feasibleOn S := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ((lifting_normalization_feasible_iff d S a b offset phi weight hg z).mp hz).1
  · intro hx
    refine ⟨liftingSourceInsert x (fun j => liftingAffineArgument (a j) (b j) (offset j) x),?_,lifting_source_project_insert _ _⟩
    apply (lifting_normalization_feasible_iff d S a b offset phi weight hg _).mpr
    simp only [lifting_source_project_insert,lifting_source_height_insert]
    simpa using hx

theorem lifting_normalization_relaxation_iff {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (a : Fin q → RealVector n) (b : Fin q → RealVector m)
    (offset : RealVector q) (phi : Fin q → ℝ → ℝ) (weight : Fin l → RealVector q)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (liftingAffineArgument (a j) (b j) (offset j) x))
    (z : Point (n+q) m) :
    z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (liftingSourceProject ⁻¹' S) ↔
      liftingSourceProject z ∈ d.relaxationOn S ∧
      ∀ j, liftingSourceHeight z j = liftingAffineArgument (a j) (b j) (offset j) (liftingSourceProject z) := by
  constructor
  · intro hz
    obtain ⟨hl,he⟩ := (lifting_normalization_affine_rows d a b offset phi weight z).mp hz.2.1
    refine ⟨⟨⟨hz.1.1,?_⟩,hl,hz.2.2⟩,he⟩
    intro i
    rw [hg]
    have hi := hz.1.2 i
    change (∑ j, weight i j * phi j (liftingSourceHeight z j)) ≤ 0 at hi
    simpa only [he] using hi
  · rintro ⟨hx,he⟩
    refine ⟨⟨hx.1.1,?_⟩,(lifting_normalization_affine_rows d a b offset phi weight z).mpr ⟨hx.2.1,he⟩,hx.2.2⟩
    intro i
    change (∑ j, weight i j * phi j (liftingSourceHeight z j)) ≤ 0
    simpa only [he,← hg] using hx.1.2 i

theorem lifting_normalization_relaxation_projection {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (a : Fin q → RealVector n) (b : Fin q → RealVector m)
    (offset : RealVector q) (phi : Fin q → ℝ → ℝ) (weight : Fin l → RealVector q)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (liftingAffineArgument (a j) (b j) (offset j) x)) :
    liftingSourceProject '' (d.normalizedLift a b offset phi weight).relaxationOn
      (liftingSourceProject ⁻¹' S) = d.relaxationOn S := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ((lifting_normalization_relaxation_iff d S a b offset phi weight hg z).mp hz).1
  · intro hx
    refine ⟨liftingSourceInsert x (fun j => liftingAffineArgument (a j) (b j) (offset j) x),?_,lifting_source_project_insert _ _⟩
    apply (lifting_normalization_relaxation_iff d S a b offset phi weight hg _).mpr
    simp only [lifting_source_project_insert,lifting_source_height_insert]
    simpa using hx

theorem lifting_normalization_minimizer_iff {n m l r q : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (a : Fin q → RealVector n) (b : Fin q → RealVector m)
    (offset : RealVector q) (phi : Fin q → ℝ → ℝ) (weight : Fin l → RealVector q)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (liftingAffineArgument (a j) (b j) (offset j) x))
    (z : Point (n+q) m) :
    IsMinimizer ((d.normalizedLift a b offset phi weight).feasibleOn (liftingSourceProject ⁻¹' S))
      (d.normalizedLift a b offset phi weight).objective z ↔
      z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (liftingSourceProject ⁻¹' S) ∧
      IsMinimizer (d.feasibleOn S) d.objective (liftingSourceProject z) := by
  constructor
  · intro hz
    refine ⟨hz.1,((lifting_normalization_feasible_iff d S a b offset phi weight hg z).mp hz.1).1,?_⟩
    intro x hx
    have hp : x ∈ liftingSourceProject '' (d.normalizedLift a b offset phi weight).feasibleOn
        (liftingSourceProject ⁻¹' S) := by rw [lifting_normalization_projection d S a b offset phi weight hg]; exact hx
    obtain ⟨w,hw,rfl⟩ := hp
    simpa using hz.2 w hw
  · rintro ⟨hz,hm⟩
    refine ⟨hz,fun w hw => ?_⟩
    simpa using hm.2 _ (((lifting_normalization_feasible_iff d S a b offset phi weight hg w).mp hw).1)

end Chapter02

#print axioms Chapter02.lifting_source_project_insert
#print axioms Chapter02.lifting_source_height_insert
#print axioms Chapter02.lifting_linearForm_append
#print axioms Chapter02.lifting_source_objective
#print axioms Chapter02.lifting_source_affine_rows
#print axioms Chapter02.lifting_source_feasible_rows
#print axioms Chapter02.lifting_source_project_feasible
#print axioms Chapter02.lifting_source_graph_feasible
#print axioms Chapter02.lifting_source_mixed_projection
#print axioms Chapter02.lifting_source_minimizer_iff
#print axioms Chapter02.lifting_source_relaxation_rows
#print axioms Chapter02.lifting_source_relaxation_projection
#print axioms Chapter02.lifting_affine_component_derivative
#print axioms Chapter02.lifting_normalization_pos_row
#print axioms Chapter02.lifting_normalization_neg_row
#print axioms Chapter02.lifting_normalization_affine_rows
#print axioms Chapter02.lifting_normalization_objective
#print axioms Chapter02.lifting_normalization_feasible_iff
#print axioms Chapter02.lifting_normalization_projection
#print axioms Chapter02.lifting_normalization_relaxation_iff
#print axioms Chapter02.lifting_normalization_relaxation_projection
#print axioms Chapter02.lifting_normalization_minimizer_iff
