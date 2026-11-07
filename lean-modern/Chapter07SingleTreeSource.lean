module

public import Chapter06LevelModel
public import Chapter02STSourceGeometry

@[expose] public section

/-! Exact coordinate transport of the source data. The actual nonlinear
objective and every original affine row are retained. No nonempty-hard-region
assumption is needed for these transports or for the empty boundary. -/
noncomputable section
open Set Chapter02
open scoped BigOperators
namespace Chapter07.SingleTreeSource
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def integerIndices (n m : ℕ) : Finset (Fin (n+m)) :=
  Finset.univ.filter (fun i => n ≤ i.val)

def partition (n m : ℕ) : BBPartition (integerIndices n m) n m where
  continuousEquiv := {
    toFun := fun i => ⟨i.1.val, by
      have h := i.2
      simp only [integerIndices, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at h
      exact h⟩
    invFun := fun i => ⟨Fin.castAdd m i, by
      simp [integerIndices, not_le_of_gt i.isLt]⟩
    left_inv := by intro i; apply Subtype.ext; apply Fin.ext; rfl
    right_inv := by intro i; apply Fin.ext; rfl }
  integerEquiv := {
    toFun := fun i => ⟨i.1.val-n, by
      have h := i.1.isLt
      have hi := i.2
      simp only [integerIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega⟩
    invFun := fun i => ⟨Fin.natAdd n i, by simp [integerIndices]⟩
    left_inv := by
      intro i
      apply Subtype.ext
      apply Fin.ext
      have h := i.2
      simp only [integerIndices, Finset.mem_filter, Finset.mem_univ, true_and] at h
      change n + (i.1.val-n) = i.1.val
      omega
    right_inv := by intro i; apply Fin.ext; simp }

def data (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r) :
    BBPolyData N l r where
  coefficient := fun j => P.join (d.A j,d.B j)
  rhs := d.b
  c := fun z j => d.g j (P.split z)
  f := fun z => d.f (P.split z)

theorem objective (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (z : RealVector N) : (data P d).f z = d.f (P.split z) := rfl

theorem row (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (j : Fin l) (z : RealVector N) : (data P d).c z j = d.g j (P.split z) := rfl

theorem affine_row (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (j : Fin r) (z : RealVector N) :
    (∑ i, (data P d).coefficient j i * z i) = LinearForm (d.A j) (d.B j) (P.split z) := by
  rw [P.row_sum]
  simp [data, BBPartition.join_continuous, BBPartition.join_integer]

theorem polyhedron_iff (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (z : RealVector N) : z ∈ (data P d).polyhedron ↔ P.split z ∈ d.hard := by
  change (∀ j, (∑ i, (data P d).coefficient j i * z i) ≤ d.b j) ↔ _
  simp only [affine_row]
  rfl

theorem polyhedron_eq_image (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r) :
    (data P d).polyhedron = P.join '' d.hard := by
  ext z
  constructor
  · intro h
    exact ⟨P.split z, (polyhedron_iff P d z).mp h, P.join_split z⟩
  · rintro ⟨p, hp, rfl⟩
    exact (polyhedron_iff P d (P.join p)).mpr (by simpa using hp)

theorem polyhedron_compact (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (hh : IsCompact d.hard) : IsCompact (data P d).polyhedron := by
  rw [polyhedron_eq_image]
  exact hh.image P.continuous_join

theorem enclosing_bound (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (hh : IsCompact d.hard) : ∃ K, (data P d).Encloses K :=
  (data P d).exists_enclosing_bound (polyhedron_compact P d hh).isBounded

theorem integral_iff (P : BBPartition I n m) (z : RealVector N) :
    STSourceIntegral I z ↔ ∃ y : IntVector m, (P.split z).2 = Chapter06.Level.intCast y :=
  P.integral_iff z

theorem feasible_iff (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (z : RealVector N) : z ∈ (data P d).feasible I ↔ P.split z ∈ d.original := by
  simp only [BBPolyData.feasible, Set.mem_setOf_eq, polyhedron_iff]
  change (P.split z ∈ d.hard ∧ (∀ j, d.g j (P.split z) ≤ 0) ∧ STSourceIntegral I z) ↔ _
  rw [integral_iff]
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  tauto

theorem fiber_iff (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (a z : RealVector N) : z ∈ stSourceFiber (data P d) I a ↔
      P.split z ∈ d.hard ∧ (P.split z).2 = (P.split a).2 := by
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨(polyhedron_iff P d z).mp hz, funext fun i => he (P.integerEquiv.symm i)⟩
  · rintro ⟨hz,he⟩
    refine ⟨(polyhedron_iff P d z).mpr hz, ?_⟩
    intro i
    have h := congrFun he (P.integerEquiv i)
    simpa [BBPartition.split] using h

theorem nonlinear_fiber_iff (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (a z : RealVector N) : z ∈ stSourceNonlinearFiber (data P d) I a ↔
      (P.split z ∈ d.hard ∧ (P.split z).2 = (P.split a).2) ∧
      ∀ j, d.g j (P.split z) ≤ 0 := by
  change (z ∈ stSourceFiber (data P d) I a ∧ _) ↔ _
  rw [fiber_iff]
  rfl

theorem objective_C1 (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (hf : ContDiff ℝ 1 d.f) : ContDiff ℝ 1 (data P d).f :=
  hf.comp P.equiv.contDiff

theorem rows_C1 (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (hg : ∀ j, ContDiff ℝ 1 (d.g j)) : ContDiff ℝ 1 (data P d).c :=
  contDiff_pi.mpr fun j => (hg j).comp P.equiv.contDiff

theorem objective_convex (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (hf : ConvexOn ℝ univ d.f) : ConvexOn ℝ univ (data P d).f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change d.f (P.linearEquiv (a • x + b • y)) ≤
    a • d.f (P.linearEquiv x) + b • d.f (P.linearEquiv y)
  rw [map_add, map_smul, map_smul]
  exact hf.2 (mem_univ _) (mem_univ _) ha hb hab

theorem rows_convex (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (hg : ∀ j, ConvexOn ℝ univ (d.g j)) :
    ∀ j, ConvexOn ℝ univ (fun z => (data P d).c z j) := by
  intro j
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change d.g j (P.linearEquiv (a • x + b • y)) ≤
    a • d.g j (P.linearEquiv x) + b • d.g j (P.linearEquiv y)
  rw [map_add, map_smul, map_smul]
  exact (hg j).2 (mem_univ _) (mem_univ _) ha hb hab

theorem fiber_slater (P : BBPartition I n m) (d : Chapter06.Level.Data n m l r)
    (hs : ∀ y, (d.feasibleFiber y).Nonempty →
      ∃ p ∈ d.hardFiber y, ∀ j, d.g j p < 0) : STSourceFiberSlater (data P d) I := by
  intro a hi hne
  obtain ⟨y,hy⟩ := (integral_iff P a).mp hi
  obtain ⟨z,hz⟩ := hne
  have hz' := (nonlinear_fiber_iff P d a z).mp hz
  obtain ⟨p,hp,hg⟩ := hs y ⟨P.split z, ⟨hz'.1.1,hz'.1.2.trans hy⟩,hz'.2⟩
  refine ⟨P.join p,(fiber_iff P d a _).mpr ?_,?_⟩
  · simpa only [P.split_join] using And.intro hp.1 (hp.2.trans hy.symm)
  · intro j
    simpa only [data,P.split_join] using hg j

theorem tangent_transport (P : BBPartition I n m) (f : Point n m → ℝ)
    (hf : Differentiable ℝ f) (a z : RealVector N) :
    stTangent (fun q => f (P.split q)) a z =
      Chapter06.Level.tangent f (P.split a) (P.split z) := by
  have hd := (hf (P.split a)).hasFDerivAt.comp a P.equiv.hasFDerivAt
  change f (P.split a) + (fderiv ℝ (f ∘ P.split) a) (z-a) =
    f (P.split a) + (fderiv ℝ f (P.split a)) (P.split z-P.split a)
  rw [hd.fderiv]
  rfl

theorem hard_empty_feasible_empty (P : BBPartition I n m)
    (d : Chapter06.Level.Data n m l r) (he : ¬ d.hard.Nonempty) :
    (data P d).feasible I = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact he ⟨P.split z, ((feasible_iff P d z).mp hz).1.1⟩

end Chapter07.SingleTreeSource
#print axioms Chapter07.SingleTreeSource.partition
#print axioms Chapter07.SingleTreeSource.affine_row
#print axioms Chapter07.SingleTreeSource.feasible_iff
#print axioms Chapter07.SingleTreeSource.fiber_slater
#print axioms Chapter07.SingleTreeSource.tangent_transport
#print axioms Chapter07.SingleTreeSource.hard_empty_feasible_empty
