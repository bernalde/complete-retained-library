module

public import Chapter02BBAffine
public import Chapter02BBBounds
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Order.WithBot

@[expose] public section

/-! Coordinate and extended-bound adapter for an explicitly presented bounded
polyhedron. Every enumeration and every valid enclosing real bound is allowed.
This module supplies set/minimizer/branch transport; it does not identify an
external algorithm with the finite engine or assert full Proposition 3.1. -/

noncomputable section
open Set Metric
open scoped BigOperators
namespace Chapter02

/-- Arbitrary enumerations of complementary and designated integer coordinates. -/
structure BBPartition {N : ℕ} (I : Finset (Fin N)) (n m : ℕ) where
  continuousEquiv : {i : Fin N // i ∉ I} ≃ Fin n
  integerEquiv : {i : Fin N // i ∈ I} ≃ Fin m

def bbCanonicalPartition {N : ℕ} (I : Finset (Fin N)) :
    BBPartition I (Fintype.card {i : Fin N // i ∉ I})
      (Fintype.card {i : Fin N // i ∈ I}) :=
  ⟨Fintype.equivFin _, Fintype.equivFin _⟩

namespace BBPartition
variable {N n m : ℕ} {I : Finset (Fin N)}

def split (P : BBPartition I n m) (z : RealVector N) : Point n m :=
  (fun i => z (P.continuousEquiv.symm i), fun i => z (P.integerEquiv.symm i))

def join (P : BBPartition I n m) (p : Point n m) : RealVector N :=
  fun i => if h : i ∈ I then p.2 (P.integerEquiv ⟨i, h⟩)
    else p.1 (P.continuousEquiv ⟨i, h⟩)

@[simp] theorem join_integer (P : BBPartition I n m) (p : Point n m)
    (i : {i : Fin N // i ∈ I}) : P.join p i = p.2 (P.integerEquiv i) := by
  simp [join, i.property]

@[simp] theorem join_continuous (P : BBPartition I n m) (p : Point n m)
    (i : {i : Fin N // i ∉ I}) : P.join p i = p.1 (P.continuousEquiv i) := by
  simp [join, i.property]

@[simp] theorem join_split (P : BBPartition I n m) (z : RealVector N) :
    P.join (P.split z) = z := by
  funext i
  by_cases h : i ∈ I <;> simp [join, split, h]

@[simp] theorem split_join (P : BBPartition I n m) (p : Point n m) :
    P.split (P.join p) = p := by
  apply Prod.ext <;> funext i
  · exact (P.join_continuous p (P.continuousEquiv.symm i)).trans (by simp)
  · exact (P.join_integer p (P.integerEquiv.symm i)).trans (by simp)

def linearEquiv (P : BBPartition I n m) : RealVector N ≃ₗ[ℝ] Point n m where
  toFun := P.split
  invFun := P.join
  left_inv := P.join_split
  right_inv := P.split_join
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def equiv (P : BBPartition I n m) : RealVector N ≃L[ℝ] Point n m :=
  P.linearEquiv.toContinuousLinearEquiv

theorem continuous_split (P : BBPartition I n m) : Continuous P.split :=
  P.equiv.continuous

theorem continuous_join (P : BBPartition I n m) : Continuous P.join :=
  P.equiv.symm.continuous

theorem row_sum (P : BBPartition I n m) (a z : RealVector N) :
    ∑ i, a i * z i = LinearForm
      (fun i => a (P.continuousEquiv.symm i))
      (fun i => a (P.integerEquiv.symm i)) (P.split z) := by
  letI : Fintype {i : Fin N // i ∈ I} := Subtype.fintype _
  have hc := P.continuousEquiv.symm.sum_comp
    (fun i : {i : Fin N // i ∉ I} => a i * z i)
  have hi := P.integerEquiv.symm.sum_comp
    (fun i : {i : Fin N // i ∈ I} => a i * z i)
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => i ∈ I)
    (fun i => a i * z i)
  simp only [LinearForm, split]
  rw [hc, hi]
  simpa only [add_comm] using hs.symm

theorem integral_iff (P : BBPartition I n m) (z : RealVector N) :
    (∀ i : {i : Fin N // i ∈ I}, ∃ k : ℤ, (k : ℝ) = z i) ↔
      ∃ y : IntVector m, (P.split z).2 = fun i => (y i : ℝ) := by
  constructor
  · intro h
    choose y hy using fun i : Fin m => h (P.integerEquiv.symm i)
    exact ⟨y, funext fun i => (hy i).symm⟩
  · rintro ⟨y, hy⟩ i
    refine ⟨y (P.integerEquiv i), ?_⟩
    have := congrFun hy (P.integerEquiv i)
    simpa [split] using this.symm

end BBPartition

/-- Original-coordinate data: general objective and a vector-valued constraint
map, with an explicit finite-halfspace presentation of the polyhedron. -/
structure BBPolyData (N l r : ℕ) where
  coefficient : Fin r → RealVector N
  rhs : RealVector r
  c : RealVector N → RealVector l
  f : RealVector N → ℝ

namespace BBPolyData
variable {N n m l r : ℕ} {I : Finset (Fin N)}

def polyhedron (D : BBPolyData N l r) : Set (RealVector N) :=
  {z | ∀ j, ∑ i, D.coefficient j i * z i ≤ D.rhs j}

def Encloses (D : BBPolyData N l r) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ z ∈ D.polyhedron, ∀ i, |z i| ≤ K

theorem polyhedron_closed (D : BBPolyData N l r) : IsClosed D.polyhedron := by
  have heq : D.polyhedron = ⋂ j, {z | ∑ i, D.coefficient j i * z i ≤ D.rhs j} := by
    ext z
    simp [polyhedron]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

theorem polyhedron_compact (D : BBPolyData N l r)
    (hX : Bornology.IsBounded D.polyhedron) : IsCompact D.polyhedron :=
  isCompact_iff_isClosed_bounded.mpr ⟨D.polyhedron_closed, hX⟩

theorem exists_enclosing_bound (D : BBPolyData N l r)
    (hX : Bornology.IsBounded D.polyhedron) : ∃ K, D.Encloses K := by
  obtain ⟨K, hK⟩ := hX.exists_norm_le
  refine ⟨max 0 K, le_max_left _ _, ?_⟩
  intro z hz i
  exact (norm_le_pi_norm z i).trans ((hK z hz).trans (le_max_right _ _))

def model (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ) : ModelData n m l r where
  g := fun j p => D.c (P.join p) j
  A := fun j i => D.coefficient j (P.continuousEquiv.symm i)
  B := fun j i => D.coefficient j (P.integerEquiv.symm i)
  rhs := D.rhs
  c1 := 0
  c2 := 0
  lo := fun _ => -K
  hi := fun _ => K

def objective (D : BBPolyData N l r) (P : BBPartition I n m) : Point n m → ℝ :=
  D.f ∘ P.join

@[simp] theorem objective_split (D : BBPolyData N l r) (P : BBPartition I n m)
    (z : RealVector N) : D.objective P (P.split z) = D.f z := by
  simp [objective]

theorem linear_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (z : RealVector N) : P.split z ∈ (D.model P K).linearRegion ↔ z ∈ D.polyhedron := by
  simp only [ModelData.linearRegion, model, Set.mem_setOf_eq, ← P.row_sum, polyhedron]

theorem nonlinear_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (z : RealVector N) : P.split z ∈ (D.model P K).nonlinearRegion ↔ ∀ j, D.c z j ≤ 0 := by
  simp [ModelData.nonlinearRegion, model]

theorem rows_continuous (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hc : Continuous D.c) : ∀ j, Continuous ((D.model P K).g j) := by
  intro j
  exact ((continuous_apply j).comp hc).comp P.continuous_join

theorem c2_rows_continuous (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hc : ContDiff ℝ 2 D.c) : ∀ j, Continuous ((D.model P K).g j) :=
  D.rows_continuous P K hc.continuous

theorem c2_rows (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hc : ContDiff ℝ 2 D.c) : ∀ j, ContDiff ℝ 2 ((D.model P K).g j) := by
  intro j
  exact (contDiff_pi.mp hc j).comp P.equiv.symm.contDiff

theorem c2_objective (D : BBPolyData N l r) (P : BBPartition I n m)
    (hf : ContDiff ℝ 2 D.f) : ContDiff ℝ 2 (D.objective P) :=
  hf.comp P.equiv.symm.contDiff

theorem convex_objective (D : BBPolyData N l r) (P : BBPartition I n m)
    (hf : ConvexOn ℝ Set.univ D.f) : ConvexOn ℝ Set.univ (D.objective P) := by
  simpa [objective, BBPartition.linearEquiv, Function.comp_def] using hf.comp_linearMap P.linearEquiv.symm.toLinearMap

/-- Vector-valued convexity uses the coordinatewise order and implies each
transported scalar row is convex. It is not needed for compact attainment. -/
theorem convex_rows (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hc : ConvexOn ℝ Set.univ D.c) : ∀ j, ConvexOn ℝ Set.univ ((D.model P K).g j) := by
  intro j
  have hj : ConvexOn ℝ Set.univ (fun z => D.c z j) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    exact hc.2 hx hy ha hb hab j
  simpa [model, BBPartition.linearEquiv, Function.comp_def] using hj.comp_linearMap P.linearEquiv.symm.toLinearMap

theorem objective_continuous (D : BBPolyData N l r) (P : BBPartition I n m)
    (hf : Continuous D.f) : Continuous (D.objective P) := hf.comp P.continuous_join

theorem affine_root_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (z : RealVector N) :
    P.split z ∈ bbAffineRelaxation (D.model P K) (fun _ => -K) (fun _ => K) ↔
      z ∈ D.polyhedron := by
  constructor
  · intro hz
    exact (D.linear_iff P K z).mp hz.2.1
  · intro hz
    refine ⟨Set.mem_univ _, (D.linear_iff P K z).mpr hz, ?_⟩
    intro i
    exact abs_le.mp (hK.2 z hz (P.integerEquiv.symm i))

theorem affine_root_eq_image (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) :
    bbAffineRelaxation (D.model P K) (fun _ => -K) (fun _ => K) =
      P.split '' D.polyhedron := by
  ext p
  constructor
  · intro hp
    refine ⟨P.join p, ?_, P.split_join p⟩
    apply (D.affine_root_iff P K hK (P.join p)).mp
    simpa using hp
  · rintro ⟨z, hz, rfl⟩
    exact (D.affine_root_iff P K hK z).mpr hz

theorem affine_root_compact (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (hX : Bornology.IsBounded D.polyhedron) :
    IsCompact (bbAffineRelaxation (D.model P K) (fun _ => -K) (fun _ => K)) := by
  rw [D.affine_root_eq_image P K hK]
  exact (D.polyhedron_compact hX).image P.continuous_split

end BBPolyData

/-- Additional external bounds. The index is the actual integer-coordinate
subtype in the adapter and may be any type for independent infinite-bound controls. -/
structure BBExtendedNode (ι : Type*) where
  lower : ι → WithBot ℝ
  upper : ι → WithTop ℝ

namespace BBExtendedNode
variable {ι : Type*}

def root : BBExtendedNode ι := ⟨fun _ => ⊥, fun _ => ⊤⟩

def Holds (B : BBExtendedNode ι) (z : ι → ℝ) : Prop :=
  ∀ i, B.lower i ≤ (z i : WithBot ℝ) ∧ (z i : WithTop ℝ) ≤ B.upper i

def left (B : BBExtendedNode ι) (i : ι) (v : ℝ) : BBExtendedNode ι := by
  classical
  exact ⟨B.lower, Function.update B.upper i ((Int.floor v : ℝ) : WithTop ℝ)⟩

def right (B : BBExtendedNode ι) (i : ι) (v : ℝ) : BBExtendedNode ι := by
  classical
  exact ⟨Function.update B.lower i ((Int.ceil v : ℝ) : WithBot ℝ), B.upper⟩

def clampLower (K : ℝ) (v : WithBot ℝ) : ℝ :=
  WithBot.recBotCoe (-K) (fun x => max (-K) x) v

def clampUpper (K : ℝ) (v : WithTop ℝ) : ℝ :=
  WithTop.recTopCoe K (fun x => min K x) v

def clamp {m : ℕ} (B : BBExtendedNode ι) (e : ι ≃ Fin m) (K : ℝ) : BBNode m :=
  ⟨fun i => clampLower K (B.lower (e.symm i)),
    fun i => clampUpper K (B.upper (e.symm i))⟩

@[simp] theorem holds_root (z : ι → ℝ) : (root : BBExtendedNode ι).Holds z := by
  simp [root, Holds]

theorem clampLower_le_iff (K x : ℝ) (v : WithBot ℝ) :
    clampLower K v ≤ x ↔ -K ≤ x ∧ v ≤ (x : WithBot ℝ) := by
  induction v using WithBot.recBotCoe <;> simp [clampLower, max_le_iff]

theorem le_clampUpper_iff (K x : ℝ) (v : WithTop ℝ) :
    x ≤ clampUpper K v ↔ x ≤ K ∧ (x : WithTop ℝ) ≤ v := by
  induction v using WithTop.recTopCoe <;> simp [clampUpper, le_min_iff]

theorem lower_clamp_ge (K : ℝ) (v : WithBot ℝ) : -K ≤ clampLower K v := by
  induction v using WithBot.recBotCoe <;> simp [clampLower]

theorem upper_clamp_le (K : ℝ) (v : WithTop ℝ) : clampUpper K v ≤ K := by
  induction v using WithTop.recTopCoe <;> simp [clampUpper]

@[simp] theorem clamp_root {m : ℕ} (e : ι ≃ Fin m) (K : ℝ) :
    (root : BBExtendedNode ι).clamp e K = ⟨fun _ => -K, fun _ => K⟩ := rfl

theorem clamp_refines_root {m : ℕ} (B : BBExtendedNode ι) (e : ι ≃ Fin m) (K : ℝ) :
    (B.clamp e K).Refines ((root : BBExtendedNode ι).clamp e K) :=
  fun _ => ⟨lower_clamp_ge _ _, upper_clamp_le _ _⟩

theorem clamp_holds_iff {m : ℕ} (B : BBExtendedNode ι) (e : ι ≃ Fin m)
    (K : ℝ) (z : ι → ℝ) :
    (∀ j, (B.clamp e K).lower j ≤ z (e.symm j) ∧
      z (e.symm j) ≤ (B.clamp e K).upper j) ↔
      B.Holds z ∧ ∀ i, -K ≤ z i ∧ z i ≤ K := by
  simp only [clamp, clampLower_le_iff, le_clampUpper_iff]
  constructor
  · intro h
    constructor
    · intro i
      have hi := h (e i)
      simpa only [e.symm_apply_apply] using And.intro hi.1.2 hi.2.2
    · intro i
      have hi := h (e i)
      simpa only [e.symm_apply_apply] using And.intro hi.1.1 hi.2.1
  · rintro ⟨hb, hk⟩ j
    exact ⟨⟨(hk _).1, (hb _).1⟩, ⟨(hk _).2, (hb _).2⟩⟩

/-- The clamped upper side is not capped below: an empty child remains empty. -/
theorem clamp_left {m : ℕ} (B : BBExtendedNode ι) (e : ι ≃ Fin m)
    (K : ℝ) (i : ι) (v : ℝ) (hv : v ≤ K) :
    (B.left i v).clamp e K = (B.clamp e K).left (e i) v := by
  classical
  have hf : (Int.floor v : ℝ) ≤ K := (Int.floor_le v).trans hv
  unfold clamp left BBNode.left
  congr 1
  funext j
  by_cases hji : j = e i
  · subst j
    rw [e.symm_apply_apply, Function.update_self]
    simp [clampUpper, min_eq_right hf]
  · have hne : e.symm j ≠ i := by
      intro h
      apply hji
      simpa using congrArg e h
    simp [Function.update_of_ne hji, Function.update_of_ne hne]

/-- The clamped lower side is not capped above: an empty child remains empty. -/
theorem clamp_right {m : ℕ} (B : BBExtendedNode ι) (e : ι ≃ Fin m)
    (K : ℝ) (i : ι) (v : ℝ) (hv : -K ≤ v) :
    (B.right i v).clamp e K = (B.clamp e K).right (e i) v := by
  classical
  have hf : -K ≤ (Int.ceil v : ℝ) := hv.trans (Int.le_ceil v)
  unfold clamp right BBNode.right
  congr 1
  funext j
  by_cases hji : j = e i
  · subst j
    rw [e.symm_apply_apply, Function.update_self]
    simp [clampLower, max_eq_right hf]
  · have hne : e.symm j ≠ i := by
      intro h
      apply hji
      simpa using congrArg e h
    simp [Function.update_of_ne hji, Function.update_of_ne hne]

theorem holds_closed {α : Type*} [TopologicalSpace α] (B : BBExtendedNode ι)
    (z : α → ι → ℝ) (hz : ∀ i, Continuous (fun x => z x i)) :
    IsClosed {x | B.Holds (z x)} := by
  have heq : {x | B.Holds (z x)} = ⋂ i,
      {x | B.lower i ≤ (z x i : WithBot ℝ) ∧ (z x i : WithTop ℝ) ≤ B.upper i} := by
    ext x
    simp [Holds]
  rw [heq]
  apply isClosed_iInter
  intro i
  have hl : IsClosed {x | B.lower i ≤ (z x i : WithBot ℝ)} := by
    generalize B.lower i = v
    induction v using WithBot.recBotCoe
    · simp
    · simpa using isClosed_le continuous_const (hz i)
  have hu : IsClosed {x | (z x i : WithTop ℝ) ≤ B.upper i} := by
    generalize B.upper i = v
    induction v using WithTop.recTopCoe
    · simp
    · simpa using isClosed_le (hz i) continuous_const
  exact hl.inter hu

end BBExtendedNode

namespace BBPolyData
variable {N n m l r : ℕ} {I : Finset (Fin N)}

/-- Literal original-coordinate continuous node region. The additional bounds
are indexed by I itself, independently of any enumeration or clamping. -/
def relaxation (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) : Set (RealVector N) :=
  {z | z ∈ D.polyhedron ∧ (∀ j, D.c z j ≤ 0) ∧ B.Holds (fun i => z i)}

def feasible (D : BBPolyData N l r) (I : Finset (Fin N)) : Set (RealVector N) :=
  {z | z ∈ D.polyhedron ∧ (∀ j, D.c z j ≤ 0) ∧
    ∀ i : {i : Fin N // i ∈ I}, ∃ k : ℤ, (k : ℝ) = z i}

abbrev nodeRegion (D : BBPolyData N l r) (I : Finset (Fin N))
    (B : BBExtendedNode {i : Fin N // i ∈ I}) : Set (RealVector N) := D.relaxation B

abbrev mixedFeasible (D : BBPolyData N l r) (I : Finset (Fin N)) :
    Set (RealVector N) := D.feasible I

theorem relaxation_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I}) (z : RealVector N) :
    z ∈ D.relaxation B ↔ P.split z ∈ bbNodeRelaxation (D.model P K)
      (B.clamp P.integerEquiv K).lower (B.clamp P.integerEquiv K).upper := by
  constructor
  · rintro ⟨hX, hc, hB⟩
    refine ⟨(D.nonlinear_iff P K z).mpr hc, (D.linear_iff P K z).mpr hX, ?_⟩
    apply (B.clamp_holds_iff P.integerEquiv K (fun i => z i)).mpr
    exact ⟨hB, fun i => abs_le.mp (hK.2 z hX i)⟩
  · rintro ⟨hc, hX, hB⟩
    refine ⟨(D.linear_iff P K z).mp hX, (D.nonlinear_iff P K z).mp hc, ?_⟩
    exact ((B.clamp_holds_iff P.integerEquiv K (fun i => z i)).mp hB).1

theorem relaxation_eq_image (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    bbNodeRelaxation (D.model P K) (B.clamp P.integerEquiv K).lower
      (B.clamp P.integerEquiv K).upper = P.split '' D.relaxation B := by
  ext p
  constructor
  · intro hp
    refine ⟨P.join p, ?_, P.split_join p⟩
    apply (D.relaxation_iff P K hK B (P.join p)).mpr
    simpa using hp
  · rintro ⟨z, hz, rfl⟩
    exact (D.relaxation_iff P K hK B z).mp hz

theorem relaxation_empty_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I}) :
    D.relaxation B = ∅ ↔ bbNodeRelaxation (D.model P K)
      (B.clamp P.integerEquiv K).lower (B.clamp P.integerEquiv K).upper = ∅ := by
  rw [D.relaxation_eq_image P K hK B, Set.image_eq_empty]

theorem minimizer_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I}) (z : RealVector N) :
    IsMinimizer (D.relaxation B) D.f z ↔
      IsMinimizer (bbNodeRelaxation (D.model P K) (B.clamp P.integerEquiv K).lower
        (B.clamp P.integerEquiv K).upper) (D.objective P) (P.split z) := by
  constructor
  · rintro ⟨hz, hmin⟩
    refine ⟨(D.relaxation_iff P K hK B z).mp hz, ?_⟩
    intro p hp
    have hp' : P.join p ∈ D.relaxation B := by
      apply (D.relaxation_iff P K hK B (P.join p)).mpr
      simpa using hp
    simpa [objective] using hmin (P.join p) hp'
  · rintro ⟨hz, hmin⟩
    refine ⟨(D.relaxation_iff P K hK B z).mpr hz, ?_⟩
    intro w hw
    simpa only [objective_split] using hmin (P.split w) ((D.relaxation_iff P K hK B w).mp hw)

theorem feasible_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (z : RealVector N) :
    z ∈ D.feasible I ↔ P.split z ∈ (D.model P K).feasibleOn Set.univ := by
  constructor
  · rintro ⟨hX, hc, hI⟩
    obtain ⟨y, hy⟩ := (P.integral_iff z).mp hI
    refine ⟨⟨⟨Set.mem_univ _, (D.nonlinear_iff P K z).mpr hc⟩,
      (D.linear_iff P K z).mpr hX⟩, y, ?_, hy⟩
    intro j
    have hj := abs_le.mp (hK.2 z hX (P.integerEquiv.symm j))
    change -K ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ K
    simpa only [BBPartition.split, ← congrFun hy j] using hj
  · rintro ⟨⟨⟨_, hc⟩, hX⟩, y, _, hy⟩
    exact ⟨(D.linear_iff P K z).mp hX, (D.nonlinear_iff P K z).mp hc,
      (P.integral_iff z).mpr ⟨y, hy⟩⟩

theorem feasible_minimizer_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (z : RealVector N) :
    IsMinimizer (D.feasible I) D.f z ↔
      IsMinimizer ((D.model P K).feasibleOn Set.univ) (D.objective P) (P.split z) := by
  constructor
  · rintro ⟨hz, hm⟩
    refine ⟨(D.feasible_iff P K hK z).mp hz, ?_⟩
    intro p hp
    have hp' : P.join p ∈ D.feasible I := by
      apply (D.feasible_iff P K hK (P.join p)).mpr
      simpa using hp
    simpa [objective] using hm (P.join p) hp'
  · rintro ⟨hz, hm⟩
    refine ⟨(D.feasible_iff P K hK z).mpr hz, ?_⟩
    intro w hw
    simpa only [objective_split] using hm (P.split w) ((D.feasible_iff P K hK w).mp hw)

theorem relaxation_closed (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (hc : Continuous D.c) :
    IsClosed (D.relaxation B) := by
  have hrows : IsClosed {z | ∀ j, D.c z j ≤ 0} := by
    have heq : {z | ∀ j, D.c z j ≤ 0} = ⋂ j, {z | D.c z j ≤ 0} := by
      ext z
      simp
    rw [heq]
    exact isClosed_iInter fun j => isClosed_le ((continuous_apply j).comp hc) continuous_const
  exact D.polyhedron_closed.inter
    (hrows.inter (B.holds_closed (fun (z : RealVector N) i => z i)
      (fun i => continuous_apply i.val)))

theorem relaxation_compact (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) : IsCompact (D.relaxation B) :=
  (D.polyhedron_compact hX).of_isClosed_subset (D.relaxation_closed B hc) (fun _ hz => hz.1)

/-- Bounded X yields empty-or-attained for every external node, including X
empty and either empty or full integer index set. -/
theorem relaxation_empty_or_minimum (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron) :
    D.relaxation B = ∅ ∨ ∃ z, IsMinimizer (D.relaxation B) D.f z := by
  rcases (D.relaxation B).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (compact_feasible_attainment (D.relaxation_compact B hX hc) h
      (hf.mono (fun _ hz => hz.1)))

theorem clamped_empty_or_minimum (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I})
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : ContinuousOn D.f D.polyhedron) :
    bbNodeRelaxation (D.model P K) (B.clamp P.integerEquiv K).lower
      (B.clamp P.integerEquiv K).upper = ∅ ∨
    ∃ p, IsMinimizer (bbNodeRelaxation (D.model P K) (B.clamp P.integerEquiv K).lower
      (B.clamp P.integerEquiv K).upper) (D.objective P) p := by
  rcases D.relaxation_empty_or_minimum B hX hc hf with he | ⟨z, hz⟩
  · exact Or.inl ((D.relaxation_empty_iff P K hK B).mp he)
  · exact Or.inr ⟨P.split z, (D.minimizer_iff P K hK B z).mp hz⟩

theorem left_commutes (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I})
    (z : RealVector N) (hz : z ∈ D.polyhedron) (i : {i : Fin N // i ∈ I}) :
    (B.left i (z i)).clamp P.integerEquiv K =
      (B.clamp P.integerEquiv K).left (P.integerEquiv i) ((P.split z).2 (P.integerEquiv i)) := by
  simpa [BBPartition.split] using B.clamp_left P.integerEquiv K i (z i)
    (abs_le.mp (hK.2 z hz i)).2

theorem right_commutes (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I})
    (z : RealVector N) (hz : z ∈ D.polyhedron) (i : {i : Fin N // i ∈ I}) :
    (B.right i (z i)).clamp P.integerEquiv K =
      (B.clamp P.integerEquiv K).right (P.integerEquiv i) ((P.split z).2 (P.integerEquiv i)) := by
  simpa [BBPartition.split] using B.clamp_right P.integerEquiv K i (z i)
    (abs_le.mp (hK.2 z hz i)).1

theorem feasible_eq_image (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) : (D.model P K).feasibleOn Set.univ = P.split '' D.feasible I := by
  ext p
  constructor
  · intro hp
    refine ⟨P.join p, ?_, P.split_join p⟩
    apply (D.feasible_iff P K hK (P.join p)).mpr
    simpa using hp
  · rintro ⟨z, hz, rfl⟩
    exact (D.feasible_iff P K hK z).mp hz

theorem feasible_empty_iff (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) : D.feasible I = ∅ ↔ (D.model P K).feasibleOn Set.univ = ∅ := by
  rw [D.feasible_eq_image P K hK, Set.image_eq_empty]

theorem relaxation_not_unbounded (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron) :
    ¬ (∀ t : ℝ, ∃ z ∈ D.relaxation B, D.f z < t) := by
  intro hbad
  rcases D.relaxation_empty_or_minimum B hX hc hf with he | ⟨z, hz, hmin⟩
  · obtain ⟨z, hz, _⟩ := hbad 0
    simp only [he, Set.mem_empty_iff_false] at hz
  · obtain ⟨w, hw, hwv⟩ := hbad (D.f z)
    exact (not_lt_of_ge (hmin w hw)) hwv

theorem relaxation_no_unattained (D : BBPolyData N l r)
    (B : BBExtendedNode {i : Fin N // i ∈ I}) (hX : Bornology.IsBounded D.polyhedron)
    (hc : Continuous D.c) (hf : ContinuousOn D.f D.polyhedron)
    (hne : (D.relaxation B).Nonempty) : ∃ z, IsMinimizer (D.relaxation B) D.f z := by
  rcases D.relaxation_empty_or_minimum B hX hc hf with he | hm
  · exact (hne.ne_empty he).elim
  · exact hm

theorem clamped_not_unbounded (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I})
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : ContinuousOn D.f D.polyhedron) :
    ¬ (∀ t : ℝ, ∃ p ∈ bbNodeRelaxation (D.model P K)
      (B.clamp P.integerEquiv K).lower (B.clamp P.integerEquiv K).upper,
      D.objective P p < t) := by
  intro hbad
  rcases D.clamped_empty_or_minimum P K hK B hX hc hf with he | ⟨z, hz, hmin⟩
  · obtain ⟨z, hz, _⟩ := hbad 0
    simp only [he, Set.mem_empty_iff_false] at hz
  · obtain ⟨w, hw, hwv⟩ := hbad (D.objective P z)
    exact (not_lt_of_ge (hmin w hw)) hwv

theorem clamped_no_unattained (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (B : BBExtendedNode {i : Fin N // i ∈ I})
    (hX : Bornology.IsBounded D.polyhedron) (hc : Continuous D.c)
    (hf : ContinuousOn D.f D.polyhedron)
    (hne : (bbNodeRelaxation (D.model P K) (B.clamp P.integerEquiv K).lower
      (B.clamp P.integerEquiv K).upper).Nonempty) :
    ∃ p, IsMinimizer (bbNodeRelaxation (D.model P K) (B.clamp P.integerEquiv K).lower
      (B.clamp P.integerEquiv K).upper) (D.objective P) p := by
  rcases D.clamped_empty_or_minimum P K hK B hX hc hf with he | hm
  · exact (hne.ne_empty he).elim
  · exact hm

/-- The direct bounded-polyhedron route derives the finite engine's root mixed
compactness, including the case where the original polyhedron is empty. -/
theorem mixed_root_compact (D : BBPolyData N l r) (P : BBPartition I n m) (K : ℝ)
    (hK : D.Encloses K) (hX : Bornology.IsBounded D.polyhedron) :
    IsCompact (bbMixedBase (D.model P K) (fun _ => -K) (fun _ => K)) := by
  have hY : IsClosed (IntegerCylinder (n := n) (fun _ : Fin m => -K) (fun _ => K)) := by
    let castY : IntVector m → RealVector m := fun y i => (y i : ℝ)
    have hfin := (integerBox_finite (fun _ : Fin m => -K) (fun _ => K)).image castY
    have heq : IntegerCylinder (n := n) (fun _ : Fin m => -K) (fun _ => K) =
        Prod.snd ⁻¹' (castY '' IntegerBox (fun _ : Fin m => -K) (fun _ => K)) := by
      ext p
      simp only [IntegerCylinder, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hp⟩
        exact ⟨y, hy, hp.symm⟩
      · rintro ⟨y, hy, hp⟩
        exact ⟨y, hy, hp.symm⟩
    rw [heq]
    exact hfin.isClosed.preimage continuous_snd
  rw [← bb_affine_mixed_eq]
  exact (D.affine_root_compact P K hK hX).inter_right hY

end BBPolyData
end Chapter02

#print axioms Chapter02.BBPartition.join_integer
#print axioms Chapter02.BBPartition.join_continuous
#print axioms Chapter02.BBPartition.join_split
#print axioms Chapter02.BBPartition.split_join
#print axioms Chapter02.BBPartition.continuous_split
#print axioms Chapter02.BBPartition.continuous_join
#print axioms Chapter02.BBPartition.row_sum
#print axioms Chapter02.BBPartition.integral_iff
#print axioms Chapter02.BBPolyData.polyhedron_closed
#print axioms Chapter02.BBPolyData.polyhedron_compact
#print axioms Chapter02.BBPolyData.exists_enclosing_bound
#print axioms Chapter02.BBPolyData.objective_split
#print axioms Chapter02.BBPolyData.linear_iff
#print axioms Chapter02.BBPolyData.nonlinear_iff
#print axioms Chapter02.BBPolyData.rows_continuous
#print axioms Chapter02.BBPolyData.c2_rows_continuous
#print axioms Chapter02.BBPolyData.c2_rows
#print axioms Chapter02.BBPolyData.c2_objective
#print axioms Chapter02.BBPolyData.convex_objective
#print axioms Chapter02.BBPolyData.convex_rows
#print axioms Chapter02.BBPolyData.objective_continuous
#print axioms Chapter02.BBPolyData.affine_root_iff
#print axioms Chapter02.BBPolyData.affine_root_eq_image
#print axioms Chapter02.BBPolyData.affine_root_compact
#print axioms Chapter02.BBExtendedNode.holds_root
#print axioms Chapter02.BBExtendedNode.clampLower_le_iff
#print axioms Chapter02.BBExtendedNode.le_clampUpper_iff
#print axioms Chapter02.BBExtendedNode.lower_clamp_ge
#print axioms Chapter02.BBExtendedNode.upper_clamp_le
#print axioms Chapter02.BBExtendedNode.clamp_root
#print axioms Chapter02.BBExtendedNode.clamp_refines_root
#print axioms Chapter02.BBExtendedNode.clamp_holds_iff
#print axioms Chapter02.BBExtendedNode.clamp_left
#print axioms Chapter02.BBExtendedNode.clamp_right
#print axioms Chapter02.BBExtendedNode.holds_closed
#print axioms Chapter02.BBPolyData.relaxation_iff
#print axioms Chapter02.BBPolyData.relaxation_eq_image
#print axioms Chapter02.BBPolyData.relaxation_empty_iff
#print axioms Chapter02.BBPolyData.minimizer_iff
#print axioms Chapter02.BBPolyData.feasible_iff
#print axioms Chapter02.BBPolyData.feasible_minimizer_iff
#print axioms Chapter02.BBPolyData.relaxation_closed
#print axioms Chapter02.BBPolyData.relaxation_compact
#print axioms Chapter02.BBPolyData.relaxation_empty_or_minimum
#print axioms Chapter02.BBPolyData.clamped_empty_or_minimum
#print axioms Chapter02.BBPolyData.left_commutes
#print axioms Chapter02.BBPolyData.right_commutes
#print axioms Chapter02.BBPolyData.feasible_eq_image
#print axioms Chapter02.BBPolyData.feasible_empty_iff
#print axioms Chapter02.BBPolyData.relaxation_not_unbounded
#print axioms Chapter02.BBPolyData.relaxation_no_unattained
#print axioms Chapter02.BBPolyData.clamped_not_unbounded
#print axioms Chapter02.BBPolyData.clamped_no_unattained
#print axioms Chapter02.BBPolyData.mixed_root_compact
