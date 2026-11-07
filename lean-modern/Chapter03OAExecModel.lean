module

public import Chapter03OAKKTMaps

@[expose] public section

/-! Source data and actual fixed-solve events for the qualified Chapter 3 OA
execution. The common convexity domain is never an added master restriction.
Every event has an actual bounded integer target and definitionally matching
anchor coordinates. No progress, freshness or return claim is a field. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

structure Data (n m l r : ℕ) where
  model : ModelData n m l r
  f : Point n m → ℝ
  Df : Point n m → Point n m →L[ℝ] ℝ
  Dg : Point n m → Fin l → Point n m →L[ℝ] ℝ
  domain : Set (Point n m)

def Data.original (d : Data n m l r) : Set (Point n m) :=
  d.model.feasibleOn Set.univ

def Data.relaxation (d : Data n m l r) : Set (Point n m) :=
  d.model.relaxationOn Set.univ

def Data.box (d : Data n m l r) : Finset (IntVector m) :=
  (integerBox_finite d.model.lo d.model.hi).toFinset

def Data.nonlinear (d : Data n m l r) : Set (Fin l) :=
  {j | ¬ AffineRow (d.model.g j)}

def Data.selected (d : Data n m l r) (p : Point n m) : Set (Fin l) :=
  {j | j ∈ d.nonlinear ∧ 0 ≤ d.model.g j p}

structure Analytic (d : Data n m l r) : Prop where
  convex_f : ConvexOn ℝ d.domain d.f
  convex_g : ∀ j, ConvexOn ℝ d.domain (d.model.g j)
  original_domain : d.original ⊆ d.domain
  derivative_f : ∀ p ∈ d.domain, HasFDerivAt d.f (d.Df p) p
  derivative_g : ∀ p ∈ d.domain, ∀ j, HasFDerivAt (d.model.g j) (d.Dg p j) p

structure Event (d : Data n m l r) where
  target : IntVector m
  target_mem : target ∈ IntegerBox d.model.lo d.model.hi
  x : RealVector n
  restoration : Option (RealVector l)

def Event.anchor {d : Data n m l r} (e : Event d) : Point n m :=
  (e.x, intCast e.target)

def EventValid (d : Data n m l r) (e : Event d) : Prop :=
  e.anchor ∈ d.domain ∧ match e.restoration with
  | none => IsMinimizer (fiber d.model (intCast e.target))
      (fiberObjective d.f (intCast e.target)) e.x ∧
      Nonempty (FixedKKT d.model d.f e.x (intCast e.target))
  | some s => ¬ (fiber d.model (intCast e.target)).Nonempty ∧
      IsMinimizer (restSet d.model (intCast e.target)) restCost (weightedInsert e.x s)

theorem Data.affine_of_not_nonlinear (d : Data n m l r) (j : Fin l)
    (hj : j ∉ d.nonlinear) : AffineRow (d.model.g j) := by
  classical
  exact not_not.mp hj

@[simp] theorem Event.anchor_y {d : Data n m l r} (e : Event d) :
    e.anchor.2 = intCast e.target := rfl

theorem Event.target_mem_box {d : Data n m l r} (e : Event d) : e.target ∈ d.box := by
  simpa [Data.box] using e.target_mem

theorem event_feasible {d : Data n m l r} {e : Event d}
    (he : EventValid d e) (hn : e.restoration = none) : e.anchor ∈ d.original := by
  have hh := he.2
  rw [hn] at hh
  exact (fiber_original_iff d.model e.target e.target_mem e.x).mp hh.1.1

theorem event_fixed_minimum {d : Data n m l r} {e : Event d}
    (he : EventValid d e) (hn : e.restoration = none) :
    IsMinimizer (fiber d.model (intCast e.target))
      (fiberObjective d.f (intCast e.target)) e.x := by
  have hh := he.2
  rw [hn] at hh
  exact hh.1

theorem event_fixed_kkt {d : Data n m l r} {e : Event d}
    (he : EventValid d e) (hn : e.restoration = none) :
    Nonempty (FixedKKT d.model d.f e.x (intCast e.target)) := by
  have hh := he.2
  rw [hn] at hh
  exact hh.2

theorem event_empty {d : Data n m l r} {e : Event d}
    (he : EventValid d e) (hn : e.restoration ≠ none) :
    ¬ (fiber d.model (intCast e.target)).Nonempty := by
  cases hs : e.restoration with
  | none => exact False.elim (hn hs)
  | some s =>
    have hh := he.2
    rw [hs] at hh
    exact hh.1

theorem event_restoration_minimum {d : Data n m l r} {e : Event d}
    (he : EventValid d e) {s : RealVector l} (hs : e.restoration = some s) :
    IsMinimizer (restSet d.model (intCast e.target)) restCost (weightedInsert e.x s) := by
  have hh := he.2
  rw [hs] at hh
  exact hh.2

theorem event_restoration_positive {d : Data n m l r} {e : Event d}
    (he : EventValid d e) {s : RealVector l} (hs : e.restoration = some s) :
    0 < ∑ j, s j := by
  apply (rest_minimum_positive_iff_empty d.model _ _ _
    (event_restoration_minimum he hs)).mpr
  exact event_empty he (by simp [hs])

theorem original_subset_relaxation (d : Data n m l r) :
    d.original ⊆ d.relaxation := source_mixed_subset_relaxation d.model Set.univ

theorem relaxation_mem_iff (d : Data n m l r) (p : Point n m) :
    p ∈ d.relaxation ↔ (∀ j, d.model.g j p ≤ 0) ∧
      p ∈ d.model.linearRegion ∧ ∀ i, d.model.lo i ≤ p.2 i ∧ p.2 i ≤ d.model.hi i := by
  simp [Data.relaxation, ModelData.relaxationOn, ContinuousRelaxation,
    ModelData.nonlinearRegion]

/-- M7: the literal thesis has no external hard rows. Its actual bound rows
make the duplicated real-box metadata redundant in continuous initialization. -/
theorem thesis_relaxation_iff (d : Data n m l 0) (B : IntegerBoundRows d.model)
    (p : Point n m) : p ∈ d.relaxation ↔ ∀ j, d.model.g j p ≤ 0 := by
  rw [relaxation_mem_iff]
  constructor
  · exact fun h => h.1
  · intro hg
    exact ⟨hg, fun i => Fin.elim0 i, B.bounds_of_rows hg⟩

theorem thesis_original_iff (d : Data n m l 0) (B : IntegerBoundRows d.model)
    (p : Point n m) : p ∈ d.original ↔ (∀ j, d.model.g j p ≤ 0) ∧ integral p := by
  rw [Data.original, ← B.original_iff]
  change ((∀ j, d.model.g j p ≤ 0) ∧ p ∈ d.model.linearRegion ∧ integral p) ↔ _
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · exact fun h => ⟨h.1,fun i => Fin.elim0 i,h.2⟩

/-- No hard-domain replacement occurs in thesis restoration. Every source
row, including affine physical bounds, has its own nonnegative slack. -/
theorem thesis_restoration_iff (d : Data n m l 0) (y : RealVector m)
    (x : RealVector n) (s : RealVector l) :
    weightedInsert x s ∈ restSet d.model y ↔
      (∀ j, d.model.g j (x,y) ≤ s j) ∧ ∀ j, 0 ≤ s j := by
  rw [restSet_insert_iff]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨fun i => Fin.elim0 i,h⟩

/-- Article initialization retains real Y bounds, separate from integrality. -/
theorem article_relaxation_iff (d : Data n m l r) (bounds : Bounds n)
    (E : HardBoundEncoding bounds d.model) (p : Point n m) :
    p ∈ d.relaxation ↔ (∀ j, d.model.g j p ≤ 0) ∧ p.1 ∈ bounds.region ∧
      ∀ i, d.model.lo i ≤ p.2 i ∧ p.2 i ≤ d.model.hi i := by
  rw [relaxation_mem_iff, ← E.region_iff]

end Chapter03.OAExec

#print axioms Chapter03.OAExec.thesis_relaxation_iff
#print axioms Chapter03.OAExec.thesis_original_iff
#print axioms Chapter03.OAExec.thesis_restoration_iff
#print axioms Chapter03.OAExec.article_relaxation_iff
#print axioms Chapter03.OAExec.event_restoration_positive
