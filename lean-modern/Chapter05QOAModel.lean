module

public import Chapter05QuadraticMaster
public import Chapter03OAKKTSource

@[expose] public section

/-! Literal compact source model and fixed row tokens for the repaired quadratic
OA master. All original nonlinear rows remain in the individual-slack problem.
Events contain actual minima, never support, multiplier, or progress oracles. -/
noncomputable section
open Set
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter05.QOA
variable {n p m r : ℕ}
attribute [local instance] Classical.propDecidable

structure Data (n p m r : ℕ) where
  f : Point n p → ℝ
  g : Fin m → Point n p → ℝ
  X : Set (RealVector n)
  Y : Finset (IntVector p)
  A : Fin r → RealVector n
  E : Fin r → RealVector p
  b : Fin r → ℝ
  relaxedY : Set (RealVector p)

def Data.affineFiber (d : Data n p m r) (y : RealVector p) : Set (RealVector n) :=
  {x ∈ d.X | ∀ i, LinearForm (d.A i) (d.E i) (x,y) ≤ d.b i}

def Data.hardFiber (d : Data n p m r) (y : IntVector p) : Set (RealVector n) :=
  d.affineFiber (intCast y)

def Data.fiberObjective (d : Data n p m r) (y : IntVector p) (x : RealVector n) : ℝ :=
  d.f (x,intCast y)

def Data.soft (d : Data n p m r) (y : IntVector p) (j : Fin m) (x : RealVector n) : ℝ :=
  d.g j (x,intCast y)

def Data.feasibleFiber (d : Data n p m r) (y : IntVector p) : Set (RealVector n) :=
  {x ∈ d.hardFiber y | ∀ j, d.soft y j x ≤ 0}

def Data.base (d : Data n p m r) : Set (Point n p) :=
  {z | ∃ y ∈ d.Y, z.2 = intCast y ∧ z.1 ∈ d.hardFiber y}

def Data.original (d : Data n p m r) : Set (Point n p) :=
  {z ∈ d.base | ∀ j, d.g j z ≤ 0}

def Data.relaxation (d : Data n p m r) : Set (Point n p) :=
  {z | z.1 ∈ d.X ∧ z.2 ∈ d.relaxedY ∧
    (∀ i, LinearForm (d.A i) (d.E i) z ≤ d.b i) ∧ ∀ j, d.g j z ≤ 0}

def Data.activeY (d : Data n p m r) : Finset (IntVector p) := by
  classical
  exact d.Y.filter (fun y => (d.hardFiber y).Nonempty)

structure Regularity (d : Data n p m r) : Prop where
  objective_convex : ConvexOn ℝ univ d.f
  objective_C2 : ContDiff ℝ 2 d.f
  constraint_convex : ∀ j, ConvexOn ℝ univ (d.g j)
  constraint_C2 : ∀ j, ContDiff ℝ 2 (d.g j)
  X_nonempty : d.X.Nonempty
  X_compact : IsCompact d.X
  X_convex : Convex ℝ d.X
  fiber_slater : ∀ y ∈ d.Y, (d.feasibleFiber y).Nonempty →
    ∃ x ∈ d.hardFiber y, ∀ j, d.soft y j x < 0

structure RelaxationRegularity (d : Data n p m r) : Prop where
  compact : IsCompact d.relaxedY
  convex : Convex ℝ d.relaxedY
  contains : ∀ y ∈ d.Y, intCast y ∈ d.relaxedY

structure Token (n p m : ℕ) where
  anchor : Point n p
  objectiveScale : ℝ
  constraintScale : Fin m → ℝ

def Token.Safe (d : Data n p m r) (t : Token n p m) : Prop :=
  (0 ≤ t.objectiveScale ∧
    t.objectiveScale ≤ Quadratic.safeScale d.f t.anchor d.base) ∧
  ∀ j, 0 ≤ t.constraintScale j ∧
    t.constraintScale j ≤ Quadratic.safeScale (d.g j) t.anchor d.base

def masterData (d : Data n p m r) :
    Quadratic.MasterData (Point n p) (Token n p m) (Fin m) :=
  ⟨d.f,d.g,Token.anchor,Token.objectiveScale,Token.constraintScale,d.base⟩

def SafeRows (d : Data n p m r) (H : List (Token n p m)) : Prop :=
  ∀ t ∈ H, t.Safe d

def master (d : Data n p m r) (H : List (Token n p m)) : Set (Point n p × ℝ) := by
  classical
  exact Quadratic.quadraticMaster (masterData d) H.toFinset

theorem master_mem_iff (d : Data n p m r) (H : List (Token n p m)) (q : Point n p × ℝ) :
    q ∈ master d H ↔ q.1 ∈ d.base ∧
      (∀ t ∈ H, Quadratic.cut d.f t.anchor t.objectiveScale q.1 ≤ q.2) ∧
      ∀ t ∈ H, ∀ j, Quadratic.cut (d.g j) t.anchor (t.constraintScale j) q.1 ≤ 0 := by
  classical
  simp [master,Quadratic.quadraticMaster,masterData]

theorem regularity_masterData {d : Data n p m r} (h : Regularity d) :
    Quadratic.MasterRegularity (masterData d) :=
  ⟨h.objective_convex,h.objective_C2,h.constraint_convex,h.constraint_C2⟩

theorem safeRows_safeHistory {d : Data n p m r} {H : List (Token n p m)}
    (h : SafeRows d H) : Quadratic.SafeHistory (masterData d) H.toFinset := by
  classical
  change ∀ t ∈ H.toFinset, t.Safe d
  intro t ht
  exact h t (List.mem_toFinset.mp ht)

theorem trueEpigraph_eq (d : Data n p m r) :
    Quadratic.trueEpigraph (masterData d) = EpigraphLift d.original d.f := by
  ext q
  simp only [Quadratic.trueEpigraph,masterData,EpigraphLift,Data.original,
    Set.mem_setOf_eq,and_assoc]

theorem base_hard {d : Data n p m r} {z : Point n p} {y : IntVector p}
    (hz : z ∈ d.base) (hy : z.2 = intCast y) : z.1 ∈ d.hardFiber y := by
  obtain ⟨v,_,hv,hx⟩ := hz
  have he : intCast v = intCast y := hv.symm.trans hy
  simpa only [Data.hardFiber,he] using hx

theorem fiber_original_iff (d : Data n p m r) (y : IntVector p) (hy : y ∈ d.Y)
    (x : RealVector n) : x ∈ d.feasibleFiber y ↔ (x,intCast y) ∈ d.original := by
  constructor
  · rintro ⟨hx,hg⟩
    exact ⟨⟨y,hy,rfl,hx⟩,hg⟩
  · rintro ⟨hb,hg⟩
    exact ⟨base_hard hb rfl,hg⟩

theorem hardFiber_convex {d : Data n p m r} (hX : Convex ℝ d.X) (y : IntVector p) :
    Convex ℝ (d.hardFiber y) := by
  intro x hx z hz a b ha hb hab
  refine ⟨hX hx.1 hz.1 ha hb hab,?_⟩
  intro i
  have he : (a • x + b • z, intCast y) =
      a • (x,intCast y) + b • (z,intCast y) := by
    apply Prod.ext
    · rfl
    · change intCast y = a • intCast y + b • intCast y
      rw [← add_smul,hab,one_smul]
  rw [he,linearForm_affine]
  calc
    a * LinearForm (d.A i) (d.E i) (x,intCast y) +
        b * LinearForm (d.A i) (d.E i) (z,intCast y)
        ≤ a * d.b i + b * d.b i := add_le_add
          (mul_le_mul_of_nonneg_left (hx.2 i) ha)
          (mul_le_mul_of_nonneg_left (hz.2 i) hb)
    _ = d.b i := by rw [← add_mul,hab,one_mul]

def Data.restSet (d : Data n p m r) (y : IntVector p) : Set (RealVector (n+m)) :=
  {q ∈ weightedX ⁻¹' d.hardFiber y |
    ∀ i, weightedLiftRows (Fin.elim0 : Fin 0 → RealVector n → ℝ) (d.soft y) i q ≤ 0}

def Data.restCost (_d : Data n p m r) : RealVector (n+m) →L[ℝ] ℝ :=
  weightedLiftObjective (fun _ : Fin m => 1)

theorem empty_hard_region (C : Set (RealVector n)) :
    weightedHardRegion C (Fin.elim0 : Fin 0 → RealVector n → ℝ) = C := by
  ext x
  simp [weightedHardRegion]

theorem restSet_insert_iff (d : Data n p m r) (y : IntVector p)
    (x : RealVector n) (s : RealVector m) :
    weightedInsert x s ∈ d.restSet y ↔
      x ∈ d.hardFiber y ∧ (∀ j, d.soft y j x ≤ s j) ∧ ∀ j, 0 ≤ s j := by
  simp only [Data.restSet,Set.mem_setOf_eq,Set.mem_preimage,weighted_lift_rows_iff,
    weightedX_insert,weightedV_insert]
  simp

@[simp] theorem restCost_insert (d : Data n p m r) (x : RealVector n) (s : RealVector m) :
    d.restCost (weightedInsert x s) = ∑ j, s j := by simp [Data.restCost]

structure Event (d : Data n p m r) where
  target : IntVector p
  target_mem : target ∈ d.Y
  x : RealVector n
  restoration : Option (RealVector m)
  objectiveScale : ℝ
  constraintScale : Fin m → ℝ

def Event.anchor {d : Data n p m r} (e : Event d) : Point n p :=
  (e.x,intCast e.target)

def Event.token {d : Data n p m r} (e : Event d) : Token n p m :=
  ⟨e.anchor,e.objectiveScale,e.constraintScale⟩

def EventValid (d : Data n p m r) (e : Event d) : Prop :=
  e.token.Safe d ∧ match e.restoration with
  | none => IsMinimizer (d.feasibleFiber e.target) (d.fiberObjective e.target) e.x
  | some s => ¬ (d.feasibleFiber e.target).Nonempty ∧
      IsMinimizer (d.restSet e.target) d.restCost (weightedInsert e.x s)

theorem event_feasible {d : Data n p m r} {e : Event d}
    (he : EventValid d e) (hn : e.restoration = none) : e.anchor ∈ d.original := by
  have h := he.2
  rw [hn] at h
  exact (fiber_original_iff d e.target e.target_mem e.x).mp h.1

theorem event_hard {d : Data n p m r} {e : Event d}
    (he : EventValid d e) : e.x ∈ d.hardFiber e.target := by
  have h := he.2
  cases hs : e.restoration with
  | none =>
    rw [hs] at h
    exact h.1.1
  | some s =>
    rw [hs] at h
    have hx := h.2.1.1
    simpa only [Set.mem_preimage,weightedX_insert] using hx

theorem event_active {d : Data n p m r} {e : Event d}
    (he : EventValid d e) : e.target ∈ d.activeY := by
  classical
  exact Finset.mem_filter.mpr ⟨e.target_mem,⟨e.x,event_hard he⟩⟩

theorem original_subset_relaxation {d : Data n p m r} (h : RelaxationRegularity d) :
    d.original ⊆ d.relaxation := by
  rintro ⟨x,z⟩ ⟨⟨y,hy,hz,hx⟩,hg⟩
  change z = intCast y at hz
  subst z
  exact ⟨hx.1,h.contains y hy,hx.2,hg⟩

theorem master_relaxation {d : Data n p m r} (hr : Regularity d)
    {H : List (Token n p m)} (hs : SafeRows d H) :
    EpigraphLift d.original d.f ⊆ master d H := by
  rw [← trueEpigraph_eq d]
  exact Quadratic.trueEpigraph_subset_quadraticMaster
    (regularity_masterData hr) (safeRows_safeHistory hs)

theorem master_lower_bound {d : Data n p m r} (hr : Regularity d)
    {H : List (Token n p m)} (hs : SafeRows d H) {q : Point n p × ℝ}
    (hq : IsMinimizer (master d H) Prod.snd q) :
    IsLowerBound d.original d.f q.2 := by
  intro z hz
  exact hq.2 (z,d.f z) (master_relaxation hr hs ⟨hz,le_rfl⟩)

theorem master_antitone (d : Data n p m r) {H K : List (Token n p m)}
    (h : H ⊆ K) : master d K ⊆ master d H := by
  intro q hq
  obtain ⟨hb,hf,hg⟩ := (master_mem_iff d K q).mp hq
  exact (master_mem_iff d H q).mpr
    ⟨hb,fun t ht => hf t (h ht),fun t ht j => hg t (h ht) j⟩

end Chapter05.QOA
