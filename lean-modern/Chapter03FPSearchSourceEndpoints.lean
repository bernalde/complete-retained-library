module

public import Chapter03FPSearchBoxSource
public import Chapter03FPSearchSoftSource

@[expose] public section

/-! Separate full-space and bounds-restricted thesis applications. The auxiliary
boxed copy establishes identities for the stronger full-space specialization;
no box-restricted Analytic or CQ is transported to full space. The direct
bounds-restricted route uses the actual g-bound rows in CQ without additional
hard copies. No original g row is deleted. -/
noncomputable section
open Chapter02 Chapter03.FP Chapter03.OAKKT
namespace Chapter03.FPSearch
variable {n m l : ℕ}

/-- Only the base changes; all original functions and derivative fields survive. -/
def boxedData (d : Data n m l) (x : Bounds n) (y : Bounds m) : Data n m l :=
  {d with base := FPUnbounded.boundProduct x y}

theorem boxedData_rows (d : Data n m l) (x : Bounds n) (y : Bounds m)
    (s : State n m) (p : Point n m) :
    Rows (boxedData d x y) s p ↔ Rows d s p := Iff.rfl

theorem boxedData_softMaster (d : Data n m l) (x : Bounds n) (y : Bounds m)
    (mode : Mode) (s : State n m) :
    softMaster (boxedData d x y) mode s = softMaster d mode s := rfl

theorem boxedData_relaxation (d : Data n m l) (x : Bounds n) (y : Bounds m)
    (hbase : d.base = Set.univ) (B : SoftBoundRows (boxedData d x y) x y) :
    (boxedData d x y).relaxation = d.relaxation := by
  ext p
  rw [B.relaxation_iff]
  simp only [Data.relaxation,hbase,Set.mem_setOf_eq,Set.mem_univ,true_and,boxedData]

theorem boxedData_original (d : Data n m l) (x : Bounds n) (y : Bounds m)
    (hbase : d.base = Set.univ) (B : SoftBoundRows (boxedData d x y) x y) :
    (boxedData d x y).original = d.original := by
  ext p
  change (p ∈ (boxedData d x y).relaxation ∧ Integral p) ↔ _
  rw [boxedData_relaxation d x y hbase B]
  rfl

/-- Equality concerns the entire retained first-search master, not just its
original feasible points. Actual seed derivatives discharge base redundancy. -/
theorem boxedData_master (d : Data n m l) (x : Bounds n) (y : Bounds m)
    (hbase : d.base = Set.univ) (B : SoftBoundRows (boxedData d x y) x y)
    (mode : Mode) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) :
    master (boxedData d x y) mode s = master d mode s := by
  rw [B.master_eq_soft mode s hd,boxedData_softMaster]
  ext p
  simp only [master,softMaster,hbase,Set.mem_setOf_eq,Set.mem_univ,true_and]

/-- The same L1 cost preserves every exact tied master optimizer. -/
theorem boxedData_master_minimizer (d : Data n m l) (x : Bounds n) (y : Bounds m)
    (hbase : d.base = Set.univ) (B : SoftBoundRows (boxedData d x y) x y)
    (mode : Mode) (s : State n m)
    (hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed) (p : Point n m) :
    IsMinimizer (master (boxedData d x y) mode s) (masterCost s) p ↔
      IsMinimizer (master d mode s) (masterCost s) p := by
  rw [boxedData_master d x y hbase B mode s hd]

/-- Actual finite target containment for the full-space thesis data. The
ambient Analytic premise belongs to d itself, not to the auxiliary boxed copy. -/
theorem fullSpace_bound_rows_target_bound (d : Data n m l)
    (x : Bounds n) (y : Bounds m) (hbase : d.base = Set.univ)
    (B : SoftBoundRows (boxedData d x y) x y) (h : Analytic d)
    (mode : Mode) (lo hi : RealVector m)
    (hl : ∀ i, y.lower i = .finite (lo i))
    (hu : ∀ i, y.upper i = .finite (hi i)) :
    TargetBound d mode (integerBox_finite lo hi).toFinset := by
  intro s hs p hp q hq
  have hd : ∀ j, HasFDerivAt (d.g j) (d.Dg j s.seed) s.seed :=
    fun j => h.derivative_g j s.seed hs.seed.1
  have hbox : p ∈ master (boxedData d x y) mode s := by
    rw [boxedData_master d x y hbase B mode s hd]
    exact hp
  exact B.soft_target_mem mode s hd lo hi hl hu hbox.2 q hq

/-- Thesis basic interpretation: no additional hard-bound CQ rows. Every
original g row is still present, and its uniform joint LICQ is explicit. -/
theorem thesis_basic_first_feasibility (d : Data n m l)
    (x : Bounds n) (y : Bounds m) (hbase : d.base = Set.univ)
    (B : SoftBoundRows (boxedData d x y) x y) (h : Analytic d)
    (lo hi : RealVector m)
    (hl : ∀ i, y.lower i = .finite (lo i))
    (hu : ∀ i, y.upper i = .finite (hi i))
    (hcq : ProjectionLICQ d (fullSpaceBaseRows d hbase)
      (integerBox_finite lo hi).toFinset) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d .basic) ∧
      ∀ (initial : Initialization d) (choose : Selector d .basic),
        ∃ out, procedureWithFuel d .basic initial choose
            ((integerBox_finite lo hi).toFinset.card + 1) = some out ∧
          out.Correct d ∧ out.Counts (integerBox_finite lo hi).toFinset.card := by
  exact fullSpace_basic_first_feasibility d hbase h
    (integerBox_finite lo hi).toFinset
    (fullSpace_bound_rows_target_bound d x y hbase B h .basic lo hi hl hu) hcq

/-- Thesis enhanced interpretation retains its actual normals and needs no CQ. -/
theorem thesis_enhanced_first_feasibility (d : Data n m l)
    (x : Bounds n) (y : Bounds m) (hbase : d.base = Set.univ)
    (B : SoftBoundRows (boxedData d x y) x y) (h : Analytic d)
    (lo hi : RealVector m)
    (hl : ∀ i, y.lower i = .finite (lo i))
    (hu : ∀ i, y.upper i = .finite (hi i)) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d .enhanced) ∧
      ∀ (initial : Initialization d) (choose : Selector d .enhanced),
        ∃ out, procedureWithFuel d .enhanced initial choose
            ((integerBox_finite lo hi).toFinset.card + 1) = some out ∧
          out.Correct d ∧ out.Counts (integerBox_finite lo hi).toFinset.card := by
  exact qualified_enhanced_first_feasibility d h
    (integerBox_finite lo hi).toFinset
    (fullSpace_bound_rows_target_bound d x y hbase B h .enhanced lo hi hl hu)

/-- Article enhanced interpretation uses its literal hard X/Y boxes. -/
theorem ArticleData.enhanced_first_feasibility (a : ArticleData n m l)
    (h : Analytic a.toData) (lo hi : RealVector m)
    (hl : ∀ i, a.yBounds.lower i = .finite (lo i))
    (hu : ∀ i, a.yBounds.upper i = .finite (hi i)) :
    Nonempty (Initialization a.toData) ∧ Nonempty (Selector a.toData .enhanced) ∧
      ∀ (initial : Initialization a.toData) (choose : Selector a.toData .enhanced),
        ∃ out, procedureWithFuel a.toData .enhanced initial choose
            ((integerBox_finite lo hi).toFinset.card + 1) = some out ∧
          out.Correct a.toData ∧ out.Counts (integerBox_finite lo hi).toFinset.card := by
  exact qualified_enhanced_first_feasibility a.toData h
    (integerBox_finite lo hi).toFinset (a.target_bound .enhanced lo hi hl hu)

/-- All original g gradients, including its actual bound rows, and no additional
hard-bound copies. Uniformity covers every selectable projection minimum. -/
def OriginalRowsProjectionLICQ (d : Data n m l) (Q : Finset (IntVector m)) : Prop :=
  ∀ q ∈ Q, ∀ p, IsMinimizer d.relaxation (distance q) p →
    JointLICQ d.g (fun j => d.Dg j p) p

/-- Actual bound rows identify the full projection domain with the all-g set.
Only ambient derivatives at the attained point inside the base are needed. -/
theorem SoftBoundRows.projection_normal {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (h : Analytic d) (q : IntVector m) (p z : Point n m)
    (hp : IsMinimizer d.relaxation (distance q) p)
    (hcq : JointLICQ d.g (fun j => d.Dg j p) p)
    (hz : ∀ j, d.g j p = 0 → d.Dg j p (z-p) ≤ 0) :
    0 ≤ @inner ℝ _ _ (Chapter03.yMap n m p - intY q)
      (Chapter03.yMap n m z - Chapter03.yMap n m p) := by
  have hset : {w | ∀ j, d.g j w ≤ 0} = d.relaxation :=
    Set.ext (fun w => (B.relaxation_iff w).symm)
  apply joint_projection_normal_of_licq d.g (fun j => d.Dg j p) q p z
  · simpa only [hset] using hp
  · exact fun j => h.derivative_g j p hp.1.1
  · exact hcq
  · exact hz

/-- Derive the basic normal law from original active rows. Every retained affine
row is enforced by its initial exact tangent; no extra normal is stored. -/
theorem SoftBoundRows.basic_normal_law {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (h : Analytic d) (Q : Finset (IntVector m))
    (hcq : OriginalRowsProjectionLICQ d Q) : NormalLaw d .basic Q := by
  intro s hs hQ p hp e he
  exact B.projection_normal h e.target e.projection p
    (hs.events e he).projection_min
    (hcq e.target (hQ e he) e.projection (hs.events e he).projection_min)
    (fun j hj => master_active_tangent d h hs hp he j hj)

theorem SoftBoundRows.target_bound {d : Data n m l} {x : Bounds n} {y : Bounds m}
    (B : SoftBoundRows d x y) (h : Analytic d) (mode : Mode)
    (lo hi : RealVector m)
    (hl : ∀ i, y.lower i = .finite (lo i))
    (hu : ∀ i, y.upper i = .finite (hi i)) :
    TargetBound d mode (integerBox_finite lo hi).toFinset := by
  intro s hs p hp q hq
  exact B.soft_target_mem mode s (fun j => h.derivative_g j s.seed hs.seed.1)
    lo hi hl hu hp.2 q hq

/-- Bounds-restricted thesis specialization: original g already encodes every
domain side. Analytic stays on that actual box; CQ uses original g exactly once.
Actual duplicate g rows survive. This is not a global-convexity extension. -/
theorem thesis_bound_rows_basic_first_feasibility (d : Data n m l)
    (x : Bounds n) (y : Bounds m) (B : SoftBoundRows d x y) (h : Analytic d)
    (lo hi : RealVector m)
    (hl : ∀ i, y.lower i = .finite (lo i))
    (hu : ∀ i, y.upper i = .finite (hi i))
    (hcq : OriginalRowsProjectionLICQ d (integerBox_finite lo hi).toFinset) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d .basic) ∧
      ∀ (initial : Initialization d) (choose : Selector d .basic),
        ∃ out, procedureWithFuel d .basic initial choose
            ((integerBox_finite lo hi).toFinset.card + 1) = some out ∧
          out.Correct d ∧ out.Counts (integerBox_finite lo hi).toFinset.card := by
  exact ⟨initialization_nonempty d h,selector_nonempty d h .basic,
    fun initial choose => initialized_finite_return d h
      (B.target_bound h .basic lo hi hl hu)
      (B.basic_normal_law h (integerBox_finite lo hi).toFinset hcq) initial choose⟩

/-- The same literal bound-row interpretation with enhanced normals needs no CQ. -/
theorem thesis_bound_rows_enhanced_first_feasibility (d : Data n m l)
    (x : Bounds n) (y : Bounds m) (B : SoftBoundRows d x y) (h : Analytic d)
    (lo hi : RealVector m)
    (hl : ∀ i, y.lower i = .finite (lo i))
    (hu : ∀ i, y.upper i = .finite (hi i)) :
    Nonempty (Initialization d) ∧ Nonempty (Selector d .enhanced) ∧
      ∀ (initial : Initialization d) (choose : Selector d .enhanced),
        ∃ out, procedureWithFuel d .enhanced initial choose
            ((integerBox_finite lo hi).toFinset.card + 1) = some out ∧
          out.Correct d ∧ out.Counts (integerBox_finite lo hi).toFinset.card := by
  exact qualified_enhanced_first_feasibility d h
    (integerBox_finite lo hi).toFinset (B.target_bound h .enhanced lo hi hl hu)

end Chapter03.FPSearch
