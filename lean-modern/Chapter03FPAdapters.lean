module

public import Chapter03FPModel
public import Chapter03FPFormulation

@[expose] public section

/-! Candidate source formulation and optimizer identities for the concrete pump.
These algebraic adapters do not assume normal validity, progress or a return theorem. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.FP Chapter03.FPFormulation
namespace Chapter03.FPAdapters
variable {n m l r : ℕ}

/-- The source base adds no restriction to a tangent master that already
retains the same affine rows and bounded integer cylinder. -/
theorem masterOn_base_eq_univ (d : Data n m l r) {k : ℕ}
    (c : TangentFamily n m l k) :
    d.model.masterOn c d.base = d.model.masterOn c Set.univ := by
  ext p
  constructor
  · rintro ⟨⟨⟨hb,hcut⟩,hlin⟩,hy⟩
    exact ⟨⟨⟨Set.mem_univ _,hcut⟩,hlin⟩,hy⟩
  · rintro ⟨⟨⟨_,hcut⟩,hlin⟩,y,hbox,hp⟩
    have hb : p ∈ d.base := by
      refine ⟨hlin,?_⟩
      rw [hp]
      exact hbox
    exact ⟨⟨⟨hb,hcut⟩,hlin⟩,y,hbox,hp⟩

theorem epigraph_base_eq_univ (d : Data n m l r) {k : ℕ}
    (c : TangentFamily n m l k) (Df : Fin k → Point n m →L[ℝ] ℝ) :
    Chapter06.EpigraphMaster d.model d.f c Df d.base =
      Chapter06.EpigraphMaster d.model d.f c Df Set.univ := by
  unfold Chapter06.EpigraphMaster
  rw [masterOn_base_eq_univ]

/-- The actual pump epigraph can therefore use convexity on the actual base. -/
theorem epigraph_eq_base (d : Data n m l r) (s : State n m) :
    epigraph d s = Chapter06.EpigraphMaster d.model d.f (family d s)
      (fun i => d.Df ((anchors d s).get i).point) d.base := by
  exact (epigraph_base_eq_univ d _ _).symm

/-- The complete master retains every extra row beyond the tangent epigraph. -/
theorem master_epigraph_intersection (d : Data n m l r) (s : State n m) :
    master d s =
      Chapter06.EpigraphMaster d.model d.f (family d s)
        (fun i => d.Df ((anchors d s).get i).point) Set.univ ∩
      {z | retainedNormals s z.1} ∩ {z | noGoods s z.1} ∩
      {z | Allows (d.level s.incumbent) z.2} := by
  ext z
  simp only [master,epigraph,Set.mem_inter_iff,Set.mem_setOf_eq]
  tauto

/-- Fully expanded source rows: affine bounds/integrality, selected nonlinear
and separate nonlinear objective tangents, normals, no-goods and height cutoff. -/
theorem master_source_rows_iff (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) : z ∈ master d s ↔
    (∀ row, LinearForm (d.model.A row) (d.model.B row) z.1 ≤ d.model.rhs row) ∧
    (∃ y : IntVector m, y ∈ IntegerBox d.model.lo d.model.hi ∧ z.1.2 = intCast y) ∧
    (∀ i j, j ∈ (family d s).selected i →
      d.model.g j ((family d s).origin i) +
        (family d s).derivative i j (z.1-(family d s).origin i) ≤ 0) ∧
    (∀ i, d.f ((anchors d s).get i).point +
      d.Df ((anchors d s).get i).point (z.1-((anchors d s).get i).point) ≤ z.2) ∧
    retainedNormals s z.1 ∧ noGoods s z.1 ∧ Allows (d.level s.incumbent) z.2 := by
  simp only [master,epigraph,Chapter06.EpigraphMaster,ModelData.masterOn,
    MixedFeasible,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_univ,true_and,
    ModelData.linearRegion,IntegerCylinder,TangentFamily.cutRegion]
  simp only [family,intCast]
  tauto

theorem epigraph_integer_box {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} (hz : z ∈ epigraph d s) :
    ∃ y : IntVector m, y ∈ IntegerBox d.model.lo d.model.hi ∧ z.1.2 = intCast y := by
  exact hz.1.2

theorem epigraph_inBox {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} (hz : z ∈ epigraph d s) :
    InBox d.model.lo d.model.hi z.1.2 := by
  obtain ⟨y,hy,he⟩ := epigraph_integer_box hz
  rw [he]
  exact hy

theorem cast_injective : Function.Injective (@intCast m) := by
  intro y c h
  funext j
  have hj := congrFun h j
  change (y j : ℝ) = (c j : ℝ) at hj
  exact_mod_cast hj

theorem integer_point_l1_nogood_iff (p : Point n m) (c : IntVector m)
    (hp : ∃ y : IntVector m, p.2 = intCast y) :
    1 ≤ l1Distance p.2 (intCast c) ↔ p.2 ≠ intCast c := by
  obtain ⟨y,hy⟩ := hp
  rw [hy]
  change 1 ≤ l1Distance (fun j => (y j:ℝ)) (fun j => (c j:ℝ)) ↔ intCast y ≠ intCast c
  rw [integer_l1_nogood_iff]
  exact cast_injective.ne_iff.symm

/-- Literal distance exclusion for every successful event in the actual history. -/
def L1NoGoods (s : State n m) (p : Point n m) : Prop :=
  ∀ e ∈ s.history, e.success ≠ none → 1 ≤ l1Distance p.2 (intCast e.target)

theorem noGoods_iff_l1 (s : State n m) (p : Point n m)
    (hp : ∃ y : IntVector m, p.2 = intCast y) :
    noGoods s p ↔ L1NoGoods s p := by
  constructor
  · intro h e he hs
    exact (integer_point_l1_nogood_iff p e.target hp).mpr (h e he hs)
  · intro h e he hs
    exact (integer_point_l1_nogood_iff p e.target hp).mp (h e he hs)

/-- All-coordinate exact auxiliaries, separately for each successful history event. -/
def AbsNoGoods (d : Data n m l r) (s : State n m) (p : Point n m) : Prop :=
  ∀ e ∈ s.history, e.success ≠ none → ∃ w v,
    AbsVector d.model.lo d.model.hi (intCast e.target) p.2 w v ∧ 1 ≤ ∑ j, w j

/-- Literal source endpoint/interior auxiliaries for the same actual history. -/
def SourceAbsNoGoods (d : Data n m l r) (s : State n m) (p : Point n m) : Prop :=
  ∀ e ∈ s.history, e.success ≠ none → ∃ w v,
    InteriorAbsVector d.model.lo d.model.hi (intCast e.target) p.2 w v ∧
      1 ≤ endpointRow d.model.lo d.model.hi (intCast e.target) p.2 w

theorem noGoods_iff_abs {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} (hz : z ∈ epigraph d s) :
    noGoods s z.1 ↔ AbsNoGoods d s z.1 := by
  obtain ⟨y,hy,he⟩ := epigraph_integer_box hz
  rw [noGoods_iff_l1 s z.1 ⟨y,he⟩]
  constructor
  · intro h e hem hs
    exact (lifted_nogood_projection_iff _ _ _ _).mpr ⟨epigraph_inBox hz,h e hem hs⟩
  · intro h e hem hs
    exact ((lifted_nogood_projection_iff _ _ _ _).mp (h e hem hs)).2

theorem noGoods_iff_source_abs {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} (hz : z ∈ epigraph d s) :
    noGoods s z.1 ↔ SourceAbsNoGoods d s z.1 := by
  obtain ⟨y,hy,he⟩ := epigraph_integer_box hz
  rw [noGoods_iff_l1 s z.1 ⟨y,he⟩]
  constructor
  · intro h e hem hs
    exact ((source_lifted_nogood_projection_iff _ _ _ _).mpr
      ⟨epigraph_inBox hz,h e hem hs⟩).2
  · intro h e hem hs
    exact ((source_lifted_nogood_projection_iff _ _ _ _).mp
      ⟨epigraph_inBox hz,h e hem hs⟩).2

/-- All history auxiliaries can be chosen as one finite family. -/
theorem history_auxiliary_assembly (s : State n m)
    (R : Event n m → (Fin m → ℝ) → (Fin m → Bool) → Prop) :
    (∀ e ∈ s.history, e.success ≠ none → ∃ w v, R e w v) ↔
    ∃ W : Fin s.history.length → Fin m → ℝ,
      ∃ V : Fin s.history.length → Fin m → Bool,
        ∀ i, (s.history.get i).success ≠ none → R (s.history.get i) (W i) (V i) := by
  classical
  constructor
  · intro h
    have heach : ∀ i : Fin s.history.length, ∃ w v,
        (s.history.get i).success ≠ none → R (s.history.get i) w v := by
      intro i
      by_cases hs : (s.history.get i).success = none
      · exact ⟨fun _ => 0,fun _ => false,fun hn => False.elim (hn hs)⟩
      · obtain ⟨w,v,hv⟩ := h _ (List.get_mem s.history i) hs
        exact ⟨w,v,fun _ => hv⟩
    choose W V hWV using heach
    exact ⟨W,V,hWV⟩
  · rintro ⟨W,V,h⟩ e he hs
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
    exact ⟨W i,V i,h i hs⟩

theorem noGoods_iff_joint_abs {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} (hz : z ∈ epigraph d s) : noGoods s z.1 ↔
    ∃ W : Fin s.history.length → Fin m → ℝ,
      ∃ V : Fin s.history.length → Fin m → Bool,
        ∀ i, (s.history.get i).success ≠ none →
          AbsVector d.model.lo d.model.hi (intCast (s.history.get i).target)
            z.1.2 (W i) (V i) ∧ 1 ≤ ∑ j, W i j := by
  rw [noGoods_iff_abs hz]
  exact history_auxiliary_assembly s _

theorem noGoods_iff_joint_source_abs {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} (hz : z ∈ epigraph d s) : noGoods s z.1 ↔
    ∃ W : Fin s.history.length → Fin m → ℝ,
      ∃ V : Fin s.history.length → Fin m → Bool,
        ∀ i, (s.history.get i).success ≠ none →
          InteriorAbsVector d.model.lo d.model.hi (intCast (s.history.get i).target)
            z.1.2 (W i) (V i) ∧
          1 ≤ endpointRow d.model.lo d.model.hi (intCast (s.history.get i).target)
            z.1.2 (W i) := by
  rw [noGoods_iff_source_abs hz]
  exact history_auxiliary_assembly s _

theorem master_l1_rows_iff (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) : z ∈ master d s ↔
    z ∈ epigraph d s ∧ retainedNormals s z.1 ∧ L1NoGoods s z.1 ∧
      Allows (d.level s.incumbent) z.2 := by
  constructor
  · rintro ⟨he,hn,hg,hc⟩
    obtain ⟨y,hy,hyi⟩ := epigraph_integer_box he
    exact ⟨he,hn,(noGoods_iff_l1 _ _ ⟨y,hyi⟩).mp hg,hc⟩
  · rintro ⟨he,hn,hg,hc⟩
    obtain ⟨y,hy,hyi⟩ := epigraph_integer_box he
    exact ⟨he,hn,(noGoods_iff_l1 _ _ ⟨y,hyi⟩).mpr hg,hc⟩

theorem master_abs_rows_iff (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) : z ∈ master d s ↔
    z ∈ epigraph d s ∧ retainedNormals s z.1 ∧ AbsNoGoods d s z.1 ∧
      Allows (d.level s.incumbent) z.2 := by
  constructor
  · rintro ⟨he,hn,hg,hc⟩
    exact ⟨he,hn,(noGoods_iff_abs he).mp hg,hc⟩
  · rintro ⟨he,hn,hg,hc⟩
    exact ⟨he,hn,(noGoods_iff_abs he).mpr hg,hc⟩

theorem master_source_abs_rows_iff (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) : z ∈ master d s ↔
    z ∈ epigraph d s ∧ retainedNormals s z.1 ∧ SourceAbsNoGoods d s z.1 ∧
      Allows (d.level s.incumbent) z.2 := by
  constructor
  · rintro ⟨he,hn,hg,hc⟩
    exact ⟨he,hn,(noGoods_iff_source_abs he).mp hg,hc⟩
  · rintro ⟨he,hn,hg,hc⟩
    exact ⟨he,hn,(noGoods_iff_source_abs he).mpr hg,hc⟩

/-- Simultaneously eliminating the complete source-history auxiliary family
recovers the actual master, with every other master row preserved. -/
theorem master_joint_source_projection_iff (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) : z ∈ master d s ↔
    ∃ W : Fin s.history.length → Fin m → ℝ,
      ∃ V : Fin s.history.length → Fin m → Bool,
        z ∈ epigraph d s ∧ retainedNormals s z.1 ∧
        (∀ i, (s.history.get i).success ≠ none →
          InteriorAbsVector d.model.lo d.model.hi (intCast (s.history.get i).target)
            z.1.2 (W i) (V i) ∧
          1 ≤ endpointRow d.model.lo d.model.hi (intCast (s.history.get i).target)
            z.1.2 (W i)) ∧ Allows (d.level s.incumbent) z.2 := by
  constructor
  · rintro ⟨he,hn,hg,hc⟩
    obtain ⟨W,V,hWV⟩ := (noGoods_iff_joint_source_abs he).mp hg
    exact ⟨W,V,he,hn,hWV,hc⟩
  · rintro ⟨W,V,he,hn,hWV,hc⟩
    exact ⟨he,hn,(noGoods_iff_joint_source_abs he).mpr ⟨W,V,hWV⟩,hc⟩

/-- A target's source bounds follow from the actual master reply. -/
theorem event_target_mem_box {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} {e : Event n m}
    (hz : z ∈ master d s) (he : EventReply d s z e) :
    e.target ∈ IntegerBox d.model.lo d.model.hi := by
  obtain ⟨y,hy,hyi⟩ := epigraph_integer_box hz.1
  have heq : e.target=y := cast_injective (he.target_eq.symm.trans hyi)
  rwa [heq]

theorem event_bigM_nonnegative {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} {e : Event n m}
    (hz : z ∈ master d s) (he : EventReply d s z e) :
    ∀ j, 0 ≤ 2*((e.target j:ℝ)-d.model.lo j) ∧
      0 ≤ 2*(d.model.hi j-(e.target j:ℝ)) := by
  intro j
  have hb := event_target_mem_box hz he j
  constructor <;> linarith [hb.1,hb.2]

/-- Displacement uses only y; neither x nor the epigraph height is included. -/
def yDisplacement (s : State n m) (z : Point n m × ℝ) : Chapter07.Vec m :=
  fun j => z.1.2 j-s.reference.2 j

def MasterL1Lift (d : Data n m l r) (s : State n m) :
    Set ((Point n m × ℝ) × Chapter07.Vec m × Chapter07.Vec m) :=
  Chapter07.L1Lift (master d s) (yDisplacement s)

def canonicalMasterLift (s : State n m) (z : Point n m × ℝ) :
    (Point n m × ℝ) × Chapter07.Vec m × Chapter07.Vec m :=
  Chapter07.l1Canonical (yDisplacement s) z

theorem master_cost_is_y_l1 (s : State n m) (z : Point n m × ℝ) :
    masterCost s z = Chapter07.l1 (yDisplacement s z) := rfl

theorem master_l1_lift_membership (d : Data n m l r) (s : State n m)
    (q : (Point n m × ℝ) × Chapter07.Vec m × Chapter07.Vec m) :
    q ∈ MasterL1Lift d s ↔ q.1 ∈ master d s ∧
      (∀ j, 0 ≤ q.2.1 j) ∧ (∀ j, 0 ≤ q.2.2 j) ∧
      ∀ j, q.2.1 j-q.2.2 j=q.1.1.2 j-s.reference.2 j := Iff.rfl

theorem canonicalMasterLift_feasible {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} (hz : z ∈ master d s) :
    canonicalMasterLift s z ∈ MasterL1Lift d s :=
  Chapter07.l1_canonical_feasible _ _ hz

theorem master_l1_lift_projection_iff (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) :
    (∃ a b : Chapter07.Vec m, (z,a,b) ∈ MasterL1Lift d s) ↔ z ∈ master d s := by
  constructor
  · rintro ⟨a,b,h⟩
    exact h.1
  · intro h
    exact ⟨Chapter07.posPart (yDisplacement s z),Chapter07.negPart (yDisplacement s z),
      canonicalMasterLift_feasible h⟩

theorem canonicalMasterLift_cost (s : State n m) (z : Point n m × ℝ) :
    Chapter07.l1LiftCost (canonicalMasterLift s z) = masterCost s z :=
  Chapter07.l1_canonical_cost _ _

theorem master_minimizer_lift {d : Data n m l r} {s : State n m}
    {z : Point n m × ℝ} (hz : IsMinimizer (master d s) (masterCost s) z) :
    IsMinimizer (MasterL1Lift d s) Chapter07.l1LiftCost (canonicalMasterLift s z) :=
  Chapter07.l1_minimizer_lift _ _ hz

theorem master_minimizer_projection {d : Data n m l r} {s : State n m}
    {q : (Point n m × ℝ) × Chapter07.Vec m × Chapter07.Vec m}
    (hq : IsMinimizer (MasterL1Lift d s) Chapter07.l1LiftCost q) :
    IsMinimizer (master d s) (masterCost s) q.1 ∧
      Chapter07.l1LiftCost q = masterCost s q.1 :=
  Chapter07.l1_minimizer_projection _ _ hq

theorem master_canonical_minimizer_iff (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) :
    IsMinimizer (MasterL1Lift d s) Chapter07.l1LiftCost (canonicalMasterLift s z) ↔
      IsMinimizer (master d s) (masterCost s) z := by
  constructor
  · intro h
    exact (master_minimizer_projection h).1
  · exact master_minimizer_lift

end Chapter03.FPAdapters



