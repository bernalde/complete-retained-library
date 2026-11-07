module

public import Chapter03OASoftAvailability

@[expose] public section

/-! Finite-fiber attainment for a fixed arbitrary soft tangent family.
The additional predicate removes complete integer fibers. Objective tangents
remain explicit hard rows; no alpha-dependent condition is hidden in `keep`.
Weights are arbitrary real numbers. Closed cost values and attainment require
neither bounded feasible sets nor positive weights, convex source hypotheses,
KKT certificates, or a particular chronological history. -/
noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OASoftMaster Chapter03.OAExistence
attribute [local instance] Classical.propDecidable
namespace Chapter03.PumpSoftAttainment
variable {n m l r k : ℕ}

/-- An arbitrary y-only restriction chooses a subset of the finite integer box. -/
def allowed (d : OAExec.Data n m l r) (keep : Point n m → Prop) : Finset (IntVector m) :=
  d.box.filter (fun y => keep (0,intCast y))

/-- All hard linear, objective, slack and softened constraint inequalities are
represented by the already accepted finite row family. -/
theorem master_rows_iff (d : OAExec.Data n m l r) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (keep : Point n m → Prop) (z : Candidate c) :
    z ∈ master d.model d.f c df keep ↔
      (∀ i, softRow d.model c df i z ≤ softRowBound d.model d.f c df i) ∧
      z.1 ∈ IntegerCylinder d.model.lo d.model.hi ∧ keep z.1 := by
  constructor
  · rintro ⟨hh,hy,hk,hs,hf,hg⟩
    refine ⟨?_,hy,hk⟩
    intro i
    rcases i with (i|i)|(a|a)
    · exact hh i
    · have h := hf i
      change df i z.1 - z.2.1 ≤ _
      dsimp only [softRowBound, Sum.elim]
      rw [map_sub] at h
      linarith
    · exact neg_nonpos.mpr (hs a)
    · have h := hg a
      change c.derivative a.1.1 a.1.2 z.1 - z.2.2 a ≤ _
      dsimp only [softRowBound, Sum.elim]
      rw [map_sub] at h
      linarith
  · rintro ⟨hr,hy,hk⟩
    refine ⟨?_,hy,hk,?_,?_,?_⟩
    · intro i; exact hr (.inl (.inl i))
    · intro a; exact neg_nonpos.mp (hr (.inr (.inl a)))
    · intro i
      have h := hr (.inl (.inr i))
      change df i z.1 - z.2.1 ≤ _ at h
      dsimp only [softRowBound, Sum.elim] at h
      rw [map_sub]
      linarith
    · intro a
      have h := hr (.inr (.inr a))
      change c.derivative a.1.1 a.1.2 z.1 - z.2.2 a ≤ _ at h
      dsimp only [softRowBound, Sum.elim] at h
      rw [map_sub]
      linarith

/-- Fixing y leaves a finite weak affine system in x, alpha and all slacks. -/
def fiberPolyhedron (d : OAExec.Data n m l r) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (y : IntVector m) : Set (SoftFiber c) :=
  {v | ∀ i, ((softRow d.model c df i).comp (softFiberEmbedding c)) v ≤
    softRowBound d.model d.f c df i - softRow d.model c df i ((0,intCast y),0,0)}

theorem fiber_row_identity (d : OAExec.Data n m l r) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (y : IntVector m) (v : SoftFiber c)
    (i : SoftRowIndex c r) :
    softRow d.model c df i (softFiberLift y v) =
      ((softRow d.model c df i).comp (softFiberEmbedding c)) v +
        softRow d.model c df i ((0,intCast y),0,0) := by
  rw [ContinuousLinearMap.comp_apply,←map_add]
  congr 1
  ext <;> simp [softFiberLift,softFiberEmbedding]

theorem fiber_mem_iff (d : OAExec.Data n m l r) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (keep : Point n m → Prop)
    (keep_same_y : ∀ p q : Point n m, p.2 = q.2 → (keep p ↔ keep q))
    (y : IntVector m) (hy : y ∈ allowed d keep) (v : SoftFiber c) :
    softFiberLift y v ∈ master d.model d.f c df keep ↔
      v ∈ fiberPolyhedron d c df y := by
  obtain ⟨hybox,hykeep⟩ := Finset.mem_filter.mp hy
  have hi : (softFiberLift y v).1 ∈ IntegerCylinder d.model.lo d.model.hi :=
    ⟨y,by simpa [OAExec.Data.box] using hybox,rfl⟩
  have hk : keep (softFiberLift y v).1 :=
    (keep_same_y (0,intCast y) (softFiberLift y v).1 rfl).mp hykeep
  rw [master_rows_iff]
  constructor
  · intro h i
    have hr := h.1 i
    rw [fiber_row_identity] at hr
    exact le_sub_iff_add_le.mpr hr
  · intro h
    refine ⟨?_,hi,hk⟩
    intro i
    rw [fiber_row_identity]
    exact le_sub_iff_add_le.mp (h i)

theorem finite_fiber_union (d : OAExec.Data n m l r) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (keep : Point n m → Prop)
    (keep_same_y : ∀ p q : Point n m, p.2 = q.2 → (keep p ↔ keep q)) :
    master d.model d.f c df keep = ⋃ y ∈ allowed d keep,
      softFiberLift y '' fiberPolyhedron d c df y := by
  ext z
  simp only [Set.mem_iUnion,Set.mem_image]
  constructor
  · intro hz
    obtain ⟨y,hy,hey⟩ := hz.2.1
    change z.1.2 = intCast y at hey
    have ha : y ∈ allowed d keep := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [OAExec.Data.box] using hy,?_⟩
      exact (keep_same_y z.1 (0,intCast y) hey).mp hz.2.2.1
    have hl : softFiberLift y (z.1.1,z.2) = z :=
      Prod.ext (Prod.ext rfl hey.symm) rfl
    refine ⟨y,ha,(z.1.1,z.2),?_,hl⟩
    apply (fiber_mem_iff d c df keep keep_same_y y ha _).mp
    rwa [hl]
  · rintro ⟨y,hy,v,hv,rfl⟩
    exact (fiber_mem_iff d c df keep keep_same_y y hy v).mpr hv

theorem cost_finite_union (d : OAExec.Data n m l r) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (keep : Point n m → Prop)
    (keep_same_y : ∀ p q : Point n m, p.2 = q.2 → (keep p ↔ keep q))
    (w : Occurrence c → ℝ) :
    cost w '' master d.model d.f c df keep = ⋃ y ∈ allowed d keep,
      fiberCostLinear w '' fiberPolyhedron d c df y := by
  rw [finite_fiber_union d c df keep keep_same_y]
  have hf (y : IntVector m) : (fun v => cost w (softFiberLift y v)) = fiberCostLinear w :=
    funext (fiber_cost_identity w y)
  simp only [Set.image_iUnion,Set.image_image,hf]

/-- Closed cost values for arbitrary real weights and every complete-fiber keep. -/
theorem soft_master_value_closed (d : OAExec.Data n m l r) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) (keep : Point n m → Prop)
    (keep_same_y : ∀ p q : Point n m, p.2 = q.2 → (keep p ↔ keep q))
    (w : Occurrence c → ℝ) : IsClosed (cost w '' master d.model d.f c df keep) := by
  rw [cost_finite_union d c df keep keep_same_y]
  apply isClosed_biUnion_finset
  intro y _
  exact finite_polyhedron_value_closed
    (fun i => (softRow d.model c df i).comp (softFiberEmbedding c))
    (fun i => softRowBound d.model d.f c df i - softRow d.model c df i ((0,intCast y),0,0))
    (fiberCostLinear w)

/-- Nonempty and bounded-below cost is sufficient; no bounded feasible-master
or positive-weight hypothesis is added. -/
theorem soft_master_attained_of_bddBelow (d : OAExec.Data n m l r)
    (c : TangentFamily n m l k) (df : Fin k → Point n m →L[ℝ] ℝ)
    (keep : Point n m → Prop)
    (keep_same_y : ∀ p q : Point n m, p.2 = q.2 → (keep p ↔ keep q))
    (w : Occurrence c → ℝ) (hne : (master d.model d.f c df keep).Nonempty)
    (hb : BddBelow (cost w '' master d.model d.f c df keep)) :
    ∃ z, IsMinimizer (master d.model d.f c df keep) (cost w) z := by
  have hleast := (soft_master_value_closed d c df keep keep_same_y w).isLeast_csInf
    (hne.image (cost w)) hb
  obtain ⟨z,hz,he⟩ := hleast.1
  refine ⟨z,hz,?_⟩
  intro q hq
  rw [he]
  exact hleast.2 ⟨q,hq,rfl⟩

end Chapter03.PumpSoftAttainment
