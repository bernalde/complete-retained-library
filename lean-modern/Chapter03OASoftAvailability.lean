module

public import Chapter03OASoftRevisitClosure
public import Chapter03OAExistenceMaster
public import Chapter03OAExecKKT
public import Chapter03OAExistenceRestoration

@[expose] public section

/-! Exact constraint-slack master availability. The finite-dimensional continuous
fiber includes every independent occurrence slack. Only nonempty bounded-below
cost values are needed for attainment; neither bounded feasible sets nor positive
weights are assumed. The successful-event result derives the cost bound from
actual KKT and explicit global coverage, not from an assumed comparison. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT Chapter03.OAExistence
attribute [local instance] Classical.propDecidable
namespace Chapter03.OASoftMaster
variable {n m l r k : ℕ}

/-- Cross-fiber sufficient coverage on the actual hard integer domain. -/
def GlobalSupportedCoverage {d : ModelData n m l r} {f : Point n m → ℝ}
    {x : RealVector n} {y : RealVector m} (K : FixedKKT d f x y)
    (c : TangentFamily n m l k) (w : Occurrence c → ℝ)
    (S : Finset (Fin l)) (occ : S → Occurrence c) : Prop :=
  Function.Injective occ ∧
  (∀ j : S, ∀ q : Point n m,
    d.g j (x,y) + K.Dg j (q-(x,y)) =
      d.g (occ j).1.2 (c.origin (occ j).1.1) +
        c.derivative (occ j).1.1 (occ j).1.2 (q-c.origin (occ j).1.1)) ∧
  (∀ j : S, 1000 * K.lambda j ≤ w (occ j)) ∧
  ∀ j, j ∉ S → K.lambda j ≠ 0 → ∀ q ∈ d.linearRegion,
    q ∈ IntegerCylinder d.lo d.hi → d.g j (x,y) + K.Dg j (q-(x,y)) ≤ 0

theorem GlobalSupportedCoverage.to_local {d : ModelData n m l r}
    {f : Point n m → ℝ} {x : RealVector n} {y : RealVector m}
    {K : FixedKKT d f x y} {c : TangentFamily n m l k}
    {w : Occurrence c → ℝ} {S : Finset (Fin l)} {occ : S → Occurrence c}
    (hc : GlobalSupportedCoverage K c w S occ)
    (hy : (x,y) ∈ IntegerCylinder d.lo d.hi) : SupportedCoverage K c w S occ := by
  refine ⟨hc.1,hc.2.1,hc.2.2.1,?_⟩
  intro j hj hn q hq hqy
  apply hc.2.2.2 j hj hn q hq
  obtain ⟨b,hb,hyb⟩ := hy
  exact ⟨b,hb,hqy.trans hyb⟩

/-- No arbitrary extra keep predicate: no-goods remove complete integer fibers. -/
def historyMaster (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) : Set (Candidate (OAExec.family d seed H)) :=
  master d.model d.f (OAExec.family d seed H) (OAExec.familyDf d seed H)
    (fun p => OAExec.noGoods H p ∧ True)

abbrev SoftFiber (c : TangentFamily n m l k) := RealVector n × ℝ × (Occurrence c → ℝ)
abbrev SoftRowIndex (c : TangentFamily n m l k) (r : ℕ) :=
  (Fin r ⊕ Fin k) ⊕ (Occurrence c ⊕ Occurrence c)

def pointProjection (c : TangentFamily n m l k) : Candidate c →L[ℝ] Point n m :=
  ContinuousLinearMap.fst ℝ (Point n m) (ℝ × (Occurrence c → ℝ))
def alphaProjection (c : TangentFamily n m l k) : Candidate c →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Occurrence c → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Point n m) (ℝ × (Occurrence c → ℝ)))
def slackProjection (c : TangentFamily n m l k) (a : Occurrence c) : Candidate c →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj a).comp
    ((ContinuousLinearMap.snd ℝ ℝ (Occurrence c → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Point n m) (ℝ × (Occurrence c → ℝ))))

def softRow (d : ModelData n m l r) (c : TangentFamily n m l k)
    (df : Fin k → Point n m →L[ℝ] ℝ) : SoftRowIndex c r → Candidate c →L[ℝ] ℝ :=
  Sum.elim (Sum.elim
    (fun i => (linearFormCLM (d.A i) (d.B i)).comp (pointProjection c))
    (fun i => (df i).comp (pointProjection c) - alphaProjection c))
    (Sum.elim (fun a => -slackProjection c a)
      (fun a => (c.derivative a.1.1 a.1.2).comp (pointProjection c) - slackProjection c a))

def softRowBound (d : ModelData n m l r) (f : Point n m → ℝ)
    (c : TangentFamily n m l k) (df : Fin k → Point n m →L[ℝ] ℝ) : SoftRowIndex c r → ℝ :=
  Sum.elim (Sum.elim d.rhs (fun i => df i (c.origin i) - f (c.origin i)))
    (Sum.elim (fun _ => 0)
      (fun a => c.derivative a.1.1 a.1.2 (c.origin a.1.1) - d.g a.1.2 (c.origin a.1.1)))

theorem soft_rows_iff (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) (z : Candidate (OAExec.family d seed H)) :
    z ∈ historyMaster d seed H ↔
      (∀ i, softRow d.model (OAExec.family d seed H) (OAExec.familyDf d seed H) i z ≤
        softRowBound d.model d.f (OAExec.family d seed H) (OAExec.familyDf d seed H) i) ∧
      z.1 ∈ IntegerCylinder d.model.lo d.model.hi ∧ OAExec.noGoods H z.1 := by
  constructor
  · rintro ⟨hh,hy,hn,hs,hf,hg⟩
    refine ⟨?_,hy,hn.1⟩
    intro i
    rcases i with (i|i)|(a|a)
    · exact hh i
    · have h := hf i
      change (OAExec.familyDf d seed H i) z.1 - z.2.1 ≤ _
      dsimp only [softRowBound, Sum.elim] 
      rw [map_sub] at h
      linarith
    · exact neg_nonpos.mpr (hs a)
    · have h := hg a
      change (OAExec.family d seed H).derivative a.1.1 a.1.2 z.1 - z.2.2 a ≤ _
      dsimp only [softRowBound, Sum.elim] 
      rw [map_sub] at h
      linarith
  · rintro ⟨hr,hy,hn⟩
    refine ⟨?_,hy,⟨hn,trivial⟩,?_,?_,?_⟩
    · intro i; exact hr (.inl (.inl i))
    · intro a; exact neg_nonpos.mp (hr (.inr (.inl a)))
    · intro i
      have h := hr (.inl (.inr i))
      change OAExec.familyDf d seed H i z.1 - z.2.1 ≤ _ at h
      dsimp only [softRowBound, Sum.elim] at h
      rw [map_sub]
      linarith
    · intro a
      have h := hr (.inr (.inr a))
      change (OAExec.family d seed H).derivative a.1.1 a.1.2 z.1 - z.2.2 a ≤ _ at h
      dsimp only [softRowBound, Sum.elim] at h
      rw [map_sub]
      linarith

def softFiberEmbedding (c : TangentFamily n m l k) : SoftFiber c →L[ℝ] Candidate c :=
  ((ContinuousLinearMap.inl ℝ (RealVector n) (RealVector m)).comp
    (ContinuousLinearMap.fst ℝ (RealVector n) (ℝ × (Occurrence c → ℝ)))).prod
    (ContinuousLinearMap.snd ℝ (RealVector n) (ℝ × (Occurrence c → ℝ)))

def softFiberLift {c : TangentFamily n m l k} (y : IntVector m) (v : SoftFiber c) : Candidate c :=
  ((v.1,intCast y),v.2)

def softFiberPolyhedron (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) (y : IntVector m) : Set (SoftFiber (OAExec.family d seed H)) :=
  {v | ∀ i, ((softRow d.model (OAExec.family d seed H) (OAExec.familyDf d seed H) i).comp
      (softFiberEmbedding (OAExec.family d seed H))) v ≤
    softRowBound d.model d.f (OAExec.family d seed H) (OAExec.familyDf d seed H) i -
      softRow d.model (OAExec.family d seed H) (OAExec.familyDf d seed H) i ((0,intCast y),0,0)}

def fiberCostLinear {c : TangentFamily n m l k} (w : Occurrence c → ℝ) : SoftFiber c →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Occurrence c → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (RealVector n) (ℝ × (Occurrence c → ℝ))) +
  ∑ a, w a • (ContinuousLinearMap.proj a).comp
    ((ContinuousLinearMap.snd ℝ ℝ (Occurrence c → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (RealVector n) (ℝ × (Occurrence c → ℝ))))

theorem fiber_cost_identity {c : TangentFamily n m l k} (w : Occurrence c → ℝ)
    (y : IntVector m) (v : SoftFiber c) : cost w (softFiberLift y v) = fiberCostLinear w v := by
  simp [cost,penalty,softFiberLift,fiberCostLinear]

theorem softFiber_row_identity (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) (y : IntVector m) (v : SoftFiber (OAExec.family d seed H))
    (i : SoftRowIndex (OAExec.family d seed H) r) :
    softRow d.model (OAExec.family d seed H) (OAExec.familyDf d seed H) i (softFiberLift y v) =
      ((softRow d.model (OAExec.family d seed H) (OAExec.familyDf d seed H) i).comp
        (softFiberEmbedding (OAExec.family d seed H))) v +
      softRow d.model (OAExec.family d seed H) (OAExec.familyDf d seed H) i ((0,intCast y),0,0) := by
  rw [ContinuousLinearMap.comp_apply,←map_add]
  congr 1
  ext <;> simp [softFiberLift,softFiberEmbedding]

theorem softFiber_mem_iff (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) (y : IntVector m) (hy : y ∈ OAExec.masterAllowed d H)
    (v : SoftFiber (OAExec.family d seed H)) :
    softFiberLift y v ∈ historyMaster d seed H ↔ v ∈ softFiberPolyhedron d seed H y := by
  obtain ⟨hybox,hyng⟩ := Finset.mem_filter.mp hy
  have hi : (softFiberLift y v).1 ∈ IntegerCylinder d.model.lo d.model.hi :=
    ⟨y,by simpa [OAExec.Data.box] using hybox,rfl⟩
  have hn : OAExec.noGoods H (softFiberLift y v).1 := hyng
  rw [soft_rows_iff]
  constructor
  · intro h i
    have hr := h.1 i
    rw [softFiber_row_identity] at hr
    exact le_sub_iff_add_le.mpr hr
  · intro h
    refine ⟨?_,hi,hn⟩
    intro i
    rw [softFiber_row_identity]
    exact le_sub_iff_add_le.mp (h i)

theorem soft_finite_fiber_union (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) :
    historyMaster d seed H = ⋃ y ∈ OAExec.masterAllowed d H,
      softFiberLift y '' softFiberPolyhedron d seed H y := by
  ext z
  simp only [Set.mem_iUnion,Set.mem_image]
  constructor
  · intro hz
    obtain ⟨y,hy,hey⟩ := hz.2.1
    change z.1.2 = intCast y at hey
    have ha : y ∈ OAExec.masterAllowed d H := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [OAExec.Data.box] using hy,?_⟩
      intro e he hn
      change intCast y ≠ intCast e.target
      rw [←hey]
      exact hz.2.2.1.1 e he hn
    have hl : softFiberLift y (z.1.1,z.2) = z := by
      exact Prod.ext (Prod.ext rfl hey.symm) rfl
    refine ⟨y,ha,(z.1.1,z.2),?_,hl⟩
    apply (softFiber_mem_iff d seed H y ha _).mp
    rwa [hl]
  · rintro ⟨y,hy,v,hv,rfl⟩
    exact (softFiber_mem_iff d seed H y hy v).mpr hv

theorem soft_cost_finite_union (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) (w : Occurrence (OAExec.family d seed H) → ℝ) :
    cost w '' historyMaster d seed H = ⋃ y ∈ OAExec.masterAllowed d H,
      fiberCostLinear w '' softFiberPolyhedron d seed H y := by
  rw [soft_finite_fiber_union]
  have hf (y : IntVector m) : (fun v => cost w (softFiberLift y v)) = fiberCostLinear w :=
    funext (fiber_cost_identity w y)
  simp only [Set.image_iUnion,Set.image_image,hf]

theorem soft_cost_values_closed (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) (w : Occurrence (OAExec.family d seed H) → ℝ) :
    IsClosed (cost w '' historyMaster d seed H) := by
  rw [soft_cost_finite_union]
  apply isClosed_biUnion_finset
  intro y _
  exact finite_polyhedron_value_closed
    (fun i => (softRow d.model (OAExec.family d seed H) (OAExec.familyDf d seed H) i).comp
      (softFiberEmbedding (OAExec.family d seed H)))
    (fun i => softRowBound d.model d.f (OAExec.family d seed H) (OAExec.familyDf d seed H) i -
      softRow d.model (OAExec.family d seed H) (OAExec.familyDf d seed H) i ((0,intCast y),0,0))
    (fiberCostLinear w)

/-- Zero weights and unbounded feasible masters are allowed. -/
theorem soft_master_attained_of_bddBelow (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) (w : Occurrence (OAExec.family d seed H) → ℝ)
    (hne : (historyMaster d seed H).Nonempty)
    (hb : BddBelow (cost w '' historyMaster d seed H)) :
    ∃ z, IsMinimizer (historyMaster d seed H) (cost w) z := by
  have hleast := (soft_cost_values_closed d seed H w).isLeast_csInf (hne.image (cost w)) hb
  obtain ⟨z,hz,he⟩ := hleast.1
  refine ⟨z,hz,?_⟩
  intro q hq
  rw [he]
  exact hleast.2 ⟨q,hq,rfl⟩

/-- Actual KKT comparison across fibers; the correction is the retained
certificate's full joint functional evaluated only in the integer direction. -/
theorem globally_supported_kkt_cross_lower {d : ModelData n m l r}
    {f : Point n m → ℝ} {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {y : RealVector m}
    (H : History d f N c df x y) (K : FixedKKT d f x y)
    {w : Occurrence c → ℝ} {S : Finset (Fin l)} {occ : S → Occurrence c}
    (hc : GlobalSupportedCoverage K c w S occ) (hw : ∀ a, 0 ≤ w a)
    {keep : Point n m → Prop} {z : Candidate c}
    (hz : z ∈ master d f c df keep) :
    f (x,y) + OAExec.fullKKTFunctional K (0,z.1.2-y) ≤ z.2.1 + penalty w z / 1000 := by
  have hs (j : S) : 1000 * (K.lambda j * K.Dg j (z.1-(x,y))) ≤
      w (occ j) * z.2.2 (occ j) := by
    have ht := hz.2.2.2.2.2 (occ j)
    rw [← hc.2.1 j z.1] at ht
    have hm := mul_le_mul_of_nonneg_left ht (K.lambda_nonneg j)
    have hd := mul_le_mul_of_nonneg_right (hc.2.2.1 j) (hz.2.2.2.1 (occ j))
    have hcompl := K.soft_compl j
    change K.lambda j * d.g j (x,y) = 0 at hcompl
    nlinarith
  have ho : (∑ j : {j : Fin l // j ∉ S}, K.lambda j * K.Dg j (z.1-(x,y))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : K.lambda j = 0
    · simp [hj]
    · have ht := hc.2.2.2 j j.2 hj z.1 hz.1 hz.2.1
      have hm := mul_le_mul_of_nonneg_left ht (K.lambda_nonneg j)
      have hcompl := K.soft_compl j
      change K.lambda j * d.g j (x,y) = 0 at hcompl
      nlinarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hs j)
  rw [← Finset.mul_sum] at hsum
  have himage := occurrence_sum_le_penalty occ hc.1 hw hz.2.2.2.1
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j : Fin l => j ∈ S)
    (fun j => K.lambda j * K.Dg j (z.1-(x,y)))
  have hfint : Subtype.fintype (fun j : Fin l => j ∈ S) = Finset.Subtype.fintype S :=
    Subsingleton.elim _ _
  rw [hfint] at hsplit
  have hsoft : 1000 * (∑ j, K.lambda j * K.Dg j (z.1-(x,y))) ≤ penalty w z := by
    rw [←hsplit]
    calc
      _ ≤ 1000 * (∑ j : S, K.lambda j * K.Dg j (z.1-(x,y))) :=
        mul_le_mul_of_nonneg_left (add_le_of_nonpos_right ho) (by norm_num)
      _ ≤ penalty w z := hsum.trans himage
  have hhard : (∑ i, K.mu i * linearFormCLM (d.A i) (d.B i) (z.1-(x,y))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have ht := OAExec.hard_full_tangent d i (x,y) z.1
    have hq : linearResidual d i z.1 ≤ 0 := sub_nonpos.mpr (hz.1 i)
    have hm := mul_le_mul_of_nonneg_left hq (K.mu_nonneg i)
    have hcompl := K.hard_compl i
    change K.mu i * linearResidual d i (x,y) = 0 at hcompl
    rw [←ht] at hm
    nlinarith
  have hf := hz.2.2.2.2.1 H.current
  rw [H.current_origin,H.current_f_derivative_eq K.Df K.derivative_f] at hf
  rw [←OAExec.fullKKTFunctional_y K z.1]
  simp only [OAExec.fullKKTFunctional,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  linarith

theorem globally_supported_kkt_cost_lower {d : ModelData n m l r}
    {f : Point n m → ℝ} {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {y : RealVector m}
    (H : History d f N c df x y) (K : FixedKKT d f x y)
    {w : Occurrence c → ℝ} {S : Finset (Fin l)} {occ : S → Occurrence c}
    (hc : GlobalSupportedCoverage K c w S occ) (hw : ∀ a, 0 ≤ w a)
    {keep : Point n m → Prop} {z : Candidate c}
    (hz : z ∈ master d f c df keep) :
    f (x,y) + OAExec.fullKKTFunctional K (0,z.1.2-y) ≤ cost w z := by
  have hh := globally_supported_kkt_cross_lower H K hc hw hz
  have hp := penalty_nonneg hw hz
  dsimp only [cost]
  linarith

theorem covered_event_cost_bddBelow (d : OAExec.Data n m l r) (a : OAExec.Analytic d)
    (seed : Point n m) (H : List (OAExec.Event d)) (hH : OAExec.ValidHistory d seed H)
    (i : Fin H.length) (K : FixedKKT d.model d.f (H.get i).x (intCast (H.get i).target))
    (w : Occurrence (OAExec.family d seed H) → ℝ) (hw : ∀ j, 0 ≤ w j)
    (S : Finset (Fin l)) (occ : S → Occurrence (OAExec.family d seed H))
    (hc : GlobalSupportedCoverage K (OAExec.family d seed H) w S occ) :
    BddBelow (cost w '' historyMaster d seed H) := by
  let value : IntVector m → ℝ := fun y =>
    d.f (H.get i).anchor + OAExec.fullKKTFunctional K (0,intCast y-intCast (H.get i).target)
  obtain ⟨b,hb⟩ := ((integerBox_finite d.model.lo d.model.hi).image value).bddBelow
  refine ⟨b,?_⟩
  rintro v ⟨q,hq,rfl⟩
  obtain ⟨y,hy,hqy⟩ := hq.2.1
  have hlo : b ≤ value y := hb ⟨y,hy,rfl⟩
  have hhi := globally_supported_kkt_cost_lower
    (OAExec.eventHistory d a seed H hH i) K hc hw hq
  rw [hqy] at hhi
  exact hlo.trans hhi

/-- Availability after a retained successful event: the cost bound and an actual
optimizer are derived. No optimizer, comparison or compact-master premise. -/
theorem covered_successful_soft_master_available (d : OAExec.Data n m l r)
    (a : OAExec.Analytic d) (seed : Point n m) (H : List (OAExec.Event d))
    (hH : OAExec.ValidHistory d seed H) (i : Fin H.length)
    (hn : (H.get i).restoration = none)
    (K : FixedKKT d.model d.f (H.get i).x (intCast (H.get i).target))
    (w : Occurrence (OAExec.family d seed H) → ℝ) (hw : ∀ j, 0 ≤ w j)
    (S : Finset (Fin l)) (occ : S → Occurrence (OAExec.family d seed H))
    (hc : GlobalSupportedCoverage K (OAExec.family d seed H) w S occ) :
    (historyMaster d seed H).Nonempty ∧ BddBelow (cost w '' historyMaster d seed H) ∧
    ∃ z, IsMinimizer (historyMaster d seed H) (cost w) z := by
  have hp := OAExec.event_feasible (hH.2 _ (List.get_mem H i)) hn
  have he := OAExec.original_epigraph_mem a hH hp
  have hnemp : (historyMaster d seed H).Nonempty :=
    ⟨embed d.f (OAExec.family d seed H) (H.get i).anchor,
      embed_of_hard_epigraph he.1 ⟨he.2,trivial⟩⟩
  have hb := covered_event_cost_bddBelow d a seed H hH i K w hw S occ hc
  exact ⟨hnemp,hb,soft_master_attained_of_bddBelow d seed H w hnemp hb⟩

/-- A soft candidate retains exactly the hard-domain/target witness needed by
the accepted individual-slack restoration existence theorem. -/
theorem soft_master_hardSlice_nonempty (d : OAExec.Data n m l r) (seed : Point n m)
    (H : List (OAExec.Event d)) {z : Candidate (OAExec.family d seed H)}
    (hz : z ∈ historyMaster d seed H) (y : IntVector m)
    (hsame : z.1.2 = intCast y) : (OAExec.hardSlice d y).Nonempty := by
  refine ⟨z.1,?_,hsame⟩
  apply (OAExec.asFP_base_iff d z.1).mpr
  obtain ⟨b,hb,hcast⟩ := hz.2.1
  refine ⟨hz.1,?_⟩
  rw [hcast]
  exact hb

/-- Reuse the accepted restoration result with its full domain, bounded
nonlinear relaxation and nonemptiness hypotheses; no restoration CQ added. -/
theorem soft_requested_restoration_minimum_exists (d : OAExec.Data n m l r)
    (a : OAExec.Analytic d) (hdom : d.domain = (OAExec.asFP d).base)
    (hbounded : Bornology.IsBounded d.relaxation) (hne : d.relaxation.Nonempty)
    (seed : Point n m) (H : List (OAExec.Event d))
    {z : Candidate (OAExec.family d seed H)} (hz : z ∈ historyMaster d seed H)
    (y : IntVector m) (hy : y ∈ IntegerBox d.model.lo d.model.hi)
    (hsame : z.1.2 = intCast y) :
    ∃ x : RealVector n, ∃ s : RealVector l,
      IsMinimizer (restSet d.model (intCast y)) restCost (weightedInsert x s) :=
  OAExec.restoration_minimum_exists d a hdom hbounded hne y hy
    (soft_master_hardSlice_nonempty d seed H hz y hsame)

/-- Feasible height rays demonstrate why bounded-master hypotheses are absent. -/
theorem historyMaster_raise_alpha {d : OAExec.Data n m l r} {seed : Point n m}
    {H : List (OAExec.Event d)} {z : Candidate (OAExec.family d seed H)}
    (hz : z ∈ historyMaster d seed H) {t : ℝ} (ht : 0 ≤ t) :
    (z.1,z.2.1+t,z.2.2) ∈ historyMaster d seed H := by
  refine ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.1,?_,hz.2.2.2.2.2⟩
  intro i
  exact (hz.2.2.2.2.1 i).trans (le_add_of_nonneg_right ht)

theorem nonempty_master_unbounded_alpha {d : OAExec.Data n m l r} {seed : Point n m}
    {H : List (OAExec.Event d)} (hne : (historyMaster d seed H).Nonempty) :
    ¬ BddAbove ((fun z => z.2.1) '' historyMaster d seed H) := by
  obtain ⟨z,hz⟩ := hne
  rintro ⟨b,hb⟩
  let t : ℝ := max 0 (b-z.2.1+1)
  have ht : 0 ≤ t := le_max_left _ _
  have h := hb ⟨(z.1,z.2.1+t,z.2.2),historyMaster_raise_alpha hz ht,rfl⟩
  have ht' : b-z.2.1+1 ≤ t := le_max_right _ _
  change z.2.1+t ≤ b at h
  linarith

namespace AvailabilityControl
open RevisitControl

theorem global_coverage : GlobalSupportedCoverage certificate tangents weight
    (nonlinearSupport certificate spec.nonlinear) (currentOccurrence retainedHistory certificate) := by
  refine ⟨current_coverage.1,current_coverage.2.1,current_coverage.2.2.1,?_⟩
  intro j hj hn q hq hy
  have hj0 : j = 0 := by
    fin_cases j <;> simp_all [certificate]
  subst j
  exact False.elim (hj (by simp [nonlinearSupport,certificate,spec,OAExec.Data.nonlinear,row_nonlinear]))

def zeroWeightOccurrence : Occurrence tangents := ⟨(0,1),Set.mem_univ _⟩

/-- A genuine nonzero-KKT availability application with zero occurrence weights
and an unbounded feasible height ray. Integral local seed; no driver trace. -/
theorem nonvacuity : certificate.lambda 0 = (1/2:ℝ) ∧ weight zeroWeightOccurrence = 0 ∧
    ¬ BddAbove ((fun z => z.2.1) '' historyMaster spec seed history) ∧
    BddBelow (cost weight '' historyMaster spec seed history) ∧
    ∃ z, IsMinimizer (historyMaster spec seed history) (cost weight) z := by
  have h := covered_successful_soft_master_available spec analytic seed history history_valid
    (0 : Fin 1) (by rfl) certificate weight weight_nonneg
    (nonlinearSupport certificate spec.nonlinear) (currentOccurrence retainedHistory certificate)
    global_coverage
  refine ⟨?_,?_,nonempty_master_unbounded_alpha h.1,h.2.1,h.2.2⟩
  · norm_num [certificate]
  · norm_num [weight,zeroWeightOccurrence]

end AvailabilityControl
end Chapter03.OASoftMaster
