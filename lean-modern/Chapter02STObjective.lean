module

public import Chapter02BBAdapter
public import Chapter02MultiplierExistence
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-! Analytic bridges for a separately qualified general-objective single-tree
repair. Height remains unrestricted except for the stated upper cutoff. No
process, source CQ implication, compact epigraph, or numerical solver is assumed. -/
noncomputable section
namespace Chapter02

section Envelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def stTangent (f : E → ℝ) (a z : E) : ℝ :=
  f a + (fderiv ℝ f a) (z-a)

def stObjectiveCuts (f : E → ℝ) (H : List E) (z : E) (eta : ℝ) : Prop :=
  ∀ a ∈ H, stTangent f a z ≤ eta

structure STObjectiveHistory (E : Type*) where
  first : E
  tail : List E

def STObjectiveHistory.anchors (H : STObjectiveHistory E) : List E := H.first :: H.tail

def STObjectiveHistory.append (H : STObjectiveHistory E) (a : E) : STObjectiveHistory E :=
  ⟨H.first,H.tail ++ [a]⟩

def stEnvelopeTail (f : E → ℝ) : List E → (E → ℝ) → E → ℝ
  | [], base => base
  | a :: tail, base => fun z => max (stTangent f a z) (stEnvelopeTail f tail base z)

def stObjectiveEnvelope (f : E → ℝ) (H : STObjectiveHistory E) : E → ℝ :=
  stEnvelopeTail f H.tail (stTangent f H.first)

theorem st_tangent_continuous (f : E → ℝ) (a : E) : Continuous (stTangent f a) :=
  continuous_const.add ((fderiv ℝ f a).continuous.comp (continuous_id.sub continuous_const))

theorem st_tangent_underestimator (f : E → ℝ) (a z : E)
    (hc : ConvexOn ℝ Set.univ f) (hd : DifferentiableAt ℝ f a) :
    stTangent f a z ≤ f z := tangent_underestimator hc hd.hasFDerivAt

theorem st_objective_cuts_valid (f : E → ℝ) (H : List E)
    (hc : ConvexOn ℝ Set.univ f) (hd : ∀ a ∈ H, DifferentiableAt ℝ f a) (z : E) :
    stObjectiveCuts f H z (f z) :=
  fun a ha => st_tangent_underestimator f a z hc (hd a ha)

theorem st_envelope_tail_continuous (f : E → ℝ) (H : List E) (base : E → ℝ)
    (hb : Continuous base) : Continuous (stEnvelopeTail f H base) := by
  induction H with
  | nil => exact hb
  | cons a tail ih => exact (st_tangent_continuous f a).max ih

theorem st_objective_envelope_continuous (f : E → ℝ) (H : STObjectiveHistory E) :
    Continuous (stObjectiveEnvelope f H) :=
  st_envelope_tail_continuous f H.tail _ (st_tangent_continuous f H.first)

theorem st_envelope_tail_le_iff (f : E → ℝ) (H : List E) (base : E → ℝ)
    (z : E) (eta : ℝ) :
    stEnvelopeTail f H base z ≤ eta ↔ base z ≤ eta ∧ stObjectiveCuts f H z eta := by
  induction H with
  | nil => simp [stEnvelopeTail,stObjectiveCuts]
  | cons a tail ih =>
    simp only [stEnvelopeTail,max_le_iff,ih,stObjectiveCuts,List.mem_cons,forall_eq_or_imp]
    tauto

theorem st_objective_envelope_le_iff (f : E → ℝ) (H : STObjectiveHistory E)
    (z : E) (eta : ℝ) :
    stObjectiveEnvelope f H z ≤ eta ↔ stObjectiveCuts f H.anchors z eta := by
  rw [stObjectiveEnvelope,st_envelope_tail_le_iff]
  simp [STObjectiveHistory.anchors,stObjectiveCuts]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem st_objective_history_append (H : STObjectiveHistory E) (a : E) :
    (H.append a).anchors = H.anchors ++ [a] := rfl

theorem st_objective_cuts_append (f : E → ℝ) (H : List E) (a z : E) (eta : ℝ) :
    stObjectiveCuts f (H ++ [a]) z eta ↔
      stObjectiveCuts f H z eta ∧ stTangent f a z ≤ eta := by
  simp [stObjectiveCuts,or_imp,forall_and]

theorem st_objective_envelope_append (f : E → ℝ) (H : STObjectiveHistory E)
    (a z : E) :
    stObjectiveEnvelope f (H.append a) z = max (stObjectiveEnvelope f H z) (stTangent f a z) := by
  apply le_antisymm
  · rw [st_objective_envelope_le_iff,st_objective_history_append,st_objective_cuts_append]
    exact ⟨(st_objective_envelope_le_iff f H z _).mp (le_max_left _ _),le_max_right _ _⟩
  · apply max_le
    · apply (st_objective_envelope_le_iff f H z _).mpr
      exact ((st_objective_cuts_append f H.anchors a z _).mp
        (by simpa only [st_objective_history_append] using
          (st_objective_envelope_le_iff f (H.append a) z _).mp le_rfl)).1
    · exact ((st_objective_cuts_append f H.anchors a z _).mp
        (by simpa only [st_objective_history_append] using
          (st_objective_envelope_le_iff f (H.append a) z _).mp le_rfl)).2

inductive STHeightCutoff
  | none
  | closed (upper : ℝ)
  | strict (upper : ℝ)

def STHeightCutoff.Holds : STHeightCutoff → ℝ → Prop
  | .none, _ => True
  | .closed upper, eta => eta ≤ upper
  | .strict upper, eta => eta < upper

theorem st_cutoff_downward (cutoff : STHeightCutoff) {a b : ℝ}
    (hab : a ≤ b) (hb : cutoff.Holds b) : cutoff.Holds a := by
  cases cutoff with
  | none => trivial
  | closed upper => exact hab.trans hb
  | strict upper => exact lt_of_le_of_lt hab hb

def stHeightLP (f : E → ℝ) (C : Set E) (H : List E) (cutoff : STHeightCutoff) :
    Set (E × ℝ) := {p | p.1 ∈ C ∧ stObjectiveCuts f H p.1 p.2 ∧ cutoff.Holds p.2}

theorem st_height_lp_mem_iff (f : E → ℝ) (C : Set E) (H : List E)
    (cutoff : STHeightCutoff) (p : E × ℝ) :
    p ∈ stHeightLP f C H cutoff ↔
      p.1 ∈ C ∧ stObjectiveCuts f H p.1 p.2 ∧ cutoff.Holds p.2 := Iff.rfl

theorem st_height_lp_envelope_iff (f : E → ℝ) (C : Set E) (H : STObjectiveHistory E)
    (cutoff : STHeightCutoff) (p : E × ℝ) :
    p ∈ stHeightLP f C H.anchors cutoff ↔
      p.1 ∈ C ∧ stObjectiveEnvelope f H p.1 ≤ p.2 ∧ cutoff.Holds p.2 := by
  rw [st_height_lp_mem_iff,st_objective_envelope_le_iff]

theorem st_height_lp_append (f : E → ℝ) (C : Set E) (H : List E)
    (a : E) (cutoff : STHeightCutoff) :
    stHeightLP f C (H ++ [a]) cutoff =
      stHeightLP f C H cutoff ∩ {p | stTangent f a p.1 ≤ p.2} := by
  ext p
  simp only [st_height_lp_mem_iff,Set.mem_inter_iff,Set.mem_setOf_eq,st_objective_cuts_append]
  tauto

theorem st_height_lp_projection (f : E → ℝ) (C : Set E) (H : STObjectiveHistory E)
    (cutoff : STHeightCutoff) (z : E) :
    (∃ eta, (z,eta) ∈ stHeightLP f C H.anchors cutoff) ↔
      z ∈ C ∧ cutoff.Holds (stObjectiveEnvelope f H z) := by
  constructor
  · rintro ⟨eta,hp⟩
    have h := (st_height_lp_envelope_iff f C H cutoff (z,eta)).mp hp
    exact ⟨h.1,st_cutoff_downward cutoff h.2.1 h.2.2⟩
  · rintro ⟨hz,hc⟩
    exact ⟨_,(st_height_lp_envelope_iff f C H cutoff _).mpr ⟨hz,le_rfl,hc⟩⟩

theorem st_height_lp_minimum_of_envelope (f : E → ℝ) (C : Set E)
    (H : STObjectiveHistory E) (cutoff : STHeightCutoff) {z : E}
    (hz : IsMinimizer C (stObjectiveEnvelope f H) z)
    (hne : (stHeightLP f C H.anchors cutoff).Nonempty) :
    IsMinimizer (stHeightLP f C H.anchors cutoff) Prod.snd
      (z,stObjectiveEnvelope f H z) := by
  obtain ⟨p,hp⟩ := hne
  have hp' := (st_height_lp_envelope_iff f C H cutoff p).mp hp
  refine ⟨(st_height_lp_envelope_iff f C H cutoff _).mpr
    ⟨hz.1,le_rfl,st_cutoff_downward cutoff ((hz.2 p.1 hp'.1).trans hp'.2.1) hp'.2.2⟩,?_⟩
  intro q hq
  have hq' := (st_height_lp_envelope_iff f C H cutoff q).mp hq
  exact (hz.2 q.1 hq'.1).trans hq'.2.1

/-- Even a strict upper cutoff attains its height minimum when it is nonempty.
The compact set is the original-coordinate projection before the cutoff. -/
theorem st_height_lp_empty_or_minimum (f : E → ℝ) (C : Set E) (H : List E)
    (cutoff : STHeightCutoff) (hC : IsCompact C) (hH : H ≠ []) :
    stHeightLP f C H cutoff = ∅ ∨
      ∃ p, IsMinimizer (stHeightLP f C H cutoff) Prod.snd p := by
  classical
  by_cases he : stHeightLP f C H cutoff = ∅
  · exact Or.inl he
  have hne := Set.nonempty_iff_ne_empty.mpr he
  obtain ⟨p,hp⟩ := hne
  cases H with
  | nil => exact (hH rfl).elim
  | cons a tail =>
    let history : STObjectiveHistory E := ⟨a,tail⟩
    obtain ⟨z,hz⟩ := compact_feasible_attainment hC ⟨p.1,hp.1⟩
      (st_objective_envelope_continuous f history).continuousOn
    exact Or.inr ⟨_,st_height_lp_minimum_of_envelope f C history cutoff hz ⟨p,hp⟩⟩

theorem st_height_lp_minimizer_height (f : E → ℝ) (C : Set E) (H : STObjectiveHistory E)
    (cutoff : STHeightCutoff) {p : E × ℝ}
    (hp : IsMinimizer (stHeightLP f C H.anchors cutoff) Prod.snd p) :
    p.2 = stObjectiveEnvelope f H p.1 := by
  have hm := (st_height_lp_envelope_iff f C H cutoff p).mp hp.1
  apply le_antisymm _ hm.2.1
  apply hp.2 (p.1,stObjectiveEnvelope f H p.1)
  exact (st_height_lp_envelope_iff f C H cutoff _).mpr
    ⟨hm.1,le_rfl,st_cutoff_downward cutoff hm.2.1 hm.2.2⟩

theorem st_height_lp_minimizer_iff (f : E → ℝ) (C : Set E) (H : STObjectiveHistory E)
    (cutoff : STHeightCutoff) (p : E × ℝ) :
    IsMinimizer (stHeightLP f C H.anchors cutoff) Prod.snd p ↔
      IsMinimizer {z | z ∈ C ∧ cutoff.Holds (stObjectiveEnvelope f H z)}
        (stObjectiveEnvelope f H) p.1 ∧ p.2 = stObjectiveEnvelope f H p.1 := by
  constructor
  · intro hp
    have ht := st_height_lp_minimizer_height f C H cutoff hp
    have hm := (st_height_lp_envelope_iff f C H cutoff p).mp hp.1
    refine ⟨⟨⟨hm.1,by simpa [ht] using hm.2.2⟩,?_⟩,ht⟩
    intro z hz
    have hh := hp.2 (z,stObjectiveEnvelope f H z)
      ((st_height_lp_envelope_iff f C H cutoff _).mpr ⟨hz.1,le_rfl,hz.2⟩)
    simpa only [ht] using hh
  · rintro ⟨⟨hp,hmin⟩,ht⟩
    refine ⟨(st_height_lp_envelope_iff f C H cutoff _).mpr
      ⟨hp.1,ht.ge,by simpa only [ht] using hp.2⟩,?_⟩
    intro q hq
    have hm := (st_height_lp_envelope_iff f C H cutoff q).mp hq
    have hh := hmin q.1 ⟨hm.1,st_cutoff_downward cutoff hm.2.1 hm.2.2⟩
    simpa only [ht] using hh.trans hm.2.1

theorem st_height_lp_no_unbounded (f : E → ℝ) (C : Set E) (H : List E)
    (cutoff : STHeightCutoff) (hC : IsCompact C) (hH : H ≠ []) :
    ¬ ∀ B : ℝ, ∃ p ∈ stHeightLP f C H cutoff, p.2 < B := by
  intro hu
  rcases st_height_lp_empty_or_minimum f C H cutoff hC hH with he | ⟨p,hp⟩
  · obtain ⟨q,hq,_⟩ := hu 0
    simp [he] at hq
  · obtain ⟨q,hq,hlt⟩ := hu p.2
    exact (not_lt_of_ge (hp.2 q hq)) hlt

theorem st_height_lp_no_unattained (f : E → ℝ) (C : Set E) (H : List E)
    (cutoff : STHeightCutoff) (hC : IsCompact C) (hH : H ≠ [])
    (hne : (stHeightLP f C H cutoff).Nonempty) :
    ∃ p, IsMinimizer (stHeightLP f C H cutoff) Prod.snd p := by
  rcases st_height_lp_empty_or_minimum f C H cutoff hC hH with he | hm
  · simp [he] at hne
  · exact hm

/-- Empty objective-cut history leaves height unbounded below even if the
original-coordinate set is nonempty and compact. It does not certify infeasibility. -/
theorem st_empty_objective_history_unbounded (f : E → ℝ) (C : Set E)
    (cutoff : STHeightCutoff) (hC : C.Nonempty) :
    ∀ B : ℝ, ∃ p ∈ stHeightLP f C [] cutoff, p.2 < B := by
  obtain ⟨z,hz⟩ := hC
  intro B
  cases cutoff with
  | none => exact ⟨(z,B-1),⟨hz,by simp [stObjectiveCuts],trivial⟩,by dsimp; linarith⟩
  | closed T =>
    refine ⟨(z,min B T-1),⟨hz,by simp [stObjectiveCuts],?_⟩,?_⟩
    · change min B T-1 ≤ T
      linarith [min_le_right B T]
    · dsimp
      linarith [min_le_left B T]
  | strict T =>
    refine ⟨(z,min B T-1),⟨hz,by simp [stObjectiveCuts],?_⟩,?_⟩
    · change min B T-1 < T
      linarith [min_le_right B T]
    · dsimp
      linarith [min_le_left B T]

end Envelope

section Transport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem st_tangent_comp_equiv (A : E ≃L[ℝ] F) (f : F → ℝ) (a z : E)
    (hf : DifferentiableAt ℝ f (A a)) :
    stTangent (f ∘ A) a z = stTangent f (A a) (A z) := by
  have hd := hf.hasFDerivAt.comp a A.hasFDerivAt
  simp only [stTangent,hd.fderiv,Function.comp_apply,ContinuousLinearMap.comp_apply,map_sub]
  rfl

theorem st_tangent_split {N n m : ℕ} {I : Finset (Fin N)} (P : BBPartition I n m)
    (f : RealVector N → ℝ) (a z : RealVector N) (hf : DifferentiableAt ℝ f a) :
    stTangent (f ∘ P.join) (P.split a) (P.split z) = stTangent f a z := by
  have hd : DifferentiableAt ℝ f (P.equiv.symm (P.split a)) := by
    change DifferentiableAt ℝ f (P.join (P.split a))
    simpa only [P.join_split] using hf
  have hh := st_tangent_comp_equiv P.equiv.symm f (P.split a) (P.split z) hd
  change stTangent (f ∘ P.join) (P.split a) (P.split z) =
    stTangent f (P.join (P.split a)) (P.join (P.split z)) at hh
  simpa only [P.join_split] using hh

theorem st_objective_cuts_split {N n m : ℕ} {I : Finset (Fin N)}
    (P : BBPartition I n m) (f : RealVector N → ℝ) (H : List (RealVector N))
    (hd : ∀ a ∈ H, DifferentiableAt ℝ f a) (z : RealVector N) (eta : ℝ) :
    stObjectiveCuts (f ∘ P.join) (H.map P.split) (P.split z) eta ↔
      stObjectiveCuts f H z eta := by
  constructor
  · intro h a ha
    have hh := h (P.split a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
    simpa only [st_tangent_split P f a z (hd a ha)] using hh
  · intro h a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    simpa only [st_tangent_split P f b z (hd b hb)] using h b hb

end Transport

section FiberSupport
variable {n m l r : ℕ}

theorem st_epigraph_fixed_fiber_iff (d : ModelData n m l r) (f : Point n m → ℝ)
    (y : RealVector m) (p : Point (n+1) m) :
    p ∈ (d.epigraphModel f).fixedNonlinearFiber y ↔
      epiProject p ∈ d.fixedNonlinearFiber y ∧ f (epiProject p) ≤ epiHeight p := by
  simp only [mem_fixedNonlinearFiber]
  rw [epigraphModel_linearRegion_iff]
  simp only [ModelData.nonlinearRegion,ModelData.epigraphModel,Fin.forall_fin_succ,
    Fin.cons_zero,Fin.cons_succ,sub_nonpos]
  change (_ ∧ _ ∧ (_ ∧ _)) ↔ (_ ∧ _ ∧ _) ∧ _
  tauto

theorem st_epigraph_fixed_minimum (d : ModelData n m l r) (f : Point n m → ℝ)
    {p : Point n m} (hp : IsMinimizer (d.fixedNonlinearFiber p.2) f p) :
    IsMinimizer ((d.epigraphModel f).fixedNonlinearFiber p.2)
      (d.epigraphModel f).objective (epiInsert p (f p)) := by
  refine ⟨(st_epigraph_fixed_fiber_iff d f p.2 _).mpr
    (by simpa using And.intro hp.1 (le_refl (f p))),?_⟩
  intro q hq
  have hh := (st_epigraph_fixed_fiber_iff d f p.2 q).mp hq
  simpa only [epigraphModel_objective,epiHeight_insert] using (hp.2 _ hh.1).trans hh.2

/-- General-objective fiber support derived from the actual fixed-fiber minimum
and a sufficient fiber CQ. Unrestricted height is used only in this KKT proof. -/
theorem st_fixed_fiber_support (d : ModelData n m l r) (f : Point n m → ℝ)
    (p : Point n m) (hconvf : ConvexOn ℝ Set.univ f)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdf : DifferentiableAt ℝ f p) (hdg : ∀ j, DifferentiableAt ℝ (d.g j) p)
    (hmin : IsMinimizer (d.fixedNonlinearFiber p.2) f p)
    (hslater : ∃ z ∈ d.fixedLinearFiber p.2, ∀ j, d.g j z < 0)
    {q : Point n m} {eta : ℝ} (hq : q ∈ d.fixedLinearFiber p.2)
    (hcuts : ∀ j, stTangent (d.g j) p q ≤ 0)
    (hobj : stTangent f p q ≤ eta) : f p ≤ eta := by
  let e := d.epigraphModel f
  let a := epiInsert p (f p)
  let D : Fin (l+1) → Point (n+1) m →L[ℝ] ℝ :=
    Fin.cons (epigraphDerivative (fderiv ℝ f p))
      (fun j => (fderiv ℝ (d.g j) p).comp epiProjectCLM)
  have hc : ∀ j, ConvexOn ℝ Set.univ (e.g j) := by
    simpa only [Set.preimage_univ] using epigraphModel_rows_convex d f Set.univ hconvf hconv
  have hd : ∀ j, HasFDerivAt (e.g j) (D j) a := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact epigraphModel_hasFDerivAt d f a _ (by simpa [a] using hdf.hasFDerivAt)
    · exact epigraphModel_oldRow_hasFDerivAt d f a j _ (by simpa [a] using (hdg j).hasFDerivAt)
  have hs : ∃ z ∈ e.fixedLinearFiber a.2, ∀ j, e.g j z < 0 := by
    obtain ⟨z,hz,hstrict⟩ := hslater
    refine ⟨epiInsert z (f z+1),?_,?_⟩
    · exact ⟨(epigraphModel_linearRegion_iff d f _).mpr (by simpa using hz.1),hz.2⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · change f (epiProject (epiInsert z (f z+1))) - epiHeight (epiInsert z (f z+1)) < 0
        simp
      · simpa [e,ModelData.epigraphModel] using hstrict j
  obtain ⟨lambda,mu,hkkt⟩ := exists_fixedNLPKKT e a D hc hd
    (st_epigraph_fixed_minimum d f hmin) hs
  have hqL : epiInsert q eta ∈ e.linearRegion :=
    (epigraphModel_linearRegion_iff d f _).mpr (by simpa using hq.1)
  have hrows : SelectedOARows e D a Set.univ (epiInsert q eta) := by
    intro j _
    refine Fin.cases ?_ (fun j => ?_) j
    · change (d.epigraphModel f).g 0 (epiInsert p (f p)) +
        epigraphDerivative (fderiv ℝ f p) (epiInsert q eta-epiInsert p (f p)) ≤ 0
      rw [epigraphModel_tangent_insert]
      exact sub_nonpos.mpr hobj
    · change stTangent (d.g j) p q ≤ 0
      exact hcuts j
  have hout := optimality_cut_of_all_oa_rows hkkt hqL hrows
  have hy : (epiInsert q eta).2 = a.2 := hq.2
  rw [hy,optimality_cut_at_anchor] at hout
  simpa [e,a] using hout

end FiberSupport
end Chapter02

#print axioms Chapter02.st_tangent_continuous
#print axioms Chapter02.st_tangent_underestimator
#print axioms Chapter02.st_objective_cuts_valid
#print axioms Chapter02.st_envelope_tail_continuous
#print axioms Chapter02.st_objective_envelope_continuous
#print axioms Chapter02.st_envelope_tail_le_iff
#print axioms Chapter02.st_objective_envelope_le_iff
#print axioms Chapter02.st_objective_history_append
#print axioms Chapter02.st_objective_cuts_append
#print axioms Chapter02.st_objective_envelope_append
#print axioms Chapter02.st_cutoff_downward
#print axioms Chapter02.st_height_lp_mem_iff
#print axioms Chapter02.st_height_lp_envelope_iff
#print axioms Chapter02.st_height_lp_append
#print axioms Chapter02.st_height_lp_projection
#print axioms Chapter02.st_height_lp_minimum_of_envelope
#print axioms Chapter02.st_height_lp_empty_or_minimum
#print axioms Chapter02.st_height_lp_minimizer_height
#print axioms Chapter02.st_height_lp_minimizer_iff
#print axioms Chapter02.st_height_lp_no_unbounded
#print axioms Chapter02.st_height_lp_no_unattained
#print axioms Chapter02.st_empty_objective_history_unbounded
#print axioms Chapter02.st_tangent_comp_equiv
#print axioms Chapter02.st_tangent_split
#print axioms Chapter02.st_objective_cuts_split
#print axioms Chapter02.st_epigraph_fixed_fiber_iff
#print axioms Chapter02.st_epigraph_fixed_minimum
#print axioms Chapter02.st_fixed_fiber_support
