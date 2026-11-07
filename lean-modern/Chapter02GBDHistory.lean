module

public import Chapter02OAHistory
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-! Literal integer/height GBD history with anchored analytic constraints and
explicit empty-affine-fiber exclusions. Raw validity stores actual optimizers
and their actual KKT data; validity, positivity and progress are derived. -/
noncomputable section
open scoped BigOperators
namespace Chapter02
variable {n m l r : ℕ}

inductive GBDPayload (n m l r : ℕ)
  | optimal (anchor : Point n m) (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
  | restoration (anchor : Point n m) (rho : ℝ)
      (lambda : Fin l → ℝ) (mu : Fin r → ℝ)
  | emptyLinear

structure GBDBatch (n m l r : ℕ) where
  integer : IntVector m
  payload : GBDPayload n m l r

def gbdBatchDerivative (d : ModelData n m l r) (p : Point n m)
    (j : Fin l) : Point n m →L[ℝ] ℝ := fderiv ℝ (d.g j) p

def gbdBatchOptimalAnchor (b : GBDBatch n m l r) : Option (Point n m) :=
  match b.payload with
  | .optimal p _ _ => some p
  | _ => none

def gbdBatchValid (d : ModelData n m l r) (b : GBDBatch n m l r) : Prop :=
  b.integer ∈ IntegerBox d.lo d.hi ∧
  match b.payload with
  | .optimal p lambda mu => p.2 = oaIntCast b.integer ∧
      IsMinimizer (d.fixedNonlinearFiber (oaIntCast b.integer)) d.objective p ∧
      FixedNLPKKT d p (gbdBatchDerivative d p) lambda mu
  | .restoration p rho lambda mu => p.2 = oaIntCast b.integer ∧
      ¬ (d.fixedNonlinearFiber (oaIntCast b.integer)).Nonempty ∧
      IsMinimizer (RestorationPairs (d.fixedLinearFiber (oaIntCast b.integer)) d.g)
        Prod.snd (p,rho) ∧ RestorationKKT d p rho (gbdBatchDerivative d p) lambda mu
  | .emptyLinear => ¬ (d.fixedLinearFiber (oaIntCast b.integer)).Nonempty

def gbdBatchConstraint (d : ModelData n m l r) (b : GBDBatch n m l r)
    (z : IntVector m × ℝ) : Prop :=
  match b.payload with
  | .optimal p lambda mu =>
      anchoredOptimalityCut d p (gbdBatchDerivative d p) lambda mu (oaIntCast z.1) ≤ z.2
  | .restoration p _ lambda mu =>
      anchoredFeasibilityCut d p (gbdBatchDerivative d p) lambda mu (oaIntCast z.1) ≤ 0
  | .emptyLinear => z.1 ≠ b.integer

def gbdMasterUnfloored (d : ModelData n m l r) (H : List (GBDBatch n m l r)) :
    Set (IntVector m × ℝ) :=
  {z | z.1 ∈ IntegerBox d.lo d.hi ∧ ∀ b ∈ H, gbdBatchConstraint d b z}

def gbdMaster (d : ModelData n m l r) (floor : ℝ) (H : List (GBDBatch n m l r)) :
    Set (IntVector m × ℝ) := {z | z ∈ gbdMasterUnfloored d H ∧ floor ≤ z.2}

def GBDFloorValid (d : ModelData n m l r) (floor : ℝ) : Prop :=
  IsLowerBound (d.feasibleOn Set.univ) d.objective floor

def GBDBaseFloorValid (d : ModelData n m l r) (floor : ℝ) : Prop :=
  IsLowerBound (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) d.objective floor

def gbdBatchSide (d : ModelData n m l r) (b : GBDBatch n m l r) (y : IntVector m) : Prop :=
  match b.payload with
  | .optimal _ _ _ => True
  | .restoration p _ lambda mu =>
      anchoredFeasibilityCut d p (gbdBatchDerivative d p) lambda mu (oaIntCast y) ≤ 0
  | .emptyLinear => y ≠ b.integer

def gbdSurvives (d : ModelData n m l r) (H : List (GBDBatch n m l r)) : Set (IntVector m) :=
  {y | y ∈ IntegerBox d.lo d.hi ∧ ∀ b ∈ H, gbdBatchSide d b y}

def gbdHeight (d : ModelData n m l r) (floor : ℝ) :
    List (GBDBatch n m l r) → IntVector m → ℝ
  | [], _ => floor
  | b :: H, y => match b.payload with
      | .optimal p lambda mu => max
          (anchoredOptimalityCut d p (gbdBatchDerivative d p) lambda mu (oaIntCast y))
          (gbdHeight d floor H y)
      | _ => gbdHeight d floor H y

@[simp] theorem gbd_master_mem_iff (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (z : IntVector m × ℝ) :
    z ∈ gbdMaster d floor H ↔ z.1 ∈ IntegerBox d.lo d.hi ∧ floor ≤ z.2 ∧
      ∀ b ∈ H, gbdBatchConstraint d b z := by
  simp only [gbdMaster,gbdMasterUnfloored,Set.mem_setOf_eq]
  tauto

theorem gbd_master_append (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (b : GBDBatch n m l r) :
    gbdMaster d floor (H ++ [b]) = gbdMaster d floor H ∩ {z | gbdBatchConstraint d b z} := by
  ext z
  simp only [gbd_master_mem_iff,List.mem_append,List.mem_singleton,Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy,hf,hc⟩
    exact ⟨⟨hy,hf,fun c h => hc c (Or.inl h)⟩,hc b (Or.inr rfl)⟩
  · rintro ⟨⟨hy,hf,hc⟩,hb⟩
    refine ⟨hy,hf,?_⟩
    intro c h
    rcases h with h | rfl
    · exact hc c h
    · exact hb

theorem gbd_height_le_iff (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (y : IntVector m) (eta : ℝ) :
    gbdHeight d floor H y ≤ eta ↔ floor ≤ eta ∧
      ∀ b ∈ H, ∀ p lambda mu, b.payload = .optimal p lambda mu →
        anchoredOptimalityCut d p (gbdBatchDerivative d p) lambda mu (oaIntCast y) ≤ eta := by
  induction H with
  | nil => simp [gbdHeight]
  | cons b H ih =>
    cases hp : b.payload with
    | optimal p lambda mu =>
      rcases p with ⟨x,v⟩
      simp [gbdHeight,hp,ih,max_le_iff,and_assoc,and_left_comm,and_comm,forall_eq']
      intro _
      constructor
      · rintro ⟨hc,ht⟩
        refine ⟨ht,?_⟩
        rintro a b lam muv rfl rfl rfl rfl
        exact hc
      · rintro ⟨ht,hc⟩
        exact ⟨hc x v lambda mu rfl rfl rfl rfl,ht⟩
    | restoration p rho lambda mu => simp [gbdHeight,hp,ih]
    | emptyLinear => simp [gbdHeight,hp,ih]

theorem gbd_master_height_iff (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (z : IntVector m × ℝ) :
    z ∈ gbdMaster d floor H ↔ z.1 ∈ gbdSurvives d H ∧ gbdHeight d floor H z.1 ≤ z.2 := by
  rw [gbd_master_mem_iff,gbd_height_le_iff]
  constructor
  · rintro ⟨hy,hf,hH⟩
    refine ⟨⟨hy,?_⟩,hf,?_⟩
    · intro b hb
      have hc := hH b hb
      cases hp : b.payload with
      | optimal p lambda mu => simp [gbdBatchSide,hp]
      | restoration p rho lambda mu => simpa [gbdBatchSide,gbdBatchConstraint,hp] using hc
      | emptyLinear => simpa [gbdBatchSide,gbdBatchConstraint,hp] using hc
    · intro b hb p lambda mu hp
      simpa [gbdBatchConstraint,hp] using hH b hb
  · rintro ⟨⟨hy,hS⟩,hf,hO⟩
    refine ⟨hy,hf,?_⟩
    intro b hb
    cases hp : b.payload with
    | optimal p lambda mu => simpa [gbdBatchConstraint,hp] using hO b hb p lambda mu hp
    | restoration p rho lambda mu => simpa [gbdBatchSide,gbdBatchConstraint,hp] using hS b hb
    | emptyLinear => simpa [gbdBatchSide,gbdBatchConstraint,hp] using hS b hb

theorem gbd_master_eq_epigraph (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) :
    gbdMaster d floor H = EpigraphLift (gbdSurvives d H) (gbdHeight d floor H) := by
  ext z
  exact gbd_master_height_iff d floor H z

theorem gbd_survives_finite (d : ModelData n m l r) (H : List (GBDBatch n m l r)) :
    (gbdSurvives d H).Finite := (integerBox_finite d.lo d.hi).subset (fun _ h => h.1)

theorem gbd_master_reply (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) :
    gbdMaster d floor H = ∅ ∨ ∃ z, IsMinimizer (gbdMaster d floor H) Prod.snd z := by
  rcases (gbdSurvives d H).eq_empty_or_nonempty with he | hn
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hy := ((gbd_master_height_iff d floor H z).mp hz).1
    simp [he] at hy
  · right
    obtain ⟨y,hy,hmin⟩ := Set.exists_min_image (gbdSurvives d H) (gbdHeight d floor H)
      (gbd_survives_finite d H) hn
    refine ⟨(y,gbdHeight d floor H y),?_,?_⟩
    · exact (gbd_master_height_iff d floor H _).mpr ⟨hy,le_rfl⟩
    · intro z hz
      have h := (gbd_master_height_iff d floor H z).mp hz
      exact (hmin z.1 h.1).trans h.2

theorem gbd_master_minimizer_height (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) {z : IntVector m × ℝ}
    (hz : IsMinimizer (gbdMaster d floor H) Prod.snd z) :
    z.2 = gbdHeight d floor H z.1 := by
  have h := (gbd_master_height_iff d floor H z).mp hz.1
  exact le_antisymm (hz.2 (z.1,gbdHeight d floor H z.1)
    ((gbd_master_height_iff d floor H _).mpr ⟨h.1,le_rfl⟩)) h.2

theorem gbd_base_floor_valid (d : ModelData n m l r) (floor : ℝ)
    (h : GBDBaseFloorValid d floor) : GBDFloorValid d floor := by
  intro p hp
  exact h p ⟨hp.1.2,hp.2⟩

theorem gbd_base_floor_exists (d : ModelData n m l r)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi)) :
    ∃ floor, GBDBaseFloorValid d floor := by
  rcases (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi).eq_empty_or_nonempty with he | hn
  · refine ⟨0,?_⟩
    intro p hp
    simp [he] at hp
  · obtain ⟨lo,hi,h⟩ := compact_objective_bounds hbase hn
      (linearForm_continuous d.c1 d.c2).continuousOn
    exact ⟨lo,fun p hp => (h p hp).1⟩

theorem gbdBatch_derivatives (d : ModelData n m l r) (p : Point n m)
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    ∀ j, HasFDerivAt (d.g j) (gbdBatchDerivative d p j) p :=
  fun j => (hdiff j p).hasFDerivAt

theorem gbdBatch_optimal_original (d : ModelData n m l r) (b : GBDBatch n m l r)
    (hb : gbdBatchValid d b) (a : Point n m) (ha : gbdBatchOptimalAnchor b = some a) :
    a ∈ d.feasibleOn Set.univ := by
  cases hp : b.payload with
  | optimal p lambda mu =>
    have hpa : p = a := by simpa [gbdBatchOptimalAnchor,hp] using ha
    subst a
    have h := hb.2
    simp only [hp] at h
    exact ⟨⟨⟨Set.mem_univ _,h.2.2.nonlinear_feasible⟩,h.2.2.linear_feasible⟩,
      b.integer,hb.1,h.1⟩
  | restoration p rho lambda mu => simp [gbdBatchOptimalAnchor,hp] at ha
  | emptyLinear => simp [gbdBatchOptimalAnchor,hp] at ha

theorem gbdBatch_restoration_positive (d : ModelData n m l r)
    (b : GBDBatch n m l r) (hb : gbdBatchValid d b)
    {p : Point n m} {rho : ℝ} {lambda : Fin l → ℝ} {mu : Fin r → ℝ}
    (hp : b.payload = .restoration p rho lambda mu) : 0 < rho := by
  have h := hb.2
  simp only [hp] at h
  exact oaBatch_restoration_positive d ⟨b.integer,p,some rho⟩
    ⟨hb.1,h.1,h.2.1,h.2.2.1⟩ rfl

theorem gbdBatch_processed_lower (d : ModelData n m l r) (b : GBDBatch n m l r)
    (hb : gbdBatchValid d b) (z : IntVector m × ℝ)
    (hc : gbdBatchConstraint d b z) (hsame : z.1 = b.integer) :
    ∃ a, gbdBatchOptimalAnchor b = some a ∧ d.objective a ≤ z.2 := by
  have h := hb.2
  cases hp : b.payload with
  | optimal p lambda mu =>
    simp only [hp] at h
    have hy : oaIntCast z.1 = p.2 := by rw [hsame,← h.1]
    refine ⟨p,by simp [gbdBatchOptimalAnchor,hp],?_⟩
    simpa [gbdBatchConstraint,hp,hy,optimality_cut_at_anchor] using hc
  | restoration p rho lambda mu =>
    simp only [hp] at h
    have hy : oaIntCast z.1 = p.2 := by rw [hsame,← h.1]
    have he := restoration_cut_at_anchor h.2.2.2
    have hpos := gbdBatch_restoration_positive d b hb hp
    have hn : rho ≤ 0 := by simpa [gbdBatchConstraint,hp,hy,he] using hc
    exact False.elim (not_le_of_gt hpos hn)
  | emptyLinear =>
    have hn : z.1 ≠ b.integer := by simpa [gbdBatchConstraint,hp] using hc
    exact False.elim (hn hsame)

theorem gbdBatch_constraint_valid (d : ModelData n m l r) (b : GBDBatch n m l r)
    (hb : gbdBatchValid d b) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (q : Point n m) (hq : q ∈ d.feasibleOn Set.univ) (y : IntVector m)
    (hy : q.2 = oaIntCast y) : gbdBatchConstraint d b (y,d.objective q) := by
  have h := hb.2
  cases hp : b.payload with
  | optimal p lambda mu =>
    simp only [hp] at h
    simpa [gbdBatchConstraint,hp,← hy] using optimality_cut_valid h.2.2 hconv hq.1.2 hq.1.1.2
  | restoration p rho lambda mu =>
    simp only [hp] at h
    simpa [gbdBatchConstraint,hp,← hy] using restoration_cut_valid h.2.2.2 hconv hq.1.2 hq.1.1.2
  | emptyLinear =>
    simp only [hp] at h
    simp only [gbdBatchConstraint,hp]
    intro he
    apply h
    exact ⟨q,hq.1.2,hy.trans (congrArg oaIntCast he)⟩

theorem gbd_master_contains_feasible (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b)
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (q : Point n m) (hq : q ∈ d.feasibleOn Set.univ) (y : IntVector m)
    (hy : q.2 = oaIntCast y) : (y,d.objective q) ∈ gbdMaster d floor H := by
  obtain ⟨z,hz,hqz⟩ := hq.2
  have he : z = y := oaIntCast_injective (hqz.symm.trans hy)
  subst z
  exact (gbd_master_mem_iff d floor H _).mpr
    ⟨hz,hf q hq,fun b hb => gbdBatch_constraint_valid d b (hH b hb) hconv q hq y hy⟩

theorem gbd_master_lowerBound (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b)
    (hf : GBDFloorValid d floor) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    {z : IntVector m × ℝ} (hz : IsMinimizer (gbdMaster d floor H) Prod.snd z) :
    IsLowerBound (d.feasibleOn Set.univ) d.objective z.2 := by
  intro q hq
  obtain ⟨y,_,hy⟩ := hq.2
  exact hz.2 _ (gbd_master_contains_feasible d floor H hH hf hconv q hq y hy)


inductive GBDRoute
  | optimal | restoration | emptyLinear
  deriving DecidableEq

def gbdBatchRoute (b : GBDBatch n m l r) : GBDRoute :=
  match b.payload with
  | .optimal _ _ _ => .optimal
  | .restoration _ _ _ _ => .restoration
  | .emptyLinear => .emptyLinear

def gbdSourceRoute (d : ModelData n m l r) (y : IntVector m) : GBDRoute → Prop
  | .optimal => (d.fixedNonlinearFiber (oaIntCast y)).Nonempty
  | .restoration => (d.fixedLinearFiber (oaIntCast y)).Nonempty ∧
      ¬ (d.fixedNonlinearFiber (oaIntCast y)).Nonempty
  | .emptyLinear => ¬ (d.fixedLinearFiber (oaIntCast y)).Nonempty

theorem gbd_source_route_unique (d : ModelData n m l r) (y : IntVector m) :
    ∃! route, gbdSourceRoute d y route := by
  have hNL : (d.fixedNonlinearFiber (oaIntCast y)).Nonempty →
      (d.fixedLinearFiber (oaIntCast y)).Nonempty := fun ⟨p,hp⟩ => ⟨p,hp.1⟩
  by_cases hL : (d.fixedLinearFiber (oaIntCast y)).Nonempty
  · by_cases hN : (d.fixedNonlinearFiber (oaIntCast y)).Nonempty
    · refine ⟨.optimal,hN,?_⟩
      intro route hr
      cases route <;> simp_all [gbdSourceRoute]
    · refine ⟨.restoration,⟨hL,hN⟩,?_⟩
      intro route hr
      cases route <;> simp_all [gbdSourceRoute]
  · refine ⟨.emptyLinear,hL,?_⟩
    intro route hr
    cases route <;> simp_all [gbdSourceRoute]

theorem gbdBatch_source_route (d : ModelData n m l r) (b : GBDBatch n m l r)
    (hb : gbdBatchValid d b) : gbdSourceRoute d b.integer (gbdBatchRoute b) := by
  have h := hb.2
  cases hp : b.payload with
  | optimal p lambda mu =>
    simp only [hp] at h
    simpa only [gbdBatchRoute,hp,gbdSourceRoute] using
      (show (d.fixedNonlinearFiber (oaIntCast b.integer)).Nonempty from ⟨p,h.2.1.1⟩)
  | restoration p rho lambda mu =>
    simp only [hp] at h
    simpa only [gbdBatchRoute,hp,gbdSourceRoute] using
      (show (d.fixedLinearFiber (oaIntCast b.integer)).Nonempty ∧
        ¬ (d.fixedNonlinearFiber (oaIntCast b.integer)).Nonempty from ⟨⟨p,h.2.2.1.1.1⟩,h.2.1⟩)
  | emptyLinear => simpa [gbdBatchRoute,gbdSourceRoute,hp] using h

theorem gbdBatch_route_iff (d : ModelData n m l r) (b : GBDBatch n m l r)
    (hb : gbdBatchValid d b) (route : GBDRoute) :
    gbdBatchRoute b = route ↔ gbdSourceRoute d b.integer route := by
  constructor
  · intro h
    rw [← h]
    exact gbdBatch_source_route d b hb
  · intro h
    obtain ⟨a,_,hu⟩ := gbd_source_route_unique d b.integer
    exact (hu _ (gbdBatch_source_route d b hb)).trans (hu _ h).symm

theorem gbd_optimal_reply_of_minimum (d : ModelData n m l r) (y : IntVector m)
    (hy : y ∈ IntegerBox d.lo d.hi) (p : Point n m) (hpy : p.2 = oaIntCast y)
    (hmin : IsMinimizer (d.fixedNonlinearFiber (oaIntCast y)) d.objective p)
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d) :
    ∃ lambda mu, gbdBatchValid d ⟨y,.optimal p lambda mu⟩ := by
  obtain ⟨lambda,mu,hkkt⟩ := exists_fixedNLPKKT d p (gbdBatchDerivative d p)
    hconv (gbdBatch_derivatives d p hdiff) (by simpa [hpy] using hmin)
    (by simpa [hpy] using hCQ y hy ⟨p,hmin.1⟩)
  exact ⟨lambda,mu,hy,hpy,hmin,hkkt⟩

theorem gbd_restoration_reply_of_minimum (d : ModelData n m l r) (y : IntVector m)
    (hy : y ∈ IntegerBox d.lo d.hi) (p : Point n m) (rho : ℝ) (hpy : p.2 = oaIntCast y)
    (hinfeas : ¬ (d.fixedNonlinearFiber (oaIntCast y)).Nonempty)
    (hmin : IsMinimizer (RestorationPairs (d.fixedLinearFiber (oaIntCast y)) d.g)
      Prod.snd (p,rho)) (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) :
    ∃ lambda mu, gbdBatchValid d ⟨y,.restoration p rho lambda mu⟩ := by
  letI : Nonempty (Fin l) := oa_infeasible_fiber_has_rows d (oaIntCast y)
    ⟨p,hmin.1.1⟩ hinfeas
  obtain ⟨lambda,mu,hkkt⟩ := exists_restorationKKT d p rho (gbdBatchDerivative d p)
    hconv (gbdBatch_derivatives d p hdiff) (by simpa [hpy] using hmin)
  exact ⟨lambda,mu,hy,hpy,hinfeas,hmin,hkkt⟩

theorem gbd_fiber_reply_exists (d : ModelData n m l r) (y : IntVector m)
    (hy : y ∈ IntegerBox d.lo d.hi)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hconv : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hdiff : ∀ j, Differentiable ℝ (d.g j)) (hCQ : OAFiberSlater d) :
    ∃ b, gbdBatchValid d b ∧ b.integer = y := by
  by_cases hL : (d.fixedLinearFiber (oaIntCast y)).Nonempty
  · by_cases hN : (d.fixedNonlinearFiber (oaIntCast y)).Nonempty
    · obtain ⟨p,hp⟩ := source_fixedNLP_minimum_attained d y hy hbase hN
        (fun j => (hdiff j).continuous)
      obtain ⟨lambda,mu,hb⟩ := gbd_optimal_reply_of_minimum d y hy p hp.1.1.2 hp hconv hdiff hCQ
      exact ⟨⟨y,.optimal p lambda mu⟩,hb,rfl⟩
    · letI : Nonempty (Fin l) := oa_infeasible_fiber_has_rows d (oaIntCast y) hL hN
      obtain ⟨⟨p,rho⟩,hp⟩ := restorationPairs_minimum_attained
        (source_fixedLinearFiber_compact d y hy hbase) hL (fun j => (hdiff j).continuous)
      obtain ⟨lambda,mu,hb⟩ := gbd_restoration_reply_of_minimum d y hy p rho
        hp.1.1.2 hN hp hconv hdiff
      exact ⟨⟨y,.restoration p rho lambda mu⟩,hb,rfl⟩
  · exact ⟨⟨y,.emptyLinear⟩,⟨hy,hL⟩,rfl⟩

theorem gbd_integer_ne_iff {m : ℕ} (y z : IntVector m) :
    y ≠ z ↔ ∃ i, y i ≤ z i - 1 ∨ z i + 1 ≤ y i := by
  constructor
  · intro h
    classical
    have hn : ∃ i, y i ≠ z i := Function.ne_iff.mp h
    obtain ⟨i,hi⟩ := hn
    exact ⟨i,by omega⟩
  · rintro ⟨i,hi⟩ he
    subst z
    omega

theorem gbd_empty_dimension_no_good (y z : IntVector 0) : ¬ y ≠ z :=
  fun h => h (Subsingleton.elim _ _)

theorem gbd_master_not_compact (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (hne : (gbdMaster d floor H).Nonempty) :
    ¬ IsCompact (gbdMaster d floor H) := by
  rw [gbd_master_eq_epigraph] at hne ⊢
  obtain ⟨z,hz⟩ := hne
  exact nonempty_epigraph_not_compact (show (gbdSurvives d H).Nonempty from ⟨z.1,hz.1⟩)

theorem gbd_unfloored_decrease (d : ModelData n m l r) (H : List (GBDBatch n m l r))
    (hH : ∀ b ∈ H, gbdBatchOptimalAnchor b = none) {z : IntVector m × ℝ}
    (hz : z ∈ gbdMasterUnfloored d H) :
    (z.1,z.2-1) ∈ gbdMasterUnfloored d H := by
  refine ⟨hz.1,?_⟩
  intro b hb
  have hc := hz.2 b hb
  have hn := hH b hb
  cases hp : b.payload with
  | optimal p lambda mu => simp [gbdBatchOptimalAnchor,hp] at hn
  | restoration p rho lambda mu => simpa [gbdBatchConstraint,hp] using hc
  | emptyLinear => simpa [gbdBatchConstraint,hp] using hc

theorem gbd_unfloored_no_minimum (d : ModelData n m l r) (H : List (GBDBatch n m l r))
    (hH : ∀ b ∈ H, gbdBatchOptimalAnchor b = none) :
    ¬ ∃ z, IsMinimizer (gbdMasterUnfloored d H) Prod.snd z := by
  rintro ⟨z,hz⟩
  have h := hz.2 _ (gbd_unfloored_decrease d H hH hz.1)
  dsimp only [Prod.snd] at h
  linarith


theorem gbd_unfloored_eq_floored_of_optimal (d : ModelData n m l r)
    (H : List (GBDBatch n m l r))
    (hopt : ∃ b ∈ H, ∃ p, gbdBatchOptimalAnchor b = some p) :
    ∃ floor, gbdMasterUnfloored d H = gbdMaster d floor H := by
  obtain ⟨b,hb,p,ha⟩ := hopt
  cases hp : b.payload with
  | optimal q lambda mu =>
    let f : IntVector m → ℝ := fun y =>
      anchoredOptimalityCut d q (gbdBatchDerivative d q) lambda mu (oaIntCast y)
    obtain ⟨floor,hfloor⟩ := ((integerBox_finite d.lo d.hi).image f).bddBelow
    refine ⟨floor,?_⟩
    ext z
    constructor
    · intro hz
      have hc : f z.1 ≤ z.2 := by simpa [f,gbdBatchConstraint,hp] using hz.2 b hb
      exact ⟨hz,(hfloor ⟨z.1,hz.1,rfl⟩).trans hc⟩
    · exact fun hz => hz.1
  | restoration q rho lambda mu => simp [gbdBatchOptimalAnchor,hp] at ha
  | emptyLinear => simp [gbdBatchOptimalAnchor,hp] at ha

theorem gbd_unfloored_reply_of_optimal (d : ModelData n m l r)
    (H : List (GBDBatch n m l r))
    (hopt : ∃ b ∈ H, ∃ p, gbdBatchOptimalAnchor b = some p) :
    gbdMasterUnfloored d H = ∅ ∨
      ∃ z, IsMinimizer (gbdMasterUnfloored d H) Prod.snd z := by
  obtain ⟨floor,h⟩ := gbd_unfloored_eq_floored_of_optimal d H hopt
  simpa only [h] using gbd_master_reply d floor H

def gbdBatchOptimalConstraint (d : ModelData n m l r) (b : GBDBatch n m l r)
    (y : RealVector m) (eta : ℝ) : Prop :=
  match b.payload with
  | .optimal p lambda mu => anchoredOptimalityCut d p (gbdBatchDerivative d p) lambda mu y ≤ eta
  | _ => True

def gbdBatchRestorationConstraint (d : ModelData n m l r) (b : GBDBatch n m l r)
    (y : RealVector m) : Prop :=
  match b.payload with
  | .restoration p _ lambda mu => anchoredFeasibilityCut d p (gbdBatchDerivative d p) lambda mu y ≤ 0
  | _ => True

def gbdEmptyExclusions (H : List (GBDBatch n m l r)) (y : RealVector m) : Prop :=
  ∀ b ∈ H, b.payload = .emptyLinear → y ≠ oaIntCast b.integer

def gbdOptimalEntries (d : ModelData n m l r) :
    (H : List (GBDBatch n m l r)) → (∀ b ∈ H, gbdBatchValid d b) → List (OptimalityCutEntry d)
  | [], _ => []
  | b :: H, hH =>
    let tail := gbdOptimalEntries d H (fun c hc => hH c (List.mem_cons_of_mem b hc))
    match hp : b.payload with
    | .optimal p lambda mu =>
      {point := p, derivative := gbdBatchDerivative d p, lambda := lambda, mu := mu,
       rows := Set.univ,
       kkt := by
         have h := (hH b (List.mem_cons_self)).2
         simp only [hp] at h
         exact h.2.2,
       support := fun _ _ => Set.mem_univ _} :: tail
    | _ => tail

def gbdRestorationEntries (d : ModelData n m l r) :
    (H : List (GBDBatch n m l r)) → (∀ b ∈ H, gbdBatchValid d b) → List (RestorationCutEntry d)
  | [], _ => []
  | b :: H, hH =>
    let tail := gbdRestorationEntries d H (fun c hc => hH c (List.mem_cons_of_mem b hc))
    match hp : b.payload with
    | .restoration p rho lambda mu =>
      {point := p, slack := rho, derivative := gbdBatchDerivative d p,
       lambda := lambda, mu := mu, rows := Set.univ,
       kkt := by
         have h := (hH b (List.mem_cons_self)).2
         simp only [hp] at h
         exact h.2.2.2,
       support := fun _ _ => Set.mem_univ _} :: tail
    | _ => tail

theorem gbd_optimal_entries_iff (d : ModelData n m l r)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b)
    (y : RealVector m) (eta : ℝ) :
    (∀ e ∈ gbdOptimalEntries d H hH,
      anchoredOptimalityCut d e.point e.derivative e.lambda e.mu y ≤ eta) ↔
      ∀ b ∈ H, gbdBatchOptimalConstraint d b y eta := by
  induction H with
  | nil => simp [gbdOptimalEntries]
  | cons b H ih =>
    cases b with
    | mk integer payload =>
      cases payload <;> simp [gbdOptimalEntries,gbdBatchOptimalConstraint,ih]

theorem gbd_restoration_entries_iff (d : ModelData n m l r)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b)
    (y : RealVector m) :
    (∀ e ∈ gbdRestorationEntries d H hH,
      anchoredFeasibilityCut d e.point e.derivative e.lambda e.mu y ≤ 0) ↔
      ∀ b ∈ H, gbdBatchRestorationConstraint d b y := by
  induction H with
  | nil => simp [gbdRestorationEntries]
  | cons b H ih =>
    cases b with
    | mk integer payload =>
      cases payload <;> simp [gbdRestorationEntries,gbdBatchRestorationConstraint,ih]

def gbdCommonMaster (d : ModelData n m l r) (H : List (GBDBatch n m l r))
    (hH : ∀ b ∈ H, gbdBatchValid d b) : Set (RealVector m × ℝ) :=
  commonGBDMaster d (gbdOptimalEntries d H hH).get (gbdRestorationEntries d H hH).get

theorem gbd_forall_get_iff {A : Type*} (L : List A) (P : A → Prop) :
    (∀ i, P (L.get i)) ↔ ∀ a ∈ L, P a := by
  constructor
  · intro h a ha
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
    exact h i
  · intro h i
    exact h _ (List.get_mem ..)

theorem gbd_common_master_mem_iff (d : ModelData n m l r)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b)
    (z : RealVector m × ℝ) :
    z ∈ gbdCommonMaster d H hH ↔ z.1 ∈ d.integerValues ∧
      (∀ b ∈ H, gbdBatchOptimalConstraint d b z.1 z.2) ∧
      (∀ b ∈ H, gbdBatchRestorationConstraint d b z.1) := by
  unfold gbdCommonMaster commonGBDMaster
  exact and_congr Iff.rfl (and_congr
    ((gbd_forall_get_iff (gbdOptimalEntries d H hH) (fun e =>
      anchoredOptimalityCut d e.point e.derivative e.lambda e.mu z.1 ≤ z.2)).trans
      (gbd_optimal_entries_iff d H hH z.1 z.2))
    ((gbd_forall_get_iff (gbdRestorationEntries d H hH) (fun e =>
      anchoredFeasibilityCut d e.point e.derivative e.lambda e.mu z.1 ≤ 0)).trans
      (gbd_restoration_entries_iff d H hH z.1)))

theorem gbd_constraints_split (d : ModelData n m l r)
    (H : List (GBDBatch n m l r)) (z : IntVector m × ℝ) :
    (∀ b ∈ H, gbdBatchConstraint d b z) ↔
      (∀ b ∈ H, gbdBatchOptimalConstraint d b (oaIntCast z.1) z.2) ∧
      (∀ b ∈ H, gbdBatchRestorationConstraint d b (oaIntCast z.1)) ∧
      gbdEmptyExclusions H (oaIntCast z.1) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro b hb
      have hc := h b hb
      cases hp : b.payload with
      | optimal p lambda mu => simpa [gbdBatchOptimalConstraint,gbdBatchConstraint,hp] using hc
      | restoration p rho lambda mu => simp [gbdBatchOptimalConstraint,hp]
      | emptyLinear => simp [gbdBatchOptimalConstraint,hp]
    · intro b hb
      have hc := h b hb
      cases hp : b.payload with
      | optimal p lambda mu => simp [gbdBatchRestorationConstraint,hp]
      | restoration p rho lambda mu => simpa [gbdBatchRestorationConstraint,gbdBatchConstraint,hp] using hc
      | emptyLinear => simp [gbdBatchRestorationConstraint,hp]
    · intro b hb hp he
      have hc : z.1 ≠ b.integer := by simpa [gbdBatchConstraint,hp] using h b hb
      exact hc (oaIntCast_injective he)
  · rintro ⟨hO,hF,hE⟩ b hb
    cases hp : b.payload with
    | optimal p lambda mu => simpa [gbdBatchOptimalConstraint,gbdBatchConstraint,hp] using hO b hb
    | restoration p rho lambda mu => simpa [gbdBatchRestorationConstraint,gbdBatchConstraint,hp] using hF b hb
    | emptyLinear =>
      simp only [gbdBatchConstraint,hp]
      intro h
      exact hE b hb hp (congrArg oaIntCast h)

theorem gbd_master_common_iff (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b)
    (z : IntVector m × ℝ) :
    z ∈ gbdMaster d floor H ↔ (oaIntCast z.1,z.2) ∈ gbdCommonMaster d H hH ∧
      floor ≤ z.2 ∧ gbdEmptyExclusions H (oaIntCast z.1) := by
  rw [gbd_master_mem_iff,gbd_common_master_mem_iff,gbd_constraints_split]
  have hi : oaIntCast z.1 ∈ d.integerValues ↔ z.1 ∈ IntegerBox d.lo d.hi := by
    constructor
    · rintro ⟨y,hy,he⟩
      have hh : z.1 = y := oaIntCast_injective he
      simpa [hh] using hy
    · intro h
      exact ⟨z.1,h,rfl⟩
  simp only [Prod.fst,Prod.snd,hi]
  tauto

theorem gbd_master_real_image (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b) :
    (fun z : IntVector m × ℝ => (oaIntCast z.1,z.2)) '' gbdMaster d floor H =
      gbdCommonMaster d H hH ∩ {z | floor ≤ z.2 ∧ gbdEmptyExclusions H z.1} := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (gbd_master_common_iff d floor H hH w).mp hw
  · rintro ⟨hc,hf,hE⟩
    obtain ⟨y,hy,he⟩ := ((gbd_common_master_mem_iff d H hH z).mp hc).1
    refine ⟨(y,z.2),?_,?_⟩
    · apply (gbd_master_common_iff d floor H hH _).mpr
      have hz : (oaIntCast y,z.2) = z := Prod.ext he.symm rfl
      change z.1 = oaIntCast y at he
      change (oaIntCast y,z.2) ∈ gbdCommonMaster d H hH ∧
        floor ≤ z.2 ∧ gbdEmptyExclusions H (oaIntCast y)
      rw [hz, ← he]
      exact ⟨hc,hf,hE⟩
    · exact Prod.ext he.symm rfl

/-- These common-history entries retain every original nonlinear row, including
restoration rows. This is the all-row OA comparison, not the S007 trace. -/
theorem gbd_optimal_entries_all_rows (d : ModelData n m l r)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b) :
    ∀ e ∈ gbdOptimalEntries d H hH, e.rows = Set.univ := by
  induction H with
  | nil => simp [gbdOptimalEntries]
  | cons b H ih =>
    cases b with
    | mk integer payload => cases payload <;> simp [gbdOptimalEntries] <;> exact ih _

theorem gbd_restoration_entries_all_rows (d : ModelData n m l r)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b) :
    ∀ e ∈ gbdRestorationEntries d H hH, e.rows = Set.univ := by
  induction H with
  | nil => simp [gbdRestorationEntries]
  | cons b H ih =>
    cases b with
    | mk integer payload => cases payload <;> simp [gbdRestorationEntries] <;> exact ih _

/-- The all-row common-history OA master has actual continuous variables and
retains L. It is not the S007 violated-restoration-row OA master. -/
def gbdAllRowsOAMaster (d : ModelData n m l r) (H : List (GBDBatch n m l r))
    (hH : ∀ b ∈ H, gbdBatchValid d b) : Set (Point n m × ℝ) :=
  commonOAMaster d (gbdOptimalEntries d H hH).get (gbdRestorationEntries d H hH).get

/-- The stronger base floor is valid on every OA relaxation point. A floor
known only on original feasible points would not justify this comparison. -/
theorem gbd_all_rows_oa_projection (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b)
    (hf : GBDBaseFloorValid d floor) (q : Point n m × ℝ)
    (hq : q ∈ gbdAllRowsOAMaster d H hH) (y : IntVector m)
    (hy : q.1.2 = oaIntCast y) : (y,q.2) ∈ gbdMaster d floor H := by
  apply (gbd_master_common_iff d floor H hH _).mpr
  refine ⟨?_,?_,?_⟩
  · have h := common_master_projection_containment d
      (gbdOptimalEntries d H hH).get (gbdRestorationEntries d H hH).get ⟨q,hq,rfl⟩
    simpa only [gbdCommonMaster, hy] using h
  · exact (hf q.1 ⟨hq.1,hq.2.1⟩).trans hq.2.2.2.2
  · intro b hb hp he
    have h := (hH b hb).2
    simp only [hp] at h
    exact h ⟨q.1,hq.1,hy.trans he⟩

/-- Both minima here are actual attained minima. The comparison is non-strict,
uses one common all-row history, and asserts no iteration-count ordering. -/
theorem gbd_all_rows_oa_minimum_order (d : ModelData n m l r) (floor : ℝ)
    (H : List (GBDBatch n m l r)) (hH : ∀ b ∈ H, gbdBatchValid d b)
    (hf : GBDBaseFloorValid d floor) {oa : Point n m × ℝ} {gbd : IntVector m × ℝ}
    (hoa : IsMinimizer (gbdAllRowsOAMaster d H hH) Prod.snd oa)
    (hgbd : IsMinimizer (gbdMaster d floor H) Prod.snd gbd) : gbd.2 ≤ oa.2 := by
  obtain ⟨y,hy,he⟩ := hoa.1.2.1
  exact hgbd.2 (y,oa.2) (gbd_all_rows_oa_projection d floor H hH hf oa hoa.1 y he)

/-- With no optimality constraint the master ignores height entirely. -/
theorem gbd_unfloored_change_height (d : ModelData n m l r)
    (H : List (GBDBatch n m l r))
    (hH : ∀ b ∈ H, gbdBatchOptimalAnchor b = none) {z : IntVector m × ℝ}
    (hz : z ∈ gbdMasterUnfloored d H) (eta : ℝ) :
    (z.1,eta) ∈ gbdMasterUnfloored d H := by
  refine ⟨hz.1,?_⟩
  intro b hb
  have hc := hz.2 b hb
  have hn := hH b hb
  cases hp : b.payload with
  | optimal p lambda mu => simp [gbdBatchOptimalAnchor,hp] at hn
  | restoration p rho lambda mu => simpa [gbdBatchConstraint,hp] using hc
  | emptyLinear => simpa [gbdBatchConstraint,hp] using hc

/-- Nonempty empty/restoration/exclusion-only histories are genuinely
unbounded below in height, not merely missing an attained minimum. -/
theorem gbd_unfloored_unbounded_below (d : ModelData n m l r)
    (H : List (GBDBatch n m l r))
    (hH : ∀ b ∈ H, gbdBatchOptimalAnchor b = none)
    (hne : (gbdMasterUnfloored d H).Nonempty) (a : ℝ) :
    ∃ z ∈ gbdMasterUnfloored d H, z.2 < a := by
  obtain ⟨z,hz⟩ := hne
  refine ⟨(z.1,a-1),gbd_unfloored_change_height d H hH hz (a-1),?_⟩
  dsimp only [Prod.snd]
  linarith

end Chapter02

#print axioms Chapter02.gbd_master_mem_iff
#print axioms Chapter02.gbd_master_append
#print axioms Chapter02.gbd_height_le_iff
#print axioms Chapter02.gbd_master_height_iff
#print axioms Chapter02.gbd_master_eq_epigraph
#print axioms Chapter02.gbd_survives_finite
#print axioms Chapter02.gbd_master_reply
#print axioms Chapter02.gbd_master_minimizer_height
#print axioms Chapter02.gbd_base_floor_valid
#print axioms Chapter02.gbd_base_floor_exists
#print axioms Chapter02.gbdBatch_derivatives
#print axioms Chapter02.gbdBatch_optimal_original
#print axioms Chapter02.gbdBatch_restoration_positive
#print axioms Chapter02.gbdBatch_processed_lower
#print axioms Chapter02.gbdBatch_constraint_valid
#print axioms Chapter02.gbd_master_contains_feasible
#print axioms Chapter02.gbd_master_lowerBound
#print axioms Chapter02.gbd_source_route_unique
#print axioms Chapter02.gbdBatch_source_route
#print axioms Chapter02.gbdBatch_route_iff
#print axioms Chapter02.gbd_optimal_reply_of_minimum
#print axioms Chapter02.gbd_restoration_reply_of_minimum
#print axioms Chapter02.gbd_fiber_reply_exists
#print axioms Chapter02.gbd_integer_ne_iff
#print axioms Chapter02.gbd_empty_dimension_no_good
#print axioms Chapter02.gbd_master_not_compact
#print axioms Chapter02.gbd_unfloored_decrease
#print axioms Chapter02.gbd_unfloored_no_minimum
#print axioms Chapter02.gbd_unfloored_eq_floored_of_optimal
#print axioms Chapter02.gbd_unfloored_reply_of_optimal
#print axioms Chapter02.gbd_optimal_entries_iff
#print axioms Chapter02.gbd_restoration_entries_iff
#print axioms Chapter02.gbd_forall_get_iff
#print axioms Chapter02.gbd_common_master_mem_iff
#print axioms Chapter02.gbd_constraints_split
#print axioms Chapter02.gbd_master_common_iff
#print axioms Chapter02.gbd_master_real_image
#print axioms Chapter02.gbd_optimal_entries_all_rows
#print axioms Chapter02.gbd_restoration_entries_all_rows
#print axioms Chapter02.gbd_all_rows_oa_projection
#print axioms Chapter02.gbd_all_rows_oa_minimum_order
#print axioms Chapter02.gbd_unfloored_change_height
#print axioms Chapter02.gbd_unfloored_unbounded_below
