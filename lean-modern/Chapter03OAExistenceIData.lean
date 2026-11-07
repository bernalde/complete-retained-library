module

public import Chapter03OAExistenceAvailability
public import Chapter03OAExecControlQualifications

@[expose] public section

/-! Explicit article-style adaptation of accepted I. The two former soft Y
bound rows are absent here: Y is hard domain metadata, and only the actual
quadratic constraint is soft. This is a separately defined problem, with exact
relaxation/fiber bridges below, not LICQ for the old all-soft I datum. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec.Controls
namespace Chapter03.OAExec.ArticleI

def model : ModelData 1 1 1 0 where
  g _ := I.data.g 0
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1

def domain : Set P := {p | 0 ≤ p.2 0 ∧ p.2 0 ≤ 1}
def spec : Data 1 1 1 0 where
  model := model
  f := I.objective
  Df _ := I.Df
  Dg p _ := I.Dg p 0
  domain := domain

def bounds : Bounds 1 where
  lower _ := .negInfinity
  upper _ := .posInfinity

def encoding : HardBoundEncoding bounds model where
  valid := by intro i; constructor <;> simp [bounds]
  side := Fin.elim0
  injective := by intro i; exact Fin.elim0 i
  lower_cover := by intro i a h; simp [bounds] at h
  upper_cover := by intro i a h; simp [bounds] at h
  row_spec j := Fin.elim0 j

theorem hard (p : P) : p ∈ model.linearRegion := by intro j; exact Fin.elim0 j

theorem domain_base : spec.domain = (asFP spec).base := by
  ext p
  rw [asFP_base_iff]
  change (0 ≤ p.2 0 ∧ p.2 0 ≤ 1) ↔ p ∈ model.linearRegion ∧
    ∀ j, model.lo j ≤ p.2 j ∧ p.2 j ≤ model.hi j
  constructor
  · intro h
    exact ⟨hard p,by simpa [model,scalar,Fin.forall_fin_one] using h⟩
  · intro h
    simpa [model,scalar,Fin.forall_fin_one] using h.2

theorem domain_convex : Convex ℝ domain := by
  change Convex ℝ spec.domain
  rw [domain_base]
  exact Chapter03.FP.base_convex _

theorem domain_article : spec.domain = articleDomain bounds spec := by
  rw [articleDomain_eq_base bounds spec encoding]
  exact domain_base

theorem objective_C1 : ContDiff ℝ 1 spec.f := I.objective_C1
theorem rows_C1 (j : Fin 1) : ContDiff ℝ 1 (model.g j) := I.rows_C1 0

theorem relaxation_iff (p : P) : p ∈ spec.relaxation ↔
    (p.1 0)^2+7/16 ≤ p.2 0 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  rw [relaxation_mem_iff]
  change ((∀ j : Fin 1, (p.1 0)^2+7/16-p.2 0 ≤ 0) ∧
    p ∈ model.linearRegion ∧ ∀ i : Fin 1, 0 ≤ p.2 i ∧ p.2 i ≤ 1) ↔ _
  simp only [Fin.forall_fin_one, hard, true_and]
  exact and_congr (sub_nonpos) Iff.rfl

theorem relaxation_eq_old : spec.relaxation = I.data.relaxationOn Set.univ := by
  ext p
  exact (relaxation_iff p).trans (I.relaxation p).symm

theorem analytic : Analytic spec where
  convex_f := I.objective_convex.subset (Set.subset_univ _) domain_convex
  convex_g j := (I.row_convex 0).subset (Set.subset_univ _) domain_convex
  derivative_f p _ := I.objective_derivative p
  derivative_g p _ j := I.row_derivative p 0
  original_domain := by
    intro p hp
    exact ((relaxation_iff p).mp (original_subset_relaxation spec hp)).2

theorem relaxation_bounded : Bornology.IsBounded spec.relaxation := by
  rw [relaxation_eq_old]
  exact I.relaxation_compact.isBounded

theorem seed_minimum : IsMinimizer spec.relaxation spec.f I.seed := by
  rw [relaxation_eq_old]
  exact I.seed_minimum

theorem seed_unique {p : P} (hm : IsMinimizer spec.relaxation spec.f p) : p = I.seed := by
  apply I.seed_unique
  rw [relaxation_eq_old] at hm
  change IsMinimizer (I.data.relaxationOn Set.univ) I.objective p at hm
  exact hm

theorem seed_valid : SeedValid spec I.seed :=
  ⟨seed_minimum, by norm_num [spec,domain,I.seed,pt,scalar],I.seed_valid.2.2⟩

theorem fiber_iff (x : V) (b : ℝ) : x ∈ fiber model (scalar b) ↔
    (x 0)^2+7/16 ≤ b := by
  change ((x,scalar b) ∈ model.linearRegion ∧ ∀ j : Fin 1,
    (x 0)^2+7/16-b ≤ 0) ↔ _
  simp [hard,Fin.forall_fin_one]

theorem fiber_eq_old (b : ℝ) (hb : 0 ≤ b ∧ b ≤ 1) :
    fiber model (scalar b) = fiber I.data (scalar b) := by
  ext x
  rw [fiber_iff,I.fiber_membership]
  simp [hb]

theorem zero_fiber_empty : ¬ (fiber model (scalar 0)).Nonempty := by
  rw [fiber_eq_old 0 (by norm_num)]
  exact I.zero_fiber_empty

theorem fixed_minimum : IsMinimizer (fiber model (scalar 1))
    (fiberObjective spec.f (scalar 1)) (scalar (3/4)) := by
  rw [fiber_eq_old 1 (by norm_num)]
  exact I.fixed_minimum

theorem fixed_unique {x : V} (hm : IsMinimizer (fiber model (scalar 1))
    (fiberObjective spec.f (scalar 1)) x) : x = scalar (3/4) := by
  apply I.fixed_unique
  simpa only [fiber_eq_old 1 (by norm_num),spec] using hm

theorem fixed_licq : FixedLICQ model (scalar (3/4)) (scalar 1)
    (spec.Dg (scalar (3/4),scalar 1)) := by
  classical
  let v : Fin 1 → V →L[ℝ] ℝ := fun _ => restrict (I.Dg (pt (3/4) 1) 0)
  have hv : LinearIndependent ℝ v := by
    apply (linearIndependent_unique_iff (v := v)).mpr
    intro he
    have hh := congrArg (fun A : V →L[ℝ] ℝ => A (scalar 1)) he
    norm_num [v,restrict_apply,I.Dg,pt,scalar] at hh
  let index : {i : Fin 1 ⊕ Fin 0 // fixedRows model (scalar 1) i (scalar (3/4)) = 0} → Fin 1 :=
    fun i => Sum.elim id Fin.elim0 i.val
  have hi : Function.Injective index := by
    intro i j _hij
    apply Subtype.ext
    rcases i.val with a | a
    · rcases j.val with b | b
      · exact congrArg Sum.inl (Subsingleton.elim a b)
      · exact Fin.elim0 b
    · exact Fin.elim0 a
  unfold FixedLICQ
  have he : (fun i : {i : Fin 1 ⊕ Fin 0 // fixedRows model (scalar 1) i (scalar (3/4)) = 0} =>
      fixedRowD model (spec.Dg (scalar (3/4),scalar 1)) i.val) = v ∘ index := by
    funext i
    rcases i.val with j | j
    · rfl
    · exact Fin.elim0 j
  rw [he]
  exact hv.comp index hi

theorem all_minima_licq (y : IntVector 1) (hy : y ∈ IntegerBox model.lo model.hi)
    (x : V) (hm : IsMinimizer (fiber model (intCast y))
      (fiberObjective spec.f (intCast y)) x) :
    FixedLICQ model x (intCast y) (spec.Dg (x,intCast y)) := by
  rcases target_cases y hy with rfl | rfl
  · exact False.elim (zero_fiber_empty ⟨x,by simpa using hm.1⟩)
  · have hx : x = scalar (3/4) := fixed_unique (by simpa using hm)
    subst x
    simpa using fixed_licq

theorem assumptions : AvailabilityAssumptions spec :=
  article_availability_assumptions bounds spec encoding analytic domain_article
    relaxation_bounded all_minima_licq

theorem bounds_region : bounds.region = Set.univ := by
  ext x
  simp [Bounds.region,bounds,ExtendedBound.lowerHolds,ExtendedBound.upperHolds]

theorem domain_unbounded : ¬ Bornology.IsBounded domain := by
  intro hb
  obtain ⟨R,hR⟩ := hb.exists_norm_le
  let T := max R 0+1
  have hT : 0 < T := by dsimp [T]; have := le_max_right R 0; linarith
  have hp : pt T 0 ∈ domain := by norm_num [domain,pt,scalar]
  have hn : ‖(pt T 0).1 0‖ ≤ ‖pt T 0‖ :=
    (norm_le_pi_norm (pt T 0).1 0).trans (norm_fst_le _)
  have hh : T ≤ R := by simpa [pt,scalar,Real.norm_eq_abs,abs_of_pos hT] using hn.trans (hR _ hp)
  have := le_max_left R 0
  dsimp [T] at hh
  linarith

end Chapter03.OAExec.ArticleI
