module

public import Chapter03OASoftExecutionAvailability
public import Chapter03OAExistenceIEvents

@[expose] public section

/-! Actual fractional initializer and explicit soft initial replies for the
accepted article-I datum. Zero seed weights are an explicit allowed policy,
not an assertion about solver marginals. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls Chapter03.OAExec Chapter03.OAExec.Controls
open Chapter03.OASoftMaster Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.OASoftExecutionAvailability.Control

abbrev spec := ArticleI.spec

theorem all_rows_nonlinear (j : Fin 1) : j ∈ spec.nonlinear := by
  fin_cases j
  change ¬ AffineRow (I.data.g 0)
  exact (I.row_classification 0).mpr rfl

theorem hard_affine : HardAffineEntailment spec := by
  intro j hj
  exact False.elim (hj (all_rows_nonlinear j))

def initialPolicy : Policy spec [] where
  seedWeight := fun _ => 0
  seed_nonneg := fun _ => le_rfl
  generation := fun i => Fin.elim0 i

@[simp] theorem initial_weight (o : Occurrence (family spec I.seed [])) :
    initialPolicy.weight I.seed o = 0 := by
  have hi : o.1.1 = 0 := Fin.eq_zero _
  simp [Policy.weight,Policy.slotWeight,initialPolicy,hi]

def ray (t : ℝ) : Candidate (family spec I.seed []) :=
  (pt t 1,1-t,fun _ => max (t-1+3/16) 0)

theorem ray_mem (t : ℝ) : ray t ∈ historyMaster spec I.seed [] := by
  refine ⟨ArticleI.hard _,?_,?_,?_,?_,?_⟩
  · exact ⟨target1,target1_mem,by ext i; norm_num [ray,pt,scalar,intCast,target1]⟩
  · exact ⟨by simp [noGoods],trivial⟩
  · intro o
    exact le_max_right _ _
  · intro i
    have hi : i = 0 := Fin.eq_zero _
    subst i
    change I.objective I.seed + I.Df (pt t 1-I.seed) ≤ 1-t
    rw [I.objective_tangent]
    simp [I.objective,pt,scalar]
  · intro o
    have hi : o.1.1 = 0 := Fin.eq_zero _
    have hj : o.1.2 = 0 := Fin.eq_zero _
    change spec.model.g o.1.2 ((family spec I.seed []).origin o.1.1) +
      (family spec I.seed []).derivative o.1.1 o.1.2
        (pt t 1-(family spec I.seed []).origin o.1.1) ≤ max (t-1+3/16) 0
    rw [hi,hj]
    change I.data.g 0 I.seed + I.Dg I.seed 0 (pt t 1-I.seed) ≤ _
    rw [I.seed_row_tangent]
    exact le_max_left _ _

@[simp] theorem ray_cost (t : ℝ) :
    cost (initialPolicy.weight I.seed) (ray t) = 1-t := by
  simp [cost,penalty,initial_weight,ray]

theorem initial_cost_unbounded :
    ¬ BddBelow (cost (initialPolicy.weight I.seed) '' historyMaster spec I.seed []) := by
  rintro ⟨b,hb⟩
  have hh := hb ⟨ray (2-b),ray_mem (2-b),rfl⟩
  rw [ray_cost] at hh
  linarith

def firstPoint : Candidate (family spec I.seed []) := ray (3/4)

theorem firstPoint_mem : firstPoint ∈ historyMaster spec I.seed [] := ray_mem _

theorem firstPoint_target : firstPoint.1.2 = intCast ArticleI.event1.target := by
  simp [firstPoint,ray,ArticleI.event1,pt]

def firstGeneration : Generation spec ArticleI.event1 :=
  generationOfValid hard_affine ArticleI.event1_valid

/-- Even the classically chosen certificate has this nonzero multiplier;
stationarity and the actual derivatives determine it on the one-row fiber. -/
theorem successful_multiplier
    (K : FixedKKT spec.model spec.f ArticleI.event1.x (intCast ArticleI.event1.target)) :
    K.lambda 0 = (2/3 : ℝ) := by
  have hd := ArticleI.event1_valid.1
  have hf : K.Df = spec.Df ArticleI.event1.anchor :=
    K.derivative_f.unique (ArticleI.analytic.derivative_f _ hd)
  have hg : K.Dg 0 = spec.Dg ArticleI.event1.anchor 0 :=
    (K.derivative_g 0).unique (ArticleI.analytic.derivative_g _ hd 0)
  have hs := congrArg (fun A : RealVector 1 →L[ℝ] ℝ => A (scalar 1)) K.stationarity
  simp only [Fin.sum_univ_one,Fin.sum_univ_zero,add_zero,hf,hg] at hs
  norm_num [restrict_apply,spec,ArticleI.spec,ArticleI.event1,Event.anchor,
    I.Df,I.Dg,scalar,pt] at hs
  linarith

theorem first_generation_weight : firstGeneration.rowWeight 0 = (2000/3 : ℝ) := by
  rw [Generation.rowWeight_success firstGeneration (show ArticleI.event1.restoration = none from rfl)]
  rw [successful_multiplier]
  norm_num

theorem fractional_initialization : IsMinimizer spec.relaxation spec.f I.seed ∧
    I.seed ∈ spec.domain ∧ ¬ integral I.seed := ArticleI.seed_valid

theorem first_fixed_gap : (0 : ℝ) < spec.f ArticleI.event1.anchor - spec.f I.seed := by
  norm_num [spec,ArticleI.spec,ArticleI.event1,Event.anchor,I.objective,I.seed,pt,scalar]

end Chapter03.OASoftExecutionAvailability.Control
