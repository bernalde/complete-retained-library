module

public import Chapter06
public import Chapter02ModelExamples

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter06
namespace Chapter06Examples

def nonlinearObjective (p : Point 1 1) : ℝ := (p.1 0)^2
def small : ModelData 1 1 2 2 := {Chapter02Examples.sample with hi := fun _ => 0}
def origins := Chapter02Examples.cuts
def objectiveDerivatives : Fin 1 → Point 1 1 →L[ℝ] ℝ :=
  fun _ => (4 : ℝ) • Chapter02Examples.coordX

theorem objective_convex : ConvexOn ℝ Set.univ nonlinearObjective := by
  have he : nonlinearObjective = (Chapter02Examples.sample.g 0 + fun _ => (1:ℝ)) := by
    funext p; simp [nonlinearObjective,Chapter02Examples.sample,Pi.add_apply]
  rw [he]
  exact (Chapter02Examples.sample_convex 0).add_const 1

theorem objective_derivative : ∀ i, HasFDerivAt nonlinearObjective
    (objectiveDerivatives i) (origins.origin i) := by
  intro i
  have h := (hasDerivAt_pow 2 (2:ℝ)).comp_hasFDerivAt (origins.origin i)
    Chapter02Examples.coordX.hasFDerivAt
  norm_num at h
  unfold nonlinearObjective objectiveDerivatives
  simpa [Chapter02Examples.coordX, Function.comp_def] using h

private noncomputable def __migrationExample_Chapter06Examples_L29_N001 : (fun _ => 0,fun _ => 0) ∈ small.feasibleOn Set.univ := by
  rw [source_feasible_iff]
  refine ⟨Set.mem_univ _, ?_, ?_, fun _ => (0:ℤ), ?_, by norm_num⟩
  · intro j; fin_cases j <;> norm_num [small,Chapter02Examples.sample]
  · intro row; fin_cases row <;> norm_num [small,Chapter02Examples.sample,LinearForm,Fin.sum_univ_one]
  · intro i; norm_num [small,Chapter02Examples.sample]

def negativeMasterPoint : Point 1 1 × ℝ := ((fun _ => -2,fun _ => 0),-12)

theorem nonlinear_master_minimizer : IsMinimizer
    (EpigraphMaster small nonlinearObjective origins objectiveDerivatives Set.univ)
    Prod.snd negativeMasterPoint := by
  constructor
  · constructor
    · refine ⟨⟨⟨Set.mem_univ _, ?_⟩, ?_⟩, fun _ => (0:ℤ), ?_, ?_⟩
      · intro i j hj
        have hj0 : j = 0 := by simpa [origins,Chapter02Examples.cuts] using hj
        subst j
        norm_num [small,Chapter02Examples.sample,origins,Chapter02Examples.cuts,
          negativeMasterPoint,Chapter02Examples.coordX]
      · intro row
        fin_cases row <;> norm_num [small,Chapter02Examples.sample,LinearForm,
          negativeMasterPoint,Fin.sum_univ_one]
      · intro i; norm_num [small,Chapter02Examples.sample]
      · norm_num [negativeMasterPoint]
    · intro i
      norm_num [nonlinearObjective,objectiveDerivatives,origins,Chapter02Examples.cuts,
        negativeMasterPoint,Chapter02Examples.coordX]
  · intro q hq
    have hrow := hq.1.1.2 1
    have hobj := hq.2 0
    norm_num [small,Chapter02Examples.sample,LinearForm,Fin.sum_univ_one] at hrow
    norm_num [nonlinearObjective,objectiveDerivatives,origins,Chapter02Examples.cuts,
      Chapter02Examples.coordX] at hobj
    change (-12 : ℝ) ≤ q.2
    linarith

private noncomputable def __migrationExample_Chapter06Examples_L66_N002 : IsLowerBound (small.feasibleOn Set.univ) nonlinearObjective (-12) :=
  source_epigraph_master_lower_bound small nonlinearObjective origins objectiveDerivatives
    Set.univ (by simpa [small] using Chapter02Examples.sample_convex) objective_convex
    (fun _ => Set.mem_univ _) (by simpa [small,origins] using Chapter02Examples.sample_derivative)
    objective_derivative nonlinear_master_minimizer

private noncomputable def __migrationExample_Chapter06Examples_L72_N003 (d μ : ℝ) (hbound : -1 ≤ d ∧ d ≤ 3) (hcut : -2*d ≤ 0) (hobj : d ≤ μ) :
    0 ≤ μ := by
  apply fixed_fiber_kkt_master_lower_bound (n:=1) (l:=1) (r:=2) 0 μ
    (fun _ => 1) (fun _ => 0) (fun _ _ => -2)
    (fun row => if row=0 then -3 else -1) (fun row _ => if row=0 then 1 else -1)
    (fun _ => 1/2) (fun _ => 0) (fun _ => d)
  · intro j; norm_num
  · intro row; norm_num
  · intro j; norm_num
  · intro row; norm_num
  · intro i; norm_num [Fin.sum_univ_one]
  · intro j _; simpa [dotProduct,Fin.sum_univ_one] using hcut
  · intro row; fin_cases row <;> norm_num [dotProduct,Fin.sum_univ_one] <;> linarith [hbound.1,hbound.2]
  · simpa [dotProduct,Fin.sum_univ_one] using hobj

private noncomputable def __migrationExample_Chapter06Examples_L87_N004 (d : ℝ) (hbound : -1 ≤ d ∧ d ≤ 1) : ¬ ((1/2 : ℝ) ≤ 0) := by
  let v : Fin 1 → ℝ := fun _ => 1/2
  let gg : Fin 1 → Fin 1 → ℝ := fun _ _ => 0
  let b : Fin 2 → ℝ := fun _ => -1
  let A : Fin 2 → Fin 1 → ℝ := fun row _ => if row=0 then 1 else -1
  let lam : Fin 1 → ℝ := fun _ => 1
  let gamma : Fin 2 → ℝ := fun _ => 0
  let delta : Fin 1 → ℝ := fun _ => d
  have hlam : ∀ j, 0 ≤ lam j := by intro j; norm_num [lam]
  have hgamma : ∀ row, 0 ≤ gamma row := by intro row; norm_num [gamma]
  have hsum : ∑ j, lam j = 1 := by norm_num [lam,Fin.sum_univ_one]
  have hcompg : ∀ j, lam j*(v j-(1/2 : ℝ)) = 0 := by intro j; norm_num [lam,v]
  have hcompl : ∀ row, gamma row*b row = 0 := by intro row; norm_num [gamma]
  have hs : ∀ i, (∑ j, lam j*gg j i)+(∑ row, gamma row*A row i) = 0 := by
    intro i; simp [lam,gg,gamma]
  have hl : ∀ row, b row+A row ⬝ᵥ delta ≤ 0 := by
    intro row; fin_cases row <;> norm_num [b,A,delta,dotProduct,Fin.sum_univ_one]
    all_goals linarith [hbound.1,hbound.2]
  intro hc
  exact restoration_rows_exclude_fiber (1/2) (by norm_num) v gg b A lam gamma delta
    hlam hgamma hsum hcompg hcompl hs
    (by intro j _; simpa [v,gg,delta,dotProduct,Fin.sum_univ_one] using hc) hl

private noncomputable def __migrationExample_Chapter06Examples_L110_N005 : IsMinimizer toyLevel toyDistance toyA := toy_projection_A_optimal
private noncomputable def __migrationExample_Chapter06Examples_L111_N006 : ¬ IsMinimizer toyTrust toyCost toyA := toy_projection_A_not_trust_optimal
private noncomputable def __migrationExample_Chapter06Examples_L112_N007 : (Level 0 4 (1/2 : ℝ)) = 2 := by norm_num [Level]

end Chapter06Examples
