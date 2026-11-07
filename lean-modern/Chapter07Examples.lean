module

public import Chapter07
public import Chapter06Examples

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter06 Chapter07
namespace Chapter07Examples

def signedVector : Vec 3 := ![-2,0,3]
private noncomputable def __migrationExample_Chapter07Examples_L10_N001 : l1 signedVector=5 := by norm_num [l1,signedVector,Fin.sum_univ_succ]
private noncomputable def __migrationExample_Chapter07Examples_L11_N002 : l1Canonical (fun _ : Unit => signedVector) () ∈
    L1Lift Set.univ (fun _ : Unit => signedVector) :=
  l1_canonical_feasible _ _ (Set.mem_univ _)
private noncomputable def __migrationExample_Chapter07Examples_L14_N003 : linf signedVector=3 := by
  apply le_antisymm
  · apply (linf_le_iff _ _).mpr; intro i; fin_cases i <;> norm_num [signedVector]
  · calc
      (3 : ℝ) = |signedVector (2 : Fin 3)| := by norm_num [signedVector]
      _ ≤ linf signedVector :=
        Finset.le_sup' (fun i => |signedVector i|) (Finset.mem_univ 2)

def base : Set ℝ := Set.Icc (-2) (-1/2)
def scalarDisplacement (x : ℝ) : Vec 1 := fun _ => x
theorem scalar_l1_minimum : IsMinimizer base (fun x => l1 (scalarDisplacement x)) (-1/2) := by
  refine ⟨by norm_num [base], ?_⟩
  intro x hx
  simp only [l1,scalarDisplacement,Fin.sum_univ_one]
  rw [abs_of_nonpos (by norm_num : (-1/2:ℝ) ≤ 0)]
  have hx' := hx.2
  rw [abs_of_nonpos (by linarith : x ≤ 0)]
  linarith
private noncomputable def __migrationExample_Chapter07Examples_L30_N004 : IsMinimizer (L1Lift base scalarDisplacement) l1LiftCost
    (l1Canonical scalarDisplacement (-1/2)) := l1_minimizer_lift _ _ scalar_l1_minimum

def actualLevel : Set (Point 1 1 × ℝ) := SourceLevel Chapter06Examples.small
  Chapter06Examples.nonlinearObjective Chapter06Examples.origins
  Chapter06Examples.objectiveDerivatives Set.univ (-12) 0 (1/2)

private noncomputable def __migrationExample_Chapter07Examples_L37_N005 : Chapter06Examples.negativeMasterPoint ∈ actualLevel := by
  refine ⟨Chapter06Examples.nonlinear_master_minimizer.1, ?_⟩
  norm_num [Chapter06Examples.negativeMasterPoint,Level]

private noncomputable def __migrationExample_Chapter07Examples_L41_N006 : l1Canonical (sourceDisplacement (fun _ => 0,fun _ => 0))
    Chapter06Examples.negativeMasterPoint ∈
    L1Lift actualLevel (sourceDisplacement (fun _ => 0,fun _ => 0)) := by
  apply l1_canonical_feasible
  refine ⟨Chapter06Examples.nonlinear_master_minimizer.1, ?_⟩
  norm_num [Chapter06Examples.negativeMasterPoint,Level]

def sourceCenter : Point 1 1 := (fun _ => 0,fun _ => 0)
def sourceNormPoint : Point 1 1 × ℝ := ((fun _ => -1/2,fun _ => 0),-6)
theorem source_norm_point_member : sourceNormPoint ∈ actualLevel := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ⟨⟨⟨Set.mem_univ _, ?_⟩, ?_⟩, fun _ => (0:ℤ), ?_, ?_⟩
    · intro i j hj
      have hj0 : j = 0 := by simpa [Chapter06Examples.origins,Chapter02Examples.cuts] using hj
      subst j
      norm_num [Chapter06Examples.small,Chapter02Examples.sample,Chapter06Examples.origins,
        Chapter02Examples.cuts,sourceNormPoint,Chapter02Examples.coordX]
    · intro row; fin_cases row <;> norm_num [Chapter06Examples.small,Chapter02Examples.sample,
        LinearForm,sourceNormPoint,Fin.sum_univ_one]
    · intro i; norm_num [Chapter06Examples.small,Chapter02Examples.sample]
    · norm_num [sourceNormPoint]
  · intro i
    norm_num [Chapter06Examples.nonlinearObjective,Chapter06Examples.objectiveDerivatives,
      Chapter06Examples.origins,Chapter02Examples.cuts,sourceNormPoint,Chapter02Examples.coordX]
  · norm_num [sourceNormPoint,Level]

theorem actual_level_x_upper {p : Point 1 1 × ℝ} (hp : p ∈ actualLevel) : p.1.1 0 ≤ -1/2 := by
  have ho := hp.1.2 0
  have hl := hp.2
  norm_num [Chapter06Examples.nonlinearObjective,Chapter06Examples.objectiveDerivatives,
    Chapter06Examples.origins,Chapter02Examples.cuts,Chapter02Examples.coordX] at ho
  norm_num [Level] at hl
  linarith

theorem source_l1_minimum : IsMinimizer actualLevel
    (fun p => l1 (sourceDisplacement sourceCenter p)) sourceNormPoint := by
  refine ⟨source_norm_point_member, ?_⟩
  intro p hp
  have hx := actual_level_x_upper hp
  have hi : ∀ i : Fin 1, i=0 := fun i => Subsingleton.elim i 0
  simp [l1,sourceDisplacement,sourceCenter,sourceNormPoint,Fin.sum_univ_two,Fin.addCases,hi,abs_div]
  linarith [neg_le_abs (p.1.1 0),abs_nonneg (p.1.2 0)]

theorem source_linf_point_value : linf (sourceDisplacement sourceCenter sourceNormPoint)=1/2 := by
  apply le_antisymm
  · apply (linf_le_iff _ _).mpr
    intro i; fin_cases i <;> norm_num [sourceDisplacement,sourceCenter,sourceNormPoint,Fin.addCases,abs_div]
  · have h := Finset.le_sup' (fun i => |sourceDisplacement sourceCenter sourceNormPoint i|)
      (Finset.mem_univ (Fin.castAdd 1 (0:Fin 1)))
    change |(-1/2:ℝ)-0| ≤ linf (sourceDisplacement sourceCenter sourceNormPoint) at h
    rw [sub_zero] at h
    norm_num [abs_div] at h
    exact h

theorem source_linf_minimum : IsMinimizer actualLevel
    (fun p => linf (sourceDisplacement sourceCenter p)) sourceNormPoint := by
  refine ⟨source_norm_point_member, ?_⟩
  intro p hp
  change linf (sourceDisplacement sourceCenter sourceNormPoint) ≤ linf (sourceDisplacement sourceCenter p)
  rw [source_linf_point_value]
  have hx := actual_level_x_upper hp
  have h := Finset.le_sup' (fun i => |sourceDisplacement sourceCenter p i|)
    (Finset.mem_univ (Fin.castAdd 1 (0:Fin 1)))
  have hh : |p.1.1 0| ≤ linf (sourceDisplacement sourceCenter p) := by
    change |p.1.1 0-0| ≤ linf (sourceDisplacement sourceCenter p) at h
    simpa only [sub_zero] using h
  linarith [neg_le_abs (p.1.1 0)]

private noncomputable def __migrationExample_Chapter07Examples_L109_N007 : IsMinimizer (L1Lift actualLevel (sourceDisplacement sourceCenter)) l1LiftCost
    (l1Canonical (sourceDisplacement sourceCenter) sourceNormPoint) :=
  l1_minimizer_lift _ _ source_l1_minimum
private noncomputable def __migrationExample_Chapter07Examples_L112_N008 : IsMinimizer (LInfLift actualLevel (sourceDisplacement sourceCenter)) Prod.snd
    (sourceNormPoint,linf (sourceDisplacement sourceCenter sourceNormPoint)) :=
  linf_minimizer_lift _ _ source_linf_minimum

private noncomputable def __migrationExample_Chapter07Examples_L116_N009 : IsMinimizer Set.univ (fun z : Vec 2 => ∑ i, ((![(2:ℝ),0]) i*z i+(z i)^2))
    (fun i => -(![(2:ℝ),0]) i/2) := by
  simpa using finite_scaled_center_minimizer (![(2:ℝ),0]) 1 (by norm_num)

private noncomputable def __migrationExample_Chapter07Examples_L120_N010 : ‖(-((2*(‖(3:ℝ)‖/(2*2)))⁻¹)) • (3:ℝ)‖ = 2 :=
  scaled_center_distance _ _ (by norm_num) (by norm_num)

private noncomputable def __migrationExample_Chapter07Examples_L123_N011 : IsLowerBound (Set.univ : Set Bool) (fun y => if y then (1:ℝ) else 0) 0 := by
  have h := processed_remaining_bound (Set.univ : Set Bool) {false}
    (fun y => if y then (1:ℝ) else 0) 0 1
    (by intro y hy; rcases hy.2 with rfl; norm_num)
    (by intro y hy; cases y <;> simp_all)
  simpa using h

end Chapter07Examples
