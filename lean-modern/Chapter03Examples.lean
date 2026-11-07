module

public import Chapter03

@[expose] public section
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03
namespace Chapter03Examples

def vec (a : ℝ) : EuclideanSpace ℝ (Fin 1) := (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm (fun _ => a)
private noncomputable def __migrationExample_Chapter03Examples_L8_N001 (a b : ℝ) : ‖vec a-vec b‖^2 = (a-b)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [vec,Fin.sum_univ_one]

def data : ModelData 0 1 1 0 where
  g := fun _ p => (p.2 0)^2-1/4
  A := fun _ _ => 0
  B := fun _ _ => 0
  rhs := fun _ => 0
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => -1
  hi := fun _ => 1

def pt (a : ℝ) : Point 0 1 := (fun _ => 0,fun _ => a)
private noncomputable def __migrationExample_Chapter03Examples_L24_N002 : pt 0 ∈ data.feasibleOn Set.univ := by
  rw [source_feasible_iff]
  refine ⟨Set.mem_univ _,?_,?_,⟨fun _ => 0,?_,by simp [pt]⟩⟩
  · intro j; norm_num [data,pt]
  · intro row; exact Fin.elim0 row
  · intro i; norm_num [data]
private noncomputable def __migrationExample_Chapter03Examples_L30_N003 : pt (1/2) ∈ data.relaxationOn Set.univ := by
  refine ⟨⟨Set.mem_univ _,?_⟩,?_,?_⟩
  · intro j; norm_num [data,pt]
  · intro row; exact Fin.elim0 row
  · intro i; norm_num [data,pt]

private noncomputable def __migrationExample_Chapter03Examples_L36_N004 : ProjectionMin (projectedSource data Set.univ) (vec 1) (vec (1/2)) := by
  refine ⟨⟨pt (1/2),?_,rfl⟩,?_⟩
  · refine ⟨⟨Set.mem_univ _,?_⟩,?_,?_⟩
    · intro j; norm_num [data,pt]
    · intro row; exact Fin.elim0 row
    · intro i; norm_num [data,pt]
  · rintro w ⟨p,hp,rfl⟩
    have hg := hp.1.2 (0 : Fin 1)
    change (p.2 0)^2-1/4 ≤ 0 at hg
    have he : yMap 0 1 p = vec (p.2 0) := by
      apply (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).injective
      funext i; fin_cases i; rfl
    rw [he]
    simp only [vec,← real_inner_self_eq_norm_sq,PiLp.inner_apply]
    simp [Fin.sum_univ_one,real_inner_eq_re_inner]
    have hupper : p.2 0 ≤ 1/2 := by nlinarith [sq_nonneg (p.2 0-1/2)]
    nlinarith [sq_nonneg (p.2 0-1/2)]

private noncomputable def __migrationExample_Chapter03Examples_L54_N005 : AbsLift 0 4 2 1 1 false := by norm_num [AbsLift,bit]
private noncomputable def __migrationExample_Chapter03Examples_L55_N006 : AbsLift 0 4 2 3 1 true := by norm_num [AbsLift,bit]
private noncomputable def __migrationExample_Chapter03Examples_L56_N007 : AbsLift 0 4 2 2 0 false := by norm_num [AbsLift,bit]
private noncomputable def __migrationExample_Chapter03Examples_L57_N008 : AbsLift 0 4 2 2 0 true := by norm_num [AbsLift,bit]
private noncomputable def __migrationExample_Chapter03Examples_L58_N009 : binaryRow (fun _ : Fin 2 => false) (fun _ => true) = 2 := by
  norm_num [binaryRow,bit,Fin.sum_univ_two]
private noncomputable def __migrationExample_Chapter03Examples_L60_N010 : ¬ (1 ≤ -(1-bit false)) := printed_binary_sign_failure.1
private noncomputable def __migrationExample_Chapter03Examples_L61_N011 : (3:ℝ)-1/10*max |3| 1 = 27/10 := by norm_num
end Chapter03Examples
