module

public import Chapter08

@[expose] public section
noncomputable section
open Chapter08
namespace Chapter08Examples

def orthant : Set (Vec 1) := {z | ∀ i, 0 ≤ z i}
def A (_ : Fin 2) : Vec 1 →ₗ[ℝ] Vec 1 := LinearMap.id
def b (i : Fin 2) : Vec 1 := fun _ => if i=0 then 1 else 2

private noncomputable def __migrationExample_Chapter08Examples_L10_N001 : BinaryConicHull A b (fun _ => orthant) (fun _ => 0) (fun _ => 3) =
    ConicUnion A b (fun _ => orthant) (fun _ => 0) (fun _ => 3) := by
  apply bounded_binary_conic_hull_exact
  intro i j; simp

private noncomputable def __migrationExample_Chapter08Examples_L15_N002 : (fun _ => (3:ℝ)) ∈ ConicUnion A b (fun _ => orthant) (fun _ => 0) (fun _ => 3) := by
  exact ⟨fun _ => ⟨by norm_num, by norm_num⟩, 1, by intro j; norm_num [A,b,orthant]⟩

private noncomputable def __migrationExample_Chapter08Examples_L18_N003 : (fun _ => (0:ℝ)) ∉ ConicUnion A b (fun _ => orthant) (fun _ => 0) (fun _ => 3) := by
  rintro ⟨_, i, hi⟩
  have h := hi 0
  fin_cases i <;> norm_num [A,b,orthant] at h

private noncomputable def __migrationExample_Chapter08Examples_L23_N004 (A0 : Fin 0 → Vec 1 →ₗ[ℝ] Vec 1) (b0 : Fin 0 → Vec 1)
    (K0 : Fin 0 → Set (Vec 1)) :
    BinaryConicHull A0 b0 K0 (fun _ => 0) (fun _ => 1) = ∅ := by
  rw [bounded_binary_conic_hull_exact A0 b0 K0 _ _ (fun i => Fin.elim0 i)]
  ext x
  simp [ConicUnion]

private noncomputable def __migrationExample_Chapter08Examples_L30_N005 : ExpCone 0 0 (-1) ∧ ¬ ExpCone 0 0 1 := by norm_num [ExpCone]
private noncomputable def __migrationExample_Chapter08Examples_L31_N006 : Rotated 0 7 0 := by norm_num [Rotated]
private noncomputable def __migrationExample_Chapter08Examples_L32_N007 (w : ℝ) (h : Rotated 0 7 w) : w=0 := by
  have hsq := h.2.2
  simp only [mul_zero, zero_mul] at hsq
  nlinarith [sq_nonneg w]

end Chapter08Examples
